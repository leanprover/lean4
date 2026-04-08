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
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Core_checkSystem___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__19___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "transform"};
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__19___closed__0 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__19___closed__0_value;
static const lean_closure_object l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__19___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_checkSystem___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__19___closed__0_value)} };
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__19___closed__1 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__19___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ExprStructEq_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0_value;
static const lean_closure_object l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ExprStructEq_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__8(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__9(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__10(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__11(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__12(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__12___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__13(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__13___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__14(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__13___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__19___closed__0_value)} };
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14___closed__0 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__19(lean_object* v_inst_203_, lean_object* v_x_204_, lean_object* v___x_205_, lean_object* v___x_206_, lean_object* v_inst_207_, lean_object* v___f_208_, lean_object* v___x_209_, lean_object* v___x_210_, lean_object* v_a_211_, lean_object* v_toBind_212_, lean_object* v___f_213_, lean_object* v_toApplicative_214_, lean_object* v_a_215_){
_start:
{
if (lean_obj_tag(v_a_215_) == 0)
{
lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_2445__overap_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
lean_dec_ref(v_toApplicative_214_);
v___x_216_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__19___closed__1));
v___x_217_ = lean_apply_2(v_inst_203_, lean_box(0), v___x_216_);
lean_inc_ref(v___x_206_);
lean_inc_ref(v___x_205_);
v___x_218_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonadLift___aux__1___boxed), 10, 9);
lean_closure_set(v___x_218_, 0, lean_box(0));
lean_closure_set(v___x_218_, 1, lean_box(0));
lean_closure_set(v___x_218_, 2, lean_box(0));
lean_closure_set(v___x_218_, 3, lean_box(0));
lean_closure_set(v___x_218_, 4, v_x_204_);
lean_closure_set(v___x_218_, 5, v___x_205_);
lean_closure_set(v___x_218_, 6, v___x_206_);
lean_closure_set(v___x_218_, 7, lean_box(0));
lean_closure_set(v___x_218_, 8, v___x_217_);
v___x_219_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonad___aux__13___boxed), 13, 12);
lean_closure_set(v___x_219_, 0, lean_box(0));
lean_closure_set(v___x_219_, 1, lean_box(0));
lean_closure_set(v___x_219_, 2, lean_box(0));
lean_closure_set(v___x_219_, 3, lean_box(0));
lean_closure_set(v___x_219_, 4, v_x_204_);
lean_closure_set(v___x_219_, 5, v___x_205_);
lean_closure_set(v___x_219_, 6, v___x_206_);
lean_closure_set(v___x_219_, 7, v_inst_207_);
lean_closure_set(v___x_219_, 8, lean_box(0));
lean_closure_set(v___x_219_, 9, lean_box(0));
lean_closure_set(v___x_219_, 10, v___x_218_);
lean_closure_set(v___x_219_, 11, v___f_208_);
v___x_2445__overap_220_ = l_Lean_Core_withIncRecDepth___redArg(v___x_209_, v___x_210_, v___x_219_);
lean_inc(v_a_211_);
v___x_221_ = lean_apply_1(v___x_2445__overap_220_, v_a_211_);
v___x_222_ = lean_apply_4(v_toBind_212_, lean_box(0), lean_box(0), v___x_221_, v___f_213_);
return v___x_222_;
}
else
{
lean_object* v_val_223_; lean_object* v_toPure_224_; lean_object* v___x_225_; 
lean_dec(v___f_213_);
lean_dec(v_toBind_212_);
lean_dec_ref(v___x_210_);
lean_dec_ref(v___x_209_);
lean_dec(v___f_208_);
lean_dec_ref(v_inst_207_);
lean_dec_ref(v___x_206_);
lean_dec_ref(v___x_205_);
lean_dec(v_inst_203_);
v_val_223_ = lean_ctor_get(v_a_215_, 0);
lean_inc(v_val_223_);
lean_dec_ref(v_a_215_);
v_toPure_224_ = lean_ctor_get(v_toApplicative_214_, 1);
lean_inc(v_toPure_224_);
lean_dec_ref(v_toApplicative_214_);
v___x_225_ = lean_apply_2(v_toPure_224_, lean_box(0), v_val_223_);
return v___x_225_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__19___boxed(lean_object* v_inst_226_, lean_object* v_x_227_, lean_object* v___x_228_, lean_object* v___x_229_, lean_object* v_inst_230_, lean_object* v___f_231_, lean_object* v___x_232_, lean_object* v___x_233_, lean_object* v_a_234_, lean_object* v_toBind_235_, lean_object* v___f_236_, lean_object* v_toApplicative_237_, lean_object* v_a_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__19(v_inst_226_, v_x_227_, v___x_228_, v___x_229_, v_inst_230_, v___f_231_, v___x_232_, v___x_233_, v_a_234_, v_toBind_235_, v___f_236_, v_toApplicative_237_, v_a_238_);
lean_dec(v_a_234_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__4(lean_object* v_a_242_, lean_object* v_inst_243_, lean_object* v_inst_244_, lean_object* v_inst_245_, lean_object* v_pre_246_, lean_object* v_post_247_, lean_object* v_x_248_, lean_object* v_x_249_, lean_object* v___y_250_, lean_object* v_a_251_){
_start:
{
lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_252_ = l_Lean_mkAppN(v_a_242_, v_a_251_);
v___x_253_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_243_, v_inst_244_, v_inst_245_, v_pre_246_, v_post_247_, v_x_248_, v_x_249_, v___x_252_, v___y_250_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__4___boxed(lean_object* v_a_254_, lean_object* v_inst_255_, lean_object* v_inst_256_, lean_object* v_inst_257_, lean_object* v_pre_258_, lean_object* v_post_259_, lean_object* v_x_260_, lean_object* v_x_261_, lean_object* v___y_262_, lean_object* v_a_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__4(v_a_254_, v_inst_255_, v_inst_256_, v_inst_257_, v_pre_258_, v_post_259_, v_x_260_, v_x_261_, v___y_262_, v_a_263_);
lean_dec_ref(v_a_263_);
lean_dec(v___y_262_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___boxed(lean_object* v_inst_265_, lean_object* v_inst_266_, lean_object* v_inst_267_, lean_object* v_pre_268_, lean_object* v_post_269_, lean_object* v_x_270_, lean_object* v_x_271_, lean_object* v_e_272_, lean_object* v_a_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_265_, v_inst_266_, v_inst_267_, v_pre_268_, v_post_269_, v_x_270_, v_x_271_, v_e_272_, v_a_273_);
lean_dec(v_a_273_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__5(lean_object* v_inst_275_, lean_object* v_inst_276_, lean_object* v_inst_277_, lean_object* v_pre_278_, lean_object* v_post_279_, lean_object* v_x_280_, lean_object* v_x_281_, lean_object* v___y_282_, lean_object* v_args_283_, lean_object* v___x_284_, lean_object* v_toBind_285_, lean_object* v_a_286_){
_start:
{
lean_object* v___f_287_; lean_object* v___x_288_; size_t v_sz_289_; size_t v___x_290_; lean_object* v___x_2175__overap_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
lean_inc_n(v___y_282_, 2);
lean_inc(v_x_281_);
lean_inc(v_post_279_);
lean_inc(v_pre_278_);
lean_inc_ref(v_inst_277_);
lean_inc(v_inst_276_);
lean_inc_ref(v_inst_275_);
v___f_287_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__4___boxed), 10, 9);
lean_closure_set(v___f_287_, 0, v_a_286_);
lean_closure_set(v___f_287_, 1, v_inst_275_);
lean_closure_set(v___f_287_, 2, v_inst_276_);
lean_closure_set(v___f_287_, 3, v_inst_277_);
lean_closure_set(v___f_287_, 4, v_pre_278_);
lean_closure_set(v___f_287_, 5, v_post_279_);
lean_closure_set(v___f_287_, 6, v_x_280_);
lean_closure_set(v___f_287_, 7, v_x_281_);
lean_closure_set(v___f_287_, 8, v___y_282_);
v___x_288_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___boxed), 9, 7);
lean_closure_set(v___x_288_, 0, v_inst_275_);
lean_closure_set(v___x_288_, 1, v_inst_276_);
lean_closure_set(v___x_288_, 2, v_inst_277_);
lean_closure_set(v___x_288_, 3, v_pre_278_);
lean_closure_set(v___x_288_, 4, v_post_279_);
lean_closure_set(v___x_288_, 5, v_x_280_);
lean_closure_set(v___x_288_, 6, v_x_281_);
v_sz_289_ = lean_array_size(v_args_283_);
v___x_290_ = ((size_t)0ULL);
v___x_2175__overap_291_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_284_, v___x_288_, v_sz_289_, v___x_290_, v_args_283_);
v___x_292_ = lean_apply_1(v___x_2175__overap_291_, v___y_282_);
v___x_293_ = lean_apply_4(v_toBind_285_, lean_box(0), lean_box(0), v___x_292_, v___f_287_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__5___boxed(lean_object* v_inst_294_, lean_object* v_inst_295_, lean_object* v_inst_296_, lean_object* v_pre_297_, lean_object* v_post_298_, lean_object* v_x_299_, lean_object* v_x_300_, lean_object* v___y_301_, lean_object* v_args_302_, lean_object* v___x_303_, lean_object* v_toBind_304_, lean_object* v_a_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__5(v_inst_294_, v_inst_295_, v_inst_296_, v_pre_297_, v_post_298_, v_x_299_, v_x_300_, v___y_301_, v_args_302_, v___x_303_, v_toBind_304_, v_a_305_);
lean_dec(v___y_301_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__6(lean_object* v_inst_307_, lean_object* v_inst_308_, lean_object* v_inst_309_, lean_object* v_pre_310_, lean_object* v_post_311_, lean_object* v_x_312_, lean_object* v_x_313_, lean_object* v___x_314_, lean_object* v_toBind_315_, lean_object* v_f_316_, lean_object* v_args_317_, lean_object* v___y_318_){
_start:
{
lean_object* v___f_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
lean_inc(v_toBind_315_);
lean_inc(v___y_318_);
lean_inc(v_x_313_);
lean_inc(v_post_311_);
lean_inc(v_pre_310_);
lean_inc_ref(v_inst_309_);
lean_inc(v_inst_308_);
lean_inc_ref(v_inst_307_);
v___f_319_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__5___boxed), 12, 11);
lean_closure_set(v___f_319_, 0, v_inst_307_);
lean_closure_set(v___f_319_, 1, v_inst_308_);
lean_closure_set(v___f_319_, 2, v_inst_309_);
lean_closure_set(v___f_319_, 3, v_pre_310_);
lean_closure_set(v___f_319_, 4, v_post_311_);
lean_closure_set(v___f_319_, 5, v_x_312_);
lean_closure_set(v___f_319_, 6, v_x_313_);
lean_closure_set(v___f_319_, 7, v___y_318_);
lean_closure_set(v___f_319_, 8, v_args_317_);
lean_closure_set(v___f_319_, 9, v___x_314_);
lean_closure_set(v___f_319_, 10, v_toBind_315_);
v___x_320_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_307_, v_inst_308_, v_inst_309_, v_pre_310_, v_post_311_, v_x_312_, v_x_313_, v_f_316_, v___y_318_);
v___x_321_ = lean_apply_4(v_toBind_315_, lean_box(0), lean_box(0), v___x_320_, v___f_319_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__6___boxed(lean_object* v_inst_322_, lean_object* v_inst_323_, lean_object* v_inst_324_, lean_object* v_pre_325_, lean_object* v_post_326_, lean_object* v_x_327_, lean_object* v_x_328_, lean_object* v___x_329_, lean_object* v_toBind_330_, lean_object* v_f_331_, lean_object* v_args_332_, lean_object* v___y_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__6(v_inst_322_, v_inst_323_, v_inst_324_, v_pre_325_, v_post_326_, v_x_327_, v_x_328_, v___x_329_, v_toBind_330_, v_f_331_, v_args_332_, v___y_333_);
lean_dec(v___y_333_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__7___boxed(lean_object* v_inst_335_, lean_object* v_inst_336_, lean_object* v_inst_337_, lean_object* v_pre_338_, lean_object* v_post_339_, lean_object* v_x_340_, lean_object* v_x_341_, lean_object* v___y_342_, lean_object* v_a_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__7(v_inst_335_, v_inst_336_, v_inst_337_, v_pre_338_, v_post_339_, v_x_340_, v_x_341_, v___y_342_, v_a_343_);
lean_dec(v___y_342_);
return v_res_344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__8(lean_object* v_binderName_345_, lean_object* v_a_346_, uint8_t v_binderInfo_347_, lean_object* v_inst_348_, lean_object* v_inst_349_, lean_object* v_inst_350_, lean_object* v_pre_351_, lean_object* v_post_352_, lean_object* v_x_353_, lean_object* v_x_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v_binderType_357_, lean_object* v_body_358_, lean_object* v_a_359_){
_start:
{
uint8_t v___y_361_; size_t v___x_368_; size_t v___x_369_; uint8_t v___x_370_; 
v___x_368_ = lean_ptr_addr(v_binderType_357_);
v___x_369_ = lean_ptr_addr(v_a_346_);
v___x_370_ = lean_usize_dec_eq(v___x_368_, v___x_369_);
if (v___x_370_ == 0)
{
v___y_361_ = v___x_370_;
goto v___jp_360_;
}
else
{
size_t v___x_371_; size_t v___x_372_; uint8_t v___x_373_; 
v___x_371_ = lean_ptr_addr(v_body_358_);
v___x_372_ = lean_ptr_addr(v_a_359_);
v___x_373_ = lean_usize_dec_eq(v___x_371_, v___x_372_);
v___y_361_ = v___x_373_;
goto v___jp_360_;
}
v___jp_360_:
{
if (v___y_361_ == 0)
{
lean_object* v___x_362_; lean_object* v___x_363_; 
lean_dec_ref(v___y_356_);
v___x_362_ = l_Lean_Expr_forallE___override(v_binderName_345_, v_a_346_, v_a_359_, v_binderInfo_347_);
v___x_363_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_348_, v_inst_349_, v_inst_350_, v_pre_351_, v_post_352_, v_x_353_, v_x_354_, v___x_362_, v___y_355_);
return v___x_363_;
}
else
{
uint8_t v___x_364_; 
v___x_364_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_347_, v_binderInfo_347_);
if (v___x_364_ == 0)
{
lean_object* v___x_365_; lean_object* v___x_366_; 
lean_dec_ref(v___y_356_);
v___x_365_ = l_Lean_Expr_forallE___override(v_binderName_345_, v_a_346_, v_a_359_, v_binderInfo_347_);
v___x_366_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_348_, v_inst_349_, v_inst_350_, v_pre_351_, v_post_352_, v_x_353_, v_x_354_, v___x_365_, v___y_355_);
return v___x_366_;
}
else
{
lean_object* v___x_367_; 
lean_dec_ref(v_a_359_);
lean_dec_ref(v_a_346_);
lean_dec(v_binderName_345_);
v___x_367_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_348_, v_inst_349_, v_inst_350_, v_pre_351_, v_post_352_, v_x_353_, v_x_354_, v___y_356_, v___y_355_);
return v___x_367_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__8___boxed(lean_object* v_binderName_374_, lean_object* v_a_375_, lean_object* v_binderInfo_376_, lean_object* v_inst_377_, lean_object* v_inst_378_, lean_object* v_inst_379_, lean_object* v_pre_380_, lean_object* v_post_381_, lean_object* v_x_382_, lean_object* v_x_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v_binderType_386_, lean_object* v_body_387_, lean_object* v_a_388_){
_start:
{
uint8_t v_binderInfo_2768__boxed_389_; lean_object* v_res_390_; 
v_binderInfo_2768__boxed_389_ = lean_unbox(v_binderInfo_376_);
v_res_390_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__8(v_binderName_374_, v_a_375_, v_binderInfo_2768__boxed_389_, v_inst_377_, v_inst_378_, v_inst_379_, v_pre_380_, v_post_381_, v_x_382_, v_x_383_, v___y_384_, v___y_385_, v_binderType_386_, v_body_387_, v_a_388_);
lean_dec_ref(v_body_387_);
lean_dec_ref(v_binderType_386_);
lean_dec(v___y_384_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__9(lean_object* v_binderName_391_, uint8_t v_binderInfo_392_, lean_object* v_inst_393_, lean_object* v_inst_394_, lean_object* v_inst_395_, lean_object* v_pre_396_, lean_object* v_post_397_, lean_object* v_x_398_, lean_object* v_x_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v_binderType_402_, lean_object* v_body_403_, lean_object* v_toBind_404_, lean_object* v_a_405_){
_start:
{
lean_object* v___x_406_; lean_object* v___f_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_406_ = lean_box(v_binderInfo_392_);
lean_inc_ref(v_body_403_);
lean_inc(v___y_400_);
lean_inc(v_x_399_);
lean_inc(v_post_397_);
lean_inc(v_pre_396_);
lean_inc_ref(v_inst_395_);
lean_inc(v_inst_394_);
lean_inc_ref(v_inst_393_);
v___f_407_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__8___boxed), 15, 14);
lean_closure_set(v___f_407_, 0, v_binderName_391_);
lean_closure_set(v___f_407_, 1, v_a_405_);
lean_closure_set(v___f_407_, 2, v___x_406_);
lean_closure_set(v___f_407_, 3, v_inst_393_);
lean_closure_set(v___f_407_, 4, v_inst_394_);
lean_closure_set(v___f_407_, 5, v_inst_395_);
lean_closure_set(v___f_407_, 6, v_pre_396_);
lean_closure_set(v___f_407_, 7, v_post_397_);
lean_closure_set(v___f_407_, 8, v_x_398_);
lean_closure_set(v___f_407_, 9, v_x_399_);
lean_closure_set(v___f_407_, 10, v___y_400_);
lean_closure_set(v___f_407_, 11, v___y_401_);
lean_closure_set(v___f_407_, 12, v_binderType_402_);
lean_closure_set(v___f_407_, 13, v_body_403_);
v___x_408_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_393_, v_inst_394_, v_inst_395_, v_pre_396_, v_post_397_, v_x_398_, v_x_399_, v_body_403_, v___y_400_);
v___x_409_ = lean_apply_4(v_toBind_404_, lean_box(0), lean_box(0), v___x_408_, v___f_407_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__9___boxed(lean_object* v_binderName_410_, lean_object* v_binderInfo_411_, lean_object* v_inst_412_, lean_object* v_inst_413_, lean_object* v_inst_414_, lean_object* v_pre_415_, lean_object* v_post_416_, lean_object* v_x_417_, lean_object* v_x_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v_binderType_421_, lean_object* v_body_422_, lean_object* v_toBind_423_, lean_object* v_a_424_){
_start:
{
uint8_t v_binderInfo_2629__boxed_425_; lean_object* v_res_426_; 
v_binderInfo_2629__boxed_425_ = lean_unbox(v_binderInfo_411_);
v_res_426_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__9(v_binderName_410_, v_binderInfo_2629__boxed_425_, v_inst_412_, v_inst_413_, v_inst_414_, v_pre_415_, v_post_416_, v_x_417_, v_x_418_, v___y_419_, v___y_420_, v_binderType_421_, v_body_422_, v_toBind_423_, v_a_424_);
lean_dec(v___y_419_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__10(lean_object* v_binderName_427_, lean_object* v_a_428_, uint8_t v_binderInfo_429_, lean_object* v_inst_430_, lean_object* v_inst_431_, lean_object* v_inst_432_, lean_object* v_pre_433_, lean_object* v_post_434_, lean_object* v_x_435_, lean_object* v_x_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v_binderType_439_, lean_object* v_body_440_, lean_object* v_a_441_){
_start:
{
uint8_t v___y_443_; size_t v___x_450_; size_t v___x_451_; uint8_t v___x_452_; 
v___x_450_ = lean_ptr_addr(v_binderType_439_);
v___x_451_ = lean_ptr_addr(v_a_428_);
v___x_452_ = lean_usize_dec_eq(v___x_450_, v___x_451_);
if (v___x_452_ == 0)
{
v___y_443_ = v___x_452_;
goto v___jp_442_;
}
else
{
size_t v___x_453_; size_t v___x_454_; uint8_t v___x_455_; 
v___x_453_ = lean_ptr_addr(v_body_440_);
v___x_454_ = lean_ptr_addr(v_a_441_);
v___x_455_ = lean_usize_dec_eq(v___x_453_, v___x_454_);
v___y_443_ = v___x_455_;
goto v___jp_442_;
}
v___jp_442_:
{
if (v___y_443_ == 0)
{
lean_object* v___x_444_; lean_object* v___x_445_; 
lean_dec_ref(v___y_438_);
v___x_444_ = l_Lean_Expr_lam___override(v_binderName_427_, v_a_428_, v_a_441_, v_binderInfo_429_);
v___x_445_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_430_, v_inst_431_, v_inst_432_, v_pre_433_, v_post_434_, v_x_435_, v_x_436_, v___x_444_, v___y_437_);
return v___x_445_;
}
else
{
uint8_t v___x_446_; 
v___x_446_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_429_, v_binderInfo_429_);
if (v___x_446_ == 0)
{
lean_object* v___x_447_; lean_object* v___x_448_; 
lean_dec_ref(v___y_438_);
v___x_447_ = l_Lean_Expr_lam___override(v_binderName_427_, v_a_428_, v_a_441_, v_binderInfo_429_);
v___x_448_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_430_, v_inst_431_, v_inst_432_, v_pre_433_, v_post_434_, v_x_435_, v_x_436_, v___x_447_, v___y_437_);
return v___x_448_;
}
else
{
lean_object* v___x_449_; 
lean_dec_ref(v_a_441_);
lean_dec_ref(v_a_428_);
lean_dec(v_binderName_427_);
v___x_449_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_430_, v_inst_431_, v_inst_432_, v_pre_433_, v_post_434_, v_x_435_, v_x_436_, v___y_438_, v___y_437_);
return v___x_449_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__10___boxed(lean_object* v_binderName_456_, lean_object* v_a_457_, lean_object* v_binderInfo_458_, lean_object* v_inst_459_, lean_object* v_inst_460_, lean_object* v_inst_461_, lean_object* v_pre_462_, lean_object* v_post_463_, lean_object* v_x_464_, lean_object* v_x_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v_binderType_468_, lean_object* v_body_469_, lean_object* v_a_470_){
_start:
{
uint8_t v_binderInfo_2743__boxed_471_; lean_object* v_res_472_; 
v_binderInfo_2743__boxed_471_ = lean_unbox(v_binderInfo_458_);
v_res_472_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__10(v_binderName_456_, v_a_457_, v_binderInfo_2743__boxed_471_, v_inst_459_, v_inst_460_, v_inst_461_, v_pre_462_, v_post_463_, v_x_464_, v_x_465_, v___y_466_, v___y_467_, v_binderType_468_, v_body_469_, v_a_470_);
lean_dec_ref(v_body_469_);
lean_dec_ref(v_binderType_468_);
lean_dec(v___y_466_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__11(lean_object* v_binderName_473_, uint8_t v_binderInfo_474_, lean_object* v_inst_475_, lean_object* v_inst_476_, lean_object* v_inst_477_, lean_object* v_pre_478_, lean_object* v_post_479_, lean_object* v_x_480_, lean_object* v_x_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v_binderType_484_, lean_object* v_body_485_, lean_object* v_toBind_486_, lean_object* v_a_487_){
_start:
{
lean_object* v___x_488_; lean_object* v___f_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_488_ = lean_box(v_binderInfo_474_);
lean_inc_ref(v_body_485_);
lean_inc(v___y_482_);
lean_inc(v_x_481_);
lean_inc(v_post_479_);
lean_inc(v_pre_478_);
lean_inc_ref(v_inst_477_);
lean_inc(v_inst_476_);
lean_inc_ref(v_inst_475_);
v___f_489_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__10___boxed), 15, 14);
lean_closure_set(v___f_489_, 0, v_binderName_473_);
lean_closure_set(v___f_489_, 1, v_a_487_);
lean_closure_set(v___f_489_, 2, v___x_488_);
lean_closure_set(v___f_489_, 3, v_inst_475_);
lean_closure_set(v___f_489_, 4, v_inst_476_);
lean_closure_set(v___f_489_, 5, v_inst_477_);
lean_closure_set(v___f_489_, 6, v_pre_478_);
lean_closure_set(v___f_489_, 7, v_post_479_);
lean_closure_set(v___f_489_, 8, v_x_480_);
lean_closure_set(v___f_489_, 9, v_x_481_);
lean_closure_set(v___f_489_, 10, v___y_482_);
lean_closure_set(v___f_489_, 11, v___y_483_);
lean_closure_set(v___f_489_, 12, v_binderType_484_);
lean_closure_set(v___f_489_, 13, v_body_485_);
v___x_490_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_475_, v_inst_476_, v_inst_477_, v_pre_478_, v_post_479_, v_x_480_, v_x_481_, v_body_485_, v___y_482_);
v___x_491_ = lean_apply_4(v_toBind_486_, lean_box(0), lean_box(0), v___x_490_, v___f_489_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__11___boxed(lean_object* v_binderName_492_, lean_object* v_binderInfo_493_, lean_object* v_inst_494_, lean_object* v_inst_495_, lean_object* v_inst_496_, lean_object* v_pre_497_, lean_object* v_post_498_, lean_object* v_x_499_, lean_object* v_x_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v_binderType_503_, lean_object* v_body_504_, lean_object* v_toBind_505_, lean_object* v_a_506_){
_start:
{
uint8_t v_binderInfo_2575__boxed_507_; lean_object* v_res_508_; 
v_binderInfo_2575__boxed_507_ = lean_unbox(v_binderInfo_493_);
v_res_508_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__11(v_binderName_492_, v_binderInfo_2575__boxed_507_, v_inst_494_, v_inst_495_, v_inst_496_, v_pre_497_, v_post_498_, v_x_499_, v_x_500_, v___y_501_, v___y_502_, v_binderType_503_, v_body_504_, v_toBind_505_, v_a_506_);
lean_dec(v___y_501_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__12(lean_object* v_declName_509_, lean_object* v_a_510_, lean_object* v_a_511_, uint8_t v_nondep_512_, lean_object* v_inst_513_, lean_object* v_inst_514_, lean_object* v_inst_515_, lean_object* v_pre_516_, lean_object* v_post_517_, lean_object* v_x_518_, lean_object* v_x_519_, lean_object* v___y_520_, lean_object* v_body_521_, lean_object* v___y_522_, lean_object* v_type_523_, lean_object* v_value_524_, lean_object* v_a_525_){
_start:
{
uint8_t v___y_527_; size_t v___x_536_; size_t v___x_537_; uint8_t v___x_538_; 
v___x_536_ = lean_ptr_addr(v_type_523_);
v___x_537_ = lean_ptr_addr(v_a_510_);
v___x_538_ = lean_usize_dec_eq(v___x_536_, v___x_537_);
if (v___x_538_ == 0)
{
v___y_527_ = v___x_538_;
goto v___jp_526_;
}
else
{
size_t v___x_539_; size_t v___x_540_; uint8_t v___x_541_; 
v___x_539_ = lean_ptr_addr(v_value_524_);
v___x_540_ = lean_ptr_addr(v_a_511_);
v___x_541_ = lean_usize_dec_eq(v___x_539_, v___x_540_);
v___y_527_ = v___x_541_;
goto v___jp_526_;
}
v___jp_526_:
{
if (v___y_527_ == 0)
{
lean_object* v___x_528_; lean_object* v___x_529_; 
lean_dec_ref(v___y_522_);
v___x_528_ = l_Lean_Expr_letE___override(v_declName_509_, v_a_510_, v_a_511_, v_a_525_, v_nondep_512_);
v___x_529_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_513_, v_inst_514_, v_inst_515_, v_pre_516_, v_post_517_, v_x_518_, v_x_519_, v___x_528_, v___y_520_);
return v___x_529_;
}
else
{
size_t v___x_530_; size_t v___x_531_; uint8_t v___x_532_; 
v___x_530_ = lean_ptr_addr(v_body_521_);
v___x_531_ = lean_ptr_addr(v_a_525_);
v___x_532_ = lean_usize_dec_eq(v___x_530_, v___x_531_);
if (v___x_532_ == 0)
{
lean_object* v___x_533_; lean_object* v___x_534_; 
lean_dec_ref(v___y_522_);
v___x_533_ = l_Lean_Expr_letE___override(v_declName_509_, v_a_510_, v_a_511_, v_a_525_, v_nondep_512_);
v___x_534_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_513_, v_inst_514_, v_inst_515_, v_pre_516_, v_post_517_, v_x_518_, v_x_519_, v___x_533_, v___y_520_);
return v___x_534_;
}
else
{
lean_object* v___x_535_; 
lean_dec_ref(v_a_525_);
lean_dec_ref(v_a_511_);
lean_dec_ref(v_a_510_);
lean_dec(v_declName_509_);
v___x_535_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_513_, v_inst_514_, v_inst_515_, v_pre_516_, v_post_517_, v_x_518_, v_x_519_, v___y_522_, v___y_520_);
return v___x_535_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__12___boxed(lean_object** _args){
lean_object* v_declName_542_ = _args[0];
lean_object* v_a_543_ = _args[1];
lean_object* v_a_544_ = _args[2];
lean_object* v_nondep_545_ = _args[3];
lean_object* v_inst_546_ = _args[4];
lean_object* v_inst_547_ = _args[5];
lean_object* v_inst_548_ = _args[6];
lean_object* v_pre_549_ = _args[7];
lean_object* v_post_550_ = _args[8];
lean_object* v_x_551_ = _args[9];
lean_object* v_x_552_ = _args[10];
lean_object* v___y_553_ = _args[11];
lean_object* v_body_554_ = _args[12];
lean_object* v___y_555_ = _args[13];
lean_object* v_type_556_ = _args[14];
lean_object* v_value_557_ = _args[15];
lean_object* v_a_558_ = _args[16];
_start:
{
uint8_t v_nondep_2793__boxed_559_; lean_object* v_res_560_; 
v_nondep_2793__boxed_559_ = lean_unbox(v_nondep_545_);
v_res_560_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__12(v_declName_542_, v_a_543_, v_a_544_, v_nondep_2793__boxed_559_, v_inst_546_, v_inst_547_, v_inst_548_, v_pre_549_, v_post_550_, v_x_551_, v_x_552_, v___y_553_, v_body_554_, v___y_555_, v_type_556_, v_value_557_, v_a_558_);
lean_dec_ref(v_value_557_);
lean_dec_ref(v_type_556_);
lean_dec_ref(v_body_554_);
lean_dec(v___y_553_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__13(lean_object* v_declName_561_, lean_object* v_a_562_, uint8_t v_nondep_563_, lean_object* v_inst_564_, lean_object* v_inst_565_, lean_object* v_inst_566_, lean_object* v_pre_567_, lean_object* v_post_568_, lean_object* v_x_569_, lean_object* v_x_570_, lean_object* v___y_571_, lean_object* v_body_572_, lean_object* v___y_573_, lean_object* v_type_574_, lean_object* v_value_575_, lean_object* v_toBind_576_, lean_object* v_a_577_){
_start:
{
lean_object* v___x_578_; lean_object* v___f_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_578_ = lean_box(v_nondep_563_);
lean_inc_ref(v_body_572_);
lean_inc(v___y_571_);
lean_inc(v_x_570_);
lean_inc(v_post_568_);
lean_inc(v_pre_567_);
lean_inc_ref(v_inst_566_);
lean_inc(v_inst_565_);
lean_inc_ref(v_inst_564_);
v___f_579_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__12___boxed), 17, 16);
lean_closure_set(v___f_579_, 0, v_declName_561_);
lean_closure_set(v___f_579_, 1, v_a_562_);
lean_closure_set(v___f_579_, 2, v_a_577_);
lean_closure_set(v___f_579_, 3, v___x_578_);
lean_closure_set(v___f_579_, 4, v_inst_564_);
lean_closure_set(v___f_579_, 5, v_inst_565_);
lean_closure_set(v___f_579_, 6, v_inst_566_);
lean_closure_set(v___f_579_, 7, v_pre_567_);
lean_closure_set(v___f_579_, 8, v_post_568_);
lean_closure_set(v___f_579_, 9, v_x_569_);
lean_closure_set(v___f_579_, 10, v_x_570_);
lean_closure_set(v___f_579_, 11, v___y_571_);
lean_closure_set(v___f_579_, 12, v_body_572_);
lean_closure_set(v___f_579_, 13, v___y_573_);
lean_closure_set(v___f_579_, 14, v_type_574_);
lean_closure_set(v___f_579_, 15, v_value_575_);
v___x_580_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_564_, v_inst_565_, v_inst_566_, v_pre_567_, v_post_568_, v_x_569_, v_x_570_, v_body_572_, v___y_571_);
v___x_581_ = lean_apply_4(v_toBind_576_, lean_box(0), lean_box(0), v___x_580_, v___f_579_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__13___boxed(lean_object** _args){
lean_object* v_declName_582_ = _args[0];
lean_object* v_a_583_ = _args[1];
lean_object* v_nondep_584_ = _args[2];
lean_object* v_inst_585_ = _args[3];
lean_object* v_inst_586_ = _args[4];
lean_object* v_inst_587_ = _args[5];
lean_object* v_pre_588_ = _args[6];
lean_object* v_post_589_ = _args[7];
lean_object* v_x_590_ = _args[8];
lean_object* v_x_591_ = _args[9];
lean_object* v___y_592_ = _args[10];
lean_object* v_body_593_ = _args[11];
lean_object* v___y_594_ = _args[12];
lean_object* v_type_595_ = _args[13];
lean_object* v_value_596_ = _args[14];
lean_object* v_toBind_597_ = _args[15];
lean_object* v_a_598_ = _args[16];
_start:
{
uint8_t v_nondep_2589__boxed_599_; lean_object* v_res_600_; 
v_nondep_2589__boxed_599_ = lean_unbox(v_nondep_584_);
v_res_600_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__13(v_declName_582_, v_a_583_, v_nondep_2589__boxed_599_, v_inst_585_, v_inst_586_, v_inst_587_, v_pre_588_, v_post_589_, v_x_590_, v_x_591_, v___y_592_, v_body_593_, v___y_594_, v_type_595_, v_value_596_, v_toBind_597_, v_a_598_);
lean_dec(v___y_592_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__14(lean_object* v_declName_601_, uint8_t v_nondep_602_, lean_object* v_inst_603_, lean_object* v_inst_604_, lean_object* v_inst_605_, lean_object* v_pre_606_, lean_object* v_post_607_, lean_object* v_x_608_, lean_object* v_x_609_, lean_object* v___y_610_, lean_object* v_body_611_, lean_object* v___y_612_, lean_object* v_type_613_, lean_object* v_value_614_, lean_object* v_toBind_615_, lean_object* v_a_616_){
_start:
{
lean_object* v___x_617_; lean_object* v___f_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_617_ = lean_box(v_nondep_602_);
lean_inc(v_toBind_615_);
lean_inc_ref(v_value_614_);
lean_inc(v___y_610_);
lean_inc(v_x_609_);
lean_inc(v_post_607_);
lean_inc(v_pre_606_);
lean_inc_ref(v_inst_605_);
lean_inc(v_inst_604_);
lean_inc_ref(v_inst_603_);
v___f_618_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__13___boxed), 17, 16);
lean_closure_set(v___f_618_, 0, v_declName_601_);
lean_closure_set(v___f_618_, 1, v_a_616_);
lean_closure_set(v___f_618_, 2, v___x_617_);
lean_closure_set(v___f_618_, 3, v_inst_603_);
lean_closure_set(v___f_618_, 4, v_inst_604_);
lean_closure_set(v___f_618_, 5, v_inst_605_);
lean_closure_set(v___f_618_, 6, v_pre_606_);
lean_closure_set(v___f_618_, 7, v_post_607_);
lean_closure_set(v___f_618_, 8, v_x_608_);
lean_closure_set(v___f_618_, 9, v_x_609_);
lean_closure_set(v___f_618_, 10, v___y_610_);
lean_closure_set(v___f_618_, 11, v_body_611_);
lean_closure_set(v___f_618_, 12, v___y_612_);
lean_closure_set(v___f_618_, 13, v_type_613_);
lean_closure_set(v___f_618_, 14, v_value_614_);
lean_closure_set(v___f_618_, 15, v_toBind_615_);
v___x_619_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_603_, v_inst_604_, v_inst_605_, v_pre_606_, v_post_607_, v_x_608_, v_x_609_, v_value_614_, v___y_610_);
v___x_620_ = lean_apply_4(v_toBind_615_, lean_box(0), lean_box(0), v___x_619_, v___f_618_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__14___boxed(lean_object* v_declName_621_, lean_object* v_nondep_622_, lean_object* v_inst_623_, lean_object* v_inst_624_, lean_object* v_inst_625_, lean_object* v_pre_626_, lean_object* v_post_627_, lean_object* v_x_628_, lean_object* v_x_629_, lean_object* v___y_630_, lean_object* v_body_631_, lean_object* v___y_632_, lean_object* v_type_633_, lean_object* v_value_634_, lean_object* v_toBind_635_, lean_object* v_a_636_){
_start:
{
uint8_t v_nondep_2604__boxed_637_; lean_object* v_res_638_; 
v_nondep_2604__boxed_637_ = lean_unbox(v_nondep_622_);
v_res_638_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__14(v_declName_621_, v_nondep_2604__boxed_637_, v_inst_623_, v_inst_624_, v_inst_625_, v_pre_626_, v_post_627_, v_x_628_, v_x_629_, v___y_630_, v_body_631_, v___y_632_, v_type_633_, v_value_634_, v_toBind_635_, v_a_636_);
lean_dec(v___y_630_);
return v_res_638_;
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0(void){
_start:
{
lean_object* v___x_639_; lean_object* v_dummy_640_; 
v___x_639_ = lean_box(0);
v_dummy_640_ = l_Lean_Expr_sort___override(v___x_639_);
return v_dummy_640_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__15(lean_object* v_expr_641_, lean_object* v_data_642_, lean_object* v_inst_643_, lean_object* v_inst_644_, lean_object* v_inst_645_, lean_object* v_pre_646_, lean_object* v_post_647_, lean_object* v_x_648_, lean_object* v_x_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v_a_652_){
_start:
{
size_t v___x_653_; size_t v___x_654_; uint8_t v___x_655_; 
v___x_653_ = lean_ptr_addr(v_expr_641_);
v___x_654_ = lean_ptr_addr(v_a_652_);
v___x_655_ = lean_usize_dec_eq(v___x_653_, v___x_654_);
if (v___x_655_ == 0)
{
lean_object* v___x_656_; lean_object* v___x_657_; 
lean_dec_ref(v___y_651_);
v___x_656_ = l_Lean_Expr_mdata___override(v_data_642_, v_a_652_);
v___x_657_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_643_, v_inst_644_, v_inst_645_, v_pre_646_, v_post_647_, v_x_648_, v_x_649_, v___x_656_, v___y_650_);
return v___x_657_;
}
else
{
lean_object* v___x_658_; 
lean_dec_ref(v_a_652_);
lean_dec(v_data_642_);
v___x_658_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_643_, v_inst_644_, v_inst_645_, v_pre_646_, v_post_647_, v_x_648_, v_x_649_, v___y_651_, v___y_650_);
return v___x_658_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__15___boxed(lean_object* v_expr_659_, lean_object* v_data_660_, lean_object* v_inst_661_, lean_object* v_inst_662_, lean_object* v_inst_663_, lean_object* v_pre_664_, lean_object* v_post_665_, lean_object* v_x_666_, lean_object* v_x_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v_a_670_){
_start:
{
lean_object* v_res_671_; 
v_res_671_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__15(v_expr_659_, v_data_660_, v_inst_661_, v_inst_662_, v_inst_663_, v_pre_664_, v_post_665_, v_x_666_, v_x_667_, v___y_668_, v___y_669_, v_a_670_);
lean_dec(v___y_668_);
lean_dec_ref(v_expr_659_);
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__16(lean_object* v_struct_672_, lean_object* v_typeName_673_, lean_object* v_idx_674_, lean_object* v_inst_675_, lean_object* v_inst_676_, lean_object* v_inst_677_, lean_object* v_pre_678_, lean_object* v_post_679_, lean_object* v_x_680_, lean_object* v_x_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v_a_684_){
_start:
{
size_t v___x_685_; size_t v___x_686_; uint8_t v___x_687_; 
v___x_685_ = lean_ptr_addr(v_struct_672_);
v___x_686_ = lean_ptr_addr(v_a_684_);
v___x_687_ = lean_usize_dec_eq(v___x_685_, v___x_686_);
if (v___x_687_ == 0)
{
lean_object* v___x_688_; lean_object* v___x_689_; 
lean_dec_ref(v___y_683_);
v___x_688_ = l_Lean_Expr_proj___override(v_typeName_673_, v_idx_674_, v_a_684_);
v___x_689_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_675_, v_inst_676_, v_inst_677_, v_pre_678_, v_post_679_, v_x_680_, v_x_681_, v___x_688_, v___y_682_);
return v___x_689_;
}
else
{
lean_object* v___x_690_; 
lean_dec_ref(v_a_684_);
lean_dec(v_idx_674_);
lean_dec(v_typeName_673_);
v___x_690_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_675_, v_inst_676_, v_inst_677_, v_pre_678_, v_post_679_, v_x_680_, v_x_681_, v___y_683_, v___y_682_);
return v___x_690_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__16___boxed(lean_object* v_struct_691_, lean_object* v_typeName_692_, lean_object* v_idx_693_, lean_object* v_inst_694_, lean_object* v_inst_695_, lean_object* v_inst_696_, lean_object* v_pre_697_, lean_object* v_post_698_, lean_object* v_x_699_, lean_object* v_x_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v_a_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__16(v_struct_691_, v_typeName_692_, v_idx_693_, v_inst_694_, v_inst_695_, v_inst_696_, v_pre_697_, v_post_698_, v_x_699_, v_x_700_, v___y_701_, v___y_702_, v_a_703_);
lean_dec(v___y_701_);
lean_dec_ref(v_struct_691_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17(lean_object* v_toApplicative_705_, lean_object* v_inst_706_, lean_object* v_inst_707_, lean_object* v_inst_708_, lean_object* v_pre_709_, lean_object* v_post_710_, lean_object* v_x_711_, lean_object* v_x_712_, lean_object* v___y_713_, lean_object* v_toBind_714_, lean_object* v___f_715_, lean_object* v___f_716_, lean_object* v_e_717_, lean_object* v_a_718_){
_start:
{
lean_object* v___y_720_; 
switch(lean_obj_tag(v_a_718_))
{
case 0:
{
lean_object* v_e_765_; lean_object* v_toPure_766_; lean_object* v___x_767_; 
lean_dec_ref(v_e_717_);
lean_dec(v___f_716_);
lean_dec(v___f_715_);
lean_dec(v_toBind_714_);
lean_dec(v_x_712_);
lean_dec(v_post_710_);
lean_dec(v_pre_709_);
lean_dec_ref(v_inst_708_);
lean_dec(v_inst_707_);
lean_dec_ref(v_inst_706_);
v_e_765_ = lean_ctor_get(v_a_718_, 0);
lean_inc_ref(v_e_765_);
lean_dec_ref(v_a_718_);
v_toPure_766_ = lean_ctor_get(v_toApplicative_705_, 1);
lean_inc(v_toPure_766_);
lean_dec_ref(v_toApplicative_705_);
v___x_767_ = lean_apply_2(v_toPure_766_, lean_box(0), v_e_765_);
return v___x_767_;
}
case 1:
{
lean_object* v_e_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
lean_dec_ref(v_e_717_);
lean_dec(v___f_716_);
lean_dec_ref(v_toApplicative_705_);
v_e_768_ = lean_ctor_get(v_a_718_, 0);
lean_inc_ref(v_e_768_);
lean_dec_ref(v_a_718_);
v___x_769_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_706_, v_inst_707_, v_inst_708_, v_pre_709_, v_post_710_, v_x_711_, v_x_712_, v_e_768_, v___y_713_);
v___x_770_ = lean_apply_4(v_toBind_714_, lean_box(0), lean_box(0), v___x_769_, v___f_715_);
return v___x_770_;
}
default: 
{
lean_object* v_e_x3f_771_; 
lean_dec(v___f_715_);
lean_dec_ref(v_toApplicative_705_);
v_e_x3f_771_ = lean_ctor_get(v_a_718_, 0);
lean_inc(v_e_x3f_771_);
lean_dec_ref(v_a_718_);
if (lean_obj_tag(v_e_x3f_771_) == 0)
{
v___y_720_ = v_e_717_;
goto v___jp_719_;
}
else
{
lean_object* v_val_772_; 
lean_dec_ref(v_e_717_);
v_val_772_ = lean_ctor_get(v_e_x3f_771_, 0);
lean_inc(v_val_772_);
lean_dec_ref(v_e_x3f_771_);
v___y_720_ = v_val_772_;
goto v___jp_719_;
}
}
}
v___jp_719_:
{
switch(lean_obj_tag(v___y_720_))
{
case 7:
{
lean_object* v_binderName_721_; lean_object* v_binderType_722_; lean_object* v_body_723_; uint8_t v_binderInfo_724_; lean_object* v___x_725_; lean_object* v___f_726_; lean_object* v___x_727_; lean_object* v___x_728_; 
lean_dec(v___f_716_);
v_binderName_721_ = lean_ctor_get(v___y_720_, 0);
lean_inc(v_binderName_721_);
v_binderType_722_ = lean_ctor_get(v___y_720_, 1);
lean_inc_ref_n(v_binderType_722_, 2);
v_body_723_ = lean_ctor_get(v___y_720_, 2);
lean_inc_ref(v_body_723_);
v_binderInfo_724_ = lean_ctor_get_uint8(v___y_720_, sizeof(void*)*3 + 8);
v___x_725_ = lean_box(v_binderInfo_724_);
lean_inc(v_toBind_714_);
lean_inc(v___y_713_);
lean_inc(v_x_712_);
lean_inc(v_post_710_);
lean_inc(v_pre_709_);
lean_inc_ref(v_inst_708_);
lean_inc(v_inst_707_);
lean_inc_ref(v_inst_706_);
v___f_726_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__9___boxed), 15, 14);
lean_closure_set(v___f_726_, 0, v_binderName_721_);
lean_closure_set(v___f_726_, 1, v___x_725_);
lean_closure_set(v___f_726_, 2, v_inst_706_);
lean_closure_set(v___f_726_, 3, v_inst_707_);
lean_closure_set(v___f_726_, 4, v_inst_708_);
lean_closure_set(v___f_726_, 5, v_pre_709_);
lean_closure_set(v___f_726_, 6, v_post_710_);
lean_closure_set(v___f_726_, 7, v_x_711_);
lean_closure_set(v___f_726_, 8, v_x_712_);
lean_closure_set(v___f_726_, 9, v___y_713_);
lean_closure_set(v___f_726_, 10, v___y_720_);
lean_closure_set(v___f_726_, 11, v_binderType_722_);
lean_closure_set(v___f_726_, 12, v_body_723_);
lean_closure_set(v___f_726_, 13, v_toBind_714_);
v___x_727_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_706_, v_inst_707_, v_inst_708_, v_pre_709_, v_post_710_, v_x_711_, v_x_712_, v_binderType_722_, v___y_713_);
v___x_728_ = lean_apply_4(v_toBind_714_, lean_box(0), lean_box(0), v___x_727_, v___f_726_);
return v___x_728_;
}
case 6:
{
lean_object* v_binderName_729_; lean_object* v_binderType_730_; lean_object* v_body_731_; uint8_t v_binderInfo_732_; lean_object* v___x_733_; lean_object* v___f_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
lean_dec(v___f_716_);
v_binderName_729_ = lean_ctor_get(v___y_720_, 0);
lean_inc(v_binderName_729_);
v_binderType_730_ = lean_ctor_get(v___y_720_, 1);
lean_inc_ref_n(v_binderType_730_, 2);
v_body_731_ = lean_ctor_get(v___y_720_, 2);
lean_inc_ref(v_body_731_);
v_binderInfo_732_ = lean_ctor_get_uint8(v___y_720_, sizeof(void*)*3 + 8);
v___x_733_ = lean_box(v_binderInfo_732_);
lean_inc(v_toBind_714_);
lean_inc(v___y_713_);
lean_inc(v_x_712_);
lean_inc(v_post_710_);
lean_inc(v_pre_709_);
lean_inc_ref(v_inst_708_);
lean_inc(v_inst_707_);
lean_inc_ref(v_inst_706_);
v___f_734_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__11___boxed), 15, 14);
lean_closure_set(v___f_734_, 0, v_binderName_729_);
lean_closure_set(v___f_734_, 1, v___x_733_);
lean_closure_set(v___f_734_, 2, v_inst_706_);
lean_closure_set(v___f_734_, 3, v_inst_707_);
lean_closure_set(v___f_734_, 4, v_inst_708_);
lean_closure_set(v___f_734_, 5, v_pre_709_);
lean_closure_set(v___f_734_, 6, v_post_710_);
lean_closure_set(v___f_734_, 7, v_x_711_);
lean_closure_set(v___f_734_, 8, v_x_712_);
lean_closure_set(v___f_734_, 9, v___y_713_);
lean_closure_set(v___f_734_, 10, v___y_720_);
lean_closure_set(v___f_734_, 11, v_binderType_730_);
lean_closure_set(v___f_734_, 12, v_body_731_);
lean_closure_set(v___f_734_, 13, v_toBind_714_);
v___x_735_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_706_, v_inst_707_, v_inst_708_, v_pre_709_, v_post_710_, v_x_711_, v_x_712_, v_binderType_730_, v___y_713_);
v___x_736_ = lean_apply_4(v_toBind_714_, lean_box(0), lean_box(0), v___x_735_, v___f_734_);
return v___x_736_;
}
case 8:
{
lean_object* v_declName_737_; lean_object* v_type_738_; lean_object* v_value_739_; lean_object* v_body_740_; uint8_t v_nondep_741_; lean_object* v___x_742_; lean_object* v___f_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
lean_dec(v___f_716_);
v_declName_737_ = lean_ctor_get(v___y_720_, 0);
lean_inc(v_declName_737_);
v_type_738_ = lean_ctor_get(v___y_720_, 1);
lean_inc_ref_n(v_type_738_, 2);
v_value_739_ = lean_ctor_get(v___y_720_, 2);
lean_inc_ref(v_value_739_);
v_body_740_ = lean_ctor_get(v___y_720_, 3);
lean_inc_ref(v_body_740_);
v_nondep_741_ = lean_ctor_get_uint8(v___y_720_, sizeof(void*)*4 + 8);
v___x_742_ = lean_box(v_nondep_741_);
lean_inc(v_toBind_714_);
lean_inc(v___y_713_);
lean_inc(v_x_712_);
lean_inc(v_post_710_);
lean_inc(v_pre_709_);
lean_inc_ref(v_inst_708_);
lean_inc(v_inst_707_);
lean_inc_ref(v_inst_706_);
v___f_743_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__14___boxed), 16, 15);
lean_closure_set(v___f_743_, 0, v_declName_737_);
lean_closure_set(v___f_743_, 1, v___x_742_);
lean_closure_set(v___f_743_, 2, v_inst_706_);
lean_closure_set(v___f_743_, 3, v_inst_707_);
lean_closure_set(v___f_743_, 4, v_inst_708_);
lean_closure_set(v___f_743_, 5, v_pre_709_);
lean_closure_set(v___f_743_, 6, v_post_710_);
lean_closure_set(v___f_743_, 7, v_x_711_);
lean_closure_set(v___f_743_, 8, v_x_712_);
lean_closure_set(v___f_743_, 9, v___y_713_);
lean_closure_set(v___f_743_, 10, v_body_740_);
lean_closure_set(v___f_743_, 11, v___y_720_);
lean_closure_set(v___f_743_, 12, v_type_738_);
lean_closure_set(v___f_743_, 13, v_value_739_);
lean_closure_set(v___f_743_, 14, v_toBind_714_);
v___x_744_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_706_, v_inst_707_, v_inst_708_, v_pre_709_, v_post_710_, v_x_711_, v_x_712_, v_type_738_, v___y_713_);
v___x_745_ = lean_apply_4(v_toBind_714_, lean_box(0), lean_box(0), v___x_744_, v___f_743_);
return v___x_745_;
}
case 5:
{
lean_object* v_dummy_746_; lean_object* v_nargs_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_2405__overap_751_; lean_object* v___x_752_; 
lean_dec(v_toBind_714_);
lean_dec(v_x_712_);
lean_dec(v_post_710_);
lean_dec(v_pre_709_);
lean_dec_ref(v_inst_708_);
lean_dec(v_inst_707_);
lean_dec_ref(v_inst_706_);
v_dummy_746_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_747_ = l_Lean_Expr_getAppNumArgs(v___y_720_);
lean_inc(v_nargs_747_);
v___x_748_ = lean_mk_array(v_nargs_747_, v_dummy_746_);
v___x_749_ = lean_unsigned_to_nat(1u);
v___x_750_ = lean_nat_sub(v_nargs_747_, v___x_749_);
lean_dec(v_nargs_747_);
v___x_2405__overap_751_ = l_Lean_Expr_withAppAux___redArg(v___f_716_, v___y_720_, v___x_748_, v___x_750_);
lean_inc(v___y_713_);
v___x_752_ = lean_apply_1(v___x_2405__overap_751_, v___y_713_);
return v___x_752_;
}
case 10:
{
lean_object* v_data_753_; lean_object* v_expr_754_; lean_object* v___f_755_; lean_object* v___x_756_; lean_object* v___x_757_; 
lean_dec(v___f_716_);
v_data_753_ = lean_ctor_get(v___y_720_, 0);
lean_inc(v_data_753_);
v_expr_754_ = lean_ctor_get(v___y_720_, 1);
lean_inc_ref_n(v_expr_754_, 2);
lean_inc(v___y_713_);
lean_inc(v_x_712_);
lean_inc(v_post_710_);
lean_inc(v_pre_709_);
lean_inc_ref(v_inst_708_);
lean_inc(v_inst_707_);
lean_inc_ref(v_inst_706_);
v___f_755_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__15___boxed), 12, 11);
lean_closure_set(v___f_755_, 0, v_expr_754_);
lean_closure_set(v___f_755_, 1, v_data_753_);
lean_closure_set(v___f_755_, 2, v_inst_706_);
lean_closure_set(v___f_755_, 3, v_inst_707_);
lean_closure_set(v___f_755_, 4, v_inst_708_);
lean_closure_set(v___f_755_, 5, v_pre_709_);
lean_closure_set(v___f_755_, 6, v_post_710_);
lean_closure_set(v___f_755_, 7, v_x_711_);
lean_closure_set(v___f_755_, 8, v_x_712_);
lean_closure_set(v___f_755_, 9, v___y_713_);
lean_closure_set(v___f_755_, 10, v___y_720_);
v___x_756_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_706_, v_inst_707_, v_inst_708_, v_pre_709_, v_post_710_, v_x_711_, v_x_712_, v_expr_754_, v___y_713_);
v___x_757_ = lean_apply_4(v_toBind_714_, lean_box(0), lean_box(0), v___x_756_, v___f_755_);
return v___x_757_;
}
case 11:
{
lean_object* v_typeName_758_; lean_object* v_idx_759_; lean_object* v_struct_760_; lean_object* v___f_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
lean_dec(v___f_716_);
v_typeName_758_ = lean_ctor_get(v___y_720_, 0);
lean_inc(v_typeName_758_);
v_idx_759_ = lean_ctor_get(v___y_720_, 1);
lean_inc(v_idx_759_);
v_struct_760_ = lean_ctor_get(v___y_720_, 2);
lean_inc_ref_n(v_struct_760_, 2);
lean_inc(v___y_713_);
lean_inc(v_x_712_);
lean_inc(v_post_710_);
lean_inc(v_pre_709_);
lean_inc_ref(v_inst_708_);
lean_inc(v_inst_707_);
lean_inc_ref(v_inst_706_);
v___f_761_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__16___boxed), 13, 12);
lean_closure_set(v___f_761_, 0, v_struct_760_);
lean_closure_set(v___f_761_, 1, v_typeName_758_);
lean_closure_set(v___f_761_, 2, v_idx_759_);
lean_closure_set(v___f_761_, 3, v_inst_706_);
lean_closure_set(v___f_761_, 4, v_inst_707_);
lean_closure_set(v___f_761_, 5, v_inst_708_);
lean_closure_set(v___f_761_, 6, v_pre_709_);
lean_closure_set(v___f_761_, 7, v_post_710_);
lean_closure_set(v___f_761_, 8, v_x_711_);
lean_closure_set(v___f_761_, 9, v_x_712_);
lean_closure_set(v___f_761_, 10, v___y_713_);
lean_closure_set(v___f_761_, 11, v___y_720_);
v___x_762_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_706_, v_inst_707_, v_inst_708_, v_pre_709_, v_post_710_, v_x_711_, v_x_712_, v_struct_760_, v___y_713_);
v___x_763_ = lean_apply_4(v_toBind_714_, lean_box(0), lean_box(0), v___x_762_, v___f_761_);
return v___x_763_;
}
default: 
{
lean_object* v___x_764_; 
lean_dec(v___f_716_);
lean_dec(v_toBind_714_);
v___x_764_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_706_, v_inst_707_, v_inst_708_, v_pre_709_, v_post_710_, v_x_711_, v_x_712_, v___y_720_, v___y_713_);
return v___x_764_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___boxed(lean_object* v_toApplicative_773_, lean_object* v_inst_774_, lean_object* v_inst_775_, lean_object* v_inst_776_, lean_object* v_pre_777_, lean_object* v_post_778_, lean_object* v_x_779_, lean_object* v_x_780_, lean_object* v___y_781_, lean_object* v_toBind_782_, lean_object* v___f_783_, lean_object* v___f_784_, lean_object* v_e_785_, lean_object* v_a_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17(v_toApplicative_773_, v_inst_774_, v_inst_775_, v_inst_776_, v_pre_777_, v_post_778_, v_x_779_, v_x_780_, v___y_781_, v_toBind_782_, v___f_783_, v___f_784_, v_e_785_, v_a_786_);
lean_dec(v___y_781_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__18(lean_object* v_inst_788_, lean_object* v_inst_789_, lean_object* v_inst_790_, lean_object* v_pre_791_, lean_object* v_post_792_, lean_object* v_x_793_, lean_object* v_x_794_, lean_object* v_toApplicative_795_, lean_object* v_toBind_796_, lean_object* v___f_797_, lean_object* v_e_798_, lean_object* v_____r_799_, lean_object* v___y_800_){
_start:
{
lean_object* v___f_801_; lean_object* v___f_802_; lean_object* v___x_803_; lean_object* v___x_804_; 
lean_inc_n(v___y_800_, 2);
lean_inc(v_x_794_);
lean_inc(v_post_792_);
lean_inc_n(v_pre_791_, 2);
lean_inc_ref(v_inst_790_);
lean_inc(v_inst_789_);
lean_inc_ref(v_inst_788_);
v___f_801_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__7___boxed), 9, 8);
lean_closure_set(v___f_801_, 0, v_inst_788_);
lean_closure_set(v___f_801_, 1, v_inst_789_);
lean_closure_set(v___f_801_, 2, v_inst_790_);
lean_closure_set(v___f_801_, 3, v_pre_791_);
lean_closure_set(v___f_801_, 4, v_post_792_);
lean_closure_set(v___f_801_, 5, v_x_793_);
lean_closure_set(v___f_801_, 6, v_x_794_);
lean_closure_set(v___f_801_, 7, v___y_800_);
lean_inc_ref(v_e_798_);
lean_inc(v_toBind_796_);
v___f_802_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___boxed), 14, 13);
lean_closure_set(v___f_802_, 0, v_toApplicative_795_);
lean_closure_set(v___f_802_, 1, v_inst_788_);
lean_closure_set(v___f_802_, 2, v_inst_789_);
lean_closure_set(v___f_802_, 3, v_inst_790_);
lean_closure_set(v___f_802_, 4, v_pre_791_);
lean_closure_set(v___f_802_, 5, v_post_792_);
lean_closure_set(v___f_802_, 6, v_x_793_);
lean_closure_set(v___f_802_, 7, v_x_794_);
lean_closure_set(v___f_802_, 8, v___y_800_);
lean_closure_set(v___f_802_, 9, v_toBind_796_);
lean_closure_set(v___f_802_, 10, v___f_801_);
lean_closure_set(v___f_802_, 11, v___f_797_);
lean_closure_set(v___f_802_, 12, v_e_798_);
v___x_803_ = lean_apply_1(v_pre_791_, v_e_798_);
v___x_804_ = lean_apply_4(v_toBind_796_, lean_box(0), lean_box(0), v___x_803_, v___f_802_);
return v___x_804_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__18___boxed(lean_object* v_inst_805_, lean_object* v_inst_806_, lean_object* v_inst_807_, lean_object* v_pre_808_, lean_object* v_post_809_, lean_object* v_x_810_, lean_object* v_x_811_, lean_object* v_toApplicative_812_, lean_object* v_toBind_813_, lean_object* v___f_814_, lean_object* v_e_815_, lean_object* v_____r_816_, lean_object* v___y_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__18(v_inst_805_, v_inst_806_, v_inst_807_, v_pre_808_, v_post_809_, v_x_810_, v_x_811_, v_toApplicative_812_, v_toBind_813_, v___f_814_, v_e_815_, v_____r_816_, v___y_817_);
lean_dec(v___y_817_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(lean_object* v_inst_819_, lean_object* v_inst_820_, lean_object* v_inst_821_, lean_object* v_pre_822_, lean_object* v_post_823_, lean_object* v_x_824_, lean_object* v_x_825_, lean_object* v_e_826_, lean_object* v_a_827_){
_start:
{
lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___f_832_; lean_object* v___f_833_; lean_object* v___x_834_; lean_object* v_toApplicative_835_; lean_object* v_toBind_836_; lean_object* v___f_837_; lean_object* v___f_838_; lean_object* v___f_839_; lean_object* v___f_840_; lean_object* v___f_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_828_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0));
v___x_829_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1));
lean_inc_ref_n(v_inst_819_, 3);
v___x_830_ = l_Lean_MonadCacheT_instMonad___redArg(v_x_824_, v___x_828_, v___x_829_, v_inst_819_);
v___x_831_ = l_Lean_MonadCacheT_instMonadControl___redArg(v_x_824_, v___x_828_, v___x_829_);
lean_inc_ref_n(v_inst_821_, 3);
lean_inc_ref(v___x_831_);
v___f_832_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_832_, 0, v___x_831_);
lean_closure_set(v___f_832_, 1, v_inst_821_);
v___f_833_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_833_, 0, v___x_831_);
lean_closure_set(v___f_833_, 1, v_inst_821_);
v___x_834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_834_, 0, v___f_832_);
lean_ctor_set(v___x_834_, 1, v___f_833_);
v_toApplicative_835_ = lean_ctor_get(v_inst_819_, 0);
lean_inc_ref_n(v_toApplicative_835_, 4);
v_toBind_836_ = lean_ctor_get(v_inst_819_, 1);
lean_inc_n(v_toBind_836_, 6);
lean_inc_n(v_x_825_, 3);
lean_inc_n(v_a_827_, 3);
lean_inc_ref_n(v_e_826_, 2);
v___f_837_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_837_, 0, v_toApplicative_835_);
lean_closure_set(v___f_837_, 1, v___x_828_);
lean_closure_set(v___f_837_, 2, v___x_829_);
lean_closure_set(v___f_837_, 3, v_e_826_);
lean_closure_set(v___f_837_, 4, v_a_827_);
lean_closure_set(v___f_837_, 5, v_x_825_);
lean_closure_set(v___f_837_, 6, v_toBind_836_);
v___f_838_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__3___boxed), 5, 4);
lean_closure_set(v___f_838_, 0, v_toApplicative_835_);
lean_closure_set(v___f_838_, 1, v___x_828_);
lean_closure_set(v___f_838_, 2, v___x_829_);
lean_closure_set(v___f_838_, 3, v_e_826_);
lean_inc_ref(v___x_830_);
lean_inc(v_post_823_);
lean_inc(v_pre_822_);
lean_inc_n(v_inst_820_, 2);
v___f_839_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__6___boxed), 12, 9);
lean_closure_set(v___f_839_, 0, v_inst_819_);
lean_closure_set(v___f_839_, 1, v_inst_820_);
lean_closure_set(v___f_839_, 2, v_inst_821_);
lean_closure_set(v___f_839_, 3, v_pre_822_);
lean_closure_set(v___f_839_, 4, v_post_823_);
lean_closure_set(v___f_839_, 5, v_x_824_);
lean_closure_set(v___f_839_, 6, v_x_825_);
lean_closure_set(v___f_839_, 7, v___x_830_);
lean_closure_set(v___f_839_, 8, v_toBind_836_);
v___f_840_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__18___boxed), 13, 11);
lean_closure_set(v___f_840_, 0, v_inst_819_);
lean_closure_set(v___f_840_, 1, v_inst_820_);
lean_closure_set(v___f_840_, 2, v_inst_821_);
lean_closure_set(v___f_840_, 3, v_pre_822_);
lean_closure_set(v___f_840_, 4, v_post_823_);
lean_closure_set(v___f_840_, 5, v_x_824_);
lean_closure_set(v___f_840_, 6, v_x_825_);
lean_closure_set(v___f_840_, 7, v_toApplicative_835_);
lean_closure_set(v___f_840_, 8, v_toBind_836_);
lean_closure_set(v___f_840_, 9, v___f_839_);
lean_closure_set(v___f_840_, 10, v_e_826_);
v___f_841_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__19___boxed), 13, 12);
lean_closure_set(v___f_841_, 0, v_inst_820_);
lean_closure_set(v___f_841_, 1, v_x_824_);
lean_closure_set(v___f_841_, 2, v___x_828_);
lean_closure_set(v___f_841_, 3, v___x_829_);
lean_closure_set(v___f_841_, 4, v_inst_819_);
lean_closure_set(v___f_841_, 5, v___f_840_);
lean_closure_set(v___f_841_, 6, v___x_830_);
lean_closure_set(v___f_841_, 7, v___x_834_);
lean_closure_set(v___f_841_, 8, v_a_827_);
lean_closure_set(v___f_841_, 9, v_toBind_836_);
lean_closure_set(v___f_841_, 10, v___f_837_);
lean_closure_set(v___f_841_, 11, v_toApplicative_835_);
v___x_842_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_842_, 0, lean_box(0));
lean_closure_set(v___x_842_, 1, lean_box(0));
lean_closure_set(v___x_842_, 2, v_a_827_);
v___x_843_ = lean_apply_2(v_x_825_, lean_box(0), v___x_842_);
v___x_844_ = lean_apply_4(v_toBind_836_, lean_box(0), lean_box(0), v___x_843_, v___f_838_);
v___x_845_ = lean_apply_4(v_toBind_836_, lean_box(0), lean_box(0), v___x_844_, v___f_841_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg___lam__0(lean_object* v_toApplicative_846_, lean_object* v_inst_847_, lean_object* v_inst_848_, lean_object* v_inst_849_, lean_object* v_pre_850_, lean_object* v_post_851_, lean_object* v_x_852_, lean_object* v_x_853_, lean_object* v_a_854_, lean_object* v_e_855_, lean_object* v_a_856_){
_start:
{
lean_object* v___y_858_; 
switch(lean_obj_tag(v_a_856_))
{
case 0:
{
lean_object* v_e_861_; lean_object* v_toPure_862_; lean_object* v___x_863_; 
lean_dec_ref(v_e_855_);
lean_dec(v_x_853_);
lean_dec(v_post_851_);
lean_dec(v_pre_850_);
lean_dec_ref(v_inst_849_);
lean_dec(v_inst_848_);
lean_dec_ref(v_inst_847_);
v_e_861_ = lean_ctor_get(v_a_856_, 0);
lean_inc_ref(v_e_861_);
lean_dec_ref(v_a_856_);
v_toPure_862_ = lean_ctor_get(v_toApplicative_846_, 1);
lean_inc(v_toPure_862_);
lean_dec_ref(v_toApplicative_846_);
v___x_863_ = lean_apply_2(v_toPure_862_, lean_box(0), v_e_861_);
return v___x_863_;
}
case 1:
{
lean_object* v_e_864_; lean_object* v___x_865_; 
lean_dec_ref(v_e_855_);
lean_dec_ref(v_toApplicative_846_);
v_e_864_ = lean_ctor_get(v_a_856_, 0);
lean_inc_ref(v_e_864_);
lean_dec_ref(v_a_856_);
v___x_865_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_847_, v_inst_848_, v_inst_849_, v_pre_850_, v_post_851_, v_x_852_, v_x_853_, v_e_864_, v_a_854_);
return v___x_865_;
}
default: 
{
lean_object* v_e_x3f_866_; 
lean_dec(v_x_853_);
lean_dec(v_post_851_);
lean_dec(v_pre_850_);
lean_dec_ref(v_inst_849_);
lean_dec(v_inst_848_);
lean_dec_ref(v_inst_847_);
v_e_x3f_866_ = lean_ctor_get(v_a_856_, 0);
lean_inc(v_e_x3f_866_);
lean_dec_ref(v_a_856_);
if (lean_obj_tag(v_e_x3f_866_) == 0)
{
v___y_858_ = v_e_855_;
goto v___jp_857_;
}
else
{
lean_object* v_val_867_; 
lean_dec_ref(v_e_855_);
v_val_867_ = lean_ctor_get(v_e_x3f_866_, 0);
lean_inc(v_val_867_);
lean_dec_ref(v_e_x3f_866_);
v___y_858_ = v_val_867_;
goto v___jp_857_;
}
}
}
v___jp_857_:
{
lean_object* v_toPure_859_; lean_object* v___x_860_; 
v_toPure_859_ = lean_ctor_get(v_toApplicative_846_, 1);
lean_inc(v_toPure_859_);
lean_dec_ref(v_toApplicative_846_);
v___x_860_ = lean_apply_2(v_toPure_859_, lean_box(0), v___y_858_);
return v___x_860_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg___lam__0___boxed(lean_object* v_toApplicative_868_, lean_object* v_inst_869_, lean_object* v_inst_870_, lean_object* v_inst_871_, lean_object* v_pre_872_, lean_object* v_post_873_, lean_object* v_x_874_, lean_object* v_x_875_, lean_object* v_a_876_, lean_object* v_e_877_, lean_object* v_a_878_){
_start:
{
lean_object* v_res_879_; 
v_res_879_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg___lam__0(v_toApplicative_868_, v_inst_869_, v_inst_870_, v_inst_871_, v_pre_872_, v_post_873_, v_x_874_, v_x_875_, v_a_876_, v_e_877_, v_a_878_);
lean_dec(v_a_876_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(lean_object* v_inst_880_, lean_object* v_inst_881_, lean_object* v_inst_882_, lean_object* v_pre_883_, lean_object* v_post_884_, lean_object* v_x_885_, lean_object* v_x_886_, lean_object* v_e_887_, lean_object* v_a_888_){
_start:
{
lean_object* v_toApplicative_889_; lean_object* v_toBind_890_; lean_object* v___f_891_; lean_object* v___x_892_; lean_object* v___x_893_; 
v_toApplicative_889_ = lean_ctor_get(v_inst_880_, 0);
lean_inc_ref(v_toApplicative_889_);
v_toBind_890_ = lean_ctor_get(v_inst_880_, 1);
lean_inc(v_toBind_890_);
lean_inc_ref(v_e_887_);
lean_inc(v_a_888_);
lean_inc(v_post_884_);
v___f_891_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg___lam__0___boxed), 11, 10);
lean_closure_set(v___f_891_, 0, v_toApplicative_889_);
lean_closure_set(v___f_891_, 1, v_inst_880_);
lean_closure_set(v___f_891_, 2, v_inst_881_);
lean_closure_set(v___f_891_, 3, v_inst_882_);
lean_closure_set(v___f_891_, 4, v_pre_883_);
lean_closure_set(v___f_891_, 5, v_post_884_);
lean_closure_set(v___f_891_, 6, v_x_885_);
lean_closure_set(v___f_891_, 7, v_x_886_);
lean_closure_set(v___f_891_, 8, v_a_888_);
lean_closure_set(v___f_891_, 9, v_e_887_);
v___x_892_ = lean_apply_1(v_post_884_, v_e_887_);
v___x_893_ = lean_apply_4(v_toBind_890_, lean_box(0), lean_box(0), v___x_892_, v___f_891_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__7(lean_object* v_inst_894_, lean_object* v_inst_895_, lean_object* v_inst_896_, lean_object* v_pre_897_, lean_object* v_post_898_, lean_object* v_x_899_, lean_object* v_x_900_, lean_object* v___y_901_, lean_object* v_a_902_){
_start:
{
lean_object* v___x_903_; 
v___x_903_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_894_, v_inst_895_, v_inst_896_, v_pre_897_, v_post_898_, v_x_899_, v_x_900_, v_a_902_, v___y_901_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg___boxed(lean_object* v_inst_904_, lean_object* v_inst_905_, lean_object* v_inst_906_, lean_object* v_pre_907_, lean_object* v_post_908_, lean_object* v_x_909_, lean_object* v_x_910_, lean_object* v_e_911_, lean_object* v_a_912_){
_start:
{
lean_object* v_res_913_; 
v_res_913_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_904_, v_inst_905_, v_inst_906_, v_pre_907_, v_post_908_, v_x_909_, v_x_910_, v_e_911_, v_a_912_);
lean_dec(v_a_912_);
return v_res_913_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit(lean_object* v_m_914_, lean_object* v_inst_915_, lean_object* v_inst_916_, lean_object* v_inst_917_, lean_object* v_pre_918_, lean_object* v_post_919_, lean_object* v_x_920_, lean_object* v_x_921_, lean_object* v_e_922_, lean_object* v_a_923_){
_start:
{
lean_object* v___x_924_; 
v___x_924_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_915_, v_inst_916_, v_inst_917_, v_pre_918_, v_post_919_, v_x_920_, v_x_921_, v_e_922_, v_a_923_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___boxed(lean_object* v_m_925_, lean_object* v_inst_926_, lean_object* v_inst_927_, lean_object* v_inst_928_, lean_object* v_pre_929_, lean_object* v_post_930_, lean_object* v_x_931_, lean_object* v_x_932_, lean_object* v_e_933_, lean_object* v_a_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit(v_m_925_, v_inst_926_, v_inst_927_, v_inst_928_, v_pre_929_, v_post_930_, v_x_931_, v_x_932_, v_e_933_, v_a_934_);
lean_dec(v_a_934_);
return v_res_935_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost(lean_object* v_m_936_, lean_object* v_inst_937_, lean_object* v_inst_938_, lean_object* v_inst_939_, lean_object* v_pre_940_, lean_object* v_post_941_, lean_object* v_x_942_, lean_object* v_x_943_, lean_object* v_e_944_, lean_object* v_a_945_){
_start:
{
lean_object* v___x_946_; 
v___x_946_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_937_, v_inst_938_, v_inst_939_, v_pre_940_, v_post_941_, v_x_942_, v_x_943_, v_e_944_, v_a_945_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___boxed(lean_object* v_m_947_, lean_object* v_inst_948_, lean_object* v_inst_949_, lean_object* v_inst_950_, lean_object* v_pre_951_, lean_object* v_post_952_, lean_object* v_x_953_, lean_object* v_x_954_, lean_object* v_e_955_, lean_object* v_a_956_){
_start:
{
lean_object* v_res_957_; 
v_res_957_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost(v_m_947_, v_inst_948_, v_inst_949_, v_inst_950_, v_pre_951_, v_post_952_, v_x_953_, v_x_954_, v_e_955_, v_a_956_);
lean_dec(v_a_956_);
return v_res_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___redArg___lam__0(lean_object* v_x_958_){
_start:
{
lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_960_ = lean_apply_1(v_x_958_, lean_box(0));
v___x_961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_961_, 0, v___x_960_);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___redArg___lam__0___boxed(lean_object* v_x_962_, lean_object* v___y_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l_Lean_Core_transform___redArg___lam__0(v_x_962_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___redArg___lam__1(lean_object* v_inst_965_, lean_object* v_00_u03b1_966_, lean_object* v_x_967_){
_start:
{
lean_object* v___f_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
v___f_968_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_968_, 0, v_x_967_);
v___x_969_ = lean_alloc_closure((void*)(l_Lean_Core_liftIOCore___boxed), 5, 2);
lean_closure_set(v___x_969_, 0, lean_box(0));
lean_closure_set(v___x_969_, 1, v___f_968_);
v___x_970_ = lean_apply_2(v_inst_965_, lean_box(0), v___x_969_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___redArg___lam__2(lean_object* v_toPure_971_, lean_object* v_____x_972_){
_start:
{
lean_object* v_fst_973_; lean_object* v___x_974_; 
v_fst_973_ = lean_ctor_get(v_____x_972_, 0);
lean_inc(v_fst_973_);
lean_dec_ref(v_____x_972_);
v___x_974_ = lean_apply_2(v_toPure_971_, lean_box(0), v_fst_973_);
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___redArg___lam__3(lean_object* v_a_975_, lean_object* v_toPure_976_, lean_object* v_s_977_){
_start:
{
lean_object* v___x_978_; lean_object* v___x_979_; 
v___x_978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_978_, 0, v_a_975_);
lean_ctor_set(v___x_978_, 1, v_s_977_);
v___x_979_ = lean_apply_2(v_toPure_976_, lean_box(0), v___x_978_);
return v___x_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___redArg___lam__4(lean_object* v_toPure_980_, lean_object* v_ref_981_, lean_object* v_x_982_, lean_object* v_toBind_983_, lean_object* v_a_984_){
_start:
{
lean_object* v___f_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; 
v___f_985_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__3), 3, 2);
lean_closure_set(v___f_985_, 0, v_a_984_);
lean_closure_set(v___f_985_, 1, v_toPure_980_);
v___x_986_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_986_, 0, lean_box(0));
lean_closure_set(v___x_986_, 1, lean_box(0));
lean_closure_set(v___x_986_, 2, v_ref_981_);
v___x_987_ = lean_apply_2(v_x_982_, lean_box(0), v___x_986_);
v___x_988_ = lean_apply_4(v_toBind_983_, lean_box(0), lean_box(0), v___x_987_, v___f_985_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___redArg___lam__5(lean_object* v_toPure_989_, lean_object* v_x_990_, lean_object* v_toBind_991_, lean_object* v_inst_992_, lean_object* v_inst_993_, lean_object* v_inst_994_, lean_object* v_pre_995_, lean_object* v_post_996_, lean_object* v_x_997_, lean_object* v_input_998_, lean_object* v_ref_999_){
_start:
{
lean_object* v___f_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
lean_inc(v_toBind_991_);
lean_inc(v_x_990_);
lean_inc(v_ref_999_);
v___f_1000_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__4), 5, 4);
lean_closure_set(v___f_1000_, 0, v_toPure_989_);
lean_closure_set(v___f_1000_, 1, v_ref_999_);
lean_closure_set(v___f_1000_, 2, v_x_990_);
lean_closure_set(v___f_1000_, 3, v_toBind_991_);
v___x_1001_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_992_, v_inst_993_, v_inst_994_, v_pre_995_, v_post_996_, v_x_997_, v_x_990_, v_input_998_, v_ref_999_);
lean_dec(v_ref_999_);
v___x_1002_ = lean_apply_4(v_toBind_991_, lean_box(0), lean_box(0), v___x_1001_, v___f_1000_);
return v___x_1002_;
}
}
static lean_object* _init_l_Lean_Core_transform___redArg___closed__0(void){
_start:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___x_1003_ = lean_box(0);
v___x_1004_ = lean_unsigned_to_nat(16u);
v___x_1005_ = lean_mk_array(v___x_1004_, v___x_1003_);
return v___x_1005_;
}
}
static lean_object* _init_l_Lean_Core_transform___redArg___closed__1(void){
_start:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1006_ = lean_obj_once(&l_Lean_Core_transform___redArg___closed__0, &l_Lean_Core_transform___redArg___closed__0_once, _init_l_Lean_Core_transform___redArg___closed__0);
v___x_1007_ = lean_unsigned_to_nat(0u);
v___x_1008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1007_);
lean_ctor_set(v___x_1008_, 1, v___x_1006_);
return v___x_1008_;
}
}
static lean_object* _init_l_Lean_Core_transform___redArg___closed__2(void){
_start:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1009_ = lean_obj_once(&l_Lean_Core_transform___redArg___closed__1, &l_Lean_Core_transform___redArg___closed__1_once, _init_l_Lean_Core_transform___redArg___closed__1);
v___x_1010_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1010_, 0, lean_box(0));
lean_closure_set(v___x_1010_, 1, lean_box(0));
lean_closure_set(v___x_1010_, 2, v___x_1009_);
return v___x_1010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___redArg(lean_object* v_inst_1011_, lean_object* v_inst_1012_, lean_object* v_inst_1013_, lean_object* v_input_1014_, lean_object* v_pre_1015_, lean_object* v_post_1016_){
_start:
{
lean_object* v_x_1017_; lean_object* v_toApplicative_1018_; lean_object* v_toBind_1019_; lean_object* v_toPure_1020_; lean_object* v_x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___f_1024_; lean_object* v___f_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
v_x_1017_ = lean_box(0);
v_toApplicative_1018_ = lean_ctor_get(v_inst_1011_, 0);
v_toBind_1019_ = lean_ctor_get(v_inst_1011_, 1);
lean_inc_n(v_toBind_1019_, 3);
v_toPure_1020_ = lean_ctor_get(v_toApplicative_1018_, 1);
lean_inc_n(v_toPure_1020_, 2);
lean_inc_n(v_inst_1012_, 2);
v_x_1021_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__1), 3, 1);
lean_closure_set(v_x_1021_, 0, v_inst_1012_);
v___x_1022_ = lean_obj_once(&l_Lean_Core_transform___redArg___closed__2, &l_Lean_Core_transform___redArg___closed__2_once, _init_l_Lean_Core_transform___redArg___closed__2);
v___x_1023_ = l_Lean_Core_transform___redArg___lam__1(v_inst_1012_, lean_box(0), v___x_1022_);
v___f_1024_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__2), 2, 1);
lean_closure_set(v___f_1024_, 0, v_toPure_1020_);
v___f_1025_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__5), 11, 10);
lean_closure_set(v___f_1025_, 0, v_toPure_1020_);
lean_closure_set(v___f_1025_, 1, v_x_1021_);
lean_closure_set(v___f_1025_, 2, v_toBind_1019_);
lean_closure_set(v___f_1025_, 3, v_inst_1011_);
lean_closure_set(v___f_1025_, 4, v_inst_1012_);
lean_closure_set(v___f_1025_, 5, v_inst_1013_);
lean_closure_set(v___f_1025_, 6, v_pre_1015_);
lean_closure_set(v___f_1025_, 7, v_post_1016_);
lean_closure_set(v___f_1025_, 8, v_x_1017_);
lean_closure_set(v___f_1025_, 9, v_input_1014_);
v___x_1026_ = lean_apply_4(v_toBind_1019_, lean_box(0), lean_box(0), v___x_1023_, v___f_1025_);
v___x_1027_ = lean_apply_4(v_toBind_1019_, lean_box(0), lean_box(0), v___x_1026_, v___f_1024_);
return v___x_1027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform(lean_object* v_m_1028_, lean_object* v_inst_1029_, lean_object* v_inst_1030_, lean_object* v_inst_1031_, lean_object* v_input_1032_, lean_object* v_pre_1033_, lean_object* v_post_1034_){
_start:
{
lean_object* v___x_1035_; 
v___x_1035_ = l_Lean_Core_transform___redArg(v_inst_1029_, v_inst_1030_, v_inst_1031_, v_input_1032_, v_pre_1033_, v_post_1034_);
return v___x_1035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_betaReduce___lam__0(lean_object* v_e_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_){
_start:
{
uint8_t v___x_1042_; uint8_t v___x_1043_; 
v___x_1042_ = 0;
v___x_1043_ = l_Lean_Expr_isHeadBetaTarget(v_e_1038_, v___x_1042_);
if (v___x_1043_ == 0)
{
lean_object* v___x_1044_; lean_object* v___x_1045_; 
lean_dec_ref(v_e_1038_);
v___x_1044_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_1045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1044_);
return v___x_1045_;
}
else
{
lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1046_ = l_Lean_Expr_headBeta(v_e_1038_);
v___x_1047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1046_);
v___x_1048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1048_, 0, v___x_1047_);
return v___x_1048_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_betaReduce___lam__0___boxed(lean_object* v_e_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_){
_start:
{
lean_object* v_res_1053_; 
v_res_1053_ = l_Lean_Core_betaReduce___lam__0(v_e_1049_, v___y_1050_, v___y_1051_);
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1050_);
return v_res_1053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_betaReduce___lam__1(lean_object* v_e_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_){
_start:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; 
v___x_1058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1058_, 0, v_e_1054_);
v___x_1059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1058_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_betaReduce___lam__1___boxed(lean_object* v_e_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_){
_start:
{
lean_object* v_res_1064_; 
v_res_1064_ = l_Lean_Core_betaReduce___lam__1(v_e_1060_, v___y_1061_, v___y_1062_);
lean_dec(v___y_1062_);
lean_dec_ref(v___y_1061_);
return v_res_1064_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; 
v___x_1070_ = l_Lean_maxRecDepthErrorMessage;
v___x_1071_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1070_);
return v___x_1071_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1072_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__3);
v___x_1073_ = l_Lean_MessageData_ofFormat(v___x_1072_);
return v___x_1073_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1074_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__4);
v___x_1075_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__2));
v___x_1076_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1075_);
lean_ctor_set(v___x_1076_, 1, v___x_1074_);
return v___x_1076_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg(lean_object* v_ref_1077_){
_start:
{
lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; 
v___x_1079_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5);
v___x_1080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1080_, 0, v_ref_1077_);
lean_ctor_set(v___x_1080_, 1, v___x_1079_);
v___x_1081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1080_);
return v___x_1081_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object* v_ref_1082_, lean_object* v___y_1083_){
_start:
{
lean_object* v_res_1084_; 
v_res_1084_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_1082_);
return v_res_1084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___redArg(lean_object* v_x_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_){
_start:
{
lean_object* v___y_1091_; lean_object* v_fileName_1100_; lean_object* v_fileMap_1101_; lean_object* v_options_1102_; lean_object* v_currRecDepth_1103_; lean_object* v_maxRecDepth_1104_; lean_object* v_ref_1105_; lean_object* v_currNamespace_1106_; lean_object* v_openDecls_1107_; lean_object* v_initHeartbeats_1108_; lean_object* v_maxHeartbeats_1109_; lean_object* v_quotContext_1110_; lean_object* v_currMacroScope_1111_; uint8_t v_diag_1112_; lean_object* v_cancelTk_x3f_1113_; uint8_t v_suppressElabErrors_1114_; lean_object* v_inheritedTraceOptions_1115_; lean_object* v___x_1121_; uint8_t v___x_1122_; 
v_fileName_1100_ = lean_ctor_get(v___y_1087_, 0);
v_fileMap_1101_ = lean_ctor_get(v___y_1087_, 1);
v_options_1102_ = lean_ctor_get(v___y_1087_, 2);
v_currRecDepth_1103_ = lean_ctor_get(v___y_1087_, 3);
v_maxRecDepth_1104_ = lean_ctor_get(v___y_1087_, 4);
v_ref_1105_ = lean_ctor_get(v___y_1087_, 5);
v_currNamespace_1106_ = lean_ctor_get(v___y_1087_, 6);
v_openDecls_1107_ = lean_ctor_get(v___y_1087_, 7);
v_initHeartbeats_1108_ = lean_ctor_get(v___y_1087_, 8);
v_maxHeartbeats_1109_ = lean_ctor_get(v___y_1087_, 9);
v_quotContext_1110_ = lean_ctor_get(v___y_1087_, 10);
v_currMacroScope_1111_ = lean_ctor_get(v___y_1087_, 11);
v_diag_1112_ = lean_ctor_get_uint8(v___y_1087_, sizeof(void*)*14);
v_cancelTk_x3f_1113_ = lean_ctor_get(v___y_1087_, 12);
v_suppressElabErrors_1114_ = lean_ctor_get_uint8(v___y_1087_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1115_ = lean_ctor_get(v___y_1087_, 13);
v___x_1121_ = lean_unsigned_to_nat(0u);
v___x_1122_ = lean_nat_dec_eq(v_maxRecDepth_1104_, v___x_1121_);
if (v___x_1122_ == 0)
{
uint8_t v___x_1123_; 
v___x_1123_ = lean_nat_dec_eq(v_currRecDepth_1103_, v_maxRecDepth_1104_);
if (v___x_1123_ == 0)
{
goto v___jp_1116_;
}
else
{
lean_object* v___x_1124_; 
lean_dec_ref(v_x_1085_);
lean_inc(v_ref_1105_);
v___x_1124_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_1105_);
v___y_1091_ = v___x_1124_;
goto v___jp_1090_;
}
}
else
{
goto v___jp_1116_;
}
v___jp_1090_:
{
if (lean_obj_tag(v___y_1091_) == 0)
{
return v___y_1091_;
}
else
{
lean_object* v_a_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1099_; 
v_a_1092_ = lean_ctor_get(v___y_1091_, 0);
v_isSharedCheck_1099_ = !lean_is_exclusive(v___y_1091_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1094_ = v___y_1091_;
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_a_1092_);
lean_dec(v___y_1091_);
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
v_reuseFailAlloc_1098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_a_1092_);
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
v___jp_1116_:
{
lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1117_ = lean_unsigned_to_nat(1u);
v___x_1118_ = lean_nat_add(v_currRecDepth_1103_, v___x_1117_);
lean_inc_ref(v_inheritedTraceOptions_1115_);
lean_inc(v_cancelTk_x3f_1113_);
lean_inc(v_currMacroScope_1111_);
lean_inc(v_quotContext_1110_);
lean_inc(v_maxHeartbeats_1109_);
lean_inc(v_initHeartbeats_1108_);
lean_inc(v_openDecls_1107_);
lean_inc(v_currNamespace_1106_);
lean_inc(v_ref_1105_);
lean_inc(v_maxRecDepth_1104_);
lean_inc_ref(v_options_1102_);
lean_inc_ref(v_fileMap_1101_);
lean_inc_ref(v_fileName_1100_);
v___x_1119_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1119_, 0, v_fileName_1100_);
lean_ctor_set(v___x_1119_, 1, v_fileMap_1101_);
lean_ctor_set(v___x_1119_, 2, v_options_1102_);
lean_ctor_set(v___x_1119_, 3, v___x_1118_);
lean_ctor_set(v___x_1119_, 4, v_maxRecDepth_1104_);
lean_ctor_set(v___x_1119_, 5, v_ref_1105_);
lean_ctor_set(v___x_1119_, 6, v_currNamespace_1106_);
lean_ctor_set(v___x_1119_, 7, v_openDecls_1107_);
lean_ctor_set(v___x_1119_, 8, v_initHeartbeats_1108_);
lean_ctor_set(v___x_1119_, 9, v_maxHeartbeats_1109_);
lean_ctor_set(v___x_1119_, 10, v_quotContext_1110_);
lean_ctor_set(v___x_1119_, 11, v_currMacroScope_1111_);
lean_ctor_set(v___x_1119_, 12, v_cancelTk_x3f_1113_);
lean_ctor_set(v___x_1119_, 13, v_inheritedTraceOptions_1115_);
lean_ctor_set_uint8(v___x_1119_, sizeof(void*)*14, v_diag_1112_);
lean_ctor_set_uint8(v___x_1119_, sizeof(void*)*14 + 1, v_suppressElabErrors_1114_);
lean_inc(v___y_1088_);
lean_inc(v___y_1086_);
v___x_1120_ = lean_apply_4(v_x_1085_, v___y_1086_, v___x_1119_, v___y_1088_, lean_box(0));
v___y_1091_ = v___x_1120_;
goto v___jp_1090_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___redArg___boxed(lean_object* v_x_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_){
_start:
{
lean_object* v_res_1130_; 
v_res_1130_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___redArg(v_x_1125_, v___y_1126_, v___y_1127_, v___y_1128_);
lean_dec(v___y_1128_);
lean_dec_ref(v___y_1127_);
lean_dec(v___y_1126_);
return v_res_1130_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_1131_, lean_object* v_x_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_){
_start:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1136_ = lean_apply_1(v_x_1132_, lean_box(0));
v___x_1137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1136_);
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_1138_, lean_object* v_x_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_){
_start:
{
lean_object* v_res_1143_; 
v_res_1143_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__0(v_00_u03b1_1138_, v_x_1139_, v___y_1140_, v___y_1141_);
lean_dec(v___y_1141_);
lean_dec_ref(v___y_1140_);
return v_res_1143_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__9___redArg(lean_object* v_a_1144_, lean_object* v_x_1145_){
_start:
{
if (lean_obj_tag(v_x_1145_) == 0)
{
uint8_t v___x_1146_; 
v___x_1146_ = 0;
return v___x_1146_;
}
else
{
lean_object* v_key_1147_; lean_object* v_tail_1148_; uint8_t v___x_1149_; 
v_key_1147_ = lean_ctor_get(v_x_1145_, 0);
v_tail_1148_ = lean_ctor_get(v_x_1145_, 2);
v___x_1149_ = l_Lean_ExprStructEq_beq(v_key_1147_, v_a_1144_);
if (v___x_1149_ == 0)
{
v_x_1145_ = v_tail_1148_;
goto _start;
}
else
{
return v___x_1149_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__9___redArg___boxed(lean_object* v_a_1151_, lean_object* v_x_1152_){
_start:
{
uint8_t v_res_1153_; lean_object* v_r_1154_; 
v_res_1153_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__9___redArg(v_a_1151_, v_x_1152_);
lean_dec(v_x_1152_);
lean_dec_ref(v_a_1151_);
v_r_1154_ = lean_box(v_res_1153_);
return v_r_1154_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12___redArg(lean_object* v_x_1155_, lean_object* v_x_1156_){
_start:
{
if (lean_obj_tag(v_x_1156_) == 0)
{
return v_x_1155_;
}
else
{
lean_object* v_key_1157_; lean_object* v_value_1158_; lean_object* v_tail_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1182_; 
v_key_1157_ = lean_ctor_get(v_x_1156_, 0);
v_value_1158_ = lean_ctor_get(v_x_1156_, 1);
v_tail_1159_ = lean_ctor_get(v_x_1156_, 2);
v_isSharedCheck_1182_ = !lean_is_exclusive(v_x_1156_);
if (v_isSharedCheck_1182_ == 0)
{
v___x_1161_ = v_x_1156_;
v_isShared_1162_ = v_isSharedCheck_1182_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_tail_1159_);
lean_inc(v_value_1158_);
lean_inc(v_key_1157_);
lean_dec(v_x_1156_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1182_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v___x_1163_; uint64_t v___x_1164_; uint64_t v___x_1165_; uint64_t v___x_1166_; uint64_t v_fold_1167_; uint64_t v___x_1168_; uint64_t v___x_1169_; uint64_t v___x_1170_; size_t v___x_1171_; size_t v___x_1172_; size_t v___x_1173_; size_t v___x_1174_; size_t v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1178_; 
v___x_1163_ = lean_array_get_size(v_x_1155_);
v___x_1164_ = l_Lean_ExprStructEq_hash(v_key_1157_);
v___x_1165_ = 32ULL;
v___x_1166_ = lean_uint64_shift_right(v___x_1164_, v___x_1165_);
v_fold_1167_ = lean_uint64_xor(v___x_1164_, v___x_1166_);
v___x_1168_ = 16ULL;
v___x_1169_ = lean_uint64_shift_right(v_fold_1167_, v___x_1168_);
v___x_1170_ = lean_uint64_xor(v_fold_1167_, v___x_1169_);
v___x_1171_ = lean_uint64_to_usize(v___x_1170_);
v___x_1172_ = lean_usize_of_nat(v___x_1163_);
v___x_1173_ = ((size_t)1ULL);
v___x_1174_ = lean_usize_sub(v___x_1172_, v___x_1173_);
v___x_1175_ = lean_usize_land(v___x_1171_, v___x_1174_);
v___x_1176_ = lean_array_uget_borrowed(v_x_1155_, v___x_1175_);
lean_inc(v___x_1176_);
if (v_isShared_1162_ == 0)
{
lean_ctor_set(v___x_1161_, 2, v___x_1176_);
v___x_1178_ = v___x_1161_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v_key_1157_);
lean_ctor_set(v_reuseFailAlloc_1181_, 1, v_value_1158_);
lean_ctor_set(v_reuseFailAlloc_1181_, 2, v___x_1176_);
v___x_1178_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
lean_object* v___x_1179_; 
v___x_1179_ = lean_array_uset(v_x_1155_, v___x_1175_, v___x_1178_);
v_x_1155_ = v___x_1179_;
v_x_1156_ = v_tail_1159_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10_spec__11___redArg(lean_object* v_i_1183_, lean_object* v_source_1184_, lean_object* v_target_1185_){
_start:
{
lean_object* v___x_1186_; uint8_t v___x_1187_; 
v___x_1186_ = lean_array_get_size(v_source_1184_);
v___x_1187_ = lean_nat_dec_lt(v_i_1183_, v___x_1186_);
if (v___x_1187_ == 0)
{
lean_dec_ref(v_source_1184_);
lean_dec(v_i_1183_);
return v_target_1185_;
}
else
{
lean_object* v_es_1188_; lean_object* v___x_1189_; lean_object* v_source_1190_; lean_object* v_target_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; 
v_es_1188_ = lean_array_fget(v_source_1184_, v_i_1183_);
v___x_1189_ = lean_box(0);
v_source_1190_ = lean_array_fset(v_source_1184_, v_i_1183_, v___x_1189_);
v_target_1191_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12___redArg(v_target_1185_, v_es_1188_);
v___x_1192_ = lean_unsigned_to_nat(1u);
v___x_1193_ = lean_nat_add(v_i_1183_, v___x_1192_);
lean_dec(v_i_1183_);
v_i_1183_ = v___x_1193_;
v_source_1184_ = v_source_1190_;
v_target_1185_ = v_target_1191_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___redArg(lean_object* v_data_1195_){
_start:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v_nbuckets_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; 
v___x_1196_ = lean_array_get_size(v_data_1195_);
v___x_1197_ = lean_unsigned_to_nat(2u);
v_nbuckets_1198_ = lean_nat_mul(v___x_1196_, v___x_1197_);
v___x_1199_ = lean_unsigned_to_nat(0u);
v___x_1200_ = lean_box(0);
v___x_1201_ = lean_mk_array(v_nbuckets_1198_, v___x_1200_);
v___x_1202_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10_spec__11___redArg(v___x_1199_, v_data_1195_, v___x_1201_);
return v___x_1202_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11___redArg(lean_object* v_a_1203_, lean_object* v_b_1204_, lean_object* v_x_1205_){
_start:
{
if (lean_obj_tag(v_x_1205_) == 0)
{
lean_dec(v_b_1204_);
lean_dec_ref(v_a_1203_);
return v_x_1205_;
}
else
{
lean_object* v_key_1206_; lean_object* v_value_1207_; lean_object* v_tail_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1220_; 
v_key_1206_ = lean_ctor_get(v_x_1205_, 0);
v_value_1207_ = lean_ctor_get(v_x_1205_, 1);
v_tail_1208_ = lean_ctor_get(v_x_1205_, 2);
v_isSharedCheck_1220_ = !lean_is_exclusive(v_x_1205_);
if (v_isSharedCheck_1220_ == 0)
{
v___x_1210_ = v_x_1205_;
v_isShared_1211_ = v_isSharedCheck_1220_;
goto v_resetjp_1209_;
}
else
{
lean_inc(v_tail_1208_);
lean_inc(v_value_1207_);
lean_inc(v_key_1206_);
lean_dec(v_x_1205_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1220_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
uint8_t v___x_1212_; 
v___x_1212_ = l_Lean_ExprStructEq_beq(v_key_1206_, v_a_1203_);
if (v___x_1212_ == 0)
{
lean_object* v___x_1213_; lean_object* v___x_1215_; 
v___x_1213_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11___redArg(v_a_1203_, v_b_1204_, v_tail_1208_);
if (v_isShared_1211_ == 0)
{
lean_ctor_set(v___x_1210_, 2, v___x_1213_);
v___x_1215_ = v___x_1210_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v_key_1206_);
lean_ctor_set(v_reuseFailAlloc_1216_, 1, v_value_1207_);
lean_ctor_set(v_reuseFailAlloc_1216_, 2, v___x_1213_);
v___x_1215_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
return v___x_1215_;
}
}
else
{
lean_object* v___x_1218_; 
lean_dec(v_value_1207_);
lean_dec(v_key_1206_);
if (v_isShared_1211_ == 0)
{
lean_ctor_set(v___x_1210_, 1, v_b_1204_);
lean_ctor_set(v___x_1210_, 0, v_a_1203_);
v___x_1218_ = v___x_1210_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v_a_1203_);
lean_ctor_set(v_reuseFailAlloc_1219_, 1, v_b_1204_);
lean_ctor_set(v_reuseFailAlloc_1219_, 2, v_tail_1208_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6___redArg(lean_object* v_m_1221_, lean_object* v_a_1222_, lean_object* v_b_1223_){
_start:
{
lean_object* v_size_1224_; lean_object* v_buckets_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1268_; 
v_size_1224_ = lean_ctor_get(v_m_1221_, 0);
v_buckets_1225_ = lean_ctor_get(v_m_1221_, 1);
v_isSharedCheck_1268_ = !lean_is_exclusive(v_m_1221_);
if (v_isSharedCheck_1268_ == 0)
{
v___x_1227_ = v_m_1221_;
v_isShared_1228_ = v_isSharedCheck_1268_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_buckets_1225_);
lean_inc(v_size_1224_);
lean_dec(v_m_1221_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1268_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v___x_1229_; uint64_t v___x_1230_; uint64_t v___x_1231_; uint64_t v___x_1232_; uint64_t v_fold_1233_; uint64_t v___x_1234_; uint64_t v___x_1235_; uint64_t v___x_1236_; size_t v___x_1237_; size_t v___x_1238_; size_t v___x_1239_; size_t v___x_1240_; size_t v___x_1241_; lean_object* v_bkt_1242_; uint8_t v___x_1243_; 
v___x_1229_ = lean_array_get_size(v_buckets_1225_);
v___x_1230_ = l_Lean_ExprStructEq_hash(v_a_1222_);
v___x_1231_ = 32ULL;
v___x_1232_ = lean_uint64_shift_right(v___x_1230_, v___x_1231_);
v_fold_1233_ = lean_uint64_xor(v___x_1230_, v___x_1232_);
v___x_1234_ = 16ULL;
v___x_1235_ = lean_uint64_shift_right(v_fold_1233_, v___x_1234_);
v___x_1236_ = lean_uint64_xor(v_fold_1233_, v___x_1235_);
v___x_1237_ = lean_uint64_to_usize(v___x_1236_);
v___x_1238_ = lean_usize_of_nat(v___x_1229_);
v___x_1239_ = ((size_t)1ULL);
v___x_1240_ = lean_usize_sub(v___x_1238_, v___x_1239_);
v___x_1241_ = lean_usize_land(v___x_1237_, v___x_1240_);
v_bkt_1242_ = lean_array_uget_borrowed(v_buckets_1225_, v___x_1241_);
v___x_1243_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__9___redArg(v_a_1222_, v_bkt_1242_);
if (v___x_1243_ == 0)
{
lean_object* v___x_1244_; lean_object* v_size_x27_1245_; lean_object* v___x_1246_; lean_object* v_buckets_x27_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; uint8_t v___x_1253_; 
v___x_1244_ = lean_unsigned_to_nat(1u);
v_size_x27_1245_ = lean_nat_add(v_size_1224_, v___x_1244_);
lean_dec(v_size_1224_);
lean_inc(v_bkt_1242_);
v___x_1246_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1246_, 0, v_a_1222_);
lean_ctor_set(v___x_1246_, 1, v_b_1223_);
lean_ctor_set(v___x_1246_, 2, v_bkt_1242_);
v_buckets_x27_1247_ = lean_array_uset(v_buckets_1225_, v___x_1241_, v___x_1246_);
v___x_1248_ = lean_unsigned_to_nat(4u);
v___x_1249_ = lean_nat_mul(v_size_x27_1245_, v___x_1248_);
v___x_1250_ = lean_unsigned_to_nat(3u);
v___x_1251_ = lean_nat_div(v___x_1249_, v___x_1250_);
lean_dec(v___x_1249_);
v___x_1252_ = lean_array_get_size(v_buckets_x27_1247_);
v___x_1253_ = lean_nat_dec_le(v___x_1251_, v___x_1252_);
lean_dec(v___x_1251_);
if (v___x_1253_ == 0)
{
lean_object* v_val_1254_; lean_object* v___x_1256_; 
v_val_1254_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___redArg(v_buckets_x27_1247_);
if (v_isShared_1228_ == 0)
{
lean_ctor_set(v___x_1227_, 1, v_val_1254_);
lean_ctor_set(v___x_1227_, 0, v_size_x27_1245_);
v___x_1256_ = v___x_1227_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v_size_x27_1245_);
lean_ctor_set(v_reuseFailAlloc_1257_, 1, v_val_1254_);
v___x_1256_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
return v___x_1256_;
}
}
else
{
lean_object* v___x_1259_; 
if (v_isShared_1228_ == 0)
{
lean_ctor_set(v___x_1227_, 1, v_buckets_x27_1247_);
lean_ctor_set(v___x_1227_, 0, v_size_x27_1245_);
v___x_1259_ = v___x_1227_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v_size_x27_1245_);
lean_ctor_set(v_reuseFailAlloc_1260_, 1, v_buckets_x27_1247_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
return v___x_1259_;
}
}
}
else
{
lean_object* v___x_1261_; lean_object* v_buckets_x27_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1266_; 
lean_inc(v_bkt_1242_);
v___x_1261_ = lean_box(0);
v_buckets_x27_1262_ = lean_array_uset(v_buckets_1225_, v___x_1241_, v___x_1261_);
v___x_1263_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11___redArg(v_a_1222_, v_b_1223_, v_bkt_1242_);
v___x_1264_ = lean_array_uset(v_buckets_x27_1262_, v___x_1241_, v___x_1263_);
if (v_isShared_1228_ == 0)
{
lean_ctor_set(v___x_1227_, 1, v___x_1264_);
v___x_1266_ = v___x_1227_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v_size_1224_);
lean_ctor_set(v_reuseFailAlloc_1267_, 1, v___x_1264_);
v___x_1266_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
return v___x_1266_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__2(lean_object* v_a_1269_, lean_object* v_e_1270_, lean_object* v_a_1271_){
_start:
{
lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; 
v___x_1273_ = lean_st_ref_take(v_a_1269_);
v___x_1274_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6___redArg(v___x_1273_, v_e_1270_, v_a_1271_);
v___x_1275_ = lean_st_ref_set(v_a_1269_, v___x_1274_);
v___x_1276_ = lean_box(0);
return v___x_1276_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__2___boxed(lean_object* v_a_1277_, lean_object* v_e_1278_, lean_object* v_a_1279_, lean_object* v___y_1280_){
_start:
{
lean_object* v_res_1281_; 
v_res_1281_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__2(v_a_1277_, v_e_1278_, v_a_1279_);
lean_dec(v_a_1277_);
return v_res_1281_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___redArg(lean_object* v_a_1282_, lean_object* v_x_1283_){
_start:
{
if (lean_obj_tag(v_x_1283_) == 0)
{
lean_object* v___x_1284_; 
v___x_1284_ = lean_box(0);
return v___x_1284_;
}
else
{
lean_object* v_key_1285_; lean_object* v_value_1286_; lean_object* v_tail_1287_; uint8_t v___x_1288_; 
v_key_1285_ = lean_ctor_get(v_x_1283_, 0);
v_value_1286_ = lean_ctor_get(v_x_1283_, 1);
v_tail_1287_ = lean_ctor_get(v_x_1283_, 2);
v___x_1288_ = l_Lean_ExprStructEq_beq(v_key_1285_, v_a_1282_);
if (v___x_1288_ == 0)
{
v_x_1283_ = v_tail_1287_;
goto _start;
}
else
{
lean_object* v___x_1290_; 
lean_inc(v_value_1286_);
v___x_1290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1290_, 0, v_value_1286_);
return v___x_1290_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___redArg___boxed(lean_object* v_a_1291_, lean_object* v_x_1292_){
_start:
{
lean_object* v_res_1293_; 
v_res_1293_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___redArg(v_a_1291_, v_x_1292_);
lean_dec(v_x_1292_);
lean_dec_ref(v_a_1291_);
return v_res_1293_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg(lean_object* v_m_1294_, lean_object* v_a_1295_){
_start:
{
lean_object* v_buckets_1296_; lean_object* v___x_1297_; uint64_t v___x_1298_; uint64_t v___x_1299_; uint64_t v___x_1300_; uint64_t v_fold_1301_; uint64_t v___x_1302_; uint64_t v___x_1303_; uint64_t v___x_1304_; size_t v___x_1305_; size_t v___x_1306_; size_t v___x_1307_; size_t v___x_1308_; size_t v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; 
v_buckets_1296_ = lean_ctor_get(v_m_1294_, 1);
v___x_1297_ = lean_array_get_size(v_buckets_1296_);
v___x_1298_ = l_Lean_ExprStructEq_hash(v_a_1295_);
v___x_1299_ = 32ULL;
v___x_1300_ = lean_uint64_shift_right(v___x_1298_, v___x_1299_);
v_fold_1301_ = lean_uint64_xor(v___x_1298_, v___x_1300_);
v___x_1302_ = 16ULL;
v___x_1303_ = lean_uint64_shift_right(v_fold_1301_, v___x_1302_);
v___x_1304_ = lean_uint64_xor(v_fold_1301_, v___x_1303_);
v___x_1305_ = lean_uint64_to_usize(v___x_1304_);
v___x_1306_ = lean_usize_of_nat(v___x_1297_);
v___x_1307_ = ((size_t)1ULL);
v___x_1308_ = lean_usize_sub(v___x_1306_, v___x_1307_);
v___x_1309_ = lean_usize_land(v___x_1305_, v___x_1308_);
v___x_1310_ = lean_array_uget_borrowed(v_buckets_1296_, v___x_1309_);
v___x_1311_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___redArg(v_a_1295_, v___x_1310_);
return v___x_1311_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_m_1312_, lean_object* v_a_1313_){
_start:
{
lean_object* v_res_1314_; 
v_res_1314_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg(v_m_1312_, v_a_1313_);
lean_dec_ref(v_a_1313_);
lean_dec_ref(v_m_1312_);
return v_res_1314_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1(lean_object* v_pre_1315_, lean_object* v_post_1316_, size_t v_sz_1317_, size_t v_i_1318_, lean_object* v_bs_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_){
_start:
{
uint8_t v___x_1324_; 
v___x_1324_ = lean_usize_dec_lt(v_i_1318_, v_sz_1317_);
if (v___x_1324_ == 0)
{
lean_object* v___x_1325_; 
lean_dec_ref(v_post_1316_);
lean_dec_ref(v_pre_1315_);
v___x_1325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1325_, 0, v_bs_1319_);
return v___x_1325_;
}
else
{
lean_object* v_v_1326_; lean_object* v___x_1327_; 
v_v_1326_ = lean_array_uget_borrowed(v_bs_1319_, v_i_1318_);
lean_inc(v_v_1326_);
lean_inc_ref(v_post_1316_);
lean_inc_ref(v_pre_1315_);
v___x_1327_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1315_, v_post_1316_, v_v_1326_, v___y_1320_, v___y_1321_, v___y_1322_);
if (lean_obj_tag(v___x_1327_) == 0)
{
lean_object* v_a_1328_; lean_object* v___x_1329_; lean_object* v_bs_x27_1330_; size_t v___x_1331_; size_t v___x_1332_; lean_object* v___x_1333_; 
v_a_1328_ = lean_ctor_get(v___x_1327_, 0);
lean_inc(v_a_1328_);
lean_dec_ref(v___x_1327_);
v___x_1329_ = lean_unsigned_to_nat(0u);
v_bs_x27_1330_ = lean_array_uset(v_bs_1319_, v_i_1318_, v___x_1329_);
v___x_1331_ = ((size_t)1ULL);
v___x_1332_ = lean_usize_add(v_i_1318_, v___x_1331_);
v___x_1333_ = lean_array_uset(v_bs_x27_1330_, v_i_1318_, v_a_1328_);
v_i_1318_ = v___x_1332_;
v_bs_1319_ = v___x_1333_;
goto _start;
}
else
{
lean_object* v_a_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1342_; 
lean_dec_ref(v_bs_1319_);
lean_dec_ref(v_post_1316_);
lean_dec_ref(v_pre_1315_);
v_a_1335_ = lean_ctor_get(v___x_1327_, 0);
v_isSharedCheck_1342_ = !lean_is_exclusive(v___x_1327_);
if (v_isSharedCheck_1342_ == 0)
{
v___x_1337_ = v___x_1327_;
v_isShared_1338_ = v_isSharedCheck_1342_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_a_1335_);
lean_dec(v___x_1327_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1342_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v___x_1340_; 
if (v_isShared_1338_ == 0)
{
v___x_1340_ = v___x_1337_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v_a_1335_);
v___x_1340_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
return v___x_1340_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__4(lean_object* v_pre_1343_, lean_object* v_post_1344_, lean_object* v_x_1345_, lean_object* v_x_1346_, lean_object* v_x_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_){
_start:
{
if (lean_obj_tag(v_x_1345_) == 5)
{
lean_object* v_fn_1352_; lean_object* v_arg_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; 
v_fn_1352_ = lean_ctor_get(v_x_1345_, 0);
lean_inc_ref(v_fn_1352_);
v_arg_1353_ = lean_ctor_get(v_x_1345_, 1);
lean_inc_ref(v_arg_1353_);
lean_dec_ref(v_x_1345_);
v___x_1354_ = lean_array_set(v_x_1346_, v_x_1347_, v_arg_1353_);
v___x_1355_ = lean_unsigned_to_nat(1u);
v___x_1356_ = lean_nat_sub(v_x_1347_, v___x_1355_);
lean_dec(v_x_1347_);
v_x_1345_ = v_fn_1352_;
v_x_1346_ = v___x_1354_;
v_x_1347_ = v___x_1356_;
goto _start;
}
else
{
lean_object* v___x_1358_; 
lean_dec(v_x_1347_);
lean_inc_ref(v_post_1344_);
lean_inc_ref(v_pre_1343_);
v___x_1358_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1343_, v_post_1344_, v_x_1345_, v___y_1348_, v___y_1349_, v___y_1350_);
if (lean_obj_tag(v___x_1358_) == 0)
{
lean_object* v_a_1359_; size_t v_sz_1360_; size_t v___x_1361_; lean_object* v___x_1362_; 
v_a_1359_ = lean_ctor_get(v___x_1358_, 0);
lean_inc(v_a_1359_);
lean_dec_ref(v___x_1358_);
v_sz_1360_ = lean_array_size(v_x_1346_);
v___x_1361_ = ((size_t)0ULL);
lean_inc_ref(v_post_1344_);
lean_inc_ref(v_pre_1343_);
v___x_1362_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1(v_pre_1343_, v_post_1344_, v_sz_1360_, v___x_1361_, v_x_1346_, v___y_1348_, v___y_1349_, v___y_1350_);
if (lean_obj_tag(v___x_1362_) == 0)
{
lean_object* v_a_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; 
v_a_1363_ = lean_ctor_get(v___x_1362_, 0);
lean_inc(v_a_1363_);
lean_dec_ref(v___x_1362_);
v___x_1364_ = l_Lean_mkAppN(v_a_1359_, v_a_1363_);
lean_dec(v_a_1363_);
v___x_1365_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1343_, v_post_1344_, v___x_1364_, v___y_1348_, v___y_1349_, v___y_1350_);
return v___x_1365_;
}
else
{
lean_object* v_a_1366_; lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1373_; 
lean_dec(v_a_1359_);
lean_dec_ref(v_post_1344_);
lean_dec_ref(v_pre_1343_);
v_a_1366_ = lean_ctor_get(v___x_1362_, 0);
v_isSharedCheck_1373_ = !lean_is_exclusive(v___x_1362_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1368_ = v___x_1362_;
v_isShared_1369_ = v_isSharedCheck_1373_;
goto v_resetjp_1367_;
}
else
{
lean_inc(v_a_1366_);
lean_dec(v___x_1362_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1373_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
lean_object* v___x_1371_; 
if (v_isShared_1369_ == 0)
{
v___x_1371_ = v___x_1368_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v_a_1366_);
v___x_1371_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
return v___x_1371_;
}
}
}
}
else
{
lean_dec_ref(v_x_1346_);
lean_dec_ref(v_post_1344_);
lean_dec_ref(v_pre_1343_);
return v___x_1358_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__1(lean_object* v___x_1374_, lean_object* v_pre_1375_, lean_object* v_e_1376_, lean_object* v_post_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_){
_start:
{
lean_object* v___y_1383_; lean_object* v___y_1384_; uint8_t v___y_1385_; lean_object* v___y_1386_; lean_object* v___y_1387_; lean_object* v___y_1388_; lean_object* v___y_1389_; uint8_t v___y_1390_; uint8_t v___y_1400_; lean_object* v___y_1401_; lean_object* v___y_1402_; lean_object* v___y_1403_; lean_object* v___y_1404_; uint8_t v___y_1405_; lean_object* v___y_1413_; uint8_t v___y_1414_; lean_object* v___y_1415_; lean_object* v___y_1416_; lean_object* v___y_1417_; uint8_t v___y_1418_; lean_object* v___x_1425_; 
v___x_1425_ = l_Lean_Core_checkSystem(v___x_1374_, v___y_1379_, v___y_1380_);
if (lean_obj_tag(v___x_1425_) == 0)
{
lean_object* v___x_1426_; 
lean_dec_ref(v___x_1425_);
lean_inc_ref(v_pre_1375_);
lean_inc(v___y_1380_);
lean_inc_ref(v___y_1379_);
lean_inc_ref(v_e_1376_);
v___x_1426_ = lean_apply_4(v_pre_1375_, v_e_1376_, v___y_1379_, v___y_1380_, lean_box(0));
if (lean_obj_tag(v___x_1426_) == 0)
{
lean_object* v_a_1427_; lean_object* v___x_1429_; uint8_t v_isShared_1430_; uint8_t v_isSharedCheck_1516_; 
v_a_1427_ = lean_ctor_get(v___x_1426_, 0);
v_isSharedCheck_1516_ = !lean_is_exclusive(v___x_1426_);
if (v_isSharedCheck_1516_ == 0)
{
v___x_1429_ = v___x_1426_;
v_isShared_1430_ = v_isSharedCheck_1516_;
goto v_resetjp_1428_;
}
else
{
lean_inc(v_a_1427_);
lean_dec(v___x_1426_);
v___x_1429_ = lean_box(0);
v_isShared_1430_ = v_isSharedCheck_1516_;
goto v_resetjp_1428_;
}
v_resetjp_1428_:
{
lean_object* v___y_1432_; 
switch(lean_obj_tag(v_a_1427_))
{
case 0:
{
lean_object* v_e_1506_; lean_object* v___x_1508_; 
lean_dec_ref(v_post_1377_);
lean_dec_ref(v_e_1376_);
lean_dec_ref(v_pre_1375_);
v_e_1506_ = lean_ctor_get(v_a_1427_, 0);
lean_inc_ref(v_e_1506_);
lean_dec_ref(v_a_1427_);
if (v_isShared_1430_ == 0)
{
lean_ctor_set(v___x_1429_, 0, v_e_1506_);
v___x_1508_ = v___x_1429_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v_e_1506_);
v___x_1508_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
return v___x_1508_;
}
}
case 1:
{
lean_object* v_e_1510_; lean_object* v___x_1511_; 
lean_del_object(v___x_1429_);
lean_dec_ref(v_e_1376_);
v_e_1510_ = lean_ctor_get(v_a_1427_, 0);
lean_inc_ref(v_e_1510_);
lean_dec_ref(v_a_1427_);
lean_inc_ref(v_post_1377_);
lean_inc_ref(v_pre_1375_);
v___x_1511_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1375_, v_post_1377_, v_e_1510_, v___y_1378_, v___y_1379_, v___y_1380_);
if (lean_obj_tag(v___x_1511_) == 0)
{
lean_object* v_a_1512_; lean_object* v___x_1513_; 
v_a_1512_ = lean_ctor_get(v___x_1511_, 0);
lean_inc(v_a_1512_);
lean_dec_ref(v___x_1511_);
v___x_1513_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1375_, v_post_1377_, v_a_1512_, v___y_1378_, v___y_1379_, v___y_1380_);
return v___x_1513_;
}
else
{
lean_dec_ref(v_post_1377_);
lean_dec_ref(v_pre_1375_);
return v___x_1511_;
}
}
default: 
{
lean_object* v_e_x3f_1514_; 
lean_del_object(v___x_1429_);
v_e_x3f_1514_ = lean_ctor_get(v_a_1427_, 0);
lean_inc(v_e_x3f_1514_);
lean_dec_ref(v_a_1427_);
if (lean_obj_tag(v_e_x3f_1514_) == 0)
{
v___y_1432_ = v_e_1376_;
goto v___jp_1431_;
}
else
{
lean_object* v_val_1515_; 
lean_dec_ref(v_e_1376_);
v_val_1515_ = lean_ctor_get(v_e_x3f_1514_, 0);
lean_inc(v_val_1515_);
lean_dec_ref(v_e_x3f_1514_);
v___y_1432_ = v_val_1515_;
goto v___jp_1431_;
}
}
}
v___jp_1431_:
{
switch(lean_obj_tag(v___y_1432_))
{
case 7:
{
lean_object* v_binderName_1433_; lean_object* v_binderType_1434_; lean_object* v_body_1435_; uint8_t v_binderInfo_1436_; lean_object* v___x_1437_; 
v_binderName_1433_ = lean_ctor_get(v___y_1432_, 0);
lean_inc(v_binderName_1433_);
v_binderType_1434_ = lean_ctor_get(v___y_1432_, 1);
v_body_1435_ = lean_ctor_get(v___y_1432_, 2);
v_binderInfo_1436_ = lean_ctor_get_uint8(v___y_1432_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1434_);
lean_inc_ref(v_post_1377_);
lean_inc_ref(v_pre_1375_);
v___x_1437_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1375_, v_post_1377_, v_binderType_1434_, v___y_1378_, v___y_1379_, v___y_1380_);
if (lean_obj_tag(v___x_1437_) == 0)
{
lean_object* v_a_1438_; lean_object* v___x_1439_; 
v_a_1438_ = lean_ctor_get(v___x_1437_, 0);
lean_inc(v_a_1438_);
lean_dec_ref(v___x_1437_);
lean_inc_ref(v_body_1435_);
lean_inc_ref(v_post_1377_);
lean_inc_ref(v_pre_1375_);
v___x_1439_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1375_, v_post_1377_, v_body_1435_, v___y_1378_, v___y_1379_, v___y_1380_);
if (lean_obj_tag(v___x_1439_) == 0)
{
lean_object* v_a_1440_; size_t v___x_1441_; size_t v___x_1442_; uint8_t v___x_1443_; 
v_a_1440_ = lean_ctor_get(v___x_1439_, 0);
lean_inc(v_a_1440_);
lean_dec_ref(v___x_1439_);
v___x_1441_ = lean_ptr_addr(v_binderType_1434_);
v___x_1442_ = lean_ptr_addr(v_a_1438_);
v___x_1443_ = lean_usize_dec_eq(v___x_1441_, v___x_1442_);
if (v___x_1443_ == 0)
{
v___y_1413_ = v_a_1438_;
v___y_1414_ = v_binderInfo_1436_;
v___y_1415_ = v_binderName_1433_;
v___y_1416_ = v_a_1440_;
v___y_1417_ = v___y_1432_;
v___y_1418_ = v___x_1443_;
goto v___jp_1412_;
}
else
{
size_t v___x_1444_; size_t v___x_1445_; uint8_t v___x_1446_; 
v___x_1444_ = lean_ptr_addr(v_body_1435_);
v___x_1445_ = lean_ptr_addr(v_a_1440_);
v___x_1446_ = lean_usize_dec_eq(v___x_1444_, v___x_1445_);
v___y_1413_ = v_a_1438_;
v___y_1414_ = v_binderInfo_1436_;
v___y_1415_ = v_binderName_1433_;
v___y_1416_ = v_a_1440_;
v___y_1417_ = v___y_1432_;
v___y_1418_ = v___x_1446_;
goto v___jp_1412_;
}
}
else
{
lean_dec(v_a_1438_);
lean_dec(v_binderName_1433_);
lean_dec_ref(v___y_1432_);
lean_dec_ref(v_post_1377_);
lean_dec_ref(v_pre_1375_);
return v___x_1439_;
}
}
else
{
lean_dec_ref(v___y_1432_);
lean_dec(v_binderName_1433_);
lean_dec_ref(v_post_1377_);
lean_dec_ref(v_pre_1375_);
return v___x_1437_;
}
}
case 6:
{
lean_object* v_binderName_1447_; lean_object* v_binderType_1448_; lean_object* v_body_1449_; uint8_t v_binderInfo_1450_; lean_object* v___x_1451_; 
v_binderName_1447_ = lean_ctor_get(v___y_1432_, 0);
lean_inc(v_binderName_1447_);
v_binderType_1448_ = lean_ctor_get(v___y_1432_, 1);
v_body_1449_ = lean_ctor_get(v___y_1432_, 2);
v_binderInfo_1450_ = lean_ctor_get_uint8(v___y_1432_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1448_);
lean_inc_ref(v_post_1377_);
lean_inc_ref(v_pre_1375_);
v___x_1451_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1375_, v_post_1377_, v_binderType_1448_, v___y_1378_, v___y_1379_, v___y_1380_);
if (lean_obj_tag(v___x_1451_) == 0)
{
lean_object* v_a_1452_; lean_object* v___x_1453_; 
v_a_1452_ = lean_ctor_get(v___x_1451_, 0);
lean_inc(v_a_1452_);
lean_dec_ref(v___x_1451_);
lean_inc_ref(v_body_1449_);
lean_inc_ref(v_post_1377_);
lean_inc_ref(v_pre_1375_);
v___x_1453_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1375_, v_post_1377_, v_body_1449_, v___y_1378_, v___y_1379_, v___y_1380_);
if (lean_obj_tag(v___x_1453_) == 0)
{
lean_object* v_a_1454_; size_t v___x_1455_; size_t v___x_1456_; uint8_t v___x_1457_; 
v_a_1454_ = lean_ctor_get(v___x_1453_, 0);
lean_inc(v_a_1454_);
lean_dec_ref(v___x_1453_);
v___x_1455_ = lean_ptr_addr(v_binderType_1448_);
v___x_1456_ = lean_ptr_addr(v_a_1452_);
v___x_1457_ = lean_usize_dec_eq(v___x_1455_, v___x_1456_);
if (v___x_1457_ == 0)
{
v___y_1400_ = v_binderInfo_1450_;
v___y_1401_ = v_a_1452_;
v___y_1402_ = v_a_1454_;
v___y_1403_ = v_binderName_1447_;
v___y_1404_ = v___y_1432_;
v___y_1405_ = v___x_1457_;
goto v___jp_1399_;
}
else
{
size_t v___x_1458_; size_t v___x_1459_; uint8_t v___x_1460_; 
v___x_1458_ = lean_ptr_addr(v_body_1449_);
v___x_1459_ = lean_ptr_addr(v_a_1454_);
v___x_1460_ = lean_usize_dec_eq(v___x_1458_, v___x_1459_);
v___y_1400_ = v_binderInfo_1450_;
v___y_1401_ = v_a_1452_;
v___y_1402_ = v_a_1454_;
v___y_1403_ = v_binderName_1447_;
v___y_1404_ = v___y_1432_;
v___y_1405_ = v___x_1460_;
goto v___jp_1399_;
}
}
else
{
lean_dec(v_a_1452_);
lean_dec_ref(v___y_1432_);
lean_dec(v_binderName_1447_);
lean_dec_ref(v_post_1377_);
lean_dec_ref(v_pre_1375_);
return v___x_1453_;
}
}
else
{
lean_dec_ref(v___y_1432_);
lean_dec(v_binderName_1447_);
lean_dec_ref(v_post_1377_);
lean_dec_ref(v_pre_1375_);
return v___x_1451_;
}
}
case 8:
{
lean_object* v_declName_1461_; lean_object* v_type_1462_; lean_object* v_value_1463_; lean_object* v_body_1464_; uint8_t v_nondep_1465_; lean_object* v___x_1466_; 
v_declName_1461_ = lean_ctor_get(v___y_1432_, 0);
lean_inc(v_declName_1461_);
v_type_1462_ = lean_ctor_get(v___y_1432_, 1);
v_value_1463_ = lean_ctor_get(v___y_1432_, 2);
v_body_1464_ = lean_ctor_get(v___y_1432_, 3);
lean_inc_ref(v_body_1464_);
v_nondep_1465_ = lean_ctor_get_uint8(v___y_1432_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_1462_);
lean_inc_ref(v_post_1377_);
lean_inc_ref(v_pre_1375_);
v___x_1466_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1375_, v_post_1377_, v_type_1462_, v___y_1378_, v___y_1379_, v___y_1380_);
if (lean_obj_tag(v___x_1466_) == 0)
{
lean_object* v_a_1467_; lean_object* v___x_1468_; 
v_a_1467_ = lean_ctor_get(v___x_1466_, 0);
lean_inc(v_a_1467_);
lean_dec_ref(v___x_1466_);
lean_inc_ref(v_value_1463_);
lean_inc_ref(v_post_1377_);
lean_inc_ref(v_pre_1375_);
v___x_1468_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1375_, v_post_1377_, v_value_1463_, v___y_1378_, v___y_1379_, v___y_1380_);
if (lean_obj_tag(v___x_1468_) == 0)
{
lean_object* v_a_1469_; lean_object* v___x_1470_; 
v_a_1469_ = lean_ctor_get(v___x_1468_, 0);
lean_inc(v_a_1469_);
lean_dec_ref(v___x_1468_);
lean_inc_ref(v_body_1464_);
lean_inc_ref(v_post_1377_);
lean_inc_ref(v_pre_1375_);
v___x_1470_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1375_, v_post_1377_, v_body_1464_, v___y_1378_, v___y_1379_, v___y_1380_);
if (lean_obj_tag(v___x_1470_) == 0)
{
lean_object* v_a_1471_; size_t v___x_1472_; size_t v___x_1473_; uint8_t v___x_1474_; 
v_a_1471_ = lean_ctor_get(v___x_1470_, 0);
lean_inc(v_a_1471_);
lean_dec_ref(v___x_1470_);
v___x_1472_ = lean_ptr_addr(v_type_1462_);
v___x_1473_ = lean_ptr_addr(v_a_1467_);
v___x_1474_ = lean_usize_dec_eq(v___x_1472_, v___x_1473_);
if (v___x_1474_ == 0)
{
v___y_1383_ = v_a_1471_;
v___y_1384_ = v_declName_1461_;
v___y_1385_ = v_nondep_1465_;
v___y_1386_ = v_a_1469_;
v___y_1387_ = v_a_1467_;
v___y_1388_ = v_body_1464_;
v___y_1389_ = v___y_1432_;
v___y_1390_ = v___x_1474_;
goto v___jp_1382_;
}
else
{
size_t v___x_1475_; size_t v___x_1476_; uint8_t v___x_1477_; 
v___x_1475_ = lean_ptr_addr(v_value_1463_);
v___x_1476_ = lean_ptr_addr(v_a_1469_);
v___x_1477_ = lean_usize_dec_eq(v___x_1475_, v___x_1476_);
v___y_1383_ = v_a_1471_;
v___y_1384_ = v_declName_1461_;
v___y_1385_ = v_nondep_1465_;
v___y_1386_ = v_a_1469_;
v___y_1387_ = v_a_1467_;
v___y_1388_ = v_body_1464_;
v___y_1389_ = v___y_1432_;
v___y_1390_ = v___x_1477_;
goto v___jp_1382_;
}
}
else
{
lean_dec(v_a_1469_);
lean_dec(v_a_1467_);
lean_dec_ref(v_body_1464_);
lean_dec_ref(v___y_1432_);
lean_dec(v_declName_1461_);
lean_dec_ref(v_post_1377_);
lean_dec_ref(v_pre_1375_);
return v___x_1470_;
}
}
else
{
lean_dec(v_a_1467_);
lean_dec_ref(v_body_1464_);
lean_dec(v_declName_1461_);
lean_dec_ref(v___y_1432_);
lean_dec_ref(v_post_1377_);
lean_dec_ref(v_pre_1375_);
return v___x_1468_;
}
}
else
{
lean_dec_ref(v_body_1464_);
lean_dec(v_declName_1461_);
lean_dec_ref(v___y_1432_);
lean_dec_ref(v_post_1377_);
lean_dec_ref(v_pre_1375_);
return v___x_1466_;
}
}
case 5:
{
lean_object* v_dummy_1478_; lean_object* v_nargs_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; 
v_dummy_1478_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_1479_ = l_Lean_Expr_getAppNumArgs(v___y_1432_);
lean_inc(v_nargs_1479_);
v___x_1480_ = lean_mk_array(v_nargs_1479_, v_dummy_1478_);
v___x_1481_ = lean_unsigned_to_nat(1u);
v___x_1482_ = lean_nat_sub(v_nargs_1479_, v___x_1481_);
lean_dec(v_nargs_1479_);
v___x_1483_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__4(v_pre_1375_, v_post_1377_, v___y_1432_, v___x_1480_, v___x_1482_, v___y_1378_, v___y_1379_, v___y_1380_);
return v___x_1483_;
}
case 10:
{
lean_object* v_data_1484_; lean_object* v_expr_1485_; lean_object* v___x_1486_; 
v_data_1484_ = lean_ctor_get(v___y_1432_, 0);
v_expr_1485_ = lean_ctor_get(v___y_1432_, 1);
lean_inc_ref(v_expr_1485_);
lean_inc_ref(v_post_1377_);
lean_inc_ref(v_pre_1375_);
v___x_1486_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1375_, v_post_1377_, v_expr_1485_, v___y_1378_, v___y_1379_, v___y_1380_);
if (lean_obj_tag(v___x_1486_) == 0)
{
lean_object* v_a_1487_; size_t v___x_1488_; size_t v___x_1489_; uint8_t v___x_1490_; 
v_a_1487_ = lean_ctor_get(v___x_1486_, 0);
lean_inc(v_a_1487_);
lean_dec_ref(v___x_1486_);
v___x_1488_ = lean_ptr_addr(v_expr_1485_);
v___x_1489_ = lean_ptr_addr(v_a_1487_);
v___x_1490_ = lean_usize_dec_eq(v___x_1488_, v___x_1489_);
if (v___x_1490_ == 0)
{
lean_object* v___x_1491_; lean_object* v___x_1492_; 
lean_inc(v_data_1484_);
lean_dec_ref(v___y_1432_);
v___x_1491_ = l_Lean_Expr_mdata___override(v_data_1484_, v_a_1487_);
v___x_1492_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1375_, v_post_1377_, v___x_1491_, v___y_1378_, v___y_1379_, v___y_1380_);
return v___x_1492_;
}
else
{
lean_object* v___x_1493_; 
lean_dec(v_a_1487_);
v___x_1493_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1375_, v_post_1377_, v___y_1432_, v___y_1378_, v___y_1379_, v___y_1380_);
return v___x_1493_;
}
}
else
{
lean_dec_ref(v___y_1432_);
lean_dec_ref(v_post_1377_);
lean_dec_ref(v_pre_1375_);
return v___x_1486_;
}
}
case 11:
{
lean_object* v_typeName_1494_; lean_object* v_idx_1495_; lean_object* v_struct_1496_; lean_object* v___x_1497_; 
v_typeName_1494_ = lean_ctor_get(v___y_1432_, 0);
v_idx_1495_ = lean_ctor_get(v___y_1432_, 1);
v_struct_1496_ = lean_ctor_get(v___y_1432_, 2);
lean_inc_ref(v_struct_1496_);
lean_inc_ref(v_post_1377_);
lean_inc_ref(v_pre_1375_);
v___x_1497_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1375_, v_post_1377_, v_struct_1496_, v___y_1378_, v___y_1379_, v___y_1380_);
if (lean_obj_tag(v___x_1497_) == 0)
{
lean_object* v_a_1498_; size_t v___x_1499_; size_t v___x_1500_; uint8_t v___x_1501_; 
v_a_1498_ = lean_ctor_get(v___x_1497_, 0);
lean_inc(v_a_1498_);
lean_dec_ref(v___x_1497_);
v___x_1499_ = lean_ptr_addr(v_struct_1496_);
v___x_1500_ = lean_ptr_addr(v_a_1498_);
v___x_1501_ = lean_usize_dec_eq(v___x_1499_, v___x_1500_);
if (v___x_1501_ == 0)
{
lean_object* v___x_1502_; lean_object* v___x_1503_; 
lean_inc(v_idx_1495_);
lean_inc(v_typeName_1494_);
lean_dec_ref(v___y_1432_);
v___x_1502_ = l_Lean_Expr_proj___override(v_typeName_1494_, v_idx_1495_, v_a_1498_);
v___x_1503_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1375_, v_post_1377_, v___x_1502_, v___y_1378_, v___y_1379_, v___y_1380_);
return v___x_1503_;
}
else
{
lean_object* v___x_1504_; 
lean_dec(v_a_1498_);
v___x_1504_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1375_, v_post_1377_, v___y_1432_, v___y_1378_, v___y_1379_, v___y_1380_);
return v___x_1504_;
}
}
else
{
lean_dec_ref(v___y_1432_);
lean_dec_ref(v_post_1377_);
lean_dec_ref(v_pre_1375_);
return v___x_1497_;
}
}
default: 
{
lean_object* v___x_1505_; 
v___x_1505_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1375_, v_post_1377_, v___y_1432_, v___y_1378_, v___y_1379_, v___y_1380_);
return v___x_1505_;
}
}
}
}
}
else
{
lean_object* v_a_1517_; lean_object* v___x_1519_; uint8_t v_isShared_1520_; uint8_t v_isSharedCheck_1524_; 
lean_dec_ref(v_post_1377_);
lean_dec_ref(v_e_1376_);
lean_dec_ref(v_pre_1375_);
v_a_1517_ = lean_ctor_get(v___x_1426_, 0);
v_isSharedCheck_1524_ = !lean_is_exclusive(v___x_1426_);
if (v_isSharedCheck_1524_ == 0)
{
v___x_1519_ = v___x_1426_;
v_isShared_1520_ = v_isSharedCheck_1524_;
goto v_resetjp_1518_;
}
else
{
lean_inc(v_a_1517_);
lean_dec(v___x_1426_);
v___x_1519_ = lean_box(0);
v_isShared_1520_ = v_isSharedCheck_1524_;
goto v_resetjp_1518_;
}
v_resetjp_1518_:
{
lean_object* v___x_1522_; 
if (v_isShared_1520_ == 0)
{
v___x_1522_ = v___x_1519_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v_a_1517_);
v___x_1522_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
return v___x_1522_;
}
}
}
}
else
{
lean_object* v_a_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1532_; 
lean_dec_ref(v_post_1377_);
lean_dec_ref(v_e_1376_);
lean_dec_ref(v_pre_1375_);
v_a_1525_ = lean_ctor_get(v___x_1425_, 0);
v_isSharedCheck_1532_ = !lean_is_exclusive(v___x_1425_);
if (v_isSharedCheck_1532_ == 0)
{
v___x_1527_ = v___x_1425_;
v_isShared_1528_ = v_isSharedCheck_1532_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_a_1525_);
lean_dec(v___x_1425_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1532_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
lean_object* v___x_1530_; 
if (v_isShared_1528_ == 0)
{
v___x_1530_ = v___x_1527_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v_a_1525_);
v___x_1530_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
return v___x_1530_;
}
}
}
v___jp_1382_:
{
if (v___y_1390_ == 0)
{
lean_object* v___x_1391_; lean_object* v___x_1392_; 
lean_dec_ref(v___y_1389_);
lean_dec_ref(v___y_1388_);
v___x_1391_ = l_Lean_Expr_letE___override(v___y_1384_, v___y_1387_, v___y_1386_, v___y_1383_, v___y_1385_);
v___x_1392_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1375_, v_post_1377_, v___x_1391_, v___y_1378_, v___y_1379_, v___y_1380_);
return v___x_1392_;
}
else
{
size_t v___x_1393_; size_t v___x_1394_; uint8_t v___x_1395_; 
v___x_1393_ = lean_ptr_addr(v___y_1388_);
lean_dec_ref(v___y_1388_);
v___x_1394_ = lean_ptr_addr(v___y_1383_);
v___x_1395_ = lean_usize_dec_eq(v___x_1393_, v___x_1394_);
if (v___x_1395_ == 0)
{
lean_object* v___x_1396_; lean_object* v___x_1397_; 
lean_dec_ref(v___y_1389_);
v___x_1396_ = l_Lean_Expr_letE___override(v___y_1384_, v___y_1387_, v___y_1386_, v___y_1383_, v___y_1385_);
v___x_1397_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1375_, v_post_1377_, v___x_1396_, v___y_1378_, v___y_1379_, v___y_1380_);
return v___x_1397_;
}
else
{
lean_object* v___x_1398_; 
lean_dec_ref(v___y_1387_);
lean_dec_ref(v___y_1386_);
lean_dec(v___y_1384_);
lean_dec_ref(v___y_1383_);
v___x_1398_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1375_, v_post_1377_, v___y_1389_, v___y_1378_, v___y_1379_, v___y_1380_);
return v___x_1398_;
}
}
}
v___jp_1399_:
{
if (v___y_1405_ == 0)
{
lean_object* v___x_1406_; lean_object* v___x_1407_; 
lean_dec_ref(v___y_1404_);
v___x_1406_ = l_Lean_Expr_lam___override(v___y_1403_, v___y_1401_, v___y_1402_, v___y_1400_);
v___x_1407_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1375_, v_post_1377_, v___x_1406_, v___y_1378_, v___y_1379_, v___y_1380_);
return v___x_1407_;
}
else
{
uint8_t v___x_1408_; 
v___x_1408_ = l_Lean_instBEqBinderInfo_beq(v___y_1400_, v___y_1400_);
if (v___x_1408_ == 0)
{
lean_object* v___x_1409_; lean_object* v___x_1410_; 
lean_dec_ref(v___y_1404_);
v___x_1409_ = l_Lean_Expr_lam___override(v___y_1403_, v___y_1401_, v___y_1402_, v___y_1400_);
v___x_1410_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1375_, v_post_1377_, v___x_1409_, v___y_1378_, v___y_1379_, v___y_1380_);
return v___x_1410_;
}
else
{
lean_object* v___x_1411_; 
lean_dec(v___y_1403_);
lean_dec_ref(v___y_1402_);
lean_dec_ref(v___y_1401_);
v___x_1411_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1375_, v_post_1377_, v___y_1404_, v___y_1378_, v___y_1379_, v___y_1380_);
return v___x_1411_;
}
}
}
v___jp_1412_:
{
if (v___y_1418_ == 0)
{
lean_object* v___x_1419_; lean_object* v___x_1420_; 
lean_dec_ref(v___y_1417_);
v___x_1419_ = l_Lean_Expr_forallE___override(v___y_1415_, v___y_1413_, v___y_1416_, v___y_1414_);
v___x_1420_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1375_, v_post_1377_, v___x_1419_, v___y_1378_, v___y_1379_, v___y_1380_);
return v___x_1420_;
}
else
{
uint8_t v___x_1421_; 
v___x_1421_ = l_Lean_instBEqBinderInfo_beq(v___y_1414_, v___y_1414_);
if (v___x_1421_ == 0)
{
lean_object* v___x_1422_; lean_object* v___x_1423_; 
lean_dec_ref(v___y_1417_);
v___x_1422_ = l_Lean_Expr_forallE___override(v___y_1415_, v___y_1413_, v___y_1416_, v___y_1414_);
v___x_1423_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1375_, v_post_1377_, v___x_1422_, v___y_1378_, v___y_1379_, v___y_1380_);
return v___x_1423_;
}
else
{
lean_object* v___x_1424_; 
lean_dec_ref(v___y_1416_);
lean_dec(v___y_1415_);
lean_dec_ref(v___y_1413_);
v___x_1424_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1375_, v_post_1377_, v___y_1417_, v___y_1378_, v___y_1379_, v___y_1380_);
return v___x_1424_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__1___boxed(lean_object* v___x_1533_, lean_object* v_pre_1534_, lean_object* v_e_1535_, lean_object* v_post_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_){
_start:
{
lean_object* v_res_1541_; 
v_res_1541_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__1(v___x_1533_, v_pre_1534_, v_e_1535_, v_post_1536_, v___y_1537_, v___y_1538_, v___y_1539_);
lean_dec(v___y_1539_);
lean_dec_ref(v___y_1538_);
lean_dec(v___y_1537_);
return v_res_1541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(lean_object* v_pre_1542_, lean_object* v_post_1543_, lean_object* v_e_1544_, lean_object* v_a_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_){
_start:
{
lean_object* v___x_1549_; lean_object* v___x_1550_; 
lean_inc(v_a_1545_);
v___x_1549_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1549_, 0, lean_box(0));
lean_closure_set(v___x_1549_, 1, lean_box(0));
lean_closure_set(v___x_1549_, 2, v_a_1545_);
v___x_1550_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__0(lean_box(0), v___x_1549_, v___y_1546_, v___y_1547_);
if (lean_obj_tag(v___x_1550_) == 0)
{
lean_object* v_a_1551_; lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1582_; 
v_a_1551_ = lean_ctor_get(v___x_1550_, 0);
v_isSharedCheck_1582_ = !lean_is_exclusive(v___x_1550_);
if (v_isSharedCheck_1582_ == 0)
{
v___x_1553_ = v___x_1550_;
v_isShared_1554_ = v_isSharedCheck_1582_;
goto v_resetjp_1552_;
}
else
{
lean_inc(v_a_1551_);
lean_dec(v___x_1550_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1582_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
lean_object* v___x_1555_; 
v___x_1555_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg(v_a_1551_, v_e_1544_);
lean_dec(v_a_1551_);
if (lean_obj_tag(v___x_1555_) == 0)
{
lean_object* v___x_1556_; lean_object* v___f_1557_; lean_object* v___x_1558_; 
lean_del_object(v___x_1553_);
v___x_1556_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__19___closed__0));
lean_inc_ref(v_e_1544_);
v___f_1557_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__1___boxed), 8, 4);
lean_closure_set(v___f_1557_, 0, v___x_1556_);
lean_closure_set(v___f_1557_, 1, v_pre_1542_);
lean_closure_set(v___f_1557_, 2, v_e_1544_);
lean_closure_set(v___f_1557_, 3, v_post_1543_);
v___x_1558_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___redArg(v___f_1557_, v_a_1545_, v___y_1546_, v___y_1547_);
if (lean_obj_tag(v___x_1558_) == 0)
{
lean_object* v_a_1559_; lean_object* v___f_1560_; lean_object* v___x_1561_; 
v_a_1559_ = lean_ctor_get(v___x_1558_, 0);
lean_inc_n(v_a_1559_, 2);
lean_dec_ref(v___x_1558_);
lean_inc(v_a_1545_);
v___f_1560_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1560_, 0, v_a_1545_);
lean_closure_set(v___f_1560_, 1, v_e_1544_);
lean_closure_set(v___f_1560_, 2, v_a_1559_);
v___x_1561_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__0(lean_box(0), v___f_1560_, v___y_1546_, v___y_1547_);
if (lean_obj_tag(v___x_1561_) == 0)
{
lean_object* v___x_1563_; uint8_t v_isShared_1564_; uint8_t v_isSharedCheck_1568_; 
v_isSharedCheck_1568_ = !lean_is_exclusive(v___x_1561_);
if (v_isSharedCheck_1568_ == 0)
{
lean_object* v_unused_1569_; 
v_unused_1569_ = lean_ctor_get(v___x_1561_, 0);
lean_dec(v_unused_1569_);
v___x_1563_ = v___x_1561_;
v_isShared_1564_ = v_isSharedCheck_1568_;
goto v_resetjp_1562_;
}
else
{
lean_dec(v___x_1561_);
v___x_1563_ = lean_box(0);
v_isShared_1564_ = v_isSharedCheck_1568_;
goto v_resetjp_1562_;
}
v_resetjp_1562_:
{
lean_object* v___x_1566_; 
if (v_isShared_1564_ == 0)
{
lean_ctor_set(v___x_1563_, 0, v_a_1559_);
v___x_1566_ = v___x_1563_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v_a_1559_);
v___x_1566_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
return v___x_1566_;
}
}
}
else
{
lean_object* v_a_1570_; lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1577_; 
lean_dec(v_a_1559_);
v_a_1570_ = lean_ctor_get(v___x_1561_, 0);
v_isSharedCheck_1577_ = !lean_is_exclusive(v___x_1561_);
if (v_isSharedCheck_1577_ == 0)
{
v___x_1572_ = v___x_1561_;
v_isShared_1573_ = v_isSharedCheck_1577_;
goto v_resetjp_1571_;
}
else
{
lean_inc(v_a_1570_);
lean_dec(v___x_1561_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1577_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
lean_object* v___x_1575_; 
if (v_isShared_1573_ == 0)
{
v___x_1575_ = v___x_1572_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v_a_1570_);
v___x_1575_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
return v___x_1575_;
}
}
}
}
else
{
lean_dec_ref(v_e_1544_);
return v___x_1558_;
}
}
else
{
lean_object* v_val_1578_; lean_object* v___x_1580_; 
lean_dec_ref(v_e_1544_);
lean_dec_ref(v_post_1543_);
lean_dec_ref(v_pre_1542_);
v_val_1578_ = lean_ctor_get(v___x_1555_, 0);
lean_inc(v_val_1578_);
lean_dec_ref(v___x_1555_);
if (v_isShared_1554_ == 0)
{
lean_ctor_set(v___x_1553_, 0, v_val_1578_);
v___x_1580_ = v___x_1553_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v_val_1578_);
v___x_1580_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
return v___x_1580_;
}
}
}
}
else
{
lean_object* v_a_1583_; lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1590_; 
lean_dec_ref(v_e_1544_);
lean_dec_ref(v_post_1543_);
lean_dec_ref(v_pre_1542_);
v_a_1583_ = lean_ctor_get(v___x_1550_, 0);
v_isSharedCheck_1590_ = !lean_is_exclusive(v___x_1550_);
if (v_isSharedCheck_1590_ == 0)
{
v___x_1585_ = v___x_1550_;
v_isShared_1586_ = v_isSharedCheck_1590_;
goto v_resetjp_1584_;
}
else
{
lean_inc(v_a_1583_);
lean_dec(v___x_1550_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1590_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
lean_object* v___x_1588_; 
if (v_isShared_1586_ == 0)
{
v___x_1588_ = v___x_1585_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v_a_1583_);
v___x_1588_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
return v___x_1588_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(lean_object* v_pre_1591_, lean_object* v_post_1592_, lean_object* v_e_1593_, lean_object* v_a_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_){
_start:
{
lean_object* v___x_1598_; 
lean_inc_ref(v_post_1592_);
lean_inc(v___y_1596_);
lean_inc_ref(v___y_1595_);
lean_inc_ref(v_e_1593_);
v___x_1598_ = lean_apply_4(v_post_1592_, v_e_1593_, v___y_1595_, v___y_1596_, lean_box(0));
if (lean_obj_tag(v___x_1598_) == 0)
{
lean_object* v_a_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1617_; 
v_a_1599_ = lean_ctor_get(v___x_1598_, 0);
v_isSharedCheck_1617_ = !lean_is_exclusive(v___x_1598_);
if (v_isSharedCheck_1617_ == 0)
{
v___x_1601_ = v___x_1598_;
v_isShared_1602_ = v_isSharedCheck_1617_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_a_1599_);
lean_dec(v___x_1598_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1617_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
switch(lean_obj_tag(v_a_1599_))
{
case 0:
{
lean_object* v_e_1603_; lean_object* v___x_1605_; 
lean_dec_ref(v_e_1593_);
lean_dec_ref(v_post_1592_);
lean_dec_ref(v_pre_1591_);
v_e_1603_ = lean_ctor_get(v_a_1599_, 0);
lean_inc_ref(v_e_1603_);
lean_dec_ref(v_a_1599_);
if (v_isShared_1602_ == 0)
{
lean_ctor_set(v___x_1601_, 0, v_e_1603_);
v___x_1605_ = v___x_1601_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_e_1603_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
return v___x_1605_;
}
}
case 1:
{
lean_object* v_e_1607_; lean_object* v___x_1608_; 
lean_del_object(v___x_1601_);
lean_dec_ref(v_e_1593_);
v_e_1607_ = lean_ctor_get(v_a_1599_, 0);
lean_inc_ref(v_e_1607_);
lean_dec_ref(v_a_1599_);
v___x_1608_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1591_, v_post_1592_, v_e_1607_, v_a_1594_, v___y_1595_, v___y_1596_);
return v___x_1608_;
}
default: 
{
lean_object* v_e_x3f_1609_; 
lean_dec_ref(v_post_1592_);
lean_dec_ref(v_pre_1591_);
v_e_x3f_1609_ = lean_ctor_get(v_a_1599_, 0);
lean_inc(v_e_x3f_1609_);
lean_dec_ref(v_a_1599_);
if (lean_obj_tag(v_e_x3f_1609_) == 0)
{
lean_object* v___x_1611_; 
if (v_isShared_1602_ == 0)
{
lean_ctor_set(v___x_1601_, 0, v_e_1593_);
v___x_1611_ = v___x_1601_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v_e_1593_);
v___x_1611_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
return v___x_1611_;
}
}
else
{
lean_object* v_val_1613_; lean_object* v___x_1615_; 
lean_dec_ref(v_e_1593_);
v_val_1613_ = lean_ctor_get(v_e_x3f_1609_, 0);
lean_inc(v_val_1613_);
lean_dec_ref(v_e_x3f_1609_);
if (v_isShared_1602_ == 0)
{
lean_ctor_set(v___x_1601_, 0, v_val_1613_);
v___x_1615_ = v___x_1601_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v_val_1613_);
v___x_1615_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
return v___x_1615_;
}
}
}
}
}
}
else
{
lean_object* v_a_1618_; lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1625_; 
lean_dec_ref(v_e_1593_);
lean_dec_ref(v_post_1592_);
lean_dec_ref(v_pre_1591_);
v_a_1618_ = lean_ctor_get(v___x_1598_, 0);
v_isSharedCheck_1625_ = !lean_is_exclusive(v___x_1598_);
if (v_isSharedCheck_1625_ == 0)
{
v___x_1620_ = v___x_1598_;
v_isShared_1621_ = v_isSharedCheck_1625_;
goto v_resetjp_1619_;
}
else
{
lean_inc(v_a_1618_);
lean_dec(v___x_1598_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1625_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
lean_object* v___x_1623_; 
if (v_isShared_1621_ == 0)
{
v___x_1623_ = v___x_1620_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v_a_1618_);
v___x_1623_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
return v___x_1623_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_1626_, lean_object* v_post_1627_, lean_object* v_e_1628_, lean_object* v_a_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_){
_start:
{
lean_object* v_res_1633_; 
v_res_1633_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1626_, v_post_1627_, v_e_1628_, v_a_1629_, v___y_1630_, v___y_1631_);
lean_dec(v___y_1631_);
lean_dec_ref(v___y_1630_);
lean_dec(v_a_1629_);
return v_res_1633_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_1634_, lean_object* v_post_1635_, lean_object* v_sz_1636_, lean_object* v_i_1637_, lean_object* v_bs_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_){
_start:
{
size_t v_sz_boxed_1643_; size_t v_i_boxed_1644_; lean_object* v_res_1645_; 
v_sz_boxed_1643_ = lean_unbox_usize(v_sz_1636_);
lean_dec(v_sz_1636_);
v_i_boxed_1644_ = lean_unbox_usize(v_i_1637_);
lean_dec(v_i_1637_);
v_res_1645_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1(v_pre_1634_, v_post_1635_, v_sz_boxed_1643_, v_i_boxed_1644_, v_bs_1638_, v___y_1639_, v___y_1640_, v___y_1641_);
lean_dec(v___y_1641_);
lean_dec_ref(v___y_1640_);
lean_dec(v___y_1639_);
return v_res_1645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__4___boxed(lean_object* v_pre_1646_, lean_object* v_post_1647_, lean_object* v_x_1648_, lean_object* v_x_1649_, lean_object* v_x_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_){
_start:
{
lean_object* v_res_1655_; 
v_res_1655_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__4(v_pre_1646_, v_post_1647_, v_x_1648_, v_x_1649_, v_x_1650_, v___y_1651_, v___y_1652_, v___y_1653_);
lean_dec(v___y_1653_);
lean_dec_ref(v___y_1652_);
lean_dec(v___y_1651_);
return v_res_1655_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___boxed(lean_object* v_pre_1656_, lean_object* v_post_1657_, lean_object* v_e_1658_, lean_object* v_a_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_){
_start:
{
lean_object* v_res_1663_; 
v_res_1663_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1656_, v_post_1657_, v_e_1658_, v_a_1659_, v___y_1660_, v___y_1661_);
lean_dec(v___y_1661_);
lean_dec_ref(v___y_1660_);
lean_dec(v_a_1659_);
return v_res_1663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___lam__0(lean_object* v_00_u03b1_1664_, lean_object* v_x_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_){
_start:
{
lean_object* v___x_1669_; lean_object* v___x_1670_; 
v___x_1669_ = lean_apply_1(v_x_1665_, lean_box(0));
v___x_1670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1670_, 0, v___x_1669_);
return v___x_1670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___lam__0___boxed(lean_object* v_00_u03b1_1671_, lean_object* v_x_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_){
_start:
{
lean_object* v_res_1676_; 
v_res_1676_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___lam__0(v_00_u03b1_1671_, v_x_1672_, v___y_1673_, v___y_1674_);
lean_dec(v___y_1674_);
lean_dec_ref(v___y_1673_);
return v_res_1676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(lean_object* v_input_1677_, lean_object* v_pre_1678_, lean_object* v_post_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_){
_start:
{
lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v_a_1685_; lean_object* v___x_1686_; 
v___x_1683_ = lean_obj_once(&l_Lean_Core_transform___redArg___closed__2, &l_Lean_Core_transform___redArg___closed__2_once, _init_l_Lean_Core_transform___redArg___closed__2);
v___x_1684_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___lam__0(lean_box(0), v___x_1683_, v___y_1680_, v___y_1681_);
v_a_1685_ = lean_ctor_get(v___x_1684_, 0);
lean_inc(v_a_1685_);
lean_dec_ref(v___x_1684_);
v___x_1686_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1678_, v_post_1679_, v_input_1677_, v_a_1685_, v___y_1680_, v___y_1681_);
if (lean_obj_tag(v___x_1686_) == 0)
{
lean_object* v_a_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1696_; 
v_a_1687_ = lean_ctor_get(v___x_1686_, 0);
lean_inc(v_a_1687_);
lean_dec_ref(v___x_1686_);
v___x_1688_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1688_, 0, lean_box(0));
lean_closure_set(v___x_1688_, 1, lean_box(0));
lean_closure_set(v___x_1688_, 2, v_a_1685_);
v___x_1689_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___lam__0(lean_box(0), v___x_1688_, v___y_1680_, v___y_1681_);
v_isSharedCheck_1696_ = !lean_is_exclusive(v___x_1689_);
if (v_isSharedCheck_1696_ == 0)
{
lean_object* v_unused_1697_; 
v_unused_1697_ = lean_ctor_get(v___x_1689_, 0);
lean_dec(v_unused_1697_);
v___x_1691_ = v___x_1689_;
v_isShared_1692_ = v_isSharedCheck_1696_;
goto v_resetjp_1690_;
}
else
{
lean_dec(v___x_1689_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1696_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
lean_object* v___x_1694_; 
if (v_isShared_1692_ == 0)
{
lean_ctor_set(v___x_1691_, 0, v_a_1687_);
v___x_1694_ = v___x_1691_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v_a_1687_);
v___x_1694_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
return v___x_1694_;
}
}
}
else
{
lean_dec(v_a_1685_);
return v___x_1686_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___boxed(lean_object* v_input_1698_, lean_object* v_pre_1699_, lean_object* v_post_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_){
_start:
{
lean_object* v_res_1704_; 
v_res_1704_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_input_1698_, v_pre_1699_, v_post_1700_, v___y_1701_, v___y_1702_);
lean_dec(v___y_1702_);
lean_dec_ref(v___y_1701_);
return v_res_1704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_betaReduce(lean_object* v_e_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_){
_start:
{
lean_object* v___f_1711_; lean_object* v___f_1712_; lean_object* v___x_1713_; 
v___f_1711_ = ((lean_object*)(l_Lean_Core_betaReduce___closed__0));
v___f_1712_ = ((lean_object*)(l_Lean_Core_betaReduce___closed__1));
v___x_1713_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_1707_, v___f_1711_, v___f_1712_, v_a_1708_, v_a_1709_);
return v___x_1713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_betaReduce___boxed(lean_object* v_e_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_){
_start:
{
lean_object* v_res_1718_; 
v_res_1718_ = l_Lean_Core_betaReduce(v_e_1714_, v_a_1715_, v_a_1716_);
lean_dec(v_a_1716_);
lean_dec_ref(v_a_1715_);
return v_res_1718_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_1719_, lean_object* v_m_1720_, lean_object* v_a_1721_){
_start:
{
lean_object* v___x_1722_; 
v___x_1722_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg(v_m_1720_, v_a_1721_);
return v___x_1722_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_1723_, lean_object* v_m_1724_, lean_object* v_a_1725_){
_start:
{
lean_object* v_res_1726_; 
v_res_1726_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3(v_00_u03b2_1723_, v_m_1724_, v_a_1725_);
lean_dec_ref(v_a_1725_);
lean_dec_ref(v_m_1724_);
return v_res_1726_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_1727_, lean_object* v_ref_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_){
_start:
{
lean_object* v___x_1732_; 
v___x_1732_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_1728_);
return v___x_1732_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1733_, lean_object* v_ref_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_){
_start:
{
lean_object* v_res_1738_; 
v_res_1738_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_1733_, v_ref_1734_, v___y_1735_, v___y_1736_);
lean_dec(v___y_1736_);
lean_dec_ref(v___y_1735_);
return v_res_1738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5(lean_object* v_00_u03b1_1739_, lean_object* v_x_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_){
_start:
{
lean_object* v___x_1745_; 
v___x_1745_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___redArg(v_x_1740_, v___y_1741_, v___y_1742_, v___y_1743_);
return v___x_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b1_1746_, lean_object* v_x_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_){
_start:
{
lean_object* v_res_1752_; 
v_res_1752_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5(v_00_u03b1_1746_, v_x_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
lean_dec(v___y_1750_);
lean_dec_ref(v___y_1749_);
lean_dec(v___y_1748_);
return v_res_1752_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6(lean_object* v_00_u03b2_1753_, lean_object* v_m_1754_, lean_object* v_a_1755_, lean_object* v_b_1756_){
_start:
{
lean_object* v___x_1757_; 
v___x_1757_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6___redArg(v_m_1754_, v_a_1755_, v_b_1756_);
return v___x_1757_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4(lean_object* v_00_u03b2_1758_, lean_object* v_a_1759_, lean_object* v_x_1760_){
_start:
{
lean_object* v___x_1761_; 
v___x_1761_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___redArg(v_a_1759_, v_x_1760_);
return v___x_1761_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___boxed(lean_object* v_00_u03b2_1762_, lean_object* v_a_1763_, lean_object* v_x_1764_){
_start:
{
lean_object* v_res_1765_; 
v_res_1765_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4(v_00_u03b2_1762_, v_a_1763_, v_x_1764_);
lean_dec(v_x_1764_);
lean_dec_ref(v_a_1763_);
return v_res_1765_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__9(lean_object* v_00_u03b2_1766_, lean_object* v_a_1767_, lean_object* v_x_1768_){
_start:
{
uint8_t v___x_1769_; 
v___x_1769_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__9___redArg(v_a_1767_, v_x_1768_);
return v___x_1769_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__9___boxed(lean_object* v_00_u03b2_1770_, lean_object* v_a_1771_, lean_object* v_x_1772_){
_start:
{
uint8_t v_res_1773_; lean_object* v_r_1774_; 
v_res_1773_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__9(v_00_u03b2_1770_, v_a_1771_, v_x_1772_);
lean_dec(v_x_1772_);
lean_dec_ref(v_a_1771_);
v_r_1774_ = lean_box(v_res_1773_);
return v_r_1774_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10(lean_object* v_00_u03b2_1775_, lean_object* v_data_1776_){
_start:
{
lean_object* v___x_1777_; 
v___x_1777_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___redArg(v_data_1776_);
return v___x_1777_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11(lean_object* v_00_u03b2_1778_, lean_object* v_a_1779_, lean_object* v_b_1780_, lean_object* v_x_1781_){
_start:
{
lean_object* v___x_1782_; 
v___x_1782_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11___redArg(v_a_1779_, v_b_1780_, v_x_1781_);
return v___x_1782_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10_spec__11(lean_object* v_00_u03b2_1783_, lean_object* v_i_1784_, lean_object* v_source_1785_, lean_object* v_target_1786_){
_start:
{
lean_object* v___x_1787_; 
v___x_1787_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10_spec__11___redArg(v_i_1784_, v_source_1785_, v_target_1786_);
return v___x_1787_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12(lean_object* v_00_u03b2_1788_, lean_object* v_x_1789_, lean_object* v_x_1790_){
_start:
{
lean_object* v___x_1791_; 
v___x_1791_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12___redArg(v_x_1789_, v_x_1790_);
return v___x_1791_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__0(lean_object* v_toApplicative_1792_, lean_object* v_a_1793_){
_start:
{
lean_object* v_toPure_1794_; lean_object* v___x_1795_; 
v_toPure_1794_ = lean_ctor_get(v_toApplicative_1792_, 1);
lean_inc(v_toPure_1794_);
lean_dec_ref(v_toApplicative_1792_);
v___x_1795_ = lean_apply_2(v_toPure_1794_, lean_box(0), v_a_1793_);
return v___x_1795_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__13(lean_object* v___x_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_){
_start:
{
lean_object* v___x_1802_; 
v___x_1802_ = l_Lean_Core_checkSystem(v___x_1796_, v___y_1799_, v___y_1800_);
return v___x_1802_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__13___boxed(lean_object* v___x_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_){
_start:
{
lean_object* v_res_1809_; 
v_res_1809_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__13(v___x_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_);
lean_dec(v___y_1807_);
lean_dec_ref(v___y_1806_);
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
return v_res_1809_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14(lean_object* v_inst_1812_, lean_object* v_x_1813_, lean_object* v___x_1814_, lean_object* v___x_1815_, lean_object* v_inst_1816_, lean_object* v___f_1817_, lean_object* v___x_1818_, lean_object* v___x_1819_, lean_object* v_a_1820_, lean_object* v_toBind_1821_, lean_object* v___f_1822_, lean_object* v_toApplicative_1823_, lean_object* v_a_1824_){
_start:
{
if (lean_obj_tag(v_a_1824_) == 0)
{
lean_object* v___f_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_3801__overap_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; 
lean_dec_ref(v_toApplicative_1823_);
v___f_1825_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14___closed__0));
v___x_1826_ = lean_apply_2(v_inst_1812_, lean_box(0), v___f_1825_);
lean_inc_ref(v___x_1815_);
lean_inc_ref(v___x_1814_);
v___x_1827_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonadLift___aux__1___boxed), 10, 9);
lean_closure_set(v___x_1827_, 0, lean_box(0));
lean_closure_set(v___x_1827_, 1, lean_box(0));
lean_closure_set(v___x_1827_, 2, lean_box(0));
lean_closure_set(v___x_1827_, 3, lean_box(0));
lean_closure_set(v___x_1827_, 4, v_x_1813_);
lean_closure_set(v___x_1827_, 5, v___x_1814_);
lean_closure_set(v___x_1827_, 6, v___x_1815_);
lean_closure_set(v___x_1827_, 7, lean_box(0));
lean_closure_set(v___x_1827_, 8, v___x_1826_);
v___x_1828_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonad___aux__13___boxed), 13, 12);
lean_closure_set(v___x_1828_, 0, lean_box(0));
lean_closure_set(v___x_1828_, 1, lean_box(0));
lean_closure_set(v___x_1828_, 2, lean_box(0));
lean_closure_set(v___x_1828_, 3, lean_box(0));
lean_closure_set(v___x_1828_, 4, v_x_1813_);
lean_closure_set(v___x_1828_, 5, v___x_1814_);
lean_closure_set(v___x_1828_, 6, v___x_1815_);
lean_closure_set(v___x_1828_, 7, v_inst_1816_);
lean_closure_set(v___x_1828_, 8, lean_box(0));
lean_closure_set(v___x_1828_, 9, lean_box(0));
lean_closure_set(v___x_1828_, 10, v___x_1827_);
lean_closure_set(v___x_1828_, 11, v___f_1817_);
v___x_3801__overap_1829_ = l_Lean_Meta_withIncRecDepth___redArg(v___x_1818_, v___x_1819_, v___x_1828_);
lean_inc(v_a_1820_);
v___x_1830_ = lean_apply_1(v___x_3801__overap_1829_, v_a_1820_);
v___x_1831_ = lean_apply_4(v_toBind_1821_, lean_box(0), lean_box(0), v___x_1830_, v___f_1822_);
return v___x_1831_;
}
else
{
lean_object* v_val_1832_; lean_object* v_toPure_1833_; lean_object* v___x_1834_; 
lean_dec(v___f_1822_);
lean_dec(v_toBind_1821_);
lean_dec_ref(v___x_1819_);
lean_dec_ref(v___x_1818_);
lean_dec(v___f_1817_);
lean_dec_ref(v_inst_1816_);
lean_dec_ref(v___x_1815_);
lean_dec_ref(v___x_1814_);
lean_dec(v_inst_1812_);
v_val_1832_ = lean_ctor_get(v_a_1824_, 0);
lean_inc(v_val_1832_);
lean_dec_ref(v_a_1824_);
v_toPure_1833_ = lean_ctor_get(v_toApplicative_1823_, 1);
lean_inc(v_toPure_1833_);
lean_dec_ref(v_toApplicative_1823_);
v___x_1834_ = lean_apply_2(v_toPure_1833_, lean_box(0), v_val_1832_);
return v___x_1834_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14___boxed(lean_object* v_inst_1835_, lean_object* v_x_1836_, lean_object* v___x_1837_, lean_object* v___x_1838_, lean_object* v_inst_1839_, lean_object* v___f_1840_, lean_object* v___x_1841_, lean_object* v___x_1842_, lean_object* v_a_1843_, lean_object* v_toBind_1844_, lean_object* v___f_1845_, lean_object* v_toApplicative_1846_, lean_object* v_a_1847_){
_start:
{
lean_object* v_res_1848_; 
v_res_1848_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14(v_inst_1835_, v_x_1836_, v___x_1837_, v___x_1838_, v_inst_1839_, v___f_1840_, v___x_1841_, v___x_1842_, v_a_1843_, v_toBind_1844_, v___f_1845_, v_toApplicative_1846_, v_a_1847_);
lean_dec(v_a_1843_);
return v_res_1848_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__1(lean_object* v___x_1849_, lean_object* v___x_1850_, lean_object* v_declName_1851_, lean_object* v_a_1852_, lean_object* v___f_1853_, uint8_t v_nondep_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_){
_start:
{
uint8_t v___x_1857_; lean_object* v___x_3820__overap_1858_; lean_object* v___x_1859_; 
v___x_1857_ = 0;
v___x_3820__overap_1858_ = l_Lean_Meta_withLetDecl___redArg(v___x_1849_, v___x_1850_, v_declName_1851_, v_a_1852_, v_a_1856_, v___f_1853_, v_nondep_1854_, v___x_1857_);
lean_inc(v_a_1855_);
v___x_1859_ = lean_apply_1(v___x_3820__overap_1858_, v_a_1855_);
return v___x_1859_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__1___boxed(lean_object* v___x_1860_, lean_object* v___x_1861_, lean_object* v_declName_1862_, lean_object* v_a_1863_, lean_object* v___f_1864_, lean_object* v_nondep_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_){
_start:
{
uint8_t v_nondep_3999__boxed_1868_; lean_object* v_res_1869_; 
v_nondep_3999__boxed_1868_ = lean_unbox(v_nondep_1865_);
v_res_1869_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__1(v___x_1860_, v___x_1861_, v_declName_1862_, v_a_1863_, v___f_1864_, v_nondep_3999__boxed_1868_, v_a_1866_, v_a_1867_);
lean_dec(v_a_1866_);
return v_res_1869_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__4(lean_object* v_fvars_1870_, uint8_t v_usedLetOnly_1871_, lean_object* v_inst_1872_, lean_object* v_toBind_1873_, lean_object* v___f_1874_, lean_object* v_a_1875_){
_start:
{
uint8_t v___x_1876_; uint8_t v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; 
v___x_1876_ = 0;
v___x_1877_ = 1;
v___x_1878_ = lean_box(v_usedLetOnly_1871_);
v___x_1879_ = lean_box(v___x_1876_);
v___x_1880_ = lean_box(v___x_1877_);
v___x_1881_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLetFVars___boxed), 10, 5);
lean_closure_set(v___x_1881_, 0, v_fvars_1870_);
lean_closure_set(v___x_1881_, 1, v_a_1875_);
lean_closure_set(v___x_1881_, 2, v___x_1878_);
lean_closure_set(v___x_1881_, 3, v___x_1879_);
lean_closure_set(v___x_1881_, 4, v___x_1880_);
v___x_1882_ = lean_apply_2(v_inst_1872_, lean_box(0), v___x_1881_);
v___x_1883_ = lean_apply_4(v_toBind_1873_, lean_box(0), lean_box(0), v___x_1882_, v___f_1874_);
return v___x_1883_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__4___boxed(lean_object* v_fvars_1884_, lean_object* v_usedLetOnly_1885_, lean_object* v_inst_1886_, lean_object* v_toBind_1887_, lean_object* v___f_1888_, lean_object* v_a_1889_){
_start:
{
uint8_t v_usedLetOnly_boxed_1890_; lean_object* v_res_1891_; 
v_usedLetOnly_boxed_1890_ = lean_unbox(v_usedLetOnly_1885_);
v_res_1891_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__4(v_fvars_1884_, v_usedLetOnly_boxed_1890_, v_inst_1886_, v_toBind_1887_, v___f_1888_, v_a_1889_);
return v_res_1891_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__3(lean_object* v_fvars_1892_, uint8_t v_usedLetOnly_1893_, lean_object* v_inst_1894_, lean_object* v_toBind_1895_, lean_object* v___f_1896_, lean_object* v_a_1897_){
_start:
{
uint8_t v___x_1898_; uint8_t v___x_1899_; uint8_t v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; 
v___x_1898_ = 0;
v___x_1899_ = 1;
v___x_1900_ = 1;
v___x_1901_ = lean_box(v___x_1898_);
v___x_1902_ = lean_box(v_usedLetOnly_1893_);
v___x_1903_ = lean_box(v___x_1898_);
v___x_1904_ = lean_box(v___x_1899_);
v___x_1905_ = lean_box(v___x_1900_);
v___x_1906_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(v___x_1906_, 0, v_fvars_1892_);
lean_closure_set(v___x_1906_, 1, v_a_1897_);
lean_closure_set(v___x_1906_, 2, v___x_1901_);
lean_closure_set(v___x_1906_, 3, v___x_1902_);
lean_closure_set(v___x_1906_, 4, v___x_1903_);
lean_closure_set(v___x_1906_, 5, v___x_1904_);
lean_closure_set(v___x_1906_, 6, v___x_1905_);
v___x_1907_ = lean_apply_2(v_inst_1894_, lean_box(0), v___x_1906_);
v___x_1908_ = lean_apply_4(v_toBind_1895_, lean_box(0), lean_box(0), v___x_1907_, v___f_1896_);
return v___x_1908_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__3___boxed(lean_object* v_fvars_1909_, lean_object* v_usedLetOnly_1910_, lean_object* v_inst_1911_, lean_object* v_toBind_1912_, lean_object* v___f_1913_, lean_object* v_a_1914_){
_start:
{
uint8_t v_usedLetOnly_boxed_1915_; lean_object* v_res_1916_; 
v_usedLetOnly_boxed_1915_ = lean_unbox(v_usedLetOnly_1910_);
v_res_1916_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__3(v_fvars_1909_, v_usedLetOnly_boxed_1915_, v_inst_1911_, v_toBind_1912_, v___f_1913_, v_a_1914_);
return v_res_1916_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1(lean_object* v___x_1917_, lean_object* v___x_1918_, lean_object* v_binderName_1919_, uint8_t v_binderInfo_1920_, lean_object* v___f_1921_, lean_object* v_a_1922_, lean_object* v_a_1923_){
_start:
{
uint8_t v___x_1924_; lean_object* v___x_3878__overap_1925_; lean_object* v___x_1926_; 
v___x_1924_ = 0;
v___x_3878__overap_1925_ = l_Lean_Meta_withLocalDecl___redArg(v___x_1917_, v___x_1918_, v_binderName_1919_, v_binderInfo_1920_, v_a_1923_, v___f_1921_, v___x_1924_);
lean_inc(v_a_1922_);
v___x_1926_ = lean_apply_1(v___x_3878__overap_1925_, v_a_1922_);
return v___x_1926_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1___boxed(lean_object* v___x_1927_, lean_object* v___x_1928_, lean_object* v_binderName_1929_, lean_object* v_binderInfo_1930_, lean_object* v___f_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_){
_start:
{
uint8_t v_binderInfo_4067__boxed_1934_; lean_object* v_res_1935_; 
v_binderInfo_4067__boxed_1934_ = lean_unbox(v_binderInfo_1930_);
v_res_1935_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1(v___x_1927_, v___x_1928_, v_binderName_1929_, v_binderInfo_4067__boxed_1934_, v___f_1931_, v_a_1932_, v_a_1933_);
lean_dec(v_a_1932_);
return v_res_1935_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__3(lean_object* v_fvars_1936_, uint8_t v_usedLetOnly_1937_, lean_object* v_inst_1938_, lean_object* v_toBind_1939_, lean_object* v___f_1940_, lean_object* v_a_1941_){
_start:
{
uint8_t v___x_1942_; uint8_t v___x_1943_; uint8_t v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; 
v___x_1942_ = 0;
v___x_1943_ = 1;
v___x_1944_ = 1;
v___x_1945_ = lean_box(v___x_1942_);
v___x_1946_ = lean_box(v_usedLetOnly_1937_);
v___x_1947_ = lean_box(v___x_1943_);
v___x_1948_ = lean_box(v___x_1944_);
v___x_1949_ = lean_alloc_closure((void*)(l_Lean_Meta_mkForallFVars___boxed), 11, 6);
lean_closure_set(v___x_1949_, 0, v_fvars_1936_);
lean_closure_set(v___x_1949_, 1, v_a_1941_);
lean_closure_set(v___x_1949_, 2, v___x_1945_);
lean_closure_set(v___x_1949_, 3, v___x_1946_);
lean_closure_set(v___x_1949_, 4, v___x_1947_);
lean_closure_set(v___x_1949_, 5, v___x_1948_);
v___x_1950_ = lean_apply_2(v_inst_1938_, lean_box(0), v___x_1949_);
v___x_1951_ = lean_apply_4(v_toBind_1939_, lean_box(0), lean_box(0), v___x_1950_, v___f_1940_);
return v___x_1951_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__3___boxed(lean_object* v_fvars_1952_, lean_object* v_usedLetOnly_1953_, lean_object* v_inst_1954_, lean_object* v_toBind_1955_, lean_object* v___f_1956_, lean_object* v_a_1957_){
_start:
{
uint8_t v_usedLetOnly_boxed_1958_; lean_object* v_res_1959_; 
v_usedLetOnly_boxed_1958_ = lean_unbox(v_usedLetOnly_1953_);
v_res_1959_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__3(v_fvars_1952_, v_usedLetOnly_boxed_1958_, v_inst_1954_, v_toBind_1955_, v___f_1956_, v_a_1957_);
return v_res_1959_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__7(lean_object* v___f_1960_, lean_object* v___y_1961_, lean_object* v_a_1962_){
_start:
{
lean_object* v___x_1963_; 
lean_inc(v___y_1961_);
v___x_1963_ = lean_apply_2(v___f_1960_, v_a_1962_, v___y_1961_);
return v___x_1963_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__7___boxed(lean_object* v___f_1964_, lean_object* v___y_1965_, lean_object* v_a_1966_){
_start:
{
lean_object* v_res_1967_; 
v_res_1967_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__7(v___f_1964_, v___y_1965_, v_a_1966_);
lean_dec(v___y_1965_);
return v_res_1967_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1(lean_object* v_toApplicative_1968_, lean_object* v_acc_1969_, lean_object* v_next_1970_, lean_object* v_a_1971_){
_start:
{
lean_object* v_toPure_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; 
v_toPure_1972_ = lean_ctor_get(v_toApplicative_1968_, 1);
lean_inc(v_toPure_1972_);
lean_dec_ref(v_toApplicative_1968_);
v___x_1973_ = lean_array_fset(v_acc_1969_, v_next_1970_, v_a_1971_);
v___x_1974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1974_, 0, v___x_1973_);
v___x_1975_ = lean_apply_2(v_toPure_1972_, lean_box(0), v___x_1974_);
return v___x_1975_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1___boxed(lean_object* v_toApplicative_1976_, lean_object* v_acc_1977_, lean_object* v_next_1978_, lean_object* v_a_1979_){
_start:
{
lean_object* v_res_1980_; 
v_res_1980_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1(v_toApplicative_1976_, v_acc_1977_, v_next_1978_, v_a_1979_);
lean_dec(v_next_1978_);
return v_res_1980_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__2(lean_object* v_toApplicative_1981_, lean_object* v_next_1982_, lean_object* v_G_1983_, lean_object* v___y_1984_, lean_object* v_a_1985_){
_start:
{
if (lean_obj_tag(v_a_1985_) == 0)
{
lean_object* v_a_1986_; lean_object* v_toPure_1987_; lean_object* v___x_1988_; 
lean_dec(v_G_1983_);
v_a_1986_ = lean_ctor_get(v_a_1985_, 0);
lean_inc(v_a_1986_);
lean_dec_ref(v_a_1985_);
v_toPure_1987_ = lean_ctor_get(v_toApplicative_1981_, 1);
lean_inc(v_toPure_1987_);
lean_dec_ref(v_toApplicative_1981_);
v___x_1988_ = lean_apply_2(v_toPure_1987_, lean_box(0), v_a_1986_);
return v___x_1988_;
}
else
{
lean_object* v_a_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; 
lean_dec_ref(v_toApplicative_1981_);
v_a_1989_ = lean_ctor_get(v_a_1985_, 0);
lean_inc(v_a_1989_);
lean_dec_ref(v_a_1985_);
v___x_1990_ = lean_unsigned_to_nat(1u);
v___x_1991_ = lean_nat_add(v_next_1982_, v___x_1990_);
lean_inc(v___y_1984_);
v___x_1992_ = lean_apply_5(v_G_1983_, v___x_1991_, v_a_1989_, lean_box(0), lean_box(0), v___y_1984_);
return v___x_1992_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__2___boxed(lean_object* v_toApplicative_1993_, lean_object* v_next_1994_, lean_object* v_G_1995_, lean_object* v___y_1996_, lean_object* v_a_1997_){
_start:
{
lean_object* v_res_1998_; 
v_res_1998_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__2(v_toApplicative_1993_, v_next_1994_, v_G_1995_, v___y_1996_, v_a_1997_);
lean_dec(v___y_1996_);
lean_dec(v_next_1994_);
return v_res_1998_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5(lean_object* v_f_1999_, lean_object* v_inst_2000_, lean_object* v_inst_2001_, lean_object* v_inst_2002_, lean_object* v_pre_2003_, lean_object* v_post_2004_, uint8_t v_usedLetOnly_2005_, uint8_t v_skipConstInApp_2006_, uint8_t v_skipInstances_2007_, lean_object* v_x_2008_, lean_object* v_x_2009_, lean_object* v___y_2010_, lean_object* v_a_2011_){
_start:
{
lean_object* v___x_2012_; lean_object* v___x_2013_; 
v___x_2012_ = l_Lean_mkAppN(v_f_1999_, v_a_2011_);
v___x_2013_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2000_, v_inst_2001_, v_inst_2002_, v_pre_2003_, v_post_2004_, v_usedLetOnly_2005_, v_skipConstInApp_2006_, v_skipInstances_2007_, v_x_2008_, v_x_2009_, v___x_2012_, v___y_2010_);
return v___x_2013_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5___boxed(lean_object* v_f_2014_, lean_object* v_inst_2015_, lean_object* v_inst_2016_, lean_object* v_inst_2017_, lean_object* v_pre_2018_, lean_object* v_post_2019_, lean_object* v_usedLetOnly_2020_, lean_object* v_skipConstInApp_2021_, lean_object* v_skipInstances_2022_, lean_object* v_x_2023_, lean_object* v_x_2024_, lean_object* v___y_2025_, lean_object* v_a_2026_){
_start:
{
uint8_t v_usedLetOnly_boxed_2027_; uint8_t v_skipConstInApp_boxed_2028_; uint8_t v_skipInstances_boxed_2029_; lean_object* v_res_2030_; 
v_usedLetOnly_boxed_2027_ = lean_unbox(v_usedLetOnly_2020_);
v_skipConstInApp_boxed_2028_ = lean_unbox(v_skipConstInApp_2021_);
v_skipInstances_boxed_2029_ = lean_unbox(v_skipInstances_2022_);
v_res_2030_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5(v_f_2014_, v_inst_2015_, v_inst_2016_, v_inst_2017_, v_pre_2018_, v_post_2019_, v_usedLetOnly_boxed_2027_, v_skipConstInApp_boxed_2028_, v_skipInstances_boxed_2029_, v_x_2023_, v_x_2024_, v___y_2025_, v_a_2026_);
lean_dec_ref(v_a_2026_);
lean_dec(v___y_2025_);
return v_res_2030_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___boxed(lean_object* v_inst_2031_, lean_object* v_inst_2032_, lean_object* v_inst_2033_, lean_object* v_pre_2034_, lean_object* v_post_2035_, lean_object* v_usedLetOnly_2036_, lean_object* v_skipConstInApp_2037_, lean_object* v_skipInstances_2038_, lean_object* v_x_2039_, lean_object* v_x_2040_, lean_object* v_e_2041_, lean_object* v_a_2042_){
_start:
{
uint8_t v_usedLetOnly_boxed_2043_; uint8_t v_skipConstInApp_boxed_2044_; uint8_t v_skipInstances_boxed_2045_; lean_object* v_res_2046_; 
v_usedLetOnly_boxed_2043_ = lean_unbox(v_usedLetOnly_2036_);
v_skipConstInApp_boxed_2044_ = lean_unbox(v_skipConstInApp_2037_);
v_skipInstances_boxed_2045_ = lean_unbox(v_skipInstances_2038_);
v_res_2046_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2031_, v_inst_2032_, v_inst_2033_, v_pre_2034_, v_post_2035_, v_usedLetOnly_boxed_2043_, v_skipConstInApp_boxed_2044_, v_skipInstances_boxed_2045_, v_x_2039_, v_x_2040_, v_e_2041_, v_a_2042_);
lean_dec(v_a_2042_);
return v_res_2046_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__4(lean_object* v___x_2047_, lean_object* v_toApplicative_2048_, lean_object* v_toBind_2049_, lean_object* v___f_2050_, lean_object* v_paramInfo_2051_, lean_object* v_inst_2052_, lean_object* v_inst_2053_, lean_object* v_inst_2054_, lean_object* v_pre_2055_, lean_object* v_post_2056_, uint8_t v_usedLetOnly_2057_, uint8_t v_skipConstInApp_2058_, uint8_t v_skipInstances_2059_, lean_object* v_x_2060_, lean_object* v_x_2061_, lean_object* v_next_2062_, lean_object* v_acc_2063_, lean_object* v_h_2064_, lean_object* v_G_2065_, lean_object* v___y_2066_){
_start:
{
uint8_t v___x_2067_; 
v___x_2067_ = lean_nat_dec_lt(v_next_2062_, v___x_2047_);
if (v___x_2067_ == 0)
{
lean_object* v_toPure_2068_; lean_object* v___x_2069_; 
lean_dec(v_G_2065_);
lean_dec(v_next_2062_);
lean_dec(v_x_2061_);
lean_dec(v_post_2056_);
lean_dec(v_pre_2055_);
lean_dec_ref(v_inst_2054_);
lean_dec(v_inst_2053_);
lean_dec_ref(v_inst_2052_);
lean_dec(v___f_2050_);
lean_dec(v_toBind_2049_);
v_toPure_2068_ = lean_ctor_get(v_toApplicative_2048_, 1);
lean_inc(v_toPure_2068_);
lean_dec_ref(v_toApplicative_2048_);
v___x_2069_ = lean_apply_2(v_toPure_2068_, lean_box(0), v_acc_2063_);
return v___x_2069_;
}
else
{
lean_object* v___f_2070_; lean_object* v___y_2072_; lean_object* v___x_2075_; lean_object* v___x_2076_; uint8_t v___x_2077_; 
lean_inc(v___y_2066_);
lean_inc(v_next_2062_);
lean_inc_ref(v_toApplicative_2048_);
v___f_2070_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__2___boxed), 5, 4);
lean_closure_set(v___f_2070_, 0, v_toApplicative_2048_);
lean_closure_set(v___f_2070_, 1, v_next_2062_);
lean_closure_set(v___f_2070_, 2, v_G_2065_);
lean_closure_set(v___f_2070_, 3, v___y_2066_);
v___x_2075_ = lean_array_fget_borrowed(v_acc_2063_, v_next_2062_);
v___x_2076_ = lean_array_get_size(v_paramInfo_2051_);
v___x_2077_ = lean_nat_dec_lt(v_next_2062_, v___x_2076_);
if (v___x_2077_ == 0)
{
lean_object* v___f_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; 
lean_inc(v___x_2075_);
v___f_2078_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2078_, 0, v_toApplicative_2048_);
lean_closure_set(v___f_2078_, 1, v_acc_2063_);
lean_closure_set(v___f_2078_, 2, v_next_2062_);
v___x_2079_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2052_, v_inst_2053_, v_inst_2054_, v_pre_2055_, v_post_2056_, v_usedLetOnly_2057_, v_skipConstInApp_2058_, v_skipInstances_2059_, v_x_2060_, v_x_2061_, v___x_2075_, v___y_2066_);
lean_inc(v_toBind_2049_);
v___x_2080_ = lean_apply_4(v_toBind_2049_, lean_box(0), lean_box(0), v___x_2079_, v___f_2078_);
v___y_2072_ = v___x_2080_;
goto v___jp_2071_;
}
else
{
lean_object* v___x_2081_; uint8_t v_isInstance_2082_; 
v___x_2081_ = lean_array_fget_borrowed(v_paramInfo_2051_, v_next_2062_);
v_isInstance_2082_ = lean_ctor_get_uint8(v___x_2081_, sizeof(void*)*1 + 4);
if (v_isInstance_2082_ == 0)
{
lean_object* v___f_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; 
lean_inc(v___x_2075_);
v___f_2083_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2083_, 0, v_toApplicative_2048_);
lean_closure_set(v___f_2083_, 1, v_acc_2063_);
lean_closure_set(v___f_2083_, 2, v_next_2062_);
v___x_2084_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2052_, v_inst_2053_, v_inst_2054_, v_pre_2055_, v_post_2056_, v_usedLetOnly_2057_, v_skipConstInApp_2058_, v_skipInstances_2059_, v_x_2060_, v_x_2061_, v___x_2075_, v___y_2066_);
lean_inc(v_toBind_2049_);
v___x_2085_ = lean_apply_4(v_toBind_2049_, lean_box(0), lean_box(0), v___x_2084_, v___f_2083_);
v___y_2072_ = v___x_2085_;
goto v___jp_2071_;
}
else
{
lean_object* v_toPure_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; 
lean_dec(v_next_2062_);
lean_dec(v_x_2061_);
lean_dec(v_post_2056_);
lean_dec(v_pre_2055_);
lean_dec_ref(v_inst_2054_);
lean_dec(v_inst_2053_);
lean_dec_ref(v_inst_2052_);
v_toPure_2086_ = lean_ctor_get(v_toApplicative_2048_, 1);
lean_inc(v_toPure_2086_);
lean_dec_ref(v_toApplicative_2048_);
v___x_2087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2087_, 0, v_acc_2063_);
v___x_2088_ = lean_apply_2(v_toPure_2086_, lean_box(0), v___x_2087_);
v___y_2072_ = v___x_2088_;
goto v___jp_2071_;
}
}
v___jp_2071_:
{
lean_object* v___x_2073_; lean_object* v___x_2074_; 
lean_inc(v_toBind_2049_);
v___x_2073_ = lean_apply_4(v_toBind_2049_, lean_box(0), lean_box(0), v___y_2072_, v___f_2050_);
v___x_2074_ = lean_apply_4(v_toBind_2049_, lean_box(0), lean_box(0), v___x_2073_, v___f_2070_);
return v___x_2074_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__4___boxed(lean_object** _args){
lean_object* v___x_2089_ = _args[0];
lean_object* v_toApplicative_2090_ = _args[1];
lean_object* v_toBind_2091_ = _args[2];
lean_object* v___f_2092_ = _args[3];
lean_object* v_paramInfo_2093_ = _args[4];
lean_object* v_inst_2094_ = _args[5];
lean_object* v_inst_2095_ = _args[6];
lean_object* v_inst_2096_ = _args[7];
lean_object* v_pre_2097_ = _args[8];
lean_object* v_post_2098_ = _args[9];
lean_object* v_usedLetOnly_2099_ = _args[10];
lean_object* v_skipConstInApp_2100_ = _args[11];
lean_object* v_skipInstances_2101_ = _args[12];
lean_object* v_x_2102_ = _args[13];
lean_object* v_x_2103_ = _args[14];
lean_object* v_next_2104_ = _args[15];
lean_object* v_acc_2105_ = _args[16];
lean_object* v_h_2106_ = _args[17];
lean_object* v_G_2107_ = _args[18];
lean_object* v___y_2108_ = _args[19];
_start:
{
uint8_t v_usedLetOnly_boxed_2109_; uint8_t v_skipConstInApp_boxed_2110_; uint8_t v_skipInstances_boxed_2111_; lean_object* v_res_2112_; 
v_usedLetOnly_boxed_2109_ = lean_unbox(v_usedLetOnly_2099_);
v_skipConstInApp_boxed_2110_ = lean_unbox(v_skipConstInApp_2100_);
v_skipInstances_boxed_2111_ = lean_unbox(v_skipInstances_2101_);
v_res_2112_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__4(v___x_2089_, v_toApplicative_2090_, v_toBind_2091_, v___f_2092_, v_paramInfo_2093_, v_inst_2094_, v_inst_2095_, v_inst_2096_, v_pre_2097_, v_post_2098_, v_usedLetOnly_boxed_2109_, v_skipConstInApp_boxed_2110_, v_skipInstances_boxed_2111_, v_x_2102_, v_x_2103_, v_next_2104_, v_acc_2105_, v_h_2106_, v_G_2107_, v___y_2108_);
lean_dec(v___y_2108_);
lean_dec_ref(v_paramInfo_2093_);
lean_dec(v___x_2089_);
return v_res_2112_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__3(lean_object* v___x_2113_, lean_object* v_toApplicative_2114_, lean_object* v_toBind_2115_, lean_object* v___f_2116_, lean_object* v_inst_2117_, lean_object* v_inst_2118_, lean_object* v_inst_2119_, lean_object* v_pre_2120_, lean_object* v_post_2121_, uint8_t v_usedLetOnly_2122_, uint8_t v_skipConstInApp_2123_, uint8_t v_skipInstances_2124_, lean_object* v_x_2125_, lean_object* v_x_2126_, lean_object* v_args_2127_, lean_object* v___y_2128_, lean_object* v___f_2129_, lean_object* v_a_2130_){
_start:
{
lean_object* v_paramInfo_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___f_2136_; lean_object* v___x_3638__overap_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; 
v_paramInfo_2131_ = lean_ctor_get(v_a_2130_, 0);
lean_inc_ref(v_paramInfo_2131_);
lean_dec_ref(v_a_2130_);
v___x_2132_ = lean_unsigned_to_nat(0u);
v___x_2133_ = lean_box(v_usedLetOnly_2122_);
v___x_2134_ = lean_box(v_skipConstInApp_2123_);
v___x_2135_ = lean_box(v_skipInstances_2124_);
lean_inc(v_toBind_2115_);
v___f_2136_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__4___boxed), 20, 15);
lean_closure_set(v___f_2136_, 0, v___x_2113_);
lean_closure_set(v___f_2136_, 1, v_toApplicative_2114_);
lean_closure_set(v___f_2136_, 2, v_toBind_2115_);
lean_closure_set(v___f_2136_, 3, v___f_2116_);
lean_closure_set(v___f_2136_, 4, v_paramInfo_2131_);
lean_closure_set(v___f_2136_, 5, v_inst_2117_);
lean_closure_set(v___f_2136_, 6, v_inst_2118_);
lean_closure_set(v___f_2136_, 7, v_inst_2119_);
lean_closure_set(v___f_2136_, 8, v_pre_2120_);
lean_closure_set(v___f_2136_, 9, v_post_2121_);
lean_closure_set(v___f_2136_, 10, v___x_2133_);
lean_closure_set(v___f_2136_, 11, v___x_2134_);
lean_closure_set(v___f_2136_, 12, v___x_2135_);
lean_closure_set(v___f_2136_, 13, v_x_2125_);
lean_closure_set(v___f_2136_, 14, v_x_2126_);
v___x_3638__overap_2137_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_2136_, v___x_2132_, v_args_2127_, lean_box(0));
lean_inc(v___y_2128_);
v___x_2138_ = lean_apply_1(v___x_3638__overap_2137_, v___y_2128_);
v___x_2139_ = lean_apply_4(v_toBind_2115_, lean_box(0), lean_box(0), v___x_2138_, v___f_2129_);
return v___x_2139_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__3___boxed(lean_object** _args){
lean_object* v___x_2140_ = _args[0];
lean_object* v_toApplicative_2141_ = _args[1];
lean_object* v_toBind_2142_ = _args[2];
lean_object* v___f_2143_ = _args[3];
lean_object* v_inst_2144_ = _args[4];
lean_object* v_inst_2145_ = _args[5];
lean_object* v_inst_2146_ = _args[6];
lean_object* v_pre_2147_ = _args[7];
lean_object* v_post_2148_ = _args[8];
lean_object* v_usedLetOnly_2149_ = _args[9];
lean_object* v_skipConstInApp_2150_ = _args[10];
lean_object* v_skipInstances_2151_ = _args[11];
lean_object* v_x_2152_ = _args[12];
lean_object* v_x_2153_ = _args[13];
lean_object* v_args_2154_ = _args[14];
lean_object* v___y_2155_ = _args[15];
lean_object* v___f_2156_ = _args[16];
lean_object* v_a_2157_ = _args[17];
_start:
{
uint8_t v_usedLetOnly_boxed_2158_; uint8_t v_skipConstInApp_boxed_2159_; uint8_t v_skipInstances_boxed_2160_; lean_object* v_res_2161_; 
v_usedLetOnly_boxed_2158_ = lean_unbox(v_usedLetOnly_2149_);
v_skipConstInApp_boxed_2159_ = lean_unbox(v_skipConstInApp_2150_);
v_skipInstances_boxed_2160_ = lean_unbox(v_skipInstances_2151_);
v_res_2161_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__3(v___x_2140_, v_toApplicative_2141_, v_toBind_2142_, v___f_2143_, v_inst_2144_, v_inst_2145_, v_inst_2146_, v_pre_2147_, v_post_2148_, v_usedLetOnly_boxed_2158_, v_skipConstInApp_boxed_2159_, v_skipInstances_boxed_2160_, v_x_2152_, v_x_2153_, v_args_2154_, v___y_2155_, v___f_2156_, v_a_2157_);
lean_dec(v___y_2155_);
return v_res_2161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__6(uint8_t v_skipInstances_2162_, lean_object* v_inst_2163_, lean_object* v_inst_2164_, lean_object* v_inst_2165_, lean_object* v_pre_2166_, lean_object* v_post_2167_, uint8_t v_usedLetOnly_2168_, uint8_t v_skipConstInApp_2169_, lean_object* v_x_2170_, lean_object* v_x_2171_, lean_object* v_args_2172_, lean_object* v___x_2173_, lean_object* v_toBind_2174_, lean_object* v_toApplicative_2175_, lean_object* v___f_2176_, lean_object* v_f_2177_, lean_object* v___y_2178_){
_start:
{
if (v_skipInstances_2162_ == 0)
{
lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___f_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; size_t v_sz_2187_; size_t v___x_2188_; lean_object* v___x_3651__overap_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; 
lean_dec(v___f_2176_);
lean_dec_ref(v_toApplicative_2175_);
v___x_2179_ = lean_box(v_usedLetOnly_2168_);
v___x_2180_ = lean_box(v_skipConstInApp_2169_);
v___x_2181_ = lean_box(v_skipInstances_2162_);
lean_inc_n(v___y_2178_, 2);
lean_inc(v_x_2171_);
lean_inc(v_post_2167_);
lean_inc(v_pre_2166_);
lean_inc_ref(v_inst_2165_);
lean_inc(v_inst_2164_);
lean_inc_ref(v_inst_2163_);
v___f_2182_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5___boxed), 13, 12);
lean_closure_set(v___f_2182_, 0, v_f_2177_);
lean_closure_set(v___f_2182_, 1, v_inst_2163_);
lean_closure_set(v___f_2182_, 2, v_inst_2164_);
lean_closure_set(v___f_2182_, 3, v_inst_2165_);
lean_closure_set(v___f_2182_, 4, v_pre_2166_);
lean_closure_set(v___f_2182_, 5, v_post_2167_);
lean_closure_set(v___f_2182_, 6, v___x_2179_);
lean_closure_set(v___f_2182_, 7, v___x_2180_);
lean_closure_set(v___f_2182_, 8, v___x_2181_);
lean_closure_set(v___f_2182_, 9, v_x_2170_);
lean_closure_set(v___f_2182_, 10, v_x_2171_);
lean_closure_set(v___f_2182_, 11, v___y_2178_);
v___x_2183_ = lean_box(v_usedLetOnly_2168_);
v___x_2184_ = lean_box(v_skipConstInApp_2169_);
v___x_2185_ = lean_box(v_skipInstances_2162_);
v___x_2186_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___boxed), 12, 10);
lean_closure_set(v___x_2186_, 0, v_inst_2163_);
lean_closure_set(v___x_2186_, 1, v_inst_2164_);
lean_closure_set(v___x_2186_, 2, v_inst_2165_);
lean_closure_set(v___x_2186_, 3, v_pre_2166_);
lean_closure_set(v___x_2186_, 4, v_post_2167_);
lean_closure_set(v___x_2186_, 5, v___x_2183_);
lean_closure_set(v___x_2186_, 6, v___x_2184_);
lean_closure_set(v___x_2186_, 7, v___x_2185_);
lean_closure_set(v___x_2186_, 8, v_x_2170_);
lean_closure_set(v___x_2186_, 9, v_x_2171_);
v_sz_2187_ = lean_array_size(v_args_2172_);
v___x_2188_ = ((size_t)0ULL);
v___x_3651__overap_2189_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2173_, v___x_2186_, v_sz_2187_, v___x_2188_, v_args_2172_);
v___x_2190_ = lean_apply_1(v___x_3651__overap_2189_, v___y_2178_);
v___x_2191_ = lean_apply_4(v_toBind_2174_, lean_box(0), lean_box(0), v___x_2190_, v___f_2182_);
return v___x_2191_;
}
else
{
lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___f_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___f_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; 
lean_dec_ref(v___x_2173_);
v___x_2192_ = lean_box(v_usedLetOnly_2168_);
v___x_2193_ = lean_box(v_skipConstInApp_2169_);
v___x_2194_ = lean_box(v_skipInstances_2162_);
lean_inc_n(v___y_2178_, 2);
lean_inc(v_x_2171_);
lean_inc(v_post_2167_);
lean_inc(v_pre_2166_);
lean_inc_ref(v_inst_2165_);
lean_inc_n(v_inst_2164_, 2);
lean_inc_ref(v_inst_2163_);
lean_inc_ref(v_f_2177_);
v___f_2195_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5___boxed), 13, 12);
lean_closure_set(v___f_2195_, 0, v_f_2177_);
lean_closure_set(v___f_2195_, 1, v_inst_2163_);
lean_closure_set(v___f_2195_, 2, v_inst_2164_);
lean_closure_set(v___f_2195_, 3, v_inst_2165_);
lean_closure_set(v___f_2195_, 4, v_pre_2166_);
lean_closure_set(v___f_2195_, 5, v_post_2167_);
lean_closure_set(v___f_2195_, 6, v___x_2192_);
lean_closure_set(v___f_2195_, 7, v___x_2193_);
lean_closure_set(v___f_2195_, 8, v___x_2194_);
lean_closure_set(v___f_2195_, 9, v_x_2170_);
lean_closure_set(v___f_2195_, 10, v_x_2171_);
lean_closure_set(v___f_2195_, 11, v___y_2178_);
v___x_2196_ = lean_array_get_size(v_args_2172_);
v___x_2197_ = lean_box(v_usedLetOnly_2168_);
v___x_2198_ = lean_box(v_skipConstInApp_2169_);
v___x_2199_ = lean_box(v_skipInstances_2162_);
lean_inc(v_toBind_2174_);
v___f_2200_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__3___boxed), 18, 17);
lean_closure_set(v___f_2200_, 0, v___x_2196_);
lean_closure_set(v___f_2200_, 1, v_toApplicative_2175_);
lean_closure_set(v___f_2200_, 2, v_toBind_2174_);
lean_closure_set(v___f_2200_, 3, v___f_2176_);
lean_closure_set(v___f_2200_, 4, v_inst_2163_);
lean_closure_set(v___f_2200_, 5, v_inst_2164_);
lean_closure_set(v___f_2200_, 6, v_inst_2165_);
lean_closure_set(v___f_2200_, 7, v_pre_2166_);
lean_closure_set(v___f_2200_, 8, v_post_2167_);
lean_closure_set(v___f_2200_, 9, v___x_2197_);
lean_closure_set(v___f_2200_, 10, v___x_2198_);
lean_closure_set(v___f_2200_, 11, v___x_2199_);
lean_closure_set(v___f_2200_, 12, v_x_2170_);
lean_closure_set(v___f_2200_, 13, v_x_2171_);
lean_closure_set(v___f_2200_, 14, v_args_2172_);
lean_closure_set(v___f_2200_, 15, v___y_2178_);
lean_closure_set(v___f_2200_, 16, v___f_2195_);
v___x_2201_ = lean_alloc_closure((void*)(l_Lean_Meta_getFunInfoNArgs___boxed), 7, 2);
lean_closure_set(v___x_2201_, 0, v_f_2177_);
lean_closure_set(v___x_2201_, 1, v___x_2196_);
v___x_2202_ = lean_apply_2(v_inst_2164_, lean_box(0), v___x_2201_);
v___x_2203_ = lean_apply_4(v_toBind_2174_, lean_box(0), lean_box(0), v___x_2202_, v___f_2200_);
return v___x_2203_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__6___boxed(lean_object** _args){
lean_object* v_skipInstances_2204_ = _args[0];
lean_object* v_inst_2205_ = _args[1];
lean_object* v_inst_2206_ = _args[2];
lean_object* v_inst_2207_ = _args[3];
lean_object* v_pre_2208_ = _args[4];
lean_object* v_post_2209_ = _args[5];
lean_object* v_usedLetOnly_2210_ = _args[6];
lean_object* v_skipConstInApp_2211_ = _args[7];
lean_object* v_x_2212_ = _args[8];
lean_object* v_x_2213_ = _args[9];
lean_object* v_args_2214_ = _args[10];
lean_object* v___x_2215_ = _args[11];
lean_object* v_toBind_2216_ = _args[12];
lean_object* v_toApplicative_2217_ = _args[13];
lean_object* v___f_2218_ = _args[14];
lean_object* v_f_2219_ = _args[15];
lean_object* v___y_2220_ = _args[16];
_start:
{
uint8_t v_skipInstances_boxed_2221_; uint8_t v_usedLetOnly_boxed_2222_; uint8_t v_skipConstInApp_boxed_2223_; lean_object* v_res_2224_; 
v_skipInstances_boxed_2221_ = lean_unbox(v_skipInstances_2204_);
v_usedLetOnly_boxed_2222_ = lean_unbox(v_usedLetOnly_2210_);
v_skipConstInApp_boxed_2223_ = lean_unbox(v_skipConstInApp_2211_);
v_res_2224_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__6(v_skipInstances_boxed_2221_, v_inst_2205_, v_inst_2206_, v_inst_2207_, v_pre_2208_, v_post_2209_, v_usedLetOnly_boxed_2222_, v_skipConstInApp_boxed_2223_, v_x_2212_, v_x_2213_, v_args_2214_, v___x_2215_, v_toBind_2216_, v_toApplicative_2217_, v___f_2218_, v_f_2219_, v___y_2220_);
lean_dec(v___y_2220_);
return v_res_2224_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__9(uint8_t v_skipInstances_2225_, lean_object* v_inst_2226_, lean_object* v_inst_2227_, lean_object* v_inst_2228_, lean_object* v_pre_2229_, lean_object* v_post_2230_, uint8_t v_usedLetOnly_2231_, uint8_t v_skipConstInApp_2232_, lean_object* v_x_2233_, lean_object* v_x_2234_, lean_object* v___x_2235_, lean_object* v_toBind_2236_, lean_object* v_toApplicative_2237_, lean_object* v___f_2238_, lean_object* v_f_2239_, lean_object* v_args_2240_, lean_object* v___y_2241_){
_start:
{
lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___f_2245_; lean_object* v___f_2246_; 
v___x_2242_ = lean_box(v_skipInstances_2225_);
v___x_2243_ = lean_box(v_usedLetOnly_2231_);
v___x_2244_ = lean_box(v_skipConstInApp_2232_);
lean_inc_ref(v_toApplicative_2237_);
lean_inc(v_toBind_2236_);
lean_inc(v_x_2234_);
lean_inc(v_post_2230_);
lean_inc(v_pre_2229_);
lean_inc_ref(v_inst_2228_);
lean_inc(v_inst_2227_);
lean_inc_ref(v_inst_2226_);
v___f_2245_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__6___boxed), 17, 15);
lean_closure_set(v___f_2245_, 0, v___x_2242_);
lean_closure_set(v___f_2245_, 1, v_inst_2226_);
lean_closure_set(v___f_2245_, 2, v_inst_2227_);
lean_closure_set(v___f_2245_, 3, v_inst_2228_);
lean_closure_set(v___f_2245_, 4, v_pre_2229_);
lean_closure_set(v___f_2245_, 5, v_post_2230_);
lean_closure_set(v___f_2245_, 6, v___x_2243_);
lean_closure_set(v___f_2245_, 7, v___x_2244_);
lean_closure_set(v___f_2245_, 8, v_x_2233_);
lean_closure_set(v___f_2245_, 9, v_x_2234_);
lean_closure_set(v___f_2245_, 10, v_args_2240_);
lean_closure_set(v___f_2245_, 11, v___x_2235_);
lean_closure_set(v___f_2245_, 12, v_toBind_2236_);
lean_closure_set(v___f_2245_, 13, v_toApplicative_2237_);
lean_closure_set(v___f_2245_, 14, v___f_2238_);
lean_inc(v___y_2241_);
v___f_2246_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__7___boxed), 3, 2);
lean_closure_set(v___f_2246_, 0, v___f_2245_);
lean_closure_set(v___f_2246_, 1, v___y_2241_);
if (v_skipConstInApp_2232_ == 0)
{
lean_dec_ref(v_toApplicative_2237_);
goto v___jp_2247_;
}
else
{
uint8_t v___x_2250_; 
v___x_2250_ = l_Lean_Expr_isConst(v_f_2239_);
if (v___x_2250_ == 0)
{
lean_dec_ref(v_toApplicative_2237_);
goto v___jp_2247_;
}
else
{
lean_object* v_toPure_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; 
lean_dec(v_x_2234_);
lean_dec(v_post_2230_);
lean_dec(v_pre_2229_);
lean_dec_ref(v_inst_2228_);
lean_dec(v_inst_2227_);
lean_dec_ref(v_inst_2226_);
v_toPure_2251_ = lean_ctor_get(v_toApplicative_2237_, 1);
lean_inc(v_toPure_2251_);
lean_dec_ref(v_toApplicative_2237_);
v___x_2252_ = lean_apply_2(v_toPure_2251_, lean_box(0), v_f_2239_);
v___x_2253_ = lean_apply_4(v_toBind_2236_, lean_box(0), lean_box(0), v___x_2252_, v___f_2246_);
return v___x_2253_;
}
}
v___jp_2247_:
{
lean_object* v___x_2248_; lean_object* v___x_2249_; 
v___x_2248_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2226_, v_inst_2227_, v_inst_2228_, v_pre_2229_, v_post_2230_, v_usedLetOnly_2231_, v_skipConstInApp_2232_, v_skipInstances_2225_, v_x_2233_, v_x_2234_, v_f_2239_, v___y_2241_);
v___x_2249_ = lean_apply_4(v_toBind_2236_, lean_box(0), lean_box(0), v___x_2248_, v___f_2246_);
return v___x_2249_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__9___boxed(lean_object** _args){
lean_object* v_skipInstances_2254_ = _args[0];
lean_object* v_inst_2255_ = _args[1];
lean_object* v_inst_2256_ = _args[2];
lean_object* v_inst_2257_ = _args[3];
lean_object* v_pre_2258_ = _args[4];
lean_object* v_post_2259_ = _args[5];
lean_object* v_usedLetOnly_2260_ = _args[6];
lean_object* v_skipConstInApp_2261_ = _args[7];
lean_object* v_x_2262_ = _args[8];
lean_object* v_x_2263_ = _args[9];
lean_object* v___x_2264_ = _args[10];
lean_object* v_toBind_2265_ = _args[11];
lean_object* v_toApplicative_2266_ = _args[12];
lean_object* v___f_2267_ = _args[13];
lean_object* v_f_2268_ = _args[14];
lean_object* v_args_2269_ = _args[15];
lean_object* v___y_2270_ = _args[16];
_start:
{
uint8_t v_skipInstances_boxed_2271_; uint8_t v_usedLetOnly_boxed_2272_; uint8_t v_skipConstInApp_boxed_2273_; lean_object* v_res_2274_; 
v_skipInstances_boxed_2271_ = lean_unbox(v_skipInstances_2254_);
v_usedLetOnly_boxed_2272_ = lean_unbox(v_usedLetOnly_2260_);
v_skipConstInApp_boxed_2273_ = lean_unbox(v_skipConstInApp_2261_);
v_res_2274_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__9(v_skipInstances_boxed_2271_, v_inst_2255_, v_inst_2256_, v_inst_2257_, v_pre_2258_, v_post_2259_, v_usedLetOnly_boxed_2272_, v_skipConstInApp_boxed_2273_, v_x_2262_, v_x_2263_, v___x_2264_, v_toBind_2265_, v_toApplicative_2266_, v___f_2267_, v_f_2268_, v_args_2269_, v___y_2270_);
lean_dec(v___y_2270_);
return v_res_2274_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__0(lean_object* v_fvars_2277_, lean_object* v_inst_2278_, lean_object* v_inst_2279_, lean_object* v_inst_2280_, lean_object* v_pre_2281_, lean_object* v_post_2282_, uint8_t v_usedLetOnly_2283_, uint8_t v_skipConstInApp_2284_, uint8_t v_skipInstances_2285_, lean_object* v_x_2286_, lean_object* v_x_2287_, lean_object* v_body_2288_, lean_object* v_x_2289_, lean_object* v___y_2290_){
_start:
{
lean_object* v___x_2291_; lean_object* v___x_2292_; 
v___x_2291_ = lean_array_push(v_fvars_2277_, v_x_2289_);
v___x_2292_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(v_inst_2278_, v_inst_2279_, v_inst_2280_, v_pre_2281_, v_post_2282_, v_usedLetOnly_2283_, v_skipConstInApp_2284_, v_skipInstances_2285_, v_x_2286_, v_x_2287_, v___x_2291_, v_body_2288_, v___y_2290_);
return v___x_2292_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__0___boxed(lean_object* v_fvars_2293_, lean_object* v_inst_2294_, lean_object* v_inst_2295_, lean_object* v_inst_2296_, lean_object* v_pre_2297_, lean_object* v_post_2298_, lean_object* v_usedLetOnly_2299_, lean_object* v_skipConstInApp_2300_, lean_object* v_skipInstances_2301_, lean_object* v_x_2302_, lean_object* v_x_2303_, lean_object* v_body_2304_, lean_object* v_x_2305_, lean_object* v___y_2306_){
_start:
{
uint8_t v_usedLetOnly_boxed_2307_; uint8_t v_skipConstInApp_boxed_2308_; uint8_t v_skipInstances_boxed_2309_; lean_object* v_res_2310_; 
v_usedLetOnly_boxed_2307_ = lean_unbox(v_usedLetOnly_2299_);
v_skipConstInApp_boxed_2308_ = lean_unbox(v_skipConstInApp_2300_);
v_skipInstances_boxed_2309_ = lean_unbox(v_skipInstances_2301_);
v_res_2310_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__0(v_fvars_2293_, v_inst_2294_, v_inst_2295_, v_inst_2296_, v_pre_2297_, v_post_2298_, v_usedLetOnly_boxed_2307_, v_skipConstInApp_boxed_2308_, v_skipInstances_boxed_2309_, v_x_2302_, v_x_2303_, v_body_2304_, v_x_2305_, v___y_2306_);
lean_dec(v___y_2306_);
return v_res_2310_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3___boxed(lean_object* v_inst_2311_, lean_object* v_inst_2312_, lean_object* v_inst_2313_, lean_object* v_pre_2314_, lean_object* v_post_2315_, lean_object* v_usedLetOnly_2316_, lean_object* v_skipConstInApp_2317_, lean_object* v_skipInstances_2318_, lean_object* v_x_2319_, lean_object* v_x_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_){
_start:
{
uint8_t v_usedLetOnly_boxed_2323_; uint8_t v_skipConstInApp_boxed_2324_; uint8_t v_skipInstances_boxed_2325_; lean_object* v_res_2326_; 
v_usedLetOnly_boxed_2323_ = lean_unbox(v_usedLetOnly_2316_);
v_skipConstInApp_boxed_2324_ = lean_unbox(v_skipConstInApp_2317_);
v_skipInstances_boxed_2325_ = lean_unbox(v_skipInstances_2318_);
v_res_2326_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3(v_inst_2311_, v_inst_2312_, v_inst_2313_, v_pre_2314_, v_post_2315_, v_usedLetOnly_boxed_2323_, v_skipConstInApp_boxed_2324_, v_skipInstances_boxed_2325_, v_x_2319_, v_x_2320_, v_a_2321_, v_a_2322_);
lean_dec(v_a_2321_);
return v_res_2326_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(lean_object* v_inst_2327_, lean_object* v_inst_2328_, lean_object* v_inst_2329_, lean_object* v_pre_2330_, lean_object* v_post_2331_, uint8_t v_usedLetOnly_2332_, uint8_t v_skipConstInApp_2333_, uint8_t v_skipInstances_2334_, lean_object* v_x_2335_, lean_object* v_x_2336_, lean_object* v_fvars_2337_, lean_object* v_e_2338_, lean_object* v_a_2339_){
_start:
{
lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___f_2344_; lean_object* v___f_2345_; lean_object* v___x_2346_; 
v___x_2340_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0));
v___x_2341_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1));
lean_inc_ref(v_inst_2327_);
v___x_2342_ = l_Lean_MonadCacheT_instMonad___redArg(v_x_2335_, v___x_2340_, v___x_2341_, v_inst_2327_);
v___x_2343_ = l_Lean_MonadCacheT_instMonadControl___redArg(v_x_2335_, v___x_2340_, v___x_2341_);
lean_inc_ref_n(v_inst_2329_, 2);
lean_inc_ref(v___x_2343_);
v___f_2344_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_2344_, 0, v___x_2343_);
lean_closure_set(v___f_2344_, 1, v_inst_2329_);
v___f_2345_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_2345_, 0, v___x_2343_);
lean_closure_set(v___f_2345_, 1, v_inst_2329_);
v___x_2346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2346_, 0, v___f_2344_);
lean_ctor_set(v___x_2346_, 1, v___f_2345_);
if (lean_obj_tag(v_e_2338_) == 7)
{
lean_object* v_binderName_2347_; lean_object* v_binderType_2348_; lean_object* v_body_2349_; uint8_t v_binderInfo_2350_; lean_object* v_toBind_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___f_2355_; lean_object* v___x_2356_; lean_object* v___f_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; 
v_binderName_2347_ = lean_ctor_get(v_e_2338_, 0);
lean_inc(v_binderName_2347_);
v_binderType_2348_ = lean_ctor_get(v_e_2338_, 1);
lean_inc_ref(v_binderType_2348_);
v_body_2349_ = lean_ctor_get(v_e_2338_, 2);
lean_inc_ref(v_body_2349_);
v_binderInfo_2350_ = lean_ctor_get_uint8(v_e_2338_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_2338_);
v_toBind_2351_ = lean_ctor_get(v_inst_2327_, 1);
lean_inc(v_toBind_2351_);
v___x_2352_ = lean_box(v_usedLetOnly_2332_);
v___x_2353_ = lean_box(v_skipConstInApp_2333_);
v___x_2354_ = lean_box(v_skipInstances_2334_);
lean_inc(v_x_2336_);
lean_inc(v_post_2331_);
lean_inc(v_pre_2330_);
lean_inc_ref(v_inst_2329_);
lean_inc(v_inst_2328_);
lean_inc_ref(v_inst_2327_);
lean_inc_ref(v_fvars_2337_);
v___f_2355_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__0___boxed), 14, 12);
lean_closure_set(v___f_2355_, 0, v_fvars_2337_);
lean_closure_set(v___f_2355_, 1, v_inst_2327_);
lean_closure_set(v___f_2355_, 2, v_inst_2328_);
lean_closure_set(v___f_2355_, 3, v_inst_2329_);
lean_closure_set(v___f_2355_, 4, v_pre_2330_);
lean_closure_set(v___f_2355_, 5, v_post_2331_);
lean_closure_set(v___f_2355_, 6, v___x_2352_);
lean_closure_set(v___f_2355_, 7, v___x_2353_);
lean_closure_set(v___f_2355_, 8, v___x_2354_);
lean_closure_set(v___f_2355_, 9, v_x_2335_);
lean_closure_set(v___f_2355_, 10, v_x_2336_);
lean_closure_set(v___f_2355_, 11, v_body_2349_);
v___x_2356_ = lean_box(v_binderInfo_2350_);
lean_inc(v_a_2339_);
v___f_2357_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_2357_, 0, v___x_2346_);
lean_closure_set(v___f_2357_, 1, v___x_2342_);
lean_closure_set(v___f_2357_, 2, v_binderName_2347_);
lean_closure_set(v___f_2357_, 3, v___x_2356_);
lean_closure_set(v___f_2357_, 4, v___f_2355_);
lean_closure_set(v___f_2357_, 5, v_a_2339_);
v___x_2358_ = lean_expr_instantiate_rev(v_binderType_2348_, v_fvars_2337_);
lean_dec_ref(v_fvars_2337_);
lean_dec_ref(v_binderType_2348_);
v___x_2359_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2327_, v_inst_2328_, v_inst_2329_, v_pre_2330_, v_post_2331_, v_usedLetOnly_2332_, v_skipConstInApp_2333_, v_skipInstances_2334_, v_x_2335_, v_x_2336_, v___x_2358_, v_a_2339_);
v___x_2360_ = lean_apply_4(v_toBind_2351_, lean_box(0), lean_box(0), v___x_2359_, v___f_2357_);
return v___x_2360_;
}
else
{
lean_object* v_toBind_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___f_2365_; lean_object* v___x_2366_; lean_object* v___f_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; 
lean_dec_ref(v___x_2346_);
lean_dec_ref(v___x_2342_);
v_toBind_2361_ = lean_ctor_get(v_inst_2327_, 1);
lean_inc_n(v_toBind_2361_, 2);
v___x_2362_ = lean_box(v_usedLetOnly_2332_);
v___x_2363_ = lean_box(v_skipConstInApp_2333_);
v___x_2364_ = lean_box(v_skipInstances_2334_);
lean_inc(v_a_2339_);
lean_inc(v_x_2336_);
lean_inc(v_post_2331_);
lean_inc(v_pre_2330_);
lean_inc_ref(v_inst_2329_);
lean_inc_n(v_inst_2328_, 2);
lean_inc_ref(v_inst_2327_);
v___f_2365_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3___boxed), 12, 11);
lean_closure_set(v___f_2365_, 0, v_inst_2327_);
lean_closure_set(v___f_2365_, 1, v_inst_2328_);
lean_closure_set(v___f_2365_, 2, v_inst_2329_);
lean_closure_set(v___f_2365_, 3, v_pre_2330_);
lean_closure_set(v___f_2365_, 4, v_post_2331_);
lean_closure_set(v___f_2365_, 5, v___x_2362_);
lean_closure_set(v___f_2365_, 6, v___x_2363_);
lean_closure_set(v___f_2365_, 7, v___x_2364_);
lean_closure_set(v___f_2365_, 8, v_x_2335_);
lean_closure_set(v___f_2365_, 9, v_x_2336_);
lean_closure_set(v___f_2365_, 10, v_a_2339_);
v___x_2366_ = lean_box(v_usedLetOnly_2332_);
lean_inc_ref(v_fvars_2337_);
v___f_2367_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__3___boxed), 6, 5);
lean_closure_set(v___f_2367_, 0, v_fvars_2337_);
lean_closure_set(v___f_2367_, 1, v___x_2366_);
lean_closure_set(v___f_2367_, 2, v_inst_2328_);
lean_closure_set(v___f_2367_, 3, v_toBind_2361_);
lean_closure_set(v___f_2367_, 4, v___f_2365_);
v___x_2368_ = lean_expr_instantiate_rev(v_e_2338_, v_fvars_2337_);
lean_dec_ref(v_fvars_2337_);
lean_dec_ref(v_e_2338_);
v___x_2369_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2327_, v_inst_2328_, v_inst_2329_, v_pre_2330_, v_post_2331_, v_usedLetOnly_2332_, v_skipConstInApp_2333_, v_skipInstances_2334_, v_x_2335_, v_x_2336_, v___x_2368_, v_a_2339_);
v___x_2370_ = lean_apply_4(v_toBind_2361_, lean_box(0), lean_box(0), v___x_2369_, v___f_2367_);
return v___x_2370_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__0(lean_object* v_fvars_2371_, lean_object* v_inst_2372_, lean_object* v_inst_2373_, lean_object* v_inst_2374_, lean_object* v_pre_2375_, lean_object* v_post_2376_, uint8_t v_usedLetOnly_2377_, uint8_t v_skipConstInApp_2378_, uint8_t v_skipInstances_2379_, lean_object* v_x_2380_, lean_object* v_x_2381_, lean_object* v_body_2382_, lean_object* v_x_2383_, lean_object* v___y_2384_){
_start:
{
lean_object* v___x_2385_; lean_object* v___x_2386_; 
v___x_2385_ = lean_array_push(v_fvars_2371_, v_x_2383_);
v___x_2386_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(v_inst_2372_, v_inst_2373_, v_inst_2374_, v_pre_2375_, v_post_2376_, v_usedLetOnly_2377_, v_skipConstInApp_2378_, v_skipInstances_2379_, v_x_2380_, v_x_2381_, v___x_2385_, v_body_2382_, v___y_2384_);
return v___x_2386_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__0___boxed(lean_object* v_fvars_2387_, lean_object* v_inst_2388_, lean_object* v_inst_2389_, lean_object* v_inst_2390_, lean_object* v_pre_2391_, lean_object* v_post_2392_, lean_object* v_usedLetOnly_2393_, lean_object* v_skipConstInApp_2394_, lean_object* v_skipInstances_2395_, lean_object* v_x_2396_, lean_object* v_x_2397_, lean_object* v_body_2398_, lean_object* v_x_2399_, lean_object* v___y_2400_){
_start:
{
uint8_t v_usedLetOnly_boxed_2401_; uint8_t v_skipConstInApp_boxed_2402_; uint8_t v_skipInstances_boxed_2403_; lean_object* v_res_2404_; 
v_usedLetOnly_boxed_2401_ = lean_unbox(v_usedLetOnly_2393_);
v_skipConstInApp_boxed_2402_ = lean_unbox(v_skipConstInApp_2394_);
v_skipInstances_boxed_2403_ = lean_unbox(v_skipInstances_2395_);
v_res_2404_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__0(v_fvars_2387_, v_inst_2388_, v_inst_2389_, v_inst_2390_, v_pre_2391_, v_post_2392_, v_usedLetOnly_boxed_2401_, v_skipConstInApp_boxed_2402_, v_skipInstances_boxed_2403_, v_x_2396_, v_x_2397_, v_body_2398_, v_x_2399_, v___y_2400_);
lean_dec(v___y_2400_);
return v_res_2404_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(lean_object* v_inst_2405_, lean_object* v_inst_2406_, lean_object* v_inst_2407_, lean_object* v_pre_2408_, lean_object* v_post_2409_, uint8_t v_usedLetOnly_2410_, uint8_t v_skipConstInApp_2411_, uint8_t v_skipInstances_2412_, lean_object* v_x_2413_, lean_object* v_x_2414_, lean_object* v_fvars_2415_, lean_object* v_e_2416_, lean_object* v_a_2417_){
_start:
{
lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___f_2422_; lean_object* v___f_2423_; lean_object* v___x_2424_; 
v___x_2418_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0));
v___x_2419_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1));
lean_inc_ref(v_inst_2405_);
v___x_2420_ = l_Lean_MonadCacheT_instMonad___redArg(v_x_2413_, v___x_2418_, v___x_2419_, v_inst_2405_);
v___x_2421_ = l_Lean_MonadCacheT_instMonadControl___redArg(v_x_2413_, v___x_2418_, v___x_2419_);
lean_inc_ref_n(v_inst_2407_, 2);
lean_inc_ref(v___x_2421_);
v___f_2422_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_2422_, 0, v___x_2421_);
lean_closure_set(v___f_2422_, 1, v_inst_2407_);
v___f_2423_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_2423_, 0, v___x_2421_);
lean_closure_set(v___f_2423_, 1, v_inst_2407_);
v___x_2424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2424_, 0, v___f_2422_);
lean_ctor_set(v___x_2424_, 1, v___f_2423_);
if (lean_obj_tag(v_e_2416_) == 6)
{
lean_object* v_binderName_2425_; lean_object* v_binderType_2426_; lean_object* v_body_2427_; uint8_t v_binderInfo_2428_; lean_object* v_toBind_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___f_2433_; lean_object* v___x_2434_; lean_object* v___f_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; 
v_binderName_2425_ = lean_ctor_get(v_e_2416_, 0);
lean_inc(v_binderName_2425_);
v_binderType_2426_ = lean_ctor_get(v_e_2416_, 1);
lean_inc_ref(v_binderType_2426_);
v_body_2427_ = lean_ctor_get(v_e_2416_, 2);
lean_inc_ref(v_body_2427_);
v_binderInfo_2428_ = lean_ctor_get_uint8(v_e_2416_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_2416_);
v_toBind_2429_ = lean_ctor_get(v_inst_2405_, 1);
lean_inc(v_toBind_2429_);
v___x_2430_ = lean_box(v_usedLetOnly_2410_);
v___x_2431_ = lean_box(v_skipConstInApp_2411_);
v___x_2432_ = lean_box(v_skipInstances_2412_);
lean_inc(v_x_2414_);
lean_inc(v_post_2409_);
lean_inc(v_pre_2408_);
lean_inc_ref(v_inst_2407_);
lean_inc(v_inst_2406_);
lean_inc_ref(v_inst_2405_);
lean_inc_ref(v_fvars_2415_);
v___f_2433_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__0___boxed), 14, 12);
lean_closure_set(v___f_2433_, 0, v_fvars_2415_);
lean_closure_set(v___f_2433_, 1, v_inst_2405_);
lean_closure_set(v___f_2433_, 2, v_inst_2406_);
lean_closure_set(v___f_2433_, 3, v_inst_2407_);
lean_closure_set(v___f_2433_, 4, v_pre_2408_);
lean_closure_set(v___f_2433_, 5, v_post_2409_);
lean_closure_set(v___f_2433_, 6, v___x_2430_);
lean_closure_set(v___f_2433_, 7, v___x_2431_);
lean_closure_set(v___f_2433_, 8, v___x_2432_);
lean_closure_set(v___f_2433_, 9, v_x_2413_);
lean_closure_set(v___f_2433_, 10, v_x_2414_);
lean_closure_set(v___f_2433_, 11, v_body_2427_);
v___x_2434_ = lean_box(v_binderInfo_2428_);
lean_inc(v_a_2417_);
v___f_2435_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_2435_, 0, v___x_2424_);
lean_closure_set(v___f_2435_, 1, v___x_2420_);
lean_closure_set(v___f_2435_, 2, v_binderName_2425_);
lean_closure_set(v___f_2435_, 3, v___x_2434_);
lean_closure_set(v___f_2435_, 4, v___f_2433_);
lean_closure_set(v___f_2435_, 5, v_a_2417_);
v___x_2436_ = lean_expr_instantiate_rev(v_binderType_2426_, v_fvars_2415_);
lean_dec_ref(v_fvars_2415_);
lean_dec_ref(v_binderType_2426_);
v___x_2437_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2405_, v_inst_2406_, v_inst_2407_, v_pre_2408_, v_post_2409_, v_usedLetOnly_2410_, v_skipConstInApp_2411_, v_skipInstances_2412_, v_x_2413_, v_x_2414_, v___x_2436_, v_a_2417_);
v___x_2438_ = lean_apply_4(v_toBind_2429_, lean_box(0), lean_box(0), v___x_2437_, v___f_2435_);
return v___x_2438_;
}
else
{
lean_object* v_toBind_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___f_2443_; lean_object* v___x_2444_; lean_object* v___f_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; 
lean_dec_ref(v___x_2424_);
lean_dec_ref(v___x_2420_);
v_toBind_2439_ = lean_ctor_get(v_inst_2405_, 1);
lean_inc_n(v_toBind_2439_, 2);
v___x_2440_ = lean_box(v_usedLetOnly_2410_);
v___x_2441_ = lean_box(v_skipConstInApp_2411_);
v___x_2442_ = lean_box(v_skipInstances_2412_);
lean_inc(v_a_2417_);
lean_inc(v_x_2414_);
lean_inc(v_post_2409_);
lean_inc(v_pre_2408_);
lean_inc_ref(v_inst_2407_);
lean_inc_n(v_inst_2406_, 2);
lean_inc_ref(v_inst_2405_);
v___f_2443_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3___boxed), 12, 11);
lean_closure_set(v___f_2443_, 0, v_inst_2405_);
lean_closure_set(v___f_2443_, 1, v_inst_2406_);
lean_closure_set(v___f_2443_, 2, v_inst_2407_);
lean_closure_set(v___f_2443_, 3, v_pre_2408_);
lean_closure_set(v___f_2443_, 4, v_post_2409_);
lean_closure_set(v___f_2443_, 5, v___x_2440_);
lean_closure_set(v___f_2443_, 6, v___x_2441_);
lean_closure_set(v___f_2443_, 7, v___x_2442_);
lean_closure_set(v___f_2443_, 8, v_x_2413_);
lean_closure_set(v___f_2443_, 9, v_x_2414_);
lean_closure_set(v___f_2443_, 10, v_a_2417_);
v___x_2444_ = lean_box(v_usedLetOnly_2410_);
lean_inc_ref(v_fvars_2415_);
v___f_2445_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__3___boxed), 6, 5);
lean_closure_set(v___f_2445_, 0, v_fvars_2415_);
lean_closure_set(v___f_2445_, 1, v___x_2444_);
lean_closure_set(v___f_2445_, 2, v_inst_2406_);
lean_closure_set(v___f_2445_, 3, v_toBind_2439_);
lean_closure_set(v___f_2445_, 4, v___f_2443_);
v___x_2446_ = lean_expr_instantiate_rev(v_e_2416_, v_fvars_2415_);
lean_dec_ref(v_fvars_2415_);
lean_dec_ref(v_e_2416_);
v___x_2447_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2405_, v_inst_2406_, v_inst_2407_, v_pre_2408_, v_post_2409_, v_usedLetOnly_2410_, v_skipConstInApp_2411_, v_skipInstances_2412_, v_x_2413_, v_x_2414_, v___x_2446_, v_a_2417_);
v___x_2448_ = lean_apply_4(v_toBind_2439_, lean_box(0), lean_box(0), v___x_2447_, v___f_2445_);
return v___x_2448_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__0(lean_object* v_fvars_2449_, lean_object* v_inst_2450_, lean_object* v_inst_2451_, lean_object* v_inst_2452_, lean_object* v_pre_2453_, lean_object* v_post_2454_, uint8_t v_usedLetOnly_2455_, uint8_t v_skipConstInApp_2456_, uint8_t v_skipInstances_2457_, lean_object* v_x_2458_, lean_object* v_x_2459_, lean_object* v_body_2460_, lean_object* v_x_2461_, lean_object* v___y_2462_){
_start:
{
lean_object* v___x_2463_; lean_object* v___x_2464_; 
v___x_2463_ = lean_array_push(v_fvars_2449_, v_x_2461_);
v___x_2464_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(v_inst_2450_, v_inst_2451_, v_inst_2452_, v_pre_2453_, v_post_2454_, v_usedLetOnly_2455_, v_skipConstInApp_2456_, v_skipInstances_2457_, v_x_2458_, v_x_2459_, v___x_2463_, v_body_2460_, v___y_2462_);
return v___x_2464_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__0___boxed(lean_object* v_fvars_2465_, lean_object* v_inst_2466_, lean_object* v_inst_2467_, lean_object* v_inst_2468_, lean_object* v_pre_2469_, lean_object* v_post_2470_, lean_object* v_usedLetOnly_2471_, lean_object* v_skipConstInApp_2472_, lean_object* v_skipInstances_2473_, lean_object* v_x_2474_, lean_object* v_x_2475_, lean_object* v_body_2476_, lean_object* v_x_2477_, lean_object* v___y_2478_){
_start:
{
uint8_t v_usedLetOnly_boxed_2479_; uint8_t v_skipConstInApp_boxed_2480_; uint8_t v_skipInstances_boxed_2481_; lean_object* v_res_2482_; 
v_usedLetOnly_boxed_2479_ = lean_unbox(v_usedLetOnly_2471_);
v_skipConstInApp_boxed_2480_ = lean_unbox(v_skipConstInApp_2472_);
v_skipInstances_boxed_2481_ = lean_unbox(v_skipInstances_2473_);
v_res_2482_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__0(v_fvars_2465_, v_inst_2466_, v_inst_2467_, v_inst_2468_, v_pre_2469_, v_post_2470_, v_usedLetOnly_boxed_2479_, v_skipConstInApp_boxed_2480_, v_skipInstances_boxed_2481_, v_x_2474_, v_x_2475_, v_body_2476_, v_x_2477_, v___y_2478_);
lean_dec(v___y_2478_);
return v_res_2482_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__2(lean_object* v___x_2483_, lean_object* v___x_2484_, lean_object* v_declName_2485_, lean_object* v___f_2486_, uint8_t v_nondep_2487_, lean_object* v_a_2488_, lean_object* v_value_2489_, lean_object* v_fvars_2490_, lean_object* v_inst_2491_, lean_object* v_inst_2492_, lean_object* v_inst_2493_, lean_object* v_pre_2494_, lean_object* v_post_2495_, uint8_t v_usedLetOnly_2496_, uint8_t v_skipConstInApp_2497_, uint8_t v_skipInstances_2498_, lean_object* v_x_2499_, lean_object* v_x_2500_, lean_object* v_toBind_2501_, lean_object* v_a_2502_){
_start:
{
lean_object* v___x_2503_; lean_object* v___f_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; 
v___x_2503_ = lean_box(v_nondep_2487_);
lean_inc(v_a_2488_);
v___f_2504_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_2504_, 0, v___x_2483_);
lean_closure_set(v___f_2504_, 1, v___x_2484_);
lean_closure_set(v___f_2504_, 2, v_declName_2485_);
lean_closure_set(v___f_2504_, 3, v_a_2502_);
lean_closure_set(v___f_2504_, 4, v___f_2486_);
lean_closure_set(v___f_2504_, 5, v___x_2503_);
lean_closure_set(v___f_2504_, 6, v_a_2488_);
v___x_2505_ = lean_expr_instantiate_rev(v_value_2489_, v_fvars_2490_);
v___x_2506_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2491_, v_inst_2492_, v_inst_2493_, v_pre_2494_, v_post_2495_, v_usedLetOnly_2496_, v_skipConstInApp_2497_, v_skipInstances_2498_, v_x_2499_, v_x_2500_, v___x_2505_, v_a_2488_);
v___x_2507_ = lean_apply_4(v_toBind_2501_, lean_box(0), lean_box(0), v___x_2506_, v___f_2504_);
return v___x_2507_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__2___boxed(lean_object** _args){
lean_object* v___x_2508_ = _args[0];
lean_object* v___x_2509_ = _args[1];
lean_object* v_declName_2510_ = _args[2];
lean_object* v___f_2511_ = _args[3];
lean_object* v_nondep_2512_ = _args[4];
lean_object* v_a_2513_ = _args[5];
lean_object* v_value_2514_ = _args[6];
lean_object* v_fvars_2515_ = _args[7];
lean_object* v_inst_2516_ = _args[8];
lean_object* v_inst_2517_ = _args[9];
lean_object* v_inst_2518_ = _args[10];
lean_object* v_pre_2519_ = _args[11];
lean_object* v_post_2520_ = _args[12];
lean_object* v_usedLetOnly_2521_ = _args[13];
lean_object* v_skipConstInApp_2522_ = _args[14];
lean_object* v_skipInstances_2523_ = _args[15];
lean_object* v_x_2524_ = _args[16];
lean_object* v_x_2525_ = _args[17];
lean_object* v_toBind_2526_ = _args[18];
lean_object* v_a_2527_ = _args[19];
_start:
{
uint8_t v_nondep_4209__boxed_2528_; uint8_t v_usedLetOnly_boxed_2529_; uint8_t v_skipConstInApp_boxed_2530_; uint8_t v_skipInstances_boxed_2531_; lean_object* v_res_2532_; 
v_nondep_4209__boxed_2528_ = lean_unbox(v_nondep_2512_);
v_usedLetOnly_boxed_2529_ = lean_unbox(v_usedLetOnly_2521_);
v_skipConstInApp_boxed_2530_ = lean_unbox(v_skipConstInApp_2522_);
v_skipInstances_boxed_2531_ = lean_unbox(v_skipInstances_2523_);
v_res_2532_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__2(v___x_2508_, v___x_2509_, v_declName_2510_, v___f_2511_, v_nondep_4209__boxed_2528_, v_a_2513_, v_value_2514_, v_fvars_2515_, v_inst_2516_, v_inst_2517_, v_inst_2518_, v_pre_2519_, v_post_2520_, v_usedLetOnly_boxed_2529_, v_skipConstInApp_boxed_2530_, v_skipInstances_boxed_2531_, v_x_2524_, v_x_2525_, v_toBind_2526_, v_a_2527_);
lean_dec_ref(v_fvars_2515_);
lean_dec_ref(v_value_2514_);
lean_dec(v_a_2513_);
return v_res_2532_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(lean_object* v_inst_2533_, lean_object* v_inst_2534_, lean_object* v_inst_2535_, lean_object* v_pre_2536_, lean_object* v_post_2537_, uint8_t v_usedLetOnly_2538_, uint8_t v_skipConstInApp_2539_, uint8_t v_skipInstances_2540_, lean_object* v_x_2541_, lean_object* v_x_2542_, lean_object* v_fvars_2543_, lean_object* v_e_2544_, lean_object* v_a_2545_){
_start:
{
lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___f_2550_; lean_object* v___f_2551_; lean_object* v___x_2552_; 
v___x_2546_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0));
v___x_2547_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1));
lean_inc_ref(v_inst_2533_);
v___x_2548_ = l_Lean_MonadCacheT_instMonad___redArg(v_x_2541_, v___x_2546_, v___x_2547_, v_inst_2533_);
v___x_2549_ = l_Lean_MonadCacheT_instMonadControl___redArg(v_x_2541_, v___x_2546_, v___x_2547_);
lean_inc_ref_n(v_inst_2535_, 2);
lean_inc_ref(v___x_2549_);
v___f_2550_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_2550_, 0, v___x_2549_);
lean_closure_set(v___f_2550_, 1, v_inst_2535_);
v___f_2551_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_2551_, 0, v___x_2549_);
lean_closure_set(v___f_2551_, 1, v_inst_2535_);
v___x_2552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2552_, 0, v___f_2550_);
lean_ctor_set(v___x_2552_, 1, v___f_2551_);
if (lean_obj_tag(v_e_2544_) == 8)
{
lean_object* v_declName_2553_; lean_object* v_type_2554_; lean_object* v_value_2555_; lean_object* v_body_2556_; uint8_t v_nondep_2557_; lean_object* v_toBind_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___f_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___f_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; 
v_declName_2553_ = lean_ctor_get(v_e_2544_, 0);
lean_inc(v_declName_2553_);
v_type_2554_ = lean_ctor_get(v_e_2544_, 1);
lean_inc_ref(v_type_2554_);
v_value_2555_ = lean_ctor_get(v_e_2544_, 2);
lean_inc_ref(v_value_2555_);
v_body_2556_ = lean_ctor_get(v_e_2544_, 3);
lean_inc_ref(v_body_2556_);
v_nondep_2557_ = lean_ctor_get_uint8(v_e_2544_, sizeof(void*)*4 + 8);
lean_dec_ref(v_e_2544_);
v_toBind_2558_ = lean_ctor_get(v_inst_2533_, 1);
lean_inc_n(v_toBind_2558_, 2);
v___x_2559_ = lean_box(v_usedLetOnly_2538_);
v___x_2560_ = lean_box(v_skipConstInApp_2539_);
v___x_2561_ = lean_box(v_skipInstances_2540_);
lean_inc_n(v_x_2542_, 2);
lean_inc_n(v_post_2537_, 2);
lean_inc_n(v_pre_2536_, 2);
lean_inc_ref_n(v_inst_2535_, 2);
lean_inc_n(v_inst_2534_, 2);
lean_inc_ref_n(v_inst_2533_, 2);
lean_inc_ref_n(v_fvars_2543_, 2);
v___f_2562_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__0___boxed), 14, 12);
lean_closure_set(v___f_2562_, 0, v_fvars_2543_);
lean_closure_set(v___f_2562_, 1, v_inst_2533_);
lean_closure_set(v___f_2562_, 2, v_inst_2534_);
lean_closure_set(v___f_2562_, 3, v_inst_2535_);
lean_closure_set(v___f_2562_, 4, v_pre_2536_);
lean_closure_set(v___f_2562_, 5, v_post_2537_);
lean_closure_set(v___f_2562_, 6, v___x_2559_);
lean_closure_set(v___f_2562_, 7, v___x_2560_);
lean_closure_set(v___f_2562_, 8, v___x_2561_);
lean_closure_set(v___f_2562_, 9, v_x_2541_);
lean_closure_set(v___f_2562_, 10, v_x_2542_);
lean_closure_set(v___f_2562_, 11, v_body_2556_);
v___x_2563_ = lean_box(v_nondep_2557_);
v___x_2564_ = lean_box(v_usedLetOnly_2538_);
v___x_2565_ = lean_box(v_skipConstInApp_2539_);
v___x_2566_ = lean_box(v_skipInstances_2540_);
lean_inc(v_a_2545_);
v___f_2567_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__2___boxed), 20, 19);
lean_closure_set(v___f_2567_, 0, v___x_2552_);
lean_closure_set(v___f_2567_, 1, v___x_2548_);
lean_closure_set(v___f_2567_, 2, v_declName_2553_);
lean_closure_set(v___f_2567_, 3, v___f_2562_);
lean_closure_set(v___f_2567_, 4, v___x_2563_);
lean_closure_set(v___f_2567_, 5, v_a_2545_);
lean_closure_set(v___f_2567_, 6, v_value_2555_);
lean_closure_set(v___f_2567_, 7, v_fvars_2543_);
lean_closure_set(v___f_2567_, 8, v_inst_2533_);
lean_closure_set(v___f_2567_, 9, v_inst_2534_);
lean_closure_set(v___f_2567_, 10, v_inst_2535_);
lean_closure_set(v___f_2567_, 11, v_pre_2536_);
lean_closure_set(v___f_2567_, 12, v_post_2537_);
lean_closure_set(v___f_2567_, 13, v___x_2564_);
lean_closure_set(v___f_2567_, 14, v___x_2565_);
lean_closure_set(v___f_2567_, 15, v___x_2566_);
lean_closure_set(v___f_2567_, 16, v_x_2541_);
lean_closure_set(v___f_2567_, 17, v_x_2542_);
lean_closure_set(v___f_2567_, 18, v_toBind_2558_);
v___x_2568_ = lean_expr_instantiate_rev(v_type_2554_, v_fvars_2543_);
lean_dec_ref(v_fvars_2543_);
lean_dec_ref(v_type_2554_);
v___x_2569_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2533_, v_inst_2534_, v_inst_2535_, v_pre_2536_, v_post_2537_, v_usedLetOnly_2538_, v_skipConstInApp_2539_, v_skipInstances_2540_, v_x_2541_, v_x_2542_, v___x_2568_, v_a_2545_);
v___x_2570_ = lean_apply_4(v_toBind_2558_, lean_box(0), lean_box(0), v___x_2569_, v___f_2567_);
return v___x_2570_;
}
else
{
lean_object* v_toBind_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___f_2575_; lean_object* v___x_2576_; lean_object* v___f_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; 
lean_dec_ref(v___x_2552_);
lean_dec_ref(v___x_2548_);
v_toBind_2571_ = lean_ctor_get(v_inst_2533_, 1);
lean_inc_n(v_toBind_2571_, 2);
v___x_2572_ = lean_box(v_usedLetOnly_2538_);
v___x_2573_ = lean_box(v_skipConstInApp_2539_);
v___x_2574_ = lean_box(v_skipInstances_2540_);
lean_inc(v_a_2545_);
lean_inc(v_x_2542_);
lean_inc(v_post_2537_);
lean_inc(v_pre_2536_);
lean_inc_ref(v_inst_2535_);
lean_inc_n(v_inst_2534_, 2);
lean_inc_ref(v_inst_2533_);
v___f_2575_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3___boxed), 12, 11);
lean_closure_set(v___f_2575_, 0, v_inst_2533_);
lean_closure_set(v___f_2575_, 1, v_inst_2534_);
lean_closure_set(v___f_2575_, 2, v_inst_2535_);
lean_closure_set(v___f_2575_, 3, v_pre_2536_);
lean_closure_set(v___f_2575_, 4, v_post_2537_);
lean_closure_set(v___f_2575_, 5, v___x_2572_);
lean_closure_set(v___f_2575_, 6, v___x_2573_);
lean_closure_set(v___f_2575_, 7, v___x_2574_);
lean_closure_set(v___f_2575_, 8, v_x_2541_);
lean_closure_set(v___f_2575_, 9, v_x_2542_);
lean_closure_set(v___f_2575_, 10, v_a_2545_);
v___x_2576_ = lean_box(v_usedLetOnly_2538_);
lean_inc_ref(v_fvars_2543_);
v___f_2577_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__4___boxed), 6, 5);
lean_closure_set(v___f_2577_, 0, v_fvars_2543_);
lean_closure_set(v___f_2577_, 1, v___x_2576_);
lean_closure_set(v___f_2577_, 2, v_inst_2534_);
lean_closure_set(v___f_2577_, 3, v_toBind_2571_);
lean_closure_set(v___f_2577_, 4, v___f_2575_);
v___x_2578_ = lean_expr_instantiate_rev(v_e_2544_, v_fvars_2543_);
lean_dec_ref(v_fvars_2543_);
lean_dec_ref(v_e_2544_);
v___x_2579_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2533_, v_inst_2534_, v_inst_2535_, v_pre_2536_, v_post_2537_, v_usedLetOnly_2538_, v_skipConstInApp_2539_, v_skipInstances_2540_, v_x_2541_, v_x_2542_, v___x_2578_, v_a_2545_);
v___x_2580_ = lean_apply_4(v_toBind_2571_, lean_box(0), lean_box(0), v___x_2579_, v___f_2577_);
return v___x_2580_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__8(lean_object* v_expr_2581_, lean_object* v_data_2582_, lean_object* v_inst_2583_, lean_object* v_inst_2584_, lean_object* v_inst_2585_, lean_object* v_pre_2586_, lean_object* v_post_2587_, uint8_t v_usedLetOnly_2588_, uint8_t v_skipConstInApp_2589_, uint8_t v_skipInstances_2590_, lean_object* v_x_2591_, lean_object* v_x_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v_a_2595_){
_start:
{
size_t v___x_2596_; size_t v___x_2597_; uint8_t v___x_2598_; 
v___x_2596_ = lean_ptr_addr(v_expr_2581_);
v___x_2597_ = lean_ptr_addr(v_a_2595_);
v___x_2598_ = lean_usize_dec_eq(v___x_2596_, v___x_2597_);
if (v___x_2598_ == 0)
{
lean_object* v___x_2599_; lean_object* v___x_2600_; 
lean_dec_ref(v___y_2594_);
v___x_2599_ = l_Lean_Expr_mdata___override(v_data_2582_, v_a_2595_);
v___x_2600_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2583_, v_inst_2584_, v_inst_2585_, v_pre_2586_, v_post_2587_, v_usedLetOnly_2588_, v_skipConstInApp_2589_, v_skipInstances_2590_, v_x_2591_, v_x_2592_, v___x_2599_, v___y_2593_);
return v___x_2600_;
}
else
{
lean_object* v___x_2601_; 
lean_dec_ref(v_a_2595_);
lean_dec(v_data_2582_);
v___x_2601_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2583_, v_inst_2584_, v_inst_2585_, v_pre_2586_, v_post_2587_, v_usedLetOnly_2588_, v_skipConstInApp_2589_, v_skipInstances_2590_, v_x_2591_, v_x_2592_, v___y_2594_, v___y_2593_);
return v___x_2601_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__8___boxed(lean_object* v_expr_2602_, lean_object* v_data_2603_, lean_object* v_inst_2604_, lean_object* v_inst_2605_, lean_object* v_inst_2606_, lean_object* v_pre_2607_, lean_object* v_post_2608_, lean_object* v_usedLetOnly_2609_, lean_object* v_skipConstInApp_2610_, lean_object* v_skipInstances_2611_, lean_object* v_x_2612_, lean_object* v_x_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v_a_2616_){
_start:
{
uint8_t v_usedLetOnly_boxed_2617_; uint8_t v_skipConstInApp_boxed_2618_; uint8_t v_skipInstances_boxed_2619_; lean_object* v_res_2620_; 
v_usedLetOnly_boxed_2617_ = lean_unbox(v_usedLetOnly_2609_);
v_skipConstInApp_boxed_2618_ = lean_unbox(v_skipConstInApp_2610_);
v_skipInstances_boxed_2619_ = lean_unbox(v_skipInstances_2611_);
v_res_2620_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__8(v_expr_2602_, v_data_2603_, v_inst_2604_, v_inst_2605_, v_inst_2606_, v_pre_2607_, v_post_2608_, v_usedLetOnly_boxed_2617_, v_skipConstInApp_boxed_2618_, v_skipInstances_boxed_2619_, v_x_2612_, v_x_2613_, v___y_2614_, v___y_2615_, v_a_2616_);
lean_dec(v___y_2614_);
lean_dec_ref(v_expr_2602_);
return v_res_2620_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__10(lean_object* v_struct_2621_, lean_object* v_typeName_2622_, lean_object* v_idx_2623_, lean_object* v_inst_2624_, lean_object* v_inst_2625_, lean_object* v_inst_2626_, lean_object* v_pre_2627_, lean_object* v_post_2628_, uint8_t v_usedLetOnly_2629_, uint8_t v_skipConstInApp_2630_, uint8_t v_skipInstances_2631_, lean_object* v_x_2632_, lean_object* v_x_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v_a_2636_){
_start:
{
size_t v___x_2637_; size_t v___x_2638_; uint8_t v___x_2639_; 
v___x_2637_ = lean_ptr_addr(v_struct_2621_);
v___x_2638_ = lean_ptr_addr(v_a_2636_);
v___x_2639_ = lean_usize_dec_eq(v___x_2637_, v___x_2638_);
if (v___x_2639_ == 0)
{
lean_object* v___x_2640_; lean_object* v___x_2641_; 
lean_dec_ref(v___y_2635_);
v___x_2640_ = l_Lean_Expr_proj___override(v_typeName_2622_, v_idx_2623_, v_a_2636_);
v___x_2641_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2624_, v_inst_2625_, v_inst_2626_, v_pre_2627_, v_post_2628_, v_usedLetOnly_2629_, v_skipConstInApp_2630_, v_skipInstances_2631_, v_x_2632_, v_x_2633_, v___x_2640_, v___y_2634_);
return v___x_2641_;
}
else
{
lean_object* v___x_2642_; 
lean_dec_ref(v_a_2636_);
lean_dec(v_idx_2623_);
lean_dec(v_typeName_2622_);
v___x_2642_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2624_, v_inst_2625_, v_inst_2626_, v_pre_2627_, v_post_2628_, v_usedLetOnly_2629_, v_skipConstInApp_2630_, v_skipInstances_2631_, v_x_2632_, v_x_2633_, v___y_2635_, v___y_2634_);
return v___x_2642_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__10___boxed(lean_object* v_struct_2643_, lean_object* v_typeName_2644_, lean_object* v_idx_2645_, lean_object* v_inst_2646_, lean_object* v_inst_2647_, lean_object* v_inst_2648_, lean_object* v_pre_2649_, lean_object* v_post_2650_, lean_object* v_usedLetOnly_2651_, lean_object* v_skipConstInApp_2652_, lean_object* v_skipInstances_2653_, lean_object* v_x_2654_, lean_object* v_x_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v_a_2658_){
_start:
{
uint8_t v_usedLetOnly_boxed_2659_; uint8_t v_skipConstInApp_boxed_2660_; uint8_t v_skipInstances_boxed_2661_; lean_object* v_res_2662_; 
v_usedLetOnly_boxed_2659_ = lean_unbox(v_usedLetOnly_2651_);
v_skipConstInApp_boxed_2660_ = lean_unbox(v_skipConstInApp_2652_);
v_skipInstances_boxed_2661_ = lean_unbox(v_skipInstances_2653_);
v_res_2662_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__10(v_struct_2643_, v_typeName_2644_, v_idx_2645_, v_inst_2646_, v_inst_2647_, v_inst_2648_, v_pre_2649_, v_post_2650_, v_usedLetOnly_boxed_2659_, v_skipConstInApp_boxed_2660_, v_skipInstances_boxed_2661_, v_x_2654_, v_x_2655_, v___y_2656_, v___y_2657_, v_a_2658_);
lean_dec(v___y_2656_);
lean_dec_ref(v_struct_2643_);
return v_res_2662_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11(lean_object* v_toApplicative_2663_, lean_object* v_inst_2664_, lean_object* v_inst_2665_, lean_object* v_inst_2666_, lean_object* v_pre_2667_, lean_object* v_post_2668_, uint8_t v_usedLetOnly_2669_, uint8_t v_skipConstInApp_2670_, uint8_t v_skipInstances_2671_, lean_object* v_x_2672_, lean_object* v_x_2673_, lean_object* v___y_2674_, lean_object* v___f_2675_, lean_object* v_toBind_2676_, lean_object* v_e_2677_, lean_object* v_a_2678_){
_start:
{
lean_object* v___y_2680_; 
switch(lean_obj_tag(v_a_2678_))
{
case 0:
{
lean_object* v_e_2712_; lean_object* v_toPure_2713_; lean_object* v___x_2714_; 
lean_dec_ref(v_e_2677_);
lean_dec(v_toBind_2676_);
lean_dec(v___f_2675_);
lean_dec(v_x_2673_);
lean_dec(v_post_2668_);
lean_dec(v_pre_2667_);
lean_dec_ref(v_inst_2666_);
lean_dec(v_inst_2665_);
lean_dec_ref(v_inst_2664_);
v_e_2712_ = lean_ctor_get(v_a_2678_, 0);
lean_inc_ref(v_e_2712_);
lean_dec_ref(v_a_2678_);
v_toPure_2713_ = lean_ctor_get(v_toApplicative_2663_, 1);
lean_inc(v_toPure_2713_);
lean_dec_ref(v_toApplicative_2663_);
v___x_2714_ = lean_apply_2(v_toPure_2713_, lean_box(0), v_e_2712_);
return v___x_2714_;
}
case 1:
{
lean_object* v_e_2715_; lean_object* v___x_2716_; 
lean_dec_ref(v_e_2677_);
lean_dec(v_toBind_2676_);
lean_dec(v___f_2675_);
lean_dec_ref(v_toApplicative_2663_);
v_e_2715_ = lean_ctor_get(v_a_2678_, 0);
lean_inc_ref(v_e_2715_);
lean_dec_ref(v_a_2678_);
v___x_2716_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2664_, v_inst_2665_, v_inst_2666_, v_pre_2667_, v_post_2668_, v_usedLetOnly_2669_, v_skipConstInApp_2670_, v_skipInstances_2671_, v_x_2672_, v_x_2673_, v_e_2715_, v___y_2674_);
return v___x_2716_;
}
default: 
{
lean_object* v_e_x3f_2717_; 
lean_dec_ref(v_toApplicative_2663_);
v_e_x3f_2717_ = lean_ctor_get(v_a_2678_, 0);
lean_inc(v_e_x3f_2717_);
lean_dec_ref(v_a_2678_);
if (lean_obj_tag(v_e_x3f_2717_) == 0)
{
v___y_2680_ = v_e_2677_;
goto v___jp_2679_;
}
else
{
lean_object* v_val_2718_; 
lean_dec_ref(v_e_2677_);
v_val_2718_ = lean_ctor_get(v_e_x3f_2717_, 0);
lean_inc(v_val_2718_);
lean_dec_ref(v_e_x3f_2717_);
v___y_2680_ = v_val_2718_;
goto v___jp_2679_;
}
}
}
v___jp_2679_:
{
switch(lean_obj_tag(v___y_2680_))
{
case 7:
{
lean_object* v___x_2681_; lean_object* v___x_2682_; 
lean_dec(v_toBind_2676_);
lean_dec(v___f_2675_);
v___x_2681_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_2682_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(v_inst_2664_, v_inst_2665_, v_inst_2666_, v_pre_2667_, v_post_2668_, v_usedLetOnly_2669_, v_skipConstInApp_2670_, v_skipInstances_2671_, v_x_2672_, v_x_2673_, v___x_2681_, v___y_2680_, v___y_2674_);
return v___x_2682_;
}
case 6:
{
lean_object* v___x_2683_; lean_object* v___x_2684_; 
lean_dec(v_toBind_2676_);
lean_dec(v___f_2675_);
v___x_2683_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_2684_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(v_inst_2664_, v_inst_2665_, v_inst_2666_, v_pre_2667_, v_post_2668_, v_usedLetOnly_2669_, v_skipConstInApp_2670_, v_skipInstances_2671_, v_x_2672_, v_x_2673_, v___x_2683_, v___y_2680_, v___y_2674_);
return v___x_2684_;
}
case 8:
{
lean_object* v___x_2685_; lean_object* v___x_2686_; 
lean_dec(v_toBind_2676_);
lean_dec(v___f_2675_);
v___x_2685_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_2686_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(v_inst_2664_, v_inst_2665_, v_inst_2666_, v_pre_2667_, v_post_2668_, v_usedLetOnly_2669_, v_skipConstInApp_2670_, v_skipInstances_2671_, v_x_2672_, v_x_2673_, v___x_2685_, v___y_2680_, v___y_2674_);
return v___x_2686_;
}
case 5:
{
lean_object* v_dummy_2687_; lean_object* v_nargs_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_3755__overap_2692_; lean_object* v___x_2693_; 
lean_dec(v_toBind_2676_);
lean_dec(v_x_2673_);
lean_dec(v_post_2668_);
lean_dec(v_pre_2667_);
lean_dec_ref(v_inst_2666_);
lean_dec(v_inst_2665_);
lean_dec_ref(v_inst_2664_);
v_dummy_2687_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_2688_ = l_Lean_Expr_getAppNumArgs(v___y_2680_);
lean_inc(v_nargs_2688_);
v___x_2689_ = lean_mk_array(v_nargs_2688_, v_dummy_2687_);
v___x_2690_ = lean_unsigned_to_nat(1u);
v___x_2691_ = lean_nat_sub(v_nargs_2688_, v___x_2690_);
lean_dec(v_nargs_2688_);
v___x_3755__overap_2692_ = l_Lean_Expr_withAppAux___redArg(v___f_2675_, v___y_2680_, v___x_2689_, v___x_2691_);
lean_inc(v___y_2674_);
v___x_2693_ = lean_apply_1(v___x_3755__overap_2692_, v___y_2674_);
return v___x_2693_;
}
case 10:
{
lean_object* v_data_2694_; lean_object* v_expr_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___f_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; 
lean_dec(v___f_2675_);
v_data_2694_ = lean_ctor_get(v___y_2680_, 0);
lean_inc(v_data_2694_);
v_expr_2695_ = lean_ctor_get(v___y_2680_, 1);
lean_inc_ref_n(v_expr_2695_, 2);
v___x_2696_ = lean_box(v_usedLetOnly_2669_);
v___x_2697_ = lean_box(v_skipConstInApp_2670_);
v___x_2698_ = lean_box(v_skipInstances_2671_);
lean_inc(v___y_2674_);
lean_inc(v_x_2673_);
lean_inc(v_post_2668_);
lean_inc(v_pre_2667_);
lean_inc_ref(v_inst_2666_);
lean_inc(v_inst_2665_);
lean_inc_ref(v_inst_2664_);
v___f_2699_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__8___boxed), 15, 14);
lean_closure_set(v___f_2699_, 0, v_expr_2695_);
lean_closure_set(v___f_2699_, 1, v_data_2694_);
lean_closure_set(v___f_2699_, 2, v_inst_2664_);
lean_closure_set(v___f_2699_, 3, v_inst_2665_);
lean_closure_set(v___f_2699_, 4, v_inst_2666_);
lean_closure_set(v___f_2699_, 5, v_pre_2667_);
lean_closure_set(v___f_2699_, 6, v_post_2668_);
lean_closure_set(v___f_2699_, 7, v___x_2696_);
lean_closure_set(v___f_2699_, 8, v___x_2697_);
lean_closure_set(v___f_2699_, 9, v___x_2698_);
lean_closure_set(v___f_2699_, 10, v_x_2672_);
lean_closure_set(v___f_2699_, 11, v_x_2673_);
lean_closure_set(v___f_2699_, 12, v___y_2674_);
lean_closure_set(v___f_2699_, 13, v___y_2680_);
v___x_2700_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2664_, v_inst_2665_, v_inst_2666_, v_pre_2667_, v_post_2668_, v_usedLetOnly_2669_, v_skipConstInApp_2670_, v_skipInstances_2671_, v_x_2672_, v_x_2673_, v_expr_2695_, v___y_2674_);
v___x_2701_ = lean_apply_4(v_toBind_2676_, lean_box(0), lean_box(0), v___x_2700_, v___f_2699_);
return v___x_2701_;
}
case 11:
{
lean_object* v_typeName_2702_; lean_object* v_idx_2703_; lean_object* v_struct_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___f_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; 
lean_dec(v___f_2675_);
v_typeName_2702_ = lean_ctor_get(v___y_2680_, 0);
lean_inc(v_typeName_2702_);
v_idx_2703_ = lean_ctor_get(v___y_2680_, 1);
lean_inc(v_idx_2703_);
v_struct_2704_ = lean_ctor_get(v___y_2680_, 2);
lean_inc_ref_n(v_struct_2704_, 2);
v___x_2705_ = lean_box(v_usedLetOnly_2669_);
v___x_2706_ = lean_box(v_skipConstInApp_2670_);
v___x_2707_ = lean_box(v_skipInstances_2671_);
lean_inc(v___y_2674_);
lean_inc(v_x_2673_);
lean_inc(v_post_2668_);
lean_inc(v_pre_2667_);
lean_inc_ref(v_inst_2666_);
lean_inc(v_inst_2665_);
lean_inc_ref(v_inst_2664_);
v___f_2708_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__10___boxed), 16, 15);
lean_closure_set(v___f_2708_, 0, v_struct_2704_);
lean_closure_set(v___f_2708_, 1, v_typeName_2702_);
lean_closure_set(v___f_2708_, 2, v_idx_2703_);
lean_closure_set(v___f_2708_, 3, v_inst_2664_);
lean_closure_set(v___f_2708_, 4, v_inst_2665_);
lean_closure_set(v___f_2708_, 5, v_inst_2666_);
lean_closure_set(v___f_2708_, 6, v_pre_2667_);
lean_closure_set(v___f_2708_, 7, v_post_2668_);
lean_closure_set(v___f_2708_, 8, v___x_2705_);
lean_closure_set(v___f_2708_, 9, v___x_2706_);
lean_closure_set(v___f_2708_, 10, v___x_2707_);
lean_closure_set(v___f_2708_, 11, v_x_2672_);
lean_closure_set(v___f_2708_, 12, v_x_2673_);
lean_closure_set(v___f_2708_, 13, v___y_2674_);
lean_closure_set(v___f_2708_, 14, v___y_2680_);
v___x_2709_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2664_, v_inst_2665_, v_inst_2666_, v_pre_2667_, v_post_2668_, v_usedLetOnly_2669_, v_skipConstInApp_2670_, v_skipInstances_2671_, v_x_2672_, v_x_2673_, v_struct_2704_, v___y_2674_);
v___x_2710_ = lean_apply_4(v_toBind_2676_, lean_box(0), lean_box(0), v___x_2709_, v___f_2708_);
return v___x_2710_;
}
default: 
{
lean_object* v___x_2711_; 
lean_dec(v_toBind_2676_);
lean_dec(v___f_2675_);
v___x_2711_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2664_, v_inst_2665_, v_inst_2666_, v_pre_2667_, v_post_2668_, v_usedLetOnly_2669_, v_skipConstInApp_2670_, v_skipInstances_2671_, v_x_2672_, v_x_2673_, v___y_2680_, v___y_2674_);
return v___x_2711_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___boxed(lean_object* v_toApplicative_2719_, lean_object* v_inst_2720_, lean_object* v_inst_2721_, lean_object* v_inst_2722_, lean_object* v_pre_2723_, lean_object* v_post_2724_, lean_object* v_usedLetOnly_2725_, lean_object* v_skipConstInApp_2726_, lean_object* v_skipInstances_2727_, lean_object* v_x_2728_, lean_object* v_x_2729_, lean_object* v___y_2730_, lean_object* v___f_2731_, lean_object* v_toBind_2732_, lean_object* v_e_2733_, lean_object* v_a_2734_){
_start:
{
uint8_t v_usedLetOnly_boxed_2735_; uint8_t v_skipConstInApp_boxed_2736_; uint8_t v_skipInstances_boxed_2737_; lean_object* v_res_2738_; 
v_usedLetOnly_boxed_2735_ = lean_unbox(v_usedLetOnly_2725_);
v_skipConstInApp_boxed_2736_ = lean_unbox(v_skipConstInApp_2726_);
v_skipInstances_boxed_2737_ = lean_unbox(v_skipInstances_2727_);
v_res_2738_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11(v_toApplicative_2719_, v_inst_2720_, v_inst_2721_, v_inst_2722_, v_pre_2723_, v_post_2724_, v_usedLetOnly_boxed_2735_, v_skipConstInApp_boxed_2736_, v_skipInstances_boxed_2737_, v_x_2728_, v_x_2729_, v___y_2730_, v___f_2731_, v_toBind_2732_, v_e_2733_, v_a_2734_);
lean_dec(v___y_2730_);
return v_res_2738_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12(lean_object* v_toApplicative_2739_, lean_object* v_inst_2740_, lean_object* v_inst_2741_, lean_object* v_inst_2742_, lean_object* v_pre_2743_, lean_object* v_post_2744_, uint8_t v_usedLetOnly_2745_, uint8_t v_skipConstInApp_2746_, uint8_t v_skipInstances_2747_, lean_object* v_x_2748_, lean_object* v_x_2749_, lean_object* v___f_2750_, lean_object* v_toBind_2751_, lean_object* v_e_2752_, lean_object* v_____r_2753_, lean_object* v___y_2754_){
_start:
{
lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___f_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; 
v___x_2755_ = lean_box(v_usedLetOnly_2745_);
v___x_2756_ = lean_box(v_skipConstInApp_2746_);
v___x_2757_ = lean_box(v_skipInstances_2747_);
lean_inc_ref(v_e_2752_);
lean_inc(v_toBind_2751_);
lean_inc(v___y_2754_);
lean_inc(v_pre_2743_);
v___f_2758_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___boxed), 16, 15);
lean_closure_set(v___f_2758_, 0, v_toApplicative_2739_);
lean_closure_set(v___f_2758_, 1, v_inst_2740_);
lean_closure_set(v___f_2758_, 2, v_inst_2741_);
lean_closure_set(v___f_2758_, 3, v_inst_2742_);
lean_closure_set(v___f_2758_, 4, v_pre_2743_);
lean_closure_set(v___f_2758_, 5, v_post_2744_);
lean_closure_set(v___f_2758_, 6, v___x_2755_);
lean_closure_set(v___f_2758_, 7, v___x_2756_);
lean_closure_set(v___f_2758_, 8, v___x_2757_);
lean_closure_set(v___f_2758_, 9, v_x_2748_);
lean_closure_set(v___f_2758_, 10, v_x_2749_);
lean_closure_set(v___f_2758_, 11, v___y_2754_);
lean_closure_set(v___f_2758_, 12, v___f_2750_);
lean_closure_set(v___f_2758_, 13, v_toBind_2751_);
lean_closure_set(v___f_2758_, 14, v_e_2752_);
v___x_2759_ = lean_apply_1(v_pre_2743_, v_e_2752_);
v___x_2760_ = lean_apply_4(v_toBind_2751_, lean_box(0), lean_box(0), v___x_2759_, v___f_2758_);
return v___x_2760_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12___boxed(lean_object* v_toApplicative_2761_, lean_object* v_inst_2762_, lean_object* v_inst_2763_, lean_object* v_inst_2764_, lean_object* v_pre_2765_, lean_object* v_post_2766_, lean_object* v_usedLetOnly_2767_, lean_object* v_skipConstInApp_2768_, lean_object* v_skipInstances_2769_, lean_object* v_x_2770_, lean_object* v_x_2771_, lean_object* v___f_2772_, lean_object* v_toBind_2773_, lean_object* v_e_2774_, lean_object* v_____r_2775_, lean_object* v___y_2776_){
_start:
{
uint8_t v_usedLetOnly_boxed_2777_; uint8_t v_skipConstInApp_boxed_2778_; uint8_t v_skipInstances_boxed_2779_; lean_object* v_res_2780_; 
v_usedLetOnly_boxed_2777_ = lean_unbox(v_usedLetOnly_2767_);
v_skipConstInApp_boxed_2778_ = lean_unbox(v_skipConstInApp_2768_);
v_skipInstances_boxed_2779_ = lean_unbox(v_skipInstances_2769_);
v_res_2780_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12(v_toApplicative_2761_, v_inst_2762_, v_inst_2763_, v_inst_2764_, v_pre_2765_, v_post_2766_, v_usedLetOnly_boxed_2777_, v_skipConstInApp_boxed_2778_, v_skipInstances_boxed_2779_, v_x_2770_, v_x_2771_, v___f_2772_, v_toBind_2773_, v_e_2774_, v_____r_2775_, v___y_2776_);
lean_dec(v___y_2776_);
return v_res_2780_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(lean_object* v_inst_2781_, lean_object* v_inst_2782_, lean_object* v_inst_2783_, lean_object* v_pre_2784_, lean_object* v_post_2785_, uint8_t v_usedLetOnly_2786_, uint8_t v_skipConstInApp_2787_, uint8_t v_skipInstances_2788_, lean_object* v_x_2789_, lean_object* v_x_2790_, lean_object* v_e_2791_, lean_object* v_a_2792_){
_start:
{
lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___f_2797_; lean_object* v___f_2798_; lean_object* v___x_2799_; lean_object* v_toApplicative_2800_; lean_object* v_toBind_2801_; lean_object* v___f_2802_; lean_object* v___f_2803_; lean_object* v___f_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___f_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___f_2812_; lean_object* v___f_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; 
v___x_2793_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0));
v___x_2794_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1));
lean_inc_ref_n(v_inst_2781_, 3);
v___x_2795_ = l_Lean_MonadCacheT_instMonad___redArg(v_x_2789_, v___x_2793_, v___x_2794_, v_inst_2781_);
v___x_2796_ = l_Lean_MonadCacheT_instMonadControl___redArg(v_x_2789_, v___x_2793_, v___x_2794_);
lean_inc_ref_n(v_inst_2783_, 3);
lean_inc_ref(v___x_2796_);
v___f_2797_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_2797_, 0, v___x_2796_);
lean_closure_set(v___f_2797_, 1, v_inst_2783_);
v___f_2798_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_2798_, 0, v___x_2796_);
lean_closure_set(v___f_2798_, 1, v_inst_2783_);
v___x_2799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2799_, 0, v___f_2797_);
lean_ctor_set(v___x_2799_, 1, v___f_2798_);
v_toApplicative_2800_ = lean_ctor_get(v_inst_2781_, 0);
lean_inc_ref_n(v_toApplicative_2800_, 6);
v_toBind_2801_ = lean_ctor_get(v_inst_2781_, 1);
lean_inc_n(v_toBind_2801_, 6);
v___f_2802_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2802_, 0, v_toApplicative_2800_);
lean_inc_n(v_x_2790_, 3);
lean_inc_n(v_a_2792_, 3);
lean_inc_ref_n(v_e_2791_, 2);
v___f_2803_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_2803_, 0, v_toApplicative_2800_);
lean_closure_set(v___f_2803_, 1, v___x_2793_);
lean_closure_set(v___f_2803_, 2, v___x_2794_);
lean_closure_set(v___f_2803_, 3, v_e_2791_);
lean_closure_set(v___f_2803_, 4, v_a_2792_);
lean_closure_set(v___f_2803_, 5, v_x_2790_);
lean_closure_set(v___f_2803_, 6, v_toBind_2801_);
v___f_2804_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__3___boxed), 5, 4);
lean_closure_set(v___f_2804_, 0, v_toApplicative_2800_);
lean_closure_set(v___f_2804_, 1, v___x_2793_);
lean_closure_set(v___f_2804_, 2, v___x_2794_);
lean_closure_set(v___f_2804_, 3, v_e_2791_);
v___x_2805_ = lean_box(v_skipInstances_2788_);
v___x_2806_ = lean_box(v_usedLetOnly_2786_);
v___x_2807_ = lean_box(v_skipConstInApp_2787_);
lean_inc_ref(v___x_2795_);
lean_inc(v_post_2785_);
lean_inc(v_pre_2784_);
lean_inc_n(v_inst_2782_, 2);
v___f_2808_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__9___boxed), 17, 14);
lean_closure_set(v___f_2808_, 0, v___x_2805_);
lean_closure_set(v___f_2808_, 1, v_inst_2781_);
lean_closure_set(v___f_2808_, 2, v_inst_2782_);
lean_closure_set(v___f_2808_, 3, v_inst_2783_);
lean_closure_set(v___f_2808_, 4, v_pre_2784_);
lean_closure_set(v___f_2808_, 5, v_post_2785_);
lean_closure_set(v___f_2808_, 6, v___x_2806_);
lean_closure_set(v___f_2808_, 7, v___x_2807_);
lean_closure_set(v___f_2808_, 8, v_x_2789_);
lean_closure_set(v___f_2808_, 9, v_x_2790_);
lean_closure_set(v___f_2808_, 10, v___x_2795_);
lean_closure_set(v___f_2808_, 11, v_toBind_2801_);
lean_closure_set(v___f_2808_, 12, v_toApplicative_2800_);
lean_closure_set(v___f_2808_, 13, v___f_2802_);
v___x_2809_ = lean_box(v_usedLetOnly_2786_);
v___x_2810_ = lean_box(v_skipConstInApp_2787_);
v___x_2811_ = lean_box(v_skipInstances_2788_);
v___f_2812_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12___boxed), 16, 14);
lean_closure_set(v___f_2812_, 0, v_toApplicative_2800_);
lean_closure_set(v___f_2812_, 1, v_inst_2781_);
lean_closure_set(v___f_2812_, 2, v_inst_2782_);
lean_closure_set(v___f_2812_, 3, v_inst_2783_);
lean_closure_set(v___f_2812_, 4, v_pre_2784_);
lean_closure_set(v___f_2812_, 5, v_post_2785_);
lean_closure_set(v___f_2812_, 6, v___x_2809_);
lean_closure_set(v___f_2812_, 7, v___x_2810_);
lean_closure_set(v___f_2812_, 8, v___x_2811_);
lean_closure_set(v___f_2812_, 9, v_x_2789_);
lean_closure_set(v___f_2812_, 10, v_x_2790_);
lean_closure_set(v___f_2812_, 11, v___f_2808_);
lean_closure_set(v___f_2812_, 12, v_toBind_2801_);
lean_closure_set(v___f_2812_, 13, v_e_2791_);
v___f_2813_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14___boxed), 13, 12);
lean_closure_set(v___f_2813_, 0, v_inst_2782_);
lean_closure_set(v___f_2813_, 1, v_x_2789_);
lean_closure_set(v___f_2813_, 2, v___x_2793_);
lean_closure_set(v___f_2813_, 3, v___x_2794_);
lean_closure_set(v___f_2813_, 4, v_inst_2781_);
lean_closure_set(v___f_2813_, 5, v___f_2812_);
lean_closure_set(v___f_2813_, 6, v___x_2799_);
lean_closure_set(v___f_2813_, 7, v___x_2795_);
lean_closure_set(v___f_2813_, 8, v_a_2792_);
lean_closure_set(v___f_2813_, 9, v_toBind_2801_);
lean_closure_set(v___f_2813_, 10, v___f_2803_);
lean_closure_set(v___f_2813_, 11, v_toApplicative_2800_);
v___x_2814_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2814_, 0, lean_box(0));
lean_closure_set(v___x_2814_, 1, lean_box(0));
lean_closure_set(v___x_2814_, 2, v_a_2792_);
v___x_2815_ = lean_apply_2(v_x_2790_, lean_box(0), v___x_2814_);
v___x_2816_ = lean_apply_4(v_toBind_2801_, lean_box(0), lean_box(0), v___x_2815_, v___f_2804_);
v___x_2817_ = lean_apply_4(v_toBind_2801_, lean_box(0), lean_box(0), v___x_2816_, v___f_2813_);
return v___x_2817_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___lam__0(lean_object* v_toApplicative_2818_, lean_object* v_inst_2819_, lean_object* v_inst_2820_, lean_object* v_inst_2821_, lean_object* v_pre_2822_, lean_object* v_post_2823_, uint8_t v_usedLetOnly_2824_, uint8_t v_skipConstInApp_2825_, uint8_t v_skipInstances_2826_, lean_object* v_x_2827_, lean_object* v_x_2828_, lean_object* v_a_2829_, lean_object* v_e_2830_, lean_object* v_a_2831_){
_start:
{
lean_object* v___y_2833_; 
switch(lean_obj_tag(v_a_2831_))
{
case 0:
{
lean_object* v_e_2836_; lean_object* v_toPure_2837_; lean_object* v___x_2838_; 
lean_dec_ref(v_e_2830_);
lean_dec(v_x_2828_);
lean_dec(v_post_2823_);
lean_dec(v_pre_2822_);
lean_dec_ref(v_inst_2821_);
lean_dec(v_inst_2820_);
lean_dec_ref(v_inst_2819_);
v_e_2836_ = lean_ctor_get(v_a_2831_, 0);
lean_inc_ref(v_e_2836_);
lean_dec_ref(v_a_2831_);
v_toPure_2837_ = lean_ctor_get(v_toApplicative_2818_, 1);
lean_inc(v_toPure_2837_);
lean_dec_ref(v_toApplicative_2818_);
v___x_2838_ = lean_apply_2(v_toPure_2837_, lean_box(0), v_e_2836_);
return v___x_2838_;
}
case 1:
{
lean_object* v_e_2839_; lean_object* v___x_2840_; 
lean_dec_ref(v_e_2830_);
lean_dec_ref(v_toApplicative_2818_);
v_e_2839_ = lean_ctor_get(v_a_2831_, 0);
lean_inc_ref(v_e_2839_);
lean_dec_ref(v_a_2831_);
v___x_2840_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2819_, v_inst_2820_, v_inst_2821_, v_pre_2822_, v_post_2823_, v_usedLetOnly_2824_, v_skipConstInApp_2825_, v_skipInstances_2826_, v_x_2827_, v_x_2828_, v_e_2839_, v_a_2829_);
return v___x_2840_;
}
default: 
{
lean_object* v_e_x3f_2841_; 
lean_dec(v_x_2828_);
lean_dec(v_post_2823_);
lean_dec(v_pre_2822_);
lean_dec_ref(v_inst_2821_);
lean_dec(v_inst_2820_);
lean_dec_ref(v_inst_2819_);
v_e_x3f_2841_ = lean_ctor_get(v_a_2831_, 0);
lean_inc(v_e_x3f_2841_);
lean_dec_ref(v_a_2831_);
if (lean_obj_tag(v_e_x3f_2841_) == 0)
{
v___y_2833_ = v_e_2830_;
goto v___jp_2832_;
}
else
{
lean_object* v_val_2842_; 
lean_dec_ref(v_e_2830_);
v_val_2842_ = lean_ctor_get(v_e_x3f_2841_, 0);
lean_inc(v_val_2842_);
lean_dec_ref(v_e_x3f_2841_);
v___y_2833_ = v_val_2842_;
goto v___jp_2832_;
}
}
}
v___jp_2832_:
{
lean_object* v_toPure_2834_; lean_object* v___x_2835_; 
v_toPure_2834_ = lean_ctor_get(v_toApplicative_2818_, 1);
lean_inc(v_toPure_2834_);
lean_dec_ref(v_toApplicative_2818_);
v___x_2835_ = lean_apply_2(v_toPure_2834_, lean_box(0), v___y_2833_);
return v___x_2835_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___lam__0___boxed(lean_object* v_toApplicative_2843_, lean_object* v_inst_2844_, lean_object* v_inst_2845_, lean_object* v_inst_2846_, lean_object* v_pre_2847_, lean_object* v_post_2848_, lean_object* v_usedLetOnly_2849_, lean_object* v_skipConstInApp_2850_, lean_object* v_skipInstances_2851_, lean_object* v_x_2852_, lean_object* v_x_2853_, lean_object* v_a_2854_, lean_object* v_e_2855_, lean_object* v_a_2856_){
_start:
{
uint8_t v_usedLetOnly_boxed_2857_; uint8_t v_skipConstInApp_boxed_2858_; uint8_t v_skipInstances_boxed_2859_; lean_object* v_res_2860_; 
v_usedLetOnly_boxed_2857_ = lean_unbox(v_usedLetOnly_2849_);
v_skipConstInApp_boxed_2858_ = lean_unbox(v_skipConstInApp_2850_);
v_skipInstances_boxed_2859_ = lean_unbox(v_skipInstances_2851_);
v_res_2860_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___lam__0(v_toApplicative_2843_, v_inst_2844_, v_inst_2845_, v_inst_2846_, v_pre_2847_, v_post_2848_, v_usedLetOnly_boxed_2857_, v_skipConstInApp_boxed_2858_, v_skipInstances_boxed_2859_, v_x_2852_, v_x_2853_, v_a_2854_, v_e_2855_, v_a_2856_);
lean_dec(v_a_2854_);
return v_res_2860_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(lean_object* v_inst_2861_, lean_object* v_inst_2862_, lean_object* v_inst_2863_, lean_object* v_pre_2864_, lean_object* v_post_2865_, uint8_t v_usedLetOnly_2866_, uint8_t v_skipConstInApp_2867_, uint8_t v_skipInstances_2868_, lean_object* v_x_2869_, lean_object* v_x_2870_, lean_object* v_e_2871_, lean_object* v_a_2872_){
_start:
{
lean_object* v_toApplicative_2873_; lean_object* v_toBind_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___f_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; 
v_toApplicative_2873_ = lean_ctor_get(v_inst_2861_, 0);
lean_inc_ref(v_toApplicative_2873_);
v_toBind_2874_ = lean_ctor_get(v_inst_2861_, 1);
lean_inc(v_toBind_2874_);
v___x_2875_ = lean_box(v_usedLetOnly_2866_);
v___x_2876_ = lean_box(v_skipConstInApp_2867_);
v___x_2877_ = lean_box(v_skipInstances_2868_);
lean_inc_ref(v_e_2871_);
lean_inc(v_a_2872_);
lean_inc(v_post_2865_);
v___f_2878_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___lam__0___boxed), 14, 13);
lean_closure_set(v___f_2878_, 0, v_toApplicative_2873_);
lean_closure_set(v___f_2878_, 1, v_inst_2861_);
lean_closure_set(v___f_2878_, 2, v_inst_2862_);
lean_closure_set(v___f_2878_, 3, v_inst_2863_);
lean_closure_set(v___f_2878_, 4, v_pre_2864_);
lean_closure_set(v___f_2878_, 5, v_post_2865_);
lean_closure_set(v___f_2878_, 6, v___x_2875_);
lean_closure_set(v___f_2878_, 7, v___x_2876_);
lean_closure_set(v___f_2878_, 8, v___x_2877_);
lean_closure_set(v___f_2878_, 9, v_x_2869_);
lean_closure_set(v___f_2878_, 10, v_x_2870_);
lean_closure_set(v___f_2878_, 11, v_a_2872_);
lean_closure_set(v___f_2878_, 12, v_e_2871_);
v___x_2879_ = lean_apply_1(v_post_2865_, v_e_2871_);
v___x_2880_ = lean_apply_4(v_toBind_2874_, lean_box(0), lean_box(0), v___x_2879_, v___f_2878_);
return v___x_2880_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3(lean_object* v_inst_2881_, lean_object* v_inst_2882_, lean_object* v_inst_2883_, lean_object* v_pre_2884_, lean_object* v_post_2885_, uint8_t v_usedLetOnly_2886_, uint8_t v_skipConstInApp_2887_, uint8_t v_skipInstances_2888_, lean_object* v_x_2889_, lean_object* v_x_2890_, lean_object* v_a_2891_, lean_object* v_a_2892_){
_start:
{
lean_object* v___x_2893_; 
v___x_2893_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2881_, v_inst_2882_, v_inst_2883_, v_pre_2884_, v_post_2885_, v_usedLetOnly_2886_, v_skipConstInApp_2887_, v_skipInstances_2888_, v_x_2889_, v_x_2890_, v_a_2892_, v_a_2891_);
return v___x_2893_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___boxed(lean_object* v_inst_2894_, lean_object* v_inst_2895_, lean_object* v_inst_2896_, lean_object* v_pre_2897_, lean_object* v_post_2898_, lean_object* v_usedLetOnly_2899_, lean_object* v_skipConstInApp_2900_, lean_object* v_skipInstances_2901_, lean_object* v_x_2902_, lean_object* v_x_2903_, lean_object* v_e_2904_, lean_object* v_a_2905_){
_start:
{
uint8_t v_usedLetOnly_boxed_2906_; uint8_t v_skipConstInApp_boxed_2907_; uint8_t v_skipInstances_boxed_2908_; lean_object* v_res_2909_; 
v_usedLetOnly_boxed_2906_ = lean_unbox(v_usedLetOnly_2899_);
v_skipConstInApp_boxed_2907_ = lean_unbox(v_skipConstInApp_2900_);
v_skipInstances_boxed_2908_ = lean_unbox(v_skipInstances_2901_);
v_res_2909_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2894_, v_inst_2895_, v_inst_2896_, v_pre_2897_, v_post_2898_, v_usedLetOnly_boxed_2906_, v_skipConstInApp_boxed_2907_, v_skipInstances_boxed_2908_, v_x_2902_, v_x_2903_, v_e_2904_, v_a_2905_);
lean_dec(v_a_2905_);
return v_res_2909_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___boxed(lean_object* v_inst_2910_, lean_object* v_inst_2911_, lean_object* v_inst_2912_, lean_object* v_pre_2913_, lean_object* v_post_2914_, lean_object* v_usedLetOnly_2915_, lean_object* v_skipConstInApp_2916_, lean_object* v_skipInstances_2917_, lean_object* v_x_2918_, lean_object* v_x_2919_, lean_object* v_fvars_2920_, lean_object* v_e_2921_, lean_object* v_a_2922_){
_start:
{
uint8_t v_usedLetOnly_boxed_2923_; uint8_t v_skipConstInApp_boxed_2924_; uint8_t v_skipInstances_boxed_2925_; lean_object* v_res_2926_; 
v_usedLetOnly_boxed_2923_ = lean_unbox(v_usedLetOnly_2915_);
v_skipConstInApp_boxed_2924_ = lean_unbox(v_skipConstInApp_2916_);
v_skipInstances_boxed_2925_ = lean_unbox(v_skipInstances_2917_);
v_res_2926_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(v_inst_2910_, v_inst_2911_, v_inst_2912_, v_pre_2913_, v_post_2914_, v_usedLetOnly_boxed_2923_, v_skipConstInApp_boxed_2924_, v_skipInstances_boxed_2925_, v_x_2918_, v_x_2919_, v_fvars_2920_, v_e_2921_, v_a_2922_);
lean_dec(v_a_2922_);
return v_res_2926_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___boxed(lean_object* v_inst_2927_, lean_object* v_inst_2928_, lean_object* v_inst_2929_, lean_object* v_pre_2930_, lean_object* v_post_2931_, lean_object* v_usedLetOnly_2932_, lean_object* v_skipConstInApp_2933_, lean_object* v_skipInstances_2934_, lean_object* v_x_2935_, lean_object* v_x_2936_, lean_object* v_fvars_2937_, lean_object* v_e_2938_, lean_object* v_a_2939_){
_start:
{
uint8_t v_usedLetOnly_boxed_2940_; uint8_t v_skipConstInApp_boxed_2941_; uint8_t v_skipInstances_boxed_2942_; lean_object* v_res_2943_; 
v_usedLetOnly_boxed_2940_ = lean_unbox(v_usedLetOnly_2932_);
v_skipConstInApp_boxed_2941_ = lean_unbox(v_skipConstInApp_2933_);
v_skipInstances_boxed_2942_ = lean_unbox(v_skipInstances_2934_);
v_res_2943_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(v_inst_2927_, v_inst_2928_, v_inst_2929_, v_pre_2930_, v_post_2931_, v_usedLetOnly_boxed_2940_, v_skipConstInApp_boxed_2941_, v_skipInstances_boxed_2942_, v_x_2935_, v_x_2936_, v_fvars_2937_, v_e_2938_, v_a_2939_);
lean_dec(v_a_2939_);
return v_res_2943_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___boxed(lean_object* v_inst_2944_, lean_object* v_inst_2945_, lean_object* v_inst_2946_, lean_object* v_pre_2947_, lean_object* v_post_2948_, lean_object* v_usedLetOnly_2949_, lean_object* v_skipConstInApp_2950_, lean_object* v_skipInstances_2951_, lean_object* v_x_2952_, lean_object* v_x_2953_, lean_object* v_fvars_2954_, lean_object* v_e_2955_, lean_object* v_a_2956_){
_start:
{
uint8_t v_usedLetOnly_boxed_2957_; uint8_t v_skipConstInApp_boxed_2958_; uint8_t v_skipInstances_boxed_2959_; lean_object* v_res_2960_; 
v_usedLetOnly_boxed_2957_ = lean_unbox(v_usedLetOnly_2949_);
v_skipConstInApp_boxed_2958_ = lean_unbox(v_skipConstInApp_2950_);
v_skipInstances_boxed_2959_ = lean_unbox(v_skipInstances_2951_);
v_res_2960_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(v_inst_2944_, v_inst_2945_, v_inst_2946_, v_pre_2947_, v_post_2948_, v_usedLetOnly_boxed_2957_, v_skipConstInApp_boxed_2958_, v_skipInstances_boxed_2959_, v_x_2952_, v_x_2953_, v_fvars_2954_, v_e_2955_, v_a_2956_);
lean_dec(v_a_2956_);
return v_res_2960_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit(lean_object* v_m_2961_, lean_object* v_inst_2962_, lean_object* v_inst_2963_, lean_object* v_inst_2964_, lean_object* v_pre_2965_, lean_object* v_post_2966_, uint8_t v_usedLetOnly_2967_, uint8_t v_skipConstInApp_2968_, uint8_t v_skipInstances_2969_, lean_object* v_x_2970_, lean_object* v_x_2971_, lean_object* v_e_2972_, lean_object* v_a_2973_){
_start:
{
lean_object* v___x_2974_; 
v___x_2974_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2962_, v_inst_2963_, v_inst_2964_, v_pre_2965_, v_post_2966_, v_usedLetOnly_2967_, v_skipConstInApp_2968_, v_skipInstances_2969_, v_x_2970_, v_x_2971_, v_e_2972_, v_a_2973_);
return v___x_2974_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___boxed(lean_object* v_m_2975_, lean_object* v_inst_2976_, lean_object* v_inst_2977_, lean_object* v_inst_2978_, lean_object* v_pre_2979_, lean_object* v_post_2980_, lean_object* v_usedLetOnly_2981_, lean_object* v_skipConstInApp_2982_, lean_object* v_skipInstances_2983_, lean_object* v_x_2984_, lean_object* v_x_2985_, lean_object* v_e_2986_, lean_object* v_a_2987_){
_start:
{
uint8_t v_usedLetOnly_boxed_2988_; uint8_t v_skipConstInApp_boxed_2989_; uint8_t v_skipInstances_boxed_2990_; lean_object* v_res_2991_; 
v_usedLetOnly_boxed_2988_ = lean_unbox(v_usedLetOnly_2981_);
v_skipConstInApp_boxed_2989_ = lean_unbox(v_skipConstInApp_2982_);
v_skipInstances_boxed_2990_ = lean_unbox(v_skipInstances_2983_);
v_res_2991_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit(v_m_2975_, v_inst_2976_, v_inst_2977_, v_inst_2978_, v_pre_2979_, v_post_2980_, v_usedLetOnly_boxed_2988_, v_skipConstInApp_boxed_2989_, v_skipInstances_boxed_2990_, v_x_2984_, v_x_2985_, v_e_2986_, v_a_2987_);
lean_dec(v_a_2987_);
return v_res_2991_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet(lean_object* v_m_2992_, lean_object* v_inst_2993_, lean_object* v_inst_2994_, lean_object* v_inst_2995_, lean_object* v_pre_2996_, lean_object* v_post_2997_, uint8_t v_usedLetOnly_2998_, uint8_t v_skipConstInApp_2999_, uint8_t v_skipInstances_3000_, lean_object* v_x_3001_, lean_object* v_x_3002_, lean_object* v_fvars_3003_, lean_object* v_e_3004_, lean_object* v_a_3005_){
_start:
{
lean_object* v___x_3006_; 
v___x_3006_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(v_inst_2993_, v_inst_2994_, v_inst_2995_, v_pre_2996_, v_post_2997_, v_usedLetOnly_2998_, v_skipConstInApp_2999_, v_skipInstances_3000_, v_x_3001_, v_x_3002_, v_fvars_3003_, v_e_3004_, v_a_3005_);
return v___x_3006_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___boxed(lean_object* v_m_3007_, lean_object* v_inst_3008_, lean_object* v_inst_3009_, lean_object* v_inst_3010_, lean_object* v_pre_3011_, lean_object* v_post_3012_, lean_object* v_usedLetOnly_3013_, lean_object* v_skipConstInApp_3014_, lean_object* v_skipInstances_3015_, lean_object* v_x_3016_, lean_object* v_x_3017_, lean_object* v_fvars_3018_, lean_object* v_e_3019_, lean_object* v_a_3020_){
_start:
{
uint8_t v_usedLetOnly_boxed_3021_; uint8_t v_skipConstInApp_boxed_3022_; uint8_t v_skipInstances_boxed_3023_; lean_object* v_res_3024_; 
v_usedLetOnly_boxed_3021_ = lean_unbox(v_usedLetOnly_3013_);
v_skipConstInApp_boxed_3022_ = lean_unbox(v_skipConstInApp_3014_);
v_skipInstances_boxed_3023_ = lean_unbox(v_skipInstances_3015_);
v_res_3024_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet(v_m_3007_, v_inst_3008_, v_inst_3009_, v_inst_3010_, v_pre_3011_, v_post_3012_, v_usedLetOnly_boxed_3021_, v_skipConstInApp_boxed_3022_, v_skipInstances_boxed_3023_, v_x_3016_, v_x_3017_, v_fvars_3018_, v_e_3019_, v_a_3020_);
lean_dec(v_a_3020_);
return v_res_3024_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost(lean_object* v_m_3025_, lean_object* v_inst_3026_, lean_object* v_inst_3027_, lean_object* v_inst_3028_, lean_object* v_pre_3029_, lean_object* v_post_3030_, uint8_t v_usedLetOnly_3031_, uint8_t v_skipConstInApp_3032_, uint8_t v_skipInstances_3033_, lean_object* v_x_3034_, lean_object* v_x_3035_, lean_object* v_e_3036_, lean_object* v_a_3037_){
_start:
{
lean_object* v___x_3038_; 
v___x_3038_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_3026_, v_inst_3027_, v_inst_3028_, v_pre_3029_, v_post_3030_, v_usedLetOnly_3031_, v_skipConstInApp_3032_, v_skipInstances_3033_, v_x_3034_, v_x_3035_, v_e_3036_, v_a_3037_);
return v___x_3038_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___boxed(lean_object* v_m_3039_, lean_object* v_inst_3040_, lean_object* v_inst_3041_, lean_object* v_inst_3042_, lean_object* v_pre_3043_, lean_object* v_post_3044_, lean_object* v_usedLetOnly_3045_, lean_object* v_skipConstInApp_3046_, lean_object* v_skipInstances_3047_, lean_object* v_x_3048_, lean_object* v_x_3049_, lean_object* v_e_3050_, lean_object* v_a_3051_){
_start:
{
uint8_t v_usedLetOnly_boxed_3052_; uint8_t v_skipConstInApp_boxed_3053_; uint8_t v_skipInstances_boxed_3054_; lean_object* v_res_3055_; 
v_usedLetOnly_boxed_3052_ = lean_unbox(v_usedLetOnly_3045_);
v_skipConstInApp_boxed_3053_ = lean_unbox(v_skipConstInApp_3046_);
v_skipInstances_boxed_3054_ = lean_unbox(v_skipInstances_3047_);
v_res_3055_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost(v_m_3039_, v_inst_3040_, v_inst_3041_, v_inst_3042_, v_pre_3043_, v_post_3044_, v_usedLetOnly_boxed_3052_, v_skipConstInApp_boxed_3053_, v_skipInstances_boxed_3054_, v_x_3048_, v_x_3049_, v_e_3050_, v_a_3051_);
lean_dec(v_a_3051_);
return v_res_3055_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda(lean_object* v_m_3056_, lean_object* v_inst_3057_, lean_object* v_inst_3058_, lean_object* v_inst_3059_, lean_object* v_pre_3060_, lean_object* v_post_3061_, uint8_t v_usedLetOnly_3062_, uint8_t v_skipConstInApp_3063_, uint8_t v_skipInstances_3064_, lean_object* v_x_3065_, lean_object* v_x_3066_, lean_object* v_fvars_3067_, lean_object* v_e_3068_, lean_object* v_a_3069_){
_start:
{
lean_object* v___x_3070_; 
v___x_3070_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(v_inst_3057_, v_inst_3058_, v_inst_3059_, v_pre_3060_, v_post_3061_, v_usedLetOnly_3062_, v_skipConstInApp_3063_, v_skipInstances_3064_, v_x_3065_, v_x_3066_, v_fvars_3067_, v_e_3068_, v_a_3069_);
return v___x_3070_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___boxed(lean_object* v_m_3071_, lean_object* v_inst_3072_, lean_object* v_inst_3073_, lean_object* v_inst_3074_, lean_object* v_pre_3075_, lean_object* v_post_3076_, lean_object* v_usedLetOnly_3077_, lean_object* v_skipConstInApp_3078_, lean_object* v_skipInstances_3079_, lean_object* v_x_3080_, lean_object* v_x_3081_, lean_object* v_fvars_3082_, lean_object* v_e_3083_, lean_object* v_a_3084_){
_start:
{
uint8_t v_usedLetOnly_boxed_3085_; uint8_t v_skipConstInApp_boxed_3086_; uint8_t v_skipInstances_boxed_3087_; lean_object* v_res_3088_; 
v_usedLetOnly_boxed_3085_ = lean_unbox(v_usedLetOnly_3077_);
v_skipConstInApp_boxed_3086_ = lean_unbox(v_skipConstInApp_3078_);
v_skipInstances_boxed_3087_ = lean_unbox(v_skipInstances_3079_);
v_res_3088_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda(v_m_3071_, v_inst_3072_, v_inst_3073_, v_inst_3074_, v_pre_3075_, v_post_3076_, v_usedLetOnly_boxed_3085_, v_skipConstInApp_boxed_3086_, v_skipInstances_boxed_3087_, v_x_3080_, v_x_3081_, v_fvars_3082_, v_e_3083_, v_a_3084_);
lean_dec(v_a_3084_);
return v_res_3088_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall(lean_object* v_m_3089_, lean_object* v_inst_3090_, lean_object* v_inst_3091_, lean_object* v_inst_3092_, lean_object* v_pre_3093_, lean_object* v_post_3094_, uint8_t v_usedLetOnly_3095_, uint8_t v_skipConstInApp_3096_, uint8_t v_skipInstances_3097_, lean_object* v_x_3098_, lean_object* v_x_3099_, lean_object* v_fvars_3100_, lean_object* v_e_3101_, lean_object* v_a_3102_){
_start:
{
lean_object* v___x_3103_; 
v___x_3103_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(v_inst_3090_, v_inst_3091_, v_inst_3092_, v_pre_3093_, v_post_3094_, v_usedLetOnly_3095_, v_skipConstInApp_3096_, v_skipInstances_3097_, v_x_3098_, v_x_3099_, v_fvars_3100_, v_e_3101_, v_a_3102_);
return v___x_3103_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___boxed(lean_object* v_m_3104_, lean_object* v_inst_3105_, lean_object* v_inst_3106_, lean_object* v_inst_3107_, lean_object* v_pre_3108_, lean_object* v_post_3109_, lean_object* v_usedLetOnly_3110_, lean_object* v_skipConstInApp_3111_, lean_object* v_skipInstances_3112_, lean_object* v_x_3113_, lean_object* v_x_3114_, lean_object* v_fvars_3115_, lean_object* v_e_3116_, lean_object* v_a_3117_){
_start:
{
uint8_t v_usedLetOnly_boxed_3118_; uint8_t v_skipConstInApp_boxed_3119_; uint8_t v_skipInstances_boxed_3120_; lean_object* v_res_3121_; 
v_usedLetOnly_boxed_3118_ = lean_unbox(v_usedLetOnly_3110_);
v_skipConstInApp_boxed_3119_ = lean_unbox(v_skipConstInApp_3111_);
v_skipInstances_boxed_3120_ = lean_unbox(v_skipInstances_3112_);
v_res_3121_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall(v_m_3104_, v_inst_3105_, v_inst_3106_, v_inst_3107_, v_pre_3108_, v_post_3109_, v_usedLetOnly_boxed_3118_, v_skipConstInApp_boxed_3119_, v_skipInstances_boxed_3120_, v_x_3113_, v_x_3114_, v_fvars_3115_, v_e_3116_, v_a_3117_);
lean_dec(v_a_3117_);
return v_res_3121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__0(lean_object* v_x_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_){
_start:
{
lean_object* v___x_3128_; lean_object* v___x_3129_; 
v___x_3128_ = lean_apply_1(v_x_3122_, lean_box(0));
v___x_3129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3129_, 0, v___x_3128_);
return v___x_3129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__0___boxed(lean_object* v_x_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_){
_start:
{
lean_object* v_res_3136_; 
v_res_3136_ = l_Lean_Meta_transformWithCache___redArg___lam__0(v_x_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_);
lean_dec(v___y_3134_);
lean_dec_ref(v___y_3133_);
lean_dec(v___y_3132_);
lean_dec_ref(v___y_3131_);
return v_res_3136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__1(lean_object* v_inst_3137_, lean_object* v_00_u03b1_3138_, lean_object* v_x_3139_){
_start:
{
lean_object* v___f_3140_; lean_object* v___x_3141_; 
v___f_3140_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_3140_, 0, v_x_3139_);
v___x_3141_ = lean_apply_2(v_inst_3137_, lean_box(0), v___f_3140_);
return v___x_3141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__4(lean_object* v_toPure_3142_, lean_object* v_x_3143_, lean_object* v_toBind_3144_, lean_object* v_inst_3145_, lean_object* v_inst_3146_, lean_object* v_inst_3147_, lean_object* v_pre_3148_, lean_object* v_post_3149_, uint8_t v_usedLetOnly_3150_, uint8_t v_skipConstInApp_3151_, uint8_t v_skipInstances_3152_, lean_object* v_x_3153_, lean_object* v_input_3154_, lean_object* v_ref_3155_){
_start:
{
lean_object* v___f_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; 
lean_inc(v_toBind_3144_);
lean_inc(v_x_3143_);
lean_inc(v_ref_3155_);
v___f_3156_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__4), 5, 4);
lean_closure_set(v___f_3156_, 0, v_toPure_3142_);
lean_closure_set(v___f_3156_, 1, v_ref_3155_);
lean_closure_set(v___f_3156_, 2, v_x_3143_);
lean_closure_set(v___f_3156_, 3, v_toBind_3144_);
v___x_3157_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_3145_, v_inst_3146_, v_inst_3147_, v_pre_3148_, v_post_3149_, v_usedLetOnly_3150_, v_skipConstInApp_3151_, v_skipInstances_3152_, v_x_3153_, v_x_3143_, v_input_3154_, v_ref_3155_);
lean_dec(v_ref_3155_);
v___x_3158_ = lean_apply_4(v_toBind_3144_, lean_box(0), lean_box(0), v___x_3157_, v___f_3156_);
return v___x_3158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__4___boxed(lean_object* v_toPure_3159_, lean_object* v_x_3160_, lean_object* v_toBind_3161_, lean_object* v_inst_3162_, lean_object* v_inst_3163_, lean_object* v_inst_3164_, lean_object* v_pre_3165_, lean_object* v_post_3166_, lean_object* v_usedLetOnly_3167_, lean_object* v_skipConstInApp_3168_, lean_object* v_skipInstances_3169_, lean_object* v_x_3170_, lean_object* v_input_3171_, lean_object* v_ref_3172_){
_start:
{
uint8_t v_usedLetOnly_boxed_3173_; uint8_t v_skipConstInApp_boxed_3174_; uint8_t v_skipInstances_boxed_3175_; lean_object* v_res_3176_; 
v_usedLetOnly_boxed_3173_ = lean_unbox(v_usedLetOnly_3167_);
v_skipConstInApp_boxed_3174_ = lean_unbox(v_skipConstInApp_3168_);
v_skipInstances_boxed_3175_ = lean_unbox(v_skipInstances_3169_);
v_res_3176_ = l_Lean_Meta_transformWithCache___redArg___lam__4(v_toPure_3159_, v_x_3160_, v_toBind_3161_, v_inst_3162_, v_inst_3163_, v_inst_3164_, v_pre_3165_, v_post_3166_, v_usedLetOnly_boxed_3173_, v_skipConstInApp_boxed_3174_, v_skipInstances_boxed_3175_, v_x_3170_, v_input_3171_, v_ref_3172_);
return v_res_3176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg(lean_object* v_inst_3177_, lean_object* v_inst_3178_, lean_object* v_inst_3179_, lean_object* v_input_3180_, lean_object* v_cache_3181_, lean_object* v_pre_3182_, lean_object* v_post_3183_, uint8_t v_usedLetOnly_3184_, uint8_t v_skipConstInApp_3185_, uint8_t v_skipInstances_3186_){
_start:
{
lean_object* v_x_3187_; lean_object* v_toApplicative_3188_; lean_object* v_toBind_3189_; lean_object* v_toPure_3190_; lean_object* v_x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___f_3197_; lean_object* v___x_3198_; 
v_x_3187_ = lean_box(0);
v_toApplicative_3188_ = lean_ctor_get(v_inst_3177_, 0);
v_toBind_3189_ = lean_ctor_get(v_inst_3177_, 1);
lean_inc_n(v_toBind_3189_, 2);
v_toPure_3190_ = lean_ctor_get(v_toApplicative_3188_, 1);
lean_inc(v_toPure_3190_);
lean_inc_n(v_inst_3178_, 2);
v_x_3191_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__1), 3, 1);
lean_closure_set(v_x_3191_, 0, v_inst_3178_);
v___x_3192_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_3192_, 0, lean_box(0));
lean_closure_set(v___x_3192_, 1, lean_box(0));
lean_closure_set(v___x_3192_, 2, v_cache_3181_);
v___x_3193_ = l_Lean_Meta_transformWithCache___redArg___lam__1(v_inst_3178_, lean_box(0), v___x_3192_);
v___x_3194_ = lean_box(v_usedLetOnly_3184_);
v___x_3195_ = lean_box(v_skipConstInApp_3185_);
v___x_3196_ = lean_box(v_skipInstances_3186_);
v___f_3197_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__4___boxed), 14, 13);
lean_closure_set(v___f_3197_, 0, v_toPure_3190_);
lean_closure_set(v___f_3197_, 1, v_x_3191_);
lean_closure_set(v___f_3197_, 2, v_toBind_3189_);
lean_closure_set(v___f_3197_, 3, v_inst_3177_);
lean_closure_set(v___f_3197_, 4, v_inst_3178_);
lean_closure_set(v___f_3197_, 5, v_inst_3179_);
lean_closure_set(v___f_3197_, 6, v_pre_3182_);
lean_closure_set(v___f_3197_, 7, v_post_3183_);
lean_closure_set(v___f_3197_, 8, v___x_3194_);
lean_closure_set(v___f_3197_, 9, v___x_3195_);
lean_closure_set(v___f_3197_, 10, v___x_3196_);
lean_closure_set(v___f_3197_, 11, v_x_3187_);
lean_closure_set(v___f_3197_, 12, v_input_3180_);
v___x_3198_ = lean_apply_4(v_toBind_3189_, lean_box(0), lean_box(0), v___x_3193_, v___f_3197_);
return v___x_3198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___boxed(lean_object* v_inst_3199_, lean_object* v_inst_3200_, lean_object* v_inst_3201_, lean_object* v_input_3202_, lean_object* v_cache_3203_, lean_object* v_pre_3204_, lean_object* v_post_3205_, lean_object* v_usedLetOnly_3206_, lean_object* v_skipConstInApp_3207_, lean_object* v_skipInstances_3208_){
_start:
{
uint8_t v_usedLetOnly_boxed_3209_; uint8_t v_skipConstInApp_boxed_3210_; uint8_t v_skipInstances_boxed_3211_; lean_object* v_res_3212_; 
v_usedLetOnly_boxed_3209_ = lean_unbox(v_usedLetOnly_3206_);
v_skipConstInApp_boxed_3210_ = lean_unbox(v_skipConstInApp_3207_);
v_skipInstances_boxed_3211_ = lean_unbox(v_skipInstances_3208_);
v_res_3212_ = l_Lean_Meta_transformWithCache___redArg(v_inst_3199_, v_inst_3200_, v_inst_3201_, v_input_3202_, v_cache_3203_, v_pre_3204_, v_post_3205_, v_usedLetOnly_boxed_3209_, v_skipConstInApp_boxed_3210_, v_skipInstances_boxed_3211_);
return v_res_3212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache(lean_object* v_m_3213_, lean_object* v_inst_3214_, lean_object* v_inst_3215_, lean_object* v_inst_3216_, lean_object* v_input_3217_, lean_object* v_cache_3218_, lean_object* v_pre_3219_, lean_object* v_post_3220_, uint8_t v_usedLetOnly_3221_, uint8_t v_skipConstInApp_3222_, uint8_t v_skipInstances_3223_){
_start:
{
lean_object* v_x_3224_; lean_object* v_toApplicative_3225_; lean_object* v_toBind_3226_; lean_object* v_toPure_3227_; lean_object* v_x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___f_3234_; lean_object* v___x_3235_; 
v_x_3224_ = lean_box(0);
v_toApplicative_3225_ = lean_ctor_get(v_inst_3214_, 0);
v_toBind_3226_ = lean_ctor_get(v_inst_3214_, 1);
lean_inc_n(v_toBind_3226_, 2);
v_toPure_3227_ = lean_ctor_get(v_toApplicative_3225_, 1);
lean_inc(v_toPure_3227_);
lean_inc_n(v_inst_3215_, 2);
v_x_3228_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__1), 3, 1);
lean_closure_set(v_x_3228_, 0, v_inst_3215_);
v___x_3229_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_3229_, 0, lean_box(0));
lean_closure_set(v___x_3229_, 1, lean_box(0));
lean_closure_set(v___x_3229_, 2, v_cache_3218_);
v___x_3230_ = l_Lean_Meta_transformWithCache___redArg___lam__1(v_inst_3215_, lean_box(0), v___x_3229_);
v___x_3231_ = lean_box(v_usedLetOnly_3221_);
v___x_3232_ = lean_box(v_skipConstInApp_3222_);
v___x_3233_ = lean_box(v_skipInstances_3223_);
v___f_3234_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__4___boxed), 14, 13);
lean_closure_set(v___f_3234_, 0, v_toPure_3227_);
lean_closure_set(v___f_3234_, 1, v_x_3228_);
lean_closure_set(v___f_3234_, 2, v_toBind_3226_);
lean_closure_set(v___f_3234_, 3, v_inst_3214_);
lean_closure_set(v___f_3234_, 4, v_inst_3215_);
lean_closure_set(v___f_3234_, 5, v_inst_3216_);
lean_closure_set(v___f_3234_, 6, v_pre_3219_);
lean_closure_set(v___f_3234_, 7, v_post_3220_);
lean_closure_set(v___f_3234_, 8, v___x_3231_);
lean_closure_set(v___f_3234_, 9, v___x_3232_);
lean_closure_set(v___f_3234_, 10, v___x_3233_);
lean_closure_set(v___f_3234_, 11, v_x_3224_);
lean_closure_set(v___f_3234_, 12, v_input_3217_);
v___x_3235_ = lean_apply_4(v_toBind_3226_, lean_box(0), lean_box(0), v___x_3230_, v___f_3234_);
return v___x_3235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___boxed(lean_object* v_m_3236_, lean_object* v_inst_3237_, lean_object* v_inst_3238_, lean_object* v_inst_3239_, lean_object* v_input_3240_, lean_object* v_cache_3241_, lean_object* v_pre_3242_, lean_object* v_post_3243_, lean_object* v_usedLetOnly_3244_, lean_object* v_skipConstInApp_3245_, lean_object* v_skipInstances_3246_){
_start:
{
uint8_t v_usedLetOnly_boxed_3247_; uint8_t v_skipConstInApp_boxed_3248_; uint8_t v_skipInstances_boxed_3249_; lean_object* v_res_3250_; 
v_usedLetOnly_boxed_3247_ = lean_unbox(v_usedLetOnly_3244_);
v_skipConstInApp_boxed_3248_ = lean_unbox(v_skipConstInApp_3245_);
v_skipInstances_boxed_3249_ = lean_unbox(v_skipInstances_3246_);
v_res_3250_ = l_Lean_Meta_transformWithCache(v_m_3236_, v_inst_3237_, v_inst_3238_, v_inst_3239_, v_input_3240_, v_cache_3241_, v_pre_3242_, v_post_3243_, v_usedLetOnly_boxed_3247_, v_skipConstInApp_boxed_3248_, v_skipInstances_boxed_3249_);
return v_res_3250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___redArg___lam__5(lean_object* v_toPure_3251_, lean_object* v_x_3252_, lean_object* v_toBind_3253_, lean_object* v_inst_3254_, lean_object* v_inst_3255_, lean_object* v_inst_3256_, lean_object* v_pre_3257_, lean_object* v_post_3258_, uint8_t v_usedLetOnly_3259_, uint8_t v_skipConstInApp_3260_, uint8_t v___x_3261_, lean_object* v_x_3262_, lean_object* v_input_3263_, lean_object* v_ref_3264_){
_start:
{
lean_object* v___f_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; 
lean_inc(v_toBind_3253_);
lean_inc(v_x_3252_);
lean_inc(v_ref_3264_);
v___f_3265_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__4), 5, 4);
lean_closure_set(v___f_3265_, 0, v_toPure_3251_);
lean_closure_set(v___f_3265_, 1, v_ref_3264_);
lean_closure_set(v___f_3265_, 2, v_x_3252_);
lean_closure_set(v___f_3265_, 3, v_toBind_3253_);
v___x_3266_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_3254_, v_inst_3255_, v_inst_3256_, v_pre_3257_, v_post_3258_, v_usedLetOnly_3259_, v_skipConstInApp_3260_, v___x_3261_, v_x_3262_, v_x_3252_, v_input_3263_, v_ref_3264_);
lean_dec(v_ref_3264_);
v___x_3267_ = lean_apply_4(v_toBind_3253_, lean_box(0), lean_box(0), v___x_3266_, v___f_3265_);
return v___x_3267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___redArg___lam__5___boxed(lean_object* v_toPure_3268_, lean_object* v_x_3269_, lean_object* v_toBind_3270_, lean_object* v_inst_3271_, lean_object* v_inst_3272_, lean_object* v_inst_3273_, lean_object* v_pre_3274_, lean_object* v_post_3275_, lean_object* v_usedLetOnly_3276_, lean_object* v_skipConstInApp_3277_, lean_object* v___x_3278_, lean_object* v_x_3279_, lean_object* v_input_3280_, lean_object* v_ref_3281_){
_start:
{
uint8_t v_usedLetOnly_boxed_3282_; uint8_t v_skipConstInApp_boxed_3283_; uint8_t v___x_114__boxed_3284_; lean_object* v_res_3285_; 
v_usedLetOnly_boxed_3282_ = lean_unbox(v_usedLetOnly_3276_);
v_skipConstInApp_boxed_3283_ = lean_unbox(v_skipConstInApp_3277_);
v___x_114__boxed_3284_ = lean_unbox(v___x_3278_);
v_res_3285_ = l_Lean_Meta_transform___redArg___lam__5(v_toPure_3268_, v_x_3269_, v_toBind_3270_, v_inst_3271_, v_inst_3272_, v_inst_3273_, v_pre_3274_, v_post_3275_, v_usedLetOnly_boxed_3282_, v_skipConstInApp_boxed_3283_, v___x_114__boxed_3284_, v_x_3279_, v_input_3280_, v_ref_3281_);
return v_res_3285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___redArg(lean_object* v_inst_3286_, lean_object* v_inst_3287_, lean_object* v_inst_3288_, lean_object* v_input_3289_, lean_object* v_pre_3290_, lean_object* v_post_3291_, uint8_t v_usedLetOnly_3292_, uint8_t v_skipConstInApp_3293_){
_start:
{
lean_object* v_toApplicative_3294_; lean_object* v_toBind_3295_; lean_object* v_x_3296_; lean_object* v_toPure_3297_; lean_object* v_x_3298_; uint8_t v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___f_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___f_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; 
v_toApplicative_3294_ = lean_ctor_get(v_inst_3286_, 0);
v_toBind_3295_ = lean_ctor_get(v_inst_3286_, 1);
lean_inc_n(v_toBind_3295_, 3);
v_x_3296_ = lean_box(0);
v_toPure_3297_ = lean_ctor_get(v_toApplicative_3294_, 1);
lean_inc_n(v_toPure_3297_, 2);
lean_inc_n(v_inst_3287_, 2);
v_x_3298_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__1), 3, 1);
lean_closure_set(v_x_3298_, 0, v_inst_3287_);
v___x_3299_ = 0;
v___x_3300_ = lean_obj_once(&l_Lean_Core_transform___redArg___closed__2, &l_Lean_Core_transform___redArg___closed__2_once, _init_l_Lean_Core_transform___redArg___closed__2);
v___x_3301_ = l_Lean_Meta_transformWithCache___redArg___lam__1(v_inst_3287_, lean_box(0), v___x_3300_);
v___f_3302_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__2), 2, 1);
lean_closure_set(v___f_3302_, 0, v_toPure_3297_);
v___x_3303_ = lean_box(v_usedLetOnly_3292_);
v___x_3304_ = lean_box(v_skipConstInApp_3293_);
v___x_3305_ = lean_box(v___x_3299_);
v___f_3306_ = lean_alloc_closure((void*)(l_Lean_Meta_transform___redArg___lam__5___boxed), 14, 13);
lean_closure_set(v___f_3306_, 0, v_toPure_3297_);
lean_closure_set(v___f_3306_, 1, v_x_3298_);
lean_closure_set(v___f_3306_, 2, v_toBind_3295_);
lean_closure_set(v___f_3306_, 3, v_inst_3286_);
lean_closure_set(v___f_3306_, 4, v_inst_3287_);
lean_closure_set(v___f_3306_, 5, v_inst_3288_);
lean_closure_set(v___f_3306_, 6, v_pre_3290_);
lean_closure_set(v___f_3306_, 7, v_post_3291_);
lean_closure_set(v___f_3306_, 8, v___x_3303_);
lean_closure_set(v___f_3306_, 9, v___x_3304_);
lean_closure_set(v___f_3306_, 10, v___x_3305_);
lean_closure_set(v___f_3306_, 11, v_x_3296_);
lean_closure_set(v___f_3306_, 12, v_input_3289_);
v___x_3307_ = lean_apply_4(v_toBind_3295_, lean_box(0), lean_box(0), v___x_3301_, v___f_3306_);
v___x_3308_ = lean_apply_4(v_toBind_3295_, lean_box(0), lean_box(0), v___x_3307_, v___f_3302_);
return v___x_3308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___redArg___boxed(lean_object* v_inst_3309_, lean_object* v_inst_3310_, lean_object* v_inst_3311_, lean_object* v_input_3312_, lean_object* v_pre_3313_, lean_object* v_post_3314_, lean_object* v_usedLetOnly_3315_, lean_object* v_skipConstInApp_3316_){
_start:
{
uint8_t v_usedLetOnly_boxed_3317_; uint8_t v_skipConstInApp_boxed_3318_; lean_object* v_res_3319_; 
v_usedLetOnly_boxed_3317_ = lean_unbox(v_usedLetOnly_3315_);
v_skipConstInApp_boxed_3318_ = lean_unbox(v_skipConstInApp_3316_);
v_res_3319_ = l_Lean_Meta_transform___redArg(v_inst_3309_, v_inst_3310_, v_inst_3311_, v_input_3312_, v_pre_3313_, v_post_3314_, v_usedLetOnly_boxed_3317_, v_skipConstInApp_boxed_3318_);
return v_res_3319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform(lean_object* v_m_3320_, lean_object* v_inst_3321_, lean_object* v_inst_3322_, lean_object* v_inst_3323_, lean_object* v_input_3324_, lean_object* v_pre_3325_, lean_object* v_post_3326_, uint8_t v_usedLetOnly_3327_, uint8_t v_skipConstInApp_3328_){
_start:
{
lean_object* v___x_3329_; 
v___x_3329_ = l_Lean_Meta_transform___redArg(v_inst_3321_, v_inst_3322_, v_inst_3323_, v_input_3324_, v_pre_3325_, v_post_3326_, v_usedLetOnly_3327_, v_skipConstInApp_3328_);
return v___x_3329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___boxed(lean_object* v_m_3330_, lean_object* v_inst_3331_, lean_object* v_inst_3332_, lean_object* v_inst_3333_, lean_object* v_input_3334_, lean_object* v_pre_3335_, lean_object* v_post_3336_, lean_object* v_usedLetOnly_3337_, lean_object* v_skipConstInApp_3338_){
_start:
{
uint8_t v_usedLetOnly_boxed_3339_; uint8_t v_skipConstInApp_boxed_3340_; lean_object* v_res_3341_; 
v_usedLetOnly_boxed_3339_ = lean_unbox(v_usedLetOnly_3337_);
v_skipConstInApp_boxed_3340_ = lean_unbox(v_skipConstInApp_3338_);
v_res_3341_ = l_Lean_Meta_transform(v_m_3330_, v_inst_3331_, v_inst_3332_, v_inst_3333_, v_input_3334_, v_pre_3335_, v_post_3336_, v_usedLetOnly_boxed_3339_, v_skipConstInApp_boxed_3340_);
return v_res_3341_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(lean_object* v_e_3342_, lean_object* v___y_3343_){
_start:
{
uint8_t v___x_3345_; 
v___x_3345_ = l_Lean_Expr_hasMVar(v_e_3342_);
if (v___x_3345_ == 0)
{
lean_object* v___x_3346_; 
v___x_3346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3346_, 0, v_e_3342_);
return v___x_3346_;
}
else
{
lean_object* v___x_3347_; lean_object* v_mctx_3348_; lean_object* v___x_3349_; lean_object* v_fst_3350_; lean_object* v_snd_3351_; lean_object* v___x_3352_; lean_object* v_cache_3353_; lean_object* v_zetaDeltaFVarIds_3354_; lean_object* v_postponed_3355_; lean_object* v_diag_3356_; lean_object* v___x_3358_; uint8_t v_isShared_3359_; uint8_t v_isSharedCheck_3365_; 
v___x_3347_ = lean_st_ref_get(v___y_3343_);
v_mctx_3348_ = lean_ctor_get(v___x_3347_, 0);
lean_inc_ref(v_mctx_3348_);
lean_dec(v___x_3347_);
v___x_3349_ = l_Lean_instantiateMVarsCore(v_mctx_3348_, v_e_3342_);
v_fst_3350_ = lean_ctor_get(v___x_3349_, 0);
lean_inc(v_fst_3350_);
v_snd_3351_ = lean_ctor_get(v___x_3349_, 1);
lean_inc(v_snd_3351_);
lean_dec_ref(v___x_3349_);
v___x_3352_ = lean_st_ref_take(v___y_3343_);
v_cache_3353_ = lean_ctor_get(v___x_3352_, 1);
v_zetaDeltaFVarIds_3354_ = lean_ctor_get(v___x_3352_, 2);
v_postponed_3355_ = lean_ctor_get(v___x_3352_, 3);
v_diag_3356_ = lean_ctor_get(v___x_3352_, 4);
v_isSharedCheck_3365_ = !lean_is_exclusive(v___x_3352_);
if (v_isSharedCheck_3365_ == 0)
{
lean_object* v_unused_3366_; 
v_unused_3366_ = lean_ctor_get(v___x_3352_, 0);
lean_dec(v_unused_3366_);
v___x_3358_ = v___x_3352_;
v_isShared_3359_ = v_isSharedCheck_3365_;
goto v_resetjp_3357_;
}
else
{
lean_inc(v_diag_3356_);
lean_inc(v_postponed_3355_);
lean_inc(v_zetaDeltaFVarIds_3354_);
lean_inc(v_cache_3353_);
lean_dec(v___x_3352_);
v___x_3358_ = lean_box(0);
v_isShared_3359_ = v_isSharedCheck_3365_;
goto v_resetjp_3357_;
}
v_resetjp_3357_:
{
lean_object* v___x_3361_; 
if (v_isShared_3359_ == 0)
{
lean_ctor_set(v___x_3358_, 0, v_snd_3351_);
v___x_3361_ = v___x_3358_;
goto v_reusejp_3360_;
}
else
{
lean_object* v_reuseFailAlloc_3364_; 
v_reuseFailAlloc_3364_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3364_, 0, v_snd_3351_);
lean_ctor_set(v_reuseFailAlloc_3364_, 1, v_cache_3353_);
lean_ctor_set(v_reuseFailAlloc_3364_, 2, v_zetaDeltaFVarIds_3354_);
lean_ctor_set(v_reuseFailAlloc_3364_, 3, v_postponed_3355_);
lean_ctor_set(v_reuseFailAlloc_3364_, 4, v_diag_3356_);
v___x_3361_ = v_reuseFailAlloc_3364_;
goto v_reusejp_3360_;
}
v_reusejp_3360_:
{
lean_object* v___x_3362_; lean_object* v___x_3363_; 
v___x_3362_ = lean_st_ref_set(v___y_3343_, v___x_3361_);
v___x_3363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3363_, 0, v_fst_3350_);
return v___x_3363_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg___boxed(lean_object* v_e_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_){
_start:
{
lean_object* v_res_3370_; 
v_res_3370_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(v_e_3367_, v___y_3368_);
lean_dec(v___y_3368_);
return v_res_3370_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0(lean_object* v_e_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_){
_start:
{
lean_object* v___x_3377_; 
v___x_3377_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(v_e_3371_, v___y_3373_);
return v___x_3377_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___boxed(lean_object* v_e_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_){
_start:
{
lean_object* v_res_3384_; 
v_res_3384_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0(v_e_3378_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_);
lean_dec(v___y_3382_);
lean_dec_ref(v___y_3381_);
lean_dec(v___y_3380_);
lean_dec_ref(v___y_3379_);
return v_res_3384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__0(uint8_t v_zetaHave_3385_, lean_object* v___x_3386_, uint8_t v_zetaDelta_3387_, lean_object* v_fvarId_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_){
_start:
{
lean_object* v___x_3394_; 
v___x_3394_ = l_Lean_FVarId_findDecl_x3f___redArg(v_fvarId_3388_, v___y_3389_);
if (lean_obj_tag(v___x_3394_) == 0)
{
lean_object* v_a_3395_; lean_object* v___x_3397_; uint8_t v_isShared_3398_; uint8_t v_isSharedCheck_3423_; 
v_a_3395_ = lean_ctor_get(v___x_3394_, 0);
v_isSharedCheck_3423_ = !lean_is_exclusive(v___x_3394_);
if (v_isSharedCheck_3423_ == 0)
{
v___x_3397_ = v___x_3394_;
v_isShared_3398_ = v_isSharedCheck_3423_;
goto v_resetjp_3396_;
}
else
{
lean_inc(v_a_3395_);
lean_dec(v___x_3394_);
v___x_3397_ = lean_box(0);
v_isShared_3398_ = v_isSharedCheck_3423_;
goto v_resetjp_3396_;
}
v_resetjp_3396_:
{
if (lean_obj_tag(v_a_3395_) == 1)
{
lean_object* v_val_3399_; lean_object* v___x_3401_; uint8_t v_isShared_3402_; uint8_t v_isSharedCheck_3418_; 
v_val_3399_ = lean_ctor_get(v_a_3395_, 0);
v_isSharedCheck_3418_ = !lean_is_exclusive(v_a_3395_);
if (v_isSharedCheck_3418_ == 0)
{
v___x_3401_ = v_a_3395_;
v_isShared_3402_ = v_isSharedCheck_3418_;
goto v_resetjp_3400_;
}
else
{
lean_inc(v_val_3399_);
lean_dec(v_a_3395_);
v___x_3401_ = lean_box(0);
v_isShared_3402_ = v_isSharedCheck_3418_;
goto v_resetjp_3400_;
}
v_resetjp_3400_:
{
uint8_t v___y_3404_; 
if (v_zetaDelta_3387_ == 0)
{
lean_object* v___x_3412_; uint8_t v___x_3413_; 
v___x_3412_ = l_Lean_LocalDecl_index(v_val_3399_);
v___x_3413_ = lean_nat_dec_lt(v___x_3412_, v___x_3386_);
lean_dec(v___x_3412_);
if (v___x_3413_ == 0)
{
lean_del_object(v___x_3401_);
goto v___jp_3409_;
}
else
{
lean_object* v___x_3414_; lean_object* v___x_3416_; 
lean_dec(v_val_3399_);
lean_del_object(v___x_3397_);
v___x_3414_ = lean_box(0);
if (v_isShared_3402_ == 0)
{
lean_ctor_set_tag(v___x_3401_, 0);
lean_ctor_set(v___x_3401_, 0, v___x_3414_);
v___x_3416_ = v___x_3401_;
goto v_reusejp_3415_;
}
else
{
lean_object* v_reuseFailAlloc_3417_; 
v_reuseFailAlloc_3417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3417_, 0, v___x_3414_);
v___x_3416_ = v_reuseFailAlloc_3417_;
goto v_reusejp_3415_;
}
v_reusejp_3415_:
{
return v___x_3416_;
}
}
}
else
{
lean_del_object(v___x_3401_);
goto v___jp_3409_;
}
v___jp_3403_:
{
lean_object* v___x_3405_; lean_object* v___x_3407_; 
v___x_3405_ = l_Lean_LocalDecl_value_x3f(v_val_3399_, v___y_3404_);
lean_dec(v_val_3399_);
if (v_isShared_3398_ == 0)
{
lean_ctor_set(v___x_3397_, 0, v___x_3405_);
v___x_3407_ = v___x_3397_;
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
v___jp_3409_:
{
if (v_zetaHave_3385_ == 0)
{
v___y_3404_ = v_zetaHave_3385_;
goto v___jp_3403_;
}
else
{
lean_object* v___x_3410_; uint8_t v___x_3411_; 
v___x_3410_ = l_Lean_LocalDecl_index(v_val_3399_);
v___x_3411_ = lean_nat_dec_le(v___x_3386_, v___x_3410_);
lean_dec(v___x_3410_);
v___y_3404_ = v___x_3411_;
goto v___jp_3403_;
}
}
}
}
else
{
lean_object* v___x_3419_; lean_object* v___x_3421_; 
lean_dec(v_a_3395_);
v___x_3419_ = lean_box(0);
if (v_isShared_3398_ == 0)
{
lean_ctor_set(v___x_3397_, 0, v___x_3419_);
v___x_3421_ = v___x_3397_;
goto v_reusejp_3420_;
}
else
{
lean_object* v_reuseFailAlloc_3422_; 
v_reuseFailAlloc_3422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3422_, 0, v___x_3419_);
v___x_3421_ = v_reuseFailAlloc_3422_;
goto v_reusejp_3420_;
}
v_reusejp_3420_:
{
return v___x_3421_;
}
}
}
}
else
{
lean_object* v_a_3424_; lean_object* v___x_3426_; uint8_t v_isShared_3427_; uint8_t v_isSharedCheck_3431_; 
v_a_3424_ = lean_ctor_get(v___x_3394_, 0);
v_isSharedCheck_3431_ = !lean_is_exclusive(v___x_3394_);
if (v_isSharedCheck_3431_ == 0)
{
v___x_3426_ = v___x_3394_;
v_isShared_3427_ = v_isSharedCheck_3431_;
goto v_resetjp_3425_;
}
else
{
lean_inc(v_a_3424_);
lean_dec(v___x_3394_);
v___x_3426_ = lean_box(0);
v_isShared_3427_ = v_isSharedCheck_3431_;
goto v_resetjp_3425_;
}
v_resetjp_3425_:
{
lean_object* v___x_3429_; 
if (v_isShared_3427_ == 0)
{
v___x_3429_ = v___x_3426_;
goto v_reusejp_3428_;
}
else
{
lean_object* v_reuseFailAlloc_3430_; 
v_reuseFailAlloc_3430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3430_, 0, v_a_3424_);
v___x_3429_ = v_reuseFailAlloc_3430_;
goto v_reusejp_3428_;
}
v_reusejp_3428_:
{
return v___x_3429_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__0___boxed(lean_object* v_zetaHave_3432_, lean_object* v___x_3433_, lean_object* v_zetaDelta_3434_, lean_object* v_fvarId_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_){
_start:
{
uint8_t v_zetaHave_boxed_3441_; uint8_t v_zetaDelta_boxed_3442_; lean_object* v_res_3443_; 
v_zetaHave_boxed_3441_ = lean_unbox(v_zetaHave_3432_);
v_zetaDelta_boxed_3442_ = lean_unbox(v_zetaDelta_3434_);
v_res_3443_ = l_Lean_Meta_zetaReduce___lam__0(v_zetaHave_boxed_3441_, v___x_3433_, v_zetaDelta_boxed_3442_, v_fvarId_3435_, v___y_3436_, v___y_3437_, v___y_3438_, v___y_3439_);
lean_dec(v___y_3439_);
lean_dec_ref(v___y_3438_);
lean_dec(v___y_3437_);
lean_dec_ref(v___y_3436_);
lean_dec(v___x_3433_);
return v_res_3443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__1(lean_object* v_e_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_){
_start:
{
lean_object* v___x_3450_; lean_object* v___x_3451_; 
v___x_3450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3450_, 0, v_e_3444_);
v___x_3451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3451_, 0, v___x_3450_);
return v___x_3451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__1___boxed(lean_object* v_e_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_){
_start:
{
lean_object* v_res_3458_; 
v_res_3458_ = l_Lean_Meta_zetaReduce___lam__1(v_e_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_);
lean_dec(v___y_3456_);
lean_dec_ref(v___y_3455_);
lean_dec(v___y_3454_);
lean_dec_ref(v___y_3453_);
return v_res_3458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__2(lean_object* v___f_3459_, lean_object* v_e_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_){
_start:
{
if (lean_obj_tag(v_e_3460_) == 1)
{
lean_object* v_fvarId_3466_; lean_object* v___x_3467_; 
v_fvarId_3466_ = lean_ctor_get(v_e_3460_, 0);
lean_inc(v___y_3464_);
lean_inc_ref(v___y_3463_);
lean_inc(v___y_3462_);
lean_inc_ref(v___y_3461_);
lean_inc(v_fvarId_3466_);
v___x_3467_ = lean_apply_6(v___f_3459_, v_fvarId_3466_, v___y_3461_, v___y_3462_, v___y_3463_, v___y_3464_, lean_box(0));
if (lean_obj_tag(v___x_3467_) == 0)
{
lean_object* v_a_3468_; lean_object* v___x_3470_; uint8_t v_isShared_3471_; uint8_t v_isSharedCheck_3493_; 
v_a_3468_ = lean_ctor_get(v___x_3467_, 0);
v_isSharedCheck_3493_ = !lean_is_exclusive(v___x_3467_);
if (v_isSharedCheck_3493_ == 0)
{
v___x_3470_ = v___x_3467_;
v_isShared_3471_ = v_isSharedCheck_3493_;
goto v_resetjp_3469_;
}
else
{
lean_inc(v_a_3468_);
lean_dec(v___x_3467_);
v___x_3470_ = lean_box(0);
v_isShared_3471_ = v_isSharedCheck_3493_;
goto v_resetjp_3469_;
}
v_resetjp_3469_:
{
if (lean_obj_tag(v_a_3468_) == 1)
{
lean_object* v_val_3472_; lean_object* v___x_3474_; uint8_t v_isShared_3475_; uint8_t v_isSharedCheck_3488_; 
lean_del_object(v___x_3470_);
lean_dec_ref(v_e_3460_);
v_val_3472_ = lean_ctor_get(v_a_3468_, 0);
v_isSharedCheck_3488_ = !lean_is_exclusive(v_a_3468_);
if (v_isSharedCheck_3488_ == 0)
{
v___x_3474_ = v_a_3468_;
v_isShared_3475_ = v_isSharedCheck_3488_;
goto v_resetjp_3473_;
}
else
{
lean_inc(v_val_3472_);
lean_dec(v_a_3468_);
v___x_3474_ = lean_box(0);
v_isShared_3475_ = v_isSharedCheck_3488_;
goto v_resetjp_3473_;
}
v_resetjp_3473_:
{
lean_object* v___x_3476_; lean_object* v_a_3477_; lean_object* v___x_3479_; uint8_t v_isShared_3480_; uint8_t v_isSharedCheck_3487_; 
v___x_3476_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(v_val_3472_, v___y_3462_);
v_a_3477_ = lean_ctor_get(v___x_3476_, 0);
v_isSharedCheck_3487_ = !lean_is_exclusive(v___x_3476_);
if (v_isSharedCheck_3487_ == 0)
{
v___x_3479_ = v___x_3476_;
v_isShared_3480_ = v_isSharedCheck_3487_;
goto v_resetjp_3478_;
}
else
{
lean_inc(v_a_3477_);
lean_dec(v___x_3476_);
v___x_3479_ = lean_box(0);
v_isShared_3480_ = v_isSharedCheck_3487_;
goto v_resetjp_3478_;
}
v_resetjp_3478_:
{
lean_object* v___x_3482_; 
if (v_isShared_3475_ == 0)
{
lean_ctor_set(v___x_3474_, 0, v_a_3477_);
v___x_3482_ = v___x_3474_;
goto v_reusejp_3481_;
}
else
{
lean_object* v_reuseFailAlloc_3486_; 
v_reuseFailAlloc_3486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3486_, 0, v_a_3477_);
v___x_3482_ = v_reuseFailAlloc_3486_;
goto v_reusejp_3481_;
}
v_reusejp_3481_:
{
lean_object* v___x_3484_; 
if (v_isShared_3480_ == 0)
{
lean_ctor_set(v___x_3479_, 0, v___x_3482_);
v___x_3484_ = v___x_3479_;
goto v_reusejp_3483_;
}
else
{
lean_object* v_reuseFailAlloc_3485_; 
v_reuseFailAlloc_3485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3485_, 0, v___x_3482_);
v___x_3484_ = v_reuseFailAlloc_3485_;
goto v_reusejp_3483_;
}
v_reusejp_3483_:
{
return v___x_3484_;
}
}
}
}
}
else
{
lean_object* v___x_3489_; lean_object* v___x_3491_; 
lean_dec(v_a_3468_);
v___x_3489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3489_, 0, v_e_3460_);
if (v_isShared_3471_ == 0)
{
lean_ctor_set(v___x_3470_, 0, v___x_3489_);
v___x_3491_ = v___x_3470_;
goto v_reusejp_3490_;
}
else
{
lean_object* v_reuseFailAlloc_3492_; 
v_reuseFailAlloc_3492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3492_, 0, v___x_3489_);
v___x_3491_ = v_reuseFailAlloc_3492_;
goto v_reusejp_3490_;
}
v_reusejp_3490_:
{
return v___x_3491_;
}
}
}
}
else
{
lean_object* v_a_3494_; lean_object* v___x_3496_; uint8_t v_isShared_3497_; uint8_t v_isSharedCheck_3501_; 
lean_dec_ref(v_e_3460_);
v_a_3494_ = lean_ctor_get(v___x_3467_, 0);
v_isSharedCheck_3501_ = !lean_is_exclusive(v___x_3467_);
if (v_isSharedCheck_3501_ == 0)
{
v___x_3496_ = v___x_3467_;
v_isShared_3497_ = v_isSharedCheck_3501_;
goto v_resetjp_3495_;
}
else
{
lean_inc(v_a_3494_);
lean_dec(v___x_3467_);
v___x_3496_ = lean_box(0);
v_isShared_3497_ = v_isSharedCheck_3501_;
goto v_resetjp_3495_;
}
v_resetjp_3495_:
{
lean_object* v___x_3499_; 
if (v_isShared_3497_ == 0)
{
v___x_3499_ = v___x_3496_;
goto v_reusejp_3498_;
}
else
{
lean_object* v_reuseFailAlloc_3500_; 
v_reuseFailAlloc_3500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3500_, 0, v_a_3494_);
v___x_3499_ = v_reuseFailAlloc_3500_;
goto v_reusejp_3498_;
}
v_reusejp_3498_:
{
return v___x_3499_;
}
}
}
}
else
{
lean_object* v___x_3502_; lean_object* v___x_3503_; 
lean_dec_ref(v_e_3460_);
lean_dec_ref(v___f_3459_);
v___x_3502_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_3503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3503_, 0, v___x_3502_);
return v___x_3503_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__2___boxed(lean_object* v___f_3504_, lean_object* v_e_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_){
_start:
{
lean_object* v_res_3511_; 
v_res_3511_ = l_Lean_Meta_zetaReduce___lam__2(v___f_3504_, v_e_3505_, v___y_3506_, v___y_3507_, v___y_3508_, v___y_3509_);
lean_dec(v___y_3509_);
lean_dec_ref(v___y_3508_);
lean_dec(v___y_3507_);
lean_dec_ref(v___y_3506_);
return v_res_3511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__4(lean_object* v___f_3512_, lean_object* v_e_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_){
_start:
{
lean_object* v___x_3519_; 
v___x_3519_ = l_Lean_Expr_getAppFn(v_e_3513_);
if (lean_obj_tag(v___x_3519_) == 1)
{
lean_object* v_fvarId_3520_; lean_object* v___x_3521_; 
v_fvarId_3520_ = lean_ctor_get(v___x_3519_, 0);
lean_inc(v_fvarId_3520_);
lean_dec_ref(v___x_3519_);
lean_inc(v___y_3517_);
lean_inc_ref(v___y_3516_);
lean_inc(v___y_3515_);
lean_inc_ref(v___y_3514_);
v___x_3521_ = lean_apply_6(v___f_3512_, v_fvarId_3520_, v___y_3514_, v___y_3515_, v___y_3516_, v___y_3517_, lean_box(0));
if (lean_obj_tag(v___x_3521_) == 0)
{
lean_object* v_a_3522_; lean_object* v___x_3524_; uint8_t v_isShared_3525_; uint8_t v_isSharedCheck_3554_; 
v_a_3522_ = lean_ctor_get(v___x_3521_, 0);
v_isSharedCheck_3554_ = !lean_is_exclusive(v___x_3521_);
if (v_isSharedCheck_3554_ == 0)
{
v___x_3524_ = v___x_3521_;
v_isShared_3525_ = v_isSharedCheck_3554_;
goto v_resetjp_3523_;
}
else
{
lean_inc(v_a_3522_);
lean_dec(v___x_3521_);
v___x_3524_ = lean_box(0);
v_isShared_3525_ = v_isSharedCheck_3554_;
goto v_resetjp_3523_;
}
v_resetjp_3523_:
{
if (lean_obj_tag(v_a_3522_) == 1)
{
lean_object* v_val_3526_; lean_object* v___x_3528_; uint8_t v_isShared_3529_; uint8_t v_isSharedCheck_3549_; 
lean_del_object(v___x_3524_);
v_val_3526_ = lean_ctor_get(v_a_3522_, 0);
v_isSharedCheck_3549_ = !lean_is_exclusive(v_a_3522_);
if (v_isSharedCheck_3549_ == 0)
{
v___x_3528_ = v_a_3522_;
v_isShared_3529_ = v_isSharedCheck_3549_;
goto v_resetjp_3527_;
}
else
{
lean_inc(v_val_3526_);
lean_dec(v_a_3522_);
v___x_3528_ = lean_box(0);
v_isShared_3529_ = v_isSharedCheck_3549_;
goto v_resetjp_3527_;
}
v_resetjp_3527_:
{
lean_object* v___x_3530_; lean_object* v_a_3531_; lean_object* v___x_3533_; uint8_t v_isShared_3534_; uint8_t v_isSharedCheck_3548_; 
v___x_3530_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(v_val_3526_, v___y_3515_);
v_a_3531_ = lean_ctor_get(v___x_3530_, 0);
v_isSharedCheck_3548_ = !lean_is_exclusive(v___x_3530_);
if (v_isSharedCheck_3548_ == 0)
{
v___x_3533_ = v___x_3530_;
v_isShared_3534_ = v_isSharedCheck_3548_;
goto v_resetjp_3532_;
}
else
{
lean_inc(v_a_3531_);
lean_dec(v___x_3530_);
v___x_3533_ = lean_box(0);
v_isShared_3534_ = v_isSharedCheck_3548_;
goto v_resetjp_3532_;
}
v_resetjp_3532_:
{
lean_object* v_dummy_3535_; lean_object* v_nargs_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3543_; 
v_dummy_3535_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_3536_ = l_Lean_Expr_getAppNumArgs(v_e_3513_);
lean_inc(v_nargs_3536_);
v___x_3537_ = lean_mk_array(v_nargs_3536_, v_dummy_3535_);
v___x_3538_ = lean_unsigned_to_nat(1u);
v___x_3539_ = lean_nat_sub(v_nargs_3536_, v___x_3538_);
lean_dec(v_nargs_3536_);
v___x_3540_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3513_, v___x_3537_, v___x_3539_);
v___x_3541_ = l_Lean_Expr_beta(v_a_3531_, v___x_3540_);
if (v_isShared_3529_ == 0)
{
lean_ctor_set(v___x_3528_, 0, v___x_3541_);
v___x_3543_ = v___x_3528_;
goto v_reusejp_3542_;
}
else
{
lean_object* v_reuseFailAlloc_3547_; 
v_reuseFailAlloc_3547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3547_, 0, v___x_3541_);
v___x_3543_ = v_reuseFailAlloc_3547_;
goto v_reusejp_3542_;
}
v_reusejp_3542_:
{
lean_object* v___x_3545_; 
if (v_isShared_3534_ == 0)
{
lean_ctor_set(v___x_3533_, 0, v___x_3543_);
v___x_3545_ = v___x_3533_;
goto v_reusejp_3544_;
}
else
{
lean_object* v_reuseFailAlloc_3546_; 
v_reuseFailAlloc_3546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3546_, 0, v___x_3543_);
v___x_3545_ = v_reuseFailAlloc_3546_;
goto v_reusejp_3544_;
}
v_reusejp_3544_:
{
return v___x_3545_;
}
}
}
}
}
else
{
lean_object* v___x_3550_; lean_object* v___x_3552_; 
lean_dec(v_a_3522_);
lean_dec_ref(v_e_3513_);
v___x_3550_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
if (v_isShared_3525_ == 0)
{
lean_ctor_set(v___x_3524_, 0, v___x_3550_);
v___x_3552_ = v___x_3524_;
goto v_reusejp_3551_;
}
else
{
lean_object* v_reuseFailAlloc_3553_; 
v_reuseFailAlloc_3553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3553_, 0, v___x_3550_);
v___x_3552_ = v_reuseFailAlloc_3553_;
goto v_reusejp_3551_;
}
v_reusejp_3551_:
{
return v___x_3552_;
}
}
}
}
else
{
lean_object* v_a_3555_; lean_object* v___x_3557_; uint8_t v_isShared_3558_; uint8_t v_isSharedCheck_3562_; 
lean_dec_ref(v_e_3513_);
v_a_3555_ = lean_ctor_get(v___x_3521_, 0);
v_isSharedCheck_3562_ = !lean_is_exclusive(v___x_3521_);
if (v_isSharedCheck_3562_ == 0)
{
v___x_3557_ = v___x_3521_;
v_isShared_3558_ = v_isSharedCheck_3562_;
goto v_resetjp_3556_;
}
else
{
lean_inc(v_a_3555_);
lean_dec(v___x_3521_);
v___x_3557_ = lean_box(0);
v_isShared_3558_ = v_isSharedCheck_3562_;
goto v_resetjp_3556_;
}
v_resetjp_3556_:
{
lean_object* v___x_3560_; 
if (v_isShared_3558_ == 0)
{
v___x_3560_ = v___x_3557_;
goto v_reusejp_3559_;
}
else
{
lean_object* v_reuseFailAlloc_3561_; 
v_reuseFailAlloc_3561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3561_, 0, v_a_3555_);
v___x_3560_ = v_reuseFailAlloc_3561_;
goto v_reusejp_3559_;
}
v_reusejp_3559_:
{
return v___x_3560_;
}
}
}
}
else
{
lean_object* v___x_3563_; lean_object* v___x_3564_; 
lean_dec_ref(v___x_3519_);
lean_dec_ref(v_e_3513_);
lean_dec_ref(v___f_3512_);
v___x_3563_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_3564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3564_, 0, v___x_3563_);
return v___x_3564_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__4___boxed(lean_object* v___f_3565_, lean_object* v_e_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_){
_start:
{
lean_object* v_res_3572_; 
v_res_3572_ = l_Lean_Meta_zetaReduce___lam__4(v___f_3565_, v_e_3566_, v___y_3567_, v___y_3568_, v___y_3569_, v___y_3570_);
lean_dec(v___y_3570_);
lean_dec_ref(v___y_3569_);
lean_dec(v___y_3568_);
lean_dec_ref(v___y_3567_);
return v_res_3572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0(lean_object* v_00_u03b1_3573_, lean_object* v_x_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_){
_start:
{
lean_object* v___x_3580_; lean_object* v___x_3581_; 
v___x_3580_ = lean_apply_1(v_x_3574_, lean_box(0));
v___x_3581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3581_, 0, v___x_3580_);
return v___x_3581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0___boxed(lean_object* v_00_u03b1_3582_, lean_object* v_x_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_){
_start:
{
lean_object* v_res_3589_; 
v_res_3589_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0(v_00_u03b1_3582_, v_x_3583_, v___y_3584_, v___y_3585_, v___y_3586_, v___y_3587_);
lean_dec(v___y_3587_);
lean_dec_ref(v___y_3586_);
lean_dec(v___y_3585_);
lean_dec_ref(v___y_3584_);
return v_res_3589_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__2(lean_object* v___x_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_){
_start:
{
lean_object* v___x_3596_; 
v___x_3596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3596_, 0, v___x_3590_);
return v___x_3596_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__2___boxed(lean_object* v___x_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_){
_start:
{
lean_object* v_res_3603_; 
v_res_3603_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__2(v___x_3597_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_);
lean_dec(v___y_3601_);
lean_dec_ref(v___y_3600_);
lean_dec(v___y_3599_);
lean_dec_ref(v___y_3598_);
return v_res_3603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0(lean_object* v_k_3604_, lean_object* v___y_3605_, lean_object* v_b_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_){
_start:
{
lean_object* v___x_3612_; 
lean_inc(v___y_3610_);
lean_inc_ref(v___y_3609_);
lean_inc(v___y_3608_);
lean_inc_ref(v___y_3607_);
lean_inc(v___y_3605_);
v___x_3612_ = lean_apply_7(v_k_3604_, v_b_3606_, v___y_3605_, v___y_3607_, v___y_3608_, v___y_3609_, v___y_3610_, lean_box(0));
return v___x_3612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0___boxed(lean_object* v_k_3613_, lean_object* v___y_3614_, lean_object* v_b_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_){
_start:
{
lean_object* v_res_3621_; 
v_res_3621_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0(v_k_3613_, v___y_3614_, v_b_3615_, v___y_3616_, v___y_3617_, v___y_3618_, v___y_3619_);
lean_dec(v___y_3619_);
lean_dec_ref(v___y_3618_);
lean_dec(v___y_3617_);
lean_dec_ref(v___y_3616_);
lean_dec(v___y_3614_);
return v_res_3621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(lean_object* v_name_3622_, uint8_t v_bi_3623_, lean_object* v_type_3624_, lean_object* v_k_3625_, uint8_t v_kind_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_){
_start:
{
lean_object* v___f_3633_; lean_object* v___x_3634_; 
lean_inc(v___y_3627_);
v___f_3633_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3633_, 0, v_k_3625_);
lean_closure_set(v___f_3633_, 1, v___y_3627_);
v___x_3634_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3622_, v_bi_3623_, v_type_3624_, v___f_3633_, v_kind_3626_, v___y_3628_, v___y_3629_, v___y_3630_, v___y_3631_);
if (lean_obj_tag(v___x_3634_) == 0)
{
return v___x_3634_;
}
else
{
lean_object* v_a_3635_; lean_object* v___x_3637_; uint8_t v_isShared_3638_; uint8_t v_isSharedCheck_3642_; 
v_a_3635_ = lean_ctor_get(v___x_3634_, 0);
v_isSharedCheck_3642_ = !lean_is_exclusive(v___x_3634_);
if (v_isSharedCheck_3642_ == 0)
{
v___x_3637_ = v___x_3634_;
v_isShared_3638_ = v_isSharedCheck_3642_;
goto v_resetjp_3636_;
}
else
{
lean_inc(v_a_3635_);
lean_dec(v___x_3634_);
v___x_3637_ = lean_box(0);
v_isShared_3638_ = v_isSharedCheck_3642_;
goto v_resetjp_3636_;
}
v_resetjp_3636_:
{
lean_object* v___x_3640_; 
if (v_isShared_3638_ == 0)
{
v___x_3640_ = v___x_3637_;
goto v_reusejp_3639_;
}
else
{
lean_object* v_reuseFailAlloc_3641_; 
v_reuseFailAlloc_3641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3641_, 0, v_a_3635_);
v___x_3640_ = v_reuseFailAlloc_3641_;
goto v_reusejp_3639_;
}
v_reusejp_3639_:
{
return v___x_3640_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___boxed(lean_object* v_name_3643_, lean_object* v_bi_3644_, lean_object* v_type_3645_, lean_object* v_k_3646_, lean_object* v_kind_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_){
_start:
{
uint8_t v_bi_boxed_3654_; uint8_t v_kind_boxed_3655_; lean_object* v_res_3656_; 
v_bi_boxed_3654_ = lean_unbox(v_bi_3644_);
v_kind_boxed_3655_ = lean_unbox(v_kind_3647_);
v_res_3656_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_name_3643_, v_bi_boxed_3654_, v_type_3645_, v_k_3646_, v_kind_boxed_3655_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_);
lean_dec(v___y_3652_);
lean_dec_ref(v___y_3651_);
lean_dec(v___y_3650_);
lean_dec_ref(v___y_3649_);
lean_dec(v___y_3648_);
return v_res_3656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg(lean_object* v_name_3657_, lean_object* v_type_3658_, lean_object* v_val_3659_, lean_object* v_k_3660_, uint8_t v_nondep_3661_, uint8_t v_kind_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_){
_start:
{
lean_object* v___f_3669_; lean_object* v___x_3670_; 
lean_inc(v___y_3663_);
v___f_3669_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3669_, 0, v_k_3660_);
lean_closure_set(v___f_3669_, 1, v___y_3663_);
v___x_3670_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_3657_, v_type_3658_, v_val_3659_, v___f_3669_, v_nondep_3661_, v_kind_3662_, v___y_3664_, v___y_3665_, v___y_3666_, v___y_3667_);
if (lean_obj_tag(v___x_3670_) == 0)
{
return v___x_3670_;
}
else
{
lean_object* v_a_3671_; lean_object* v___x_3673_; uint8_t v_isShared_3674_; uint8_t v_isSharedCheck_3678_; 
v_a_3671_ = lean_ctor_get(v___x_3670_, 0);
v_isSharedCheck_3678_ = !lean_is_exclusive(v___x_3670_);
if (v_isSharedCheck_3678_ == 0)
{
v___x_3673_ = v___x_3670_;
v_isShared_3674_ = v_isSharedCheck_3678_;
goto v_resetjp_3672_;
}
else
{
lean_inc(v_a_3671_);
lean_dec(v___x_3670_);
v___x_3673_ = lean_box(0);
v_isShared_3674_ = v_isSharedCheck_3678_;
goto v_resetjp_3672_;
}
v_resetjp_3672_:
{
lean_object* v___x_3676_; 
if (v_isShared_3674_ == 0)
{
v___x_3676_ = v___x_3673_;
goto v_reusejp_3675_;
}
else
{
lean_object* v_reuseFailAlloc_3677_; 
v_reuseFailAlloc_3677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3677_, 0, v_a_3671_);
v___x_3676_ = v_reuseFailAlloc_3677_;
goto v_reusejp_3675_;
}
v_reusejp_3675_:
{
return v___x_3676_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg___boxed(lean_object* v_name_3679_, lean_object* v_type_3680_, lean_object* v_val_3681_, lean_object* v_k_3682_, lean_object* v_nondep_3683_, lean_object* v_kind_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_){
_start:
{
uint8_t v_nondep_boxed_3691_; uint8_t v_kind_boxed_3692_; lean_object* v_res_3693_; 
v_nondep_boxed_3691_ = lean_unbox(v_nondep_3683_);
v_kind_boxed_3692_ = lean_unbox(v_kind_3684_);
v_res_3693_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg(v_name_3679_, v_type_3680_, v_val_3681_, v_k_3682_, v_nondep_boxed_3691_, v_kind_boxed_3692_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_, v___y_3689_);
lean_dec(v___y_3689_);
lean_dec_ref(v___y_3688_);
lean_dec(v___y_3687_);
lean_dec_ref(v___y_3686_);
lean_dec(v___y_3685_);
return v_res_3693_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0(lean_object* v_00_u03b1_3694_, lean_object* v_x_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_){
_start:
{
lean_object* v___x_3701_; lean_object* v___x_3702_; 
v___x_3701_ = lean_apply_1(v_x_3695_, lean_box(0));
v___x_3702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3702_, 0, v___x_3701_);
return v___x_3702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0___boxed(lean_object* v_00_u03b1_3703_, lean_object* v_x_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_){
_start:
{
lean_object* v_res_3710_; 
v_res_3710_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0(v_00_u03b1_3703_, v_x_3704_, v___y_3705_, v___y_3706_, v___y_3707_, v___y_3708_);
lean_dec(v___y_3708_);
lean_dec_ref(v___y_3707_);
lean_dec(v___y_3706_);
lean_dec_ref(v___y_3705_);
return v_res_3710_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg(lean_object* v_ref_3711_){
_start:
{
lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; 
v___x_3713_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5);
v___x_3714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3714_, 0, v_ref_3711_);
lean_ctor_set(v___x_3714_, 1, v___x_3713_);
v___x_3715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3715_, 0, v___x_3714_);
return v___x_3715_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg___boxed(lean_object* v_ref_3716_, lean_object* v___y_3717_){
_start:
{
lean_object* v_res_3718_; 
v_res_3718_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg(v_ref_3716_);
return v_res_3718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg(lean_object* v_x_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_){
_start:
{
lean_object* v___y_3727_; lean_object* v_fileName_3736_; lean_object* v_fileMap_3737_; lean_object* v_options_3738_; lean_object* v_currRecDepth_3739_; lean_object* v_maxRecDepth_3740_; lean_object* v_ref_3741_; lean_object* v_currNamespace_3742_; lean_object* v_openDecls_3743_; lean_object* v_initHeartbeats_3744_; lean_object* v_maxHeartbeats_3745_; lean_object* v_quotContext_3746_; lean_object* v_currMacroScope_3747_; uint8_t v_diag_3748_; lean_object* v_cancelTk_x3f_3749_; uint8_t v_suppressElabErrors_3750_; lean_object* v_inheritedTraceOptions_3751_; lean_object* v___x_3757_; uint8_t v___x_3758_; 
v_fileName_3736_ = lean_ctor_get(v___y_3723_, 0);
v_fileMap_3737_ = lean_ctor_get(v___y_3723_, 1);
v_options_3738_ = lean_ctor_get(v___y_3723_, 2);
v_currRecDepth_3739_ = lean_ctor_get(v___y_3723_, 3);
v_maxRecDepth_3740_ = lean_ctor_get(v___y_3723_, 4);
v_ref_3741_ = lean_ctor_get(v___y_3723_, 5);
v_currNamespace_3742_ = lean_ctor_get(v___y_3723_, 6);
v_openDecls_3743_ = lean_ctor_get(v___y_3723_, 7);
v_initHeartbeats_3744_ = lean_ctor_get(v___y_3723_, 8);
v_maxHeartbeats_3745_ = lean_ctor_get(v___y_3723_, 9);
v_quotContext_3746_ = lean_ctor_get(v___y_3723_, 10);
v_currMacroScope_3747_ = lean_ctor_get(v___y_3723_, 11);
v_diag_3748_ = lean_ctor_get_uint8(v___y_3723_, sizeof(void*)*14);
v_cancelTk_x3f_3749_ = lean_ctor_get(v___y_3723_, 12);
v_suppressElabErrors_3750_ = lean_ctor_get_uint8(v___y_3723_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3751_ = lean_ctor_get(v___y_3723_, 13);
v___x_3757_ = lean_unsigned_to_nat(0u);
v___x_3758_ = lean_nat_dec_eq(v_maxRecDepth_3740_, v___x_3757_);
if (v___x_3758_ == 0)
{
uint8_t v___x_3759_; 
v___x_3759_ = lean_nat_dec_eq(v_currRecDepth_3739_, v_maxRecDepth_3740_);
if (v___x_3759_ == 0)
{
goto v___jp_3752_;
}
else
{
lean_object* v___x_3760_; 
lean_dec_ref(v_x_3719_);
lean_inc(v_ref_3741_);
v___x_3760_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg(v_ref_3741_);
v___y_3727_ = v___x_3760_;
goto v___jp_3726_;
}
}
else
{
goto v___jp_3752_;
}
v___jp_3726_:
{
if (lean_obj_tag(v___y_3727_) == 0)
{
return v___y_3727_;
}
else
{
lean_object* v_a_3728_; lean_object* v___x_3730_; uint8_t v_isShared_3731_; uint8_t v_isSharedCheck_3735_; 
v_a_3728_ = lean_ctor_get(v___y_3727_, 0);
v_isSharedCheck_3735_ = !lean_is_exclusive(v___y_3727_);
if (v_isSharedCheck_3735_ == 0)
{
v___x_3730_ = v___y_3727_;
v_isShared_3731_ = v_isSharedCheck_3735_;
goto v_resetjp_3729_;
}
else
{
lean_inc(v_a_3728_);
lean_dec(v___y_3727_);
v___x_3730_ = lean_box(0);
v_isShared_3731_ = v_isSharedCheck_3735_;
goto v_resetjp_3729_;
}
v_resetjp_3729_:
{
lean_object* v___x_3733_; 
if (v_isShared_3731_ == 0)
{
v___x_3733_ = v___x_3730_;
goto v_reusejp_3732_;
}
else
{
lean_object* v_reuseFailAlloc_3734_; 
v_reuseFailAlloc_3734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3734_, 0, v_a_3728_);
v___x_3733_ = v_reuseFailAlloc_3734_;
goto v_reusejp_3732_;
}
v_reusejp_3732_:
{
return v___x_3733_;
}
}
}
}
v___jp_3752_:
{
lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; 
v___x_3753_ = lean_unsigned_to_nat(1u);
v___x_3754_ = lean_nat_add(v_currRecDepth_3739_, v___x_3753_);
lean_inc_ref(v_inheritedTraceOptions_3751_);
lean_inc(v_cancelTk_x3f_3749_);
lean_inc(v_currMacroScope_3747_);
lean_inc(v_quotContext_3746_);
lean_inc(v_maxHeartbeats_3745_);
lean_inc(v_initHeartbeats_3744_);
lean_inc(v_openDecls_3743_);
lean_inc(v_currNamespace_3742_);
lean_inc(v_ref_3741_);
lean_inc(v_maxRecDepth_3740_);
lean_inc_ref(v_options_3738_);
lean_inc_ref(v_fileMap_3737_);
lean_inc_ref(v_fileName_3736_);
v___x_3755_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3755_, 0, v_fileName_3736_);
lean_ctor_set(v___x_3755_, 1, v_fileMap_3737_);
lean_ctor_set(v___x_3755_, 2, v_options_3738_);
lean_ctor_set(v___x_3755_, 3, v___x_3754_);
lean_ctor_set(v___x_3755_, 4, v_maxRecDepth_3740_);
lean_ctor_set(v___x_3755_, 5, v_ref_3741_);
lean_ctor_set(v___x_3755_, 6, v_currNamespace_3742_);
lean_ctor_set(v___x_3755_, 7, v_openDecls_3743_);
lean_ctor_set(v___x_3755_, 8, v_initHeartbeats_3744_);
lean_ctor_set(v___x_3755_, 9, v_maxHeartbeats_3745_);
lean_ctor_set(v___x_3755_, 10, v_quotContext_3746_);
lean_ctor_set(v___x_3755_, 11, v_currMacroScope_3747_);
lean_ctor_set(v___x_3755_, 12, v_cancelTk_x3f_3749_);
lean_ctor_set(v___x_3755_, 13, v_inheritedTraceOptions_3751_);
lean_ctor_set_uint8(v___x_3755_, sizeof(void*)*14, v_diag_3748_);
lean_ctor_set_uint8(v___x_3755_, sizeof(void*)*14 + 1, v_suppressElabErrors_3750_);
lean_inc(v___y_3724_);
lean_inc(v___y_3722_);
lean_inc_ref(v___y_3721_);
lean_inc(v___y_3720_);
v___x_3756_ = lean_apply_6(v_x_3719_, v___y_3720_, v___y_3721_, v___y_3722_, v___x_3755_, v___y_3724_, lean_box(0));
v___y_3727_ = v___x_3756_;
goto v___jp_3726_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg___boxed(lean_object* v_x_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_){
_start:
{
lean_object* v_res_3768_; 
v_res_3768_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg(v_x_3761_, v___y_3762_, v___y_3763_, v___y_3764_, v___y_3765_, v___y_3766_);
lean_dec(v___y_3766_);
lean_dec_ref(v___y_3765_);
lean_dec(v___y_3764_);
lean_dec_ref(v___y_3763_);
lean_dec(v___y_3762_);
return v_res_3768_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___lam__0(lean_object* v_fvars_3769_, lean_object* v_pre_3770_, lean_object* v_post_3771_, uint8_t v_usedLetOnly_3772_, uint8_t v_skipConstInApp_3773_, uint8_t v_skipInstances_3774_, lean_object* v_body_3775_, lean_object* v_x_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_){
_start:
{
lean_object* v___x_3783_; lean_object* v___x_3784_; 
v___x_3783_ = lean_array_push(v_fvars_3769_, v_x_3776_);
v___x_3784_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6(v_pre_3770_, v_post_3771_, v_usedLetOnly_3772_, v_skipConstInApp_3773_, v_skipInstances_3774_, v___x_3783_, v_body_3775_, v___y_3777_, v___y_3778_, v___y_3779_, v___y_3780_, v___y_3781_);
return v___x_3784_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___lam__0___boxed(lean_object* v_fvars_3785_, lean_object* v_pre_3786_, lean_object* v_post_3787_, lean_object* v_usedLetOnly_3788_, lean_object* v_skipConstInApp_3789_, lean_object* v_skipInstances_3790_, lean_object* v_body_3791_, lean_object* v_x_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_){
_start:
{
uint8_t v_usedLetOnly_boxed_3799_; uint8_t v_skipConstInApp_boxed_3800_; uint8_t v_skipInstances_boxed_3801_; lean_object* v_res_3802_; 
v_usedLetOnly_boxed_3799_ = lean_unbox(v_usedLetOnly_3788_);
v_skipConstInApp_boxed_3800_ = lean_unbox(v_skipConstInApp_3789_);
v_skipInstances_boxed_3801_ = lean_unbox(v_skipInstances_3790_);
v_res_3802_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___lam__0(v_fvars_3785_, v_pre_3786_, v_post_3787_, v_usedLetOnly_boxed_3799_, v_skipConstInApp_boxed_3800_, v_skipInstances_boxed_3801_, v_body_3791_, v_x_3792_, v___y_3793_, v___y_3794_, v___y_3795_, v___y_3796_, v___y_3797_);
lean_dec(v___y_3797_);
lean_dec_ref(v___y_3796_);
lean_dec(v___y_3795_);
lean_dec_ref(v___y_3794_);
lean_dec(v___y_3793_);
return v_res_3802_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(lean_object* v_pre_3803_, lean_object* v_post_3804_, uint8_t v_usedLetOnly_3805_, uint8_t v_skipConstInApp_3806_, uint8_t v_skipInstances_3807_, lean_object* v_e_3808_, lean_object* v_a_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_){
_start:
{
lean_object* v___x_3815_; 
lean_inc_ref(v_post_3804_);
lean_inc(v___y_3813_);
lean_inc_ref(v___y_3812_);
lean_inc(v___y_3811_);
lean_inc_ref(v___y_3810_);
lean_inc_ref(v_e_3808_);
v___x_3815_ = lean_apply_6(v_post_3804_, v_e_3808_, v___y_3810_, v___y_3811_, v___y_3812_, v___y_3813_, lean_box(0));
if (lean_obj_tag(v___x_3815_) == 0)
{
lean_object* v_a_3816_; lean_object* v___x_3818_; uint8_t v_isShared_3819_; uint8_t v_isSharedCheck_3834_; 
v_a_3816_ = lean_ctor_get(v___x_3815_, 0);
v_isSharedCheck_3834_ = !lean_is_exclusive(v___x_3815_);
if (v_isSharedCheck_3834_ == 0)
{
v___x_3818_ = v___x_3815_;
v_isShared_3819_ = v_isSharedCheck_3834_;
goto v_resetjp_3817_;
}
else
{
lean_inc(v_a_3816_);
lean_dec(v___x_3815_);
v___x_3818_ = lean_box(0);
v_isShared_3819_ = v_isSharedCheck_3834_;
goto v_resetjp_3817_;
}
v_resetjp_3817_:
{
switch(lean_obj_tag(v_a_3816_))
{
case 0:
{
lean_object* v_e_3820_; lean_object* v___x_3822_; 
lean_dec_ref(v_e_3808_);
lean_dec_ref(v_post_3804_);
lean_dec_ref(v_pre_3803_);
v_e_3820_ = lean_ctor_get(v_a_3816_, 0);
lean_inc_ref(v_e_3820_);
lean_dec_ref(v_a_3816_);
if (v_isShared_3819_ == 0)
{
lean_ctor_set(v___x_3818_, 0, v_e_3820_);
v___x_3822_ = v___x_3818_;
goto v_reusejp_3821_;
}
else
{
lean_object* v_reuseFailAlloc_3823_; 
v_reuseFailAlloc_3823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3823_, 0, v_e_3820_);
v___x_3822_ = v_reuseFailAlloc_3823_;
goto v_reusejp_3821_;
}
v_reusejp_3821_:
{
return v___x_3822_;
}
}
case 1:
{
lean_object* v_e_3824_; lean_object* v___x_3825_; 
lean_del_object(v___x_3818_);
lean_dec_ref(v_e_3808_);
v_e_3824_ = lean_ctor_get(v_a_3816_, 0);
lean_inc_ref(v_e_3824_);
lean_dec_ref(v_a_3816_);
v___x_3825_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3803_, v_post_3804_, v_usedLetOnly_3805_, v_skipConstInApp_3806_, v_skipInstances_3807_, v_e_3824_, v_a_3809_, v___y_3810_, v___y_3811_, v___y_3812_, v___y_3813_);
return v___x_3825_;
}
default: 
{
lean_object* v_e_x3f_3826_; 
lean_dec_ref(v_post_3804_);
lean_dec_ref(v_pre_3803_);
v_e_x3f_3826_ = lean_ctor_get(v_a_3816_, 0);
lean_inc(v_e_x3f_3826_);
lean_dec_ref(v_a_3816_);
if (lean_obj_tag(v_e_x3f_3826_) == 0)
{
lean_object* v___x_3828_; 
if (v_isShared_3819_ == 0)
{
lean_ctor_set(v___x_3818_, 0, v_e_3808_);
v___x_3828_ = v___x_3818_;
goto v_reusejp_3827_;
}
else
{
lean_object* v_reuseFailAlloc_3829_; 
v_reuseFailAlloc_3829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3829_, 0, v_e_3808_);
v___x_3828_ = v_reuseFailAlloc_3829_;
goto v_reusejp_3827_;
}
v_reusejp_3827_:
{
return v___x_3828_;
}
}
else
{
lean_object* v_val_3830_; lean_object* v___x_3832_; 
lean_dec_ref(v_e_3808_);
v_val_3830_ = lean_ctor_get(v_e_x3f_3826_, 0);
lean_inc(v_val_3830_);
lean_dec_ref(v_e_x3f_3826_);
if (v_isShared_3819_ == 0)
{
lean_ctor_set(v___x_3818_, 0, v_val_3830_);
v___x_3832_ = v___x_3818_;
goto v_reusejp_3831_;
}
else
{
lean_object* v_reuseFailAlloc_3833_; 
v_reuseFailAlloc_3833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3833_, 0, v_val_3830_);
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
else
{
lean_object* v_a_3835_; lean_object* v___x_3837_; uint8_t v_isShared_3838_; uint8_t v_isSharedCheck_3842_; 
lean_dec_ref(v_e_3808_);
lean_dec_ref(v_post_3804_);
lean_dec_ref(v_pre_3803_);
v_a_3835_ = lean_ctor_get(v___x_3815_, 0);
v_isSharedCheck_3842_ = !lean_is_exclusive(v___x_3815_);
if (v_isSharedCheck_3842_ == 0)
{
v___x_3837_ = v___x_3815_;
v_isShared_3838_ = v_isSharedCheck_3842_;
goto v_resetjp_3836_;
}
else
{
lean_inc(v_a_3835_);
lean_dec(v___x_3815_);
v___x_3837_ = lean_box(0);
v_isShared_3838_ = v_isSharedCheck_3842_;
goto v_resetjp_3836_;
}
v_resetjp_3836_:
{
lean_object* v___x_3840_; 
if (v_isShared_3838_ == 0)
{
v___x_3840_ = v___x_3837_;
goto v_reusejp_3839_;
}
else
{
lean_object* v_reuseFailAlloc_3841_; 
v_reuseFailAlloc_3841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3841_, 0, v_a_3835_);
v___x_3840_ = v_reuseFailAlloc_3841_;
goto v_reusejp_3839_;
}
v_reusejp_3839_:
{
return v___x_3840_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6(lean_object* v_pre_3843_, lean_object* v_post_3844_, uint8_t v_usedLetOnly_3845_, uint8_t v_skipConstInApp_3846_, uint8_t v_skipInstances_3847_, lean_object* v_fvars_3848_, lean_object* v_e_3849_, lean_object* v_a_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_){
_start:
{
if (lean_obj_tag(v_e_3849_) == 6)
{
lean_object* v_binderName_3856_; lean_object* v_binderType_3857_; lean_object* v_body_3858_; uint8_t v_binderInfo_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; 
v_binderName_3856_ = lean_ctor_get(v_e_3849_, 0);
lean_inc(v_binderName_3856_);
v_binderType_3857_ = lean_ctor_get(v_e_3849_, 1);
lean_inc_ref(v_binderType_3857_);
v_body_3858_ = lean_ctor_get(v_e_3849_, 2);
lean_inc_ref(v_body_3858_);
v_binderInfo_3859_ = lean_ctor_get_uint8(v_e_3849_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_3849_);
v___x_3860_ = lean_expr_instantiate_rev(v_binderType_3857_, v_fvars_3848_);
lean_dec_ref(v_binderType_3857_);
lean_inc_ref(v_post_3844_);
lean_inc_ref(v_pre_3843_);
v___x_3861_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3843_, v_post_3844_, v_usedLetOnly_3845_, v_skipConstInApp_3846_, v_skipInstances_3847_, v___x_3860_, v_a_3850_, v___y_3851_, v___y_3852_, v___y_3853_, v___y_3854_);
if (lean_obj_tag(v___x_3861_) == 0)
{
lean_object* v_a_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___f_3866_; uint8_t v___x_3867_; lean_object* v___x_3868_; 
v_a_3862_ = lean_ctor_get(v___x_3861_, 0);
lean_inc(v_a_3862_);
lean_dec_ref(v___x_3861_);
v___x_3863_ = lean_box(v_usedLetOnly_3845_);
v___x_3864_ = lean_box(v_skipConstInApp_3846_);
v___x_3865_ = lean_box(v_skipInstances_3847_);
v___f_3866_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___lam__0___boxed), 14, 7);
lean_closure_set(v___f_3866_, 0, v_fvars_3848_);
lean_closure_set(v___f_3866_, 1, v_pre_3843_);
lean_closure_set(v___f_3866_, 2, v_post_3844_);
lean_closure_set(v___f_3866_, 3, v___x_3863_);
lean_closure_set(v___f_3866_, 4, v___x_3864_);
lean_closure_set(v___f_3866_, 5, v___x_3865_);
lean_closure_set(v___f_3866_, 6, v_body_3858_);
v___x_3867_ = 0;
v___x_3868_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_binderName_3856_, v_binderInfo_3859_, v_a_3862_, v___f_3866_, v___x_3867_, v_a_3850_, v___y_3851_, v___y_3852_, v___y_3853_, v___y_3854_);
return v___x_3868_;
}
else
{
lean_dec_ref(v_body_3858_);
lean_dec(v_binderName_3856_);
lean_dec_ref(v_fvars_3848_);
lean_dec_ref(v_post_3844_);
lean_dec_ref(v_pre_3843_);
return v___x_3861_;
}
}
else
{
lean_object* v___x_3869_; lean_object* v___x_3870_; 
v___x_3869_ = lean_expr_instantiate_rev(v_e_3849_, v_fvars_3848_);
lean_dec_ref(v_e_3849_);
lean_inc_ref(v_post_3844_);
lean_inc_ref(v_pre_3843_);
v___x_3870_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3843_, v_post_3844_, v_usedLetOnly_3845_, v_skipConstInApp_3846_, v_skipInstances_3847_, v___x_3869_, v_a_3850_, v___y_3851_, v___y_3852_, v___y_3853_, v___y_3854_);
if (lean_obj_tag(v___x_3870_) == 0)
{
lean_object* v_a_3871_; uint8_t v___x_3872_; uint8_t v___x_3873_; uint8_t v___x_3874_; lean_object* v___x_3875_; 
v_a_3871_ = lean_ctor_get(v___x_3870_, 0);
lean_inc(v_a_3871_);
lean_dec_ref(v___x_3870_);
v___x_3872_ = 0;
v___x_3873_ = 1;
v___x_3874_ = 1;
v___x_3875_ = l_Lean_Meta_mkLambdaFVars(v_fvars_3848_, v_a_3871_, v___x_3872_, v_usedLetOnly_3845_, v___x_3872_, v___x_3873_, v___x_3874_, v___y_3851_, v___y_3852_, v___y_3853_, v___y_3854_);
lean_dec_ref(v_fvars_3848_);
if (lean_obj_tag(v___x_3875_) == 0)
{
lean_object* v_a_3876_; lean_object* v___x_3877_; 
v_a_3876_ = lean_ctor_get(v___x_3875_, 0);
lean_inc(v_a_3876_);
lean_dec_ref(v___x_3875_);
v___x_3877_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_3843_, v_post_3844_, v_usedLetOnly_3845_, v_skipConstInApp_3846_, v_skipInstances_3847_, v_a_3876_, v_a_3850_, v___y_3851_, v___y_3852_, v___y_3853_, v___y_3854_);
return v___x_3877_;
}
else
{
lean_dec_ref(v_post_3844_);
lean_dec_ref(v_pre_3843_);
return v___x_3875_;
}
}
else
{
lean_dec_ref(v_fvars_3848_);
lean_dec_ref(v_post_3844_);
lean_dec_ref(v_pre_3843_);
return v___x_3870_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___lam__0(lean_object* v_fvars_3878_, lean_object* v_pre_3879_, lean_object* v_post_3880_, uint8_t v_usedLetOnly_3881_, uint8_t v_skipConstInApp_3882_, uint8_t v_skipInstances_3883_, lean_object* v_body_3884_, lean_object* v_x_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_){
_start:
{
lean_object* v___x_3892_; lean_object* v___x_3893_; 
v___x_3892_ = lean_array_push(v_fvars_3878_, v_x_3885_);
v___x_3893_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7(v_pre_3879_, v_post_3880_, v_usedLetOnly_3881_, v_skipConstInApp_3882_, v_skipInstances_3883_, v___x_3892_, v_body_3884_, v___y_3886_, v___y_3887_, v___y_3888_, v___y_3889_, v___y_3890_);
return v___x_3893_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___lam__0___boxed(lean_object* v_fvars_3894_, lean_object* v_pre_3895_, lean_object* v_post_3896_, lean_object* v_usedLetOnly_3897_, lean_object* v_skipConstInApp_3898_, lean_object* v_skipInstances_3899_, lean_object* v_body_3900_, lean_object* v_x_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_){
_start:
{
uint8_t v_usedLetOnly_boxed_3908_; uint8_t v_skipConstInApp_boxed_3909_; uint8_t v_skipInstances_boxed_3910_; lean_object* v_res_3911_; 
v_usedLetOnly_boxed_3908_ = lean_unbox(v_usedLetOnly_3897_);
v_skipConstInApp_boxed_3909_ = lean_unbox(v_skipConstInApp_3898_);
v_skipInstances_boxed_3910_ = lean_unbox(v_skipInstances_3899_);
v_res_3911_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___lam__0(v_fvars_3894_, v_pre_3895_, v_post_3896_, v_usedLetOnly_boxed_3908_, v_skipConstInApp_boxed_3909_, v_skipInstances_boxed_3910_, v_body_3900_, v_x_3901_, v___y_3902_, v___y_3903_, v___y_3904_, v___y_3905_, v___y_3906_);
lean_dec(v___y_3906_);
lean_dec_ref(v___y_3905_);
lean_dec(v___y_3904_);
lean_dec_ref(v___y_3903_);
lean_dec(v___y_3902_);
return v_res_3911_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7(lean_object* v_pre_3912_, lean_object* v_post_3913_, uint8_t v_usedLetOnly_3914_, uint8_t v_skipConstInApp_3915_, uint8_t v_skipInstances_3916_, lean_object* v_fvars_3917_, lean_object* v_e_3918_, lean_object* v_a_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_){
_start:
{
if (lean_obj_tag(v_e_3918_) == 8)
{
lean_object* v_declName_3925_; lean_object* v_type_3926_; lean_object* v_value_3927_; lean_object* v_body_3928_; uint8_t v_nondep_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; 
v_declName_3925_ = lean_ctor_get(v_e_3918_, 0);
lean_inc(v_declName_3925_);
v_type_3926_ = lean_ctor_get(v_e_3918_, 1);
lean_inc_ref(v_type_3926_);
v_value_3927_ = lean_ctor_get(v_e_3918_, 2);
lean_inc_ref(v_value_3927_);
v_body_3928_ = lean_ctor_get(v_e_3918_, 3);
lean_inc_ref(v_body_3928_);
v_nondep_3929_ = lean_ctor_get_uint8(v_e_3918_, sizeof(void*)*4 + 8);
lean_dec_ref(v_e_3918_);
v___x_3930_ = lean_expr_instantiate_rev(v_type_3926_, v_fvars_3917_);
lean_dec_ref(v_type_3926_);
lean_inc_ref(v_post_3913_);
lean_inc_ref(v_pre_3912_);
v___x_3931_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3912_, v_post_3913_, v_usedLetOnly_3914_, v_skipConstInApp_3915_, v_skipInstances_3916_, v___x_3930_, v_a_3919_, v___y_3920_, v___y_3921_, v___y_3922_, v___y_3923_);
if (lean_obj_tag(v___x_3931_) == 0)
{
lean_object* v_a_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; 
v_a_3932_ = lean_ctor_get(v___x_3931_, 0);
lean_inc(v_a_3932_);
lean_dec_ref(v___x_3931_);
v___x_3933_ = lean_expr_instantiate_rev(v_value_3927_, v_fvars_3917_);
lean_dec_ref(v_value_3927_);
lean_inc_ref(v_post_3913_);
lean_inc_ref(v_pre_3912_);
v___x_3934_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3912_, v_post_3913_, v_usedLetOnly_3914_, v_skipConstInApp_3915_, v_skipInstances_3916_, v___x_3933_, v_a_3919_, v___y_3920_, v___y_3921_, v___y_3922_, v___y_3923_);
if (lean_obj_tag(v___x_3934_) == 0)
{
lean_object* v_a_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v___f_3939_; uint8_t v___x_3940_; lean_object* v___x_3941_; 
v_a_3935_ = lean_ctor_get(v___x_3934_, 0);
lean_inc(v_a_3935_);
lean_dec_ref(v___x_3934_);
v___x_3936_ = lean_box(v_usedLetOnly_3914_);
v___x_3937_ = lean_box(v_skipConstInApp_3915_);
v___x_3938_ = lean_box(v_skipInstances_3916_);
v___f_3939_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___lam__0___boxed), 14, 7);
lean_closure_set(v___f_3939_, 0, v_fvars_3917_);
lean_closure_set(v___f_3939_, 1, v_pre_3912_);
lean_closure_set(v___f_3939_, 2, v_post_3913_);
lean_closure_set(v___f_3939_, 3, v___x_3936_);
lean_closure_set(v___f_3939_, 4, v___x_3937_);
lean_closure_set(v___f_3939_, 5, v___x_3938_);
lean_closure_set(v___f_3939_, 6, v_body_3928_);
v___x_3940_ = 0;
v___x_3941_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg(v_declName_3925_, v_a_3932_, v_a_3935_, v___f_3939_, v_nondep_3929_, v___x_3940_, v_a_3919_, v___y_3920_, v___y_3921_, v___y_3922_, v___y_3923_);
return v___x_3941_;
}
else
{
lean_dec(v_a_3932_);
lean_dec_ref(v_body_3928_);
lean_dec(v_declName_3925_);
lean_dec_ref(v_fvars_3917_);
lean_dec_ref(v_post_3913_);
lean_dec_ref(v_pre_3912_);
return v___x_3934_;
}
}
else
{
lean_dec_ref(v_body_3928_);
lean_dec_ref(v_value_3927_);
lean_dec(v_declName_3925_);
lean_dec_ref(v_fvars_3917_);
lean_dec_ref(v_post_3913_);
lean_dec_ref(v_pre_3912_);
return v___x_3931_;
}
}
else
{
lean_object* v___x_3942_; lean_object* v___x_3943_; 
v___x_3942_ = lean_expr_instantiate_rev(v_e_3918_, v_fvars_3917_);
lean_dec_ref(v_e_3918_);
lean_inc_ref(v_post_3913_);
lean_inc_ref(v_pre_3912_);
v___x_3943_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3912_, v_post_3913_, v_usedLetOnly_3914_, v_skipConstInApp_3915_, v_skipInstances_3916_, v___x_3942_, v_a_3919_, v___y_3920_, v___y_3921_, v___y_3922_, v___y_3923_);
if (lean_obj_tag(v___x_3943_) == 0)
{
lean_object* v_a_3944_; uint8_t v___x_3945_; uint8_t v___x_3946_; lean_object* v___x_3947_; 
v_a_3944_ = lean_ctor_get(v___x_3943_, 0);
lean_inc(v_a_3944_);
lean_dec_ref(v___x_3943_);
v___x_3945_ = 0;
v___x_3946_ = 1;
v___x_3947_ = l_Lean_Meta_mkLetFVars(v_fvars_3917_, v_a_3944_, v_usedLetOnly_3914_, v___x_3945_, v___x_3946_, v___y_3920_, v___y_3921_, v___y_3922_, v___y_3923_);
lean_dec_ref(v_fvars_3917_);
if (lean_obj_tag(v___x_3947_) == 0)
{
lean_object* v_a_3948_; lean_object* v___x_3949_; 
v_a_3948_ = lean_ctor_get(v___x_3947_, 0);
lean_inc(v_a_3948_);
lean_dec_ref(v___x_3947_);
v___x_3949_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_3912_, v_post_3913_, v_usedLetOnly_3914_, v_skipConstInApp_3915_, v_skipInstances_3916_, v_a_3948_, v_a_3919_, v___y_3920_, v___y_3921_, v___y_3922_, v___y_3923_);
return v___x_3949_;
}
else
{
lean_dec_ref(v_post_3913_);
lean_dec_ref(v_pre_3912_);
return v___x_3947_;
}
}
else
{
lean_dec_ref(v_fvars_3917_);
lean_dec_ref(v_post_3913_);
lean_dec_ref(v_pre_3912_);
return v___x_3943_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__2(lean_object* v_pre_3950_, lean_object* v_post_3951_, uint8_t v_usedLetOnly_3952_, uint8_t v_skipConstInApp_3953_, uint8_t v_skipInstances_3954_, size_t v_sz_3955_, size_t v_i_3956_, lean_object* v_bs_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_){
_start:
{
uint8_t v___x_3964_; 
v___x_3964_ = lean_usize_dec_lt(v_i_3956_, v_sz_3955_);
if (v___x_3964_ == 0)
{
lean_object* v___x_3965_; 
lean_dec_ref(v_post_3951_);
lean_dec_ref(v_pre_3950_);
v___x_3965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3965_, 0, v_bs_3957_);
return v___x_3965_;
}
else
{
lean_object* v_v_3966_; lean_object* v___x_3967_; 
v_v_3966_ = lean_array_uget_borrowed(v_bs_3957_, v_i_3956_);
lean_inc(v_v_3966_);
lean_inc_ref(v_post_3951_);
lean_inc_ref(v_pre_3950_);
v___x_3967_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3950_, v_post_3951_, v_usedLetOnly_3952_, v_skipConstInApp_3953_, v_skipInstances_3954_, v_v_3966_, v___y_3958_, v___y_3959_, v___y_3960_, v___y_3961_, v___y_3962_);
if (lean_obj_tag(v___x_3967_) == 0)
{
lean_object* v_a_3968_; lean_object* v___x_3969_; lean_object* v_bs_x27_3970_; size_t v___x_3971_; size_t v___x_3972_; lean_object* v___x_3973_; 
v_a_3968_ = lean_ctor_get(v___x_3967_, 0);
lean_inc(v_a_3968_);
lean_dec_ref(v___x_3967_);
v___x_3969_ = lean_unsigned_to_nat(0u);
v_bs_x27_3970_ = lean_array_uset(v_bs_3957_, v_i_3956_, v___x_3969_);
v___x_3971_ = ((size_t)1ULL);
v___x_3972_ = lean_usize_add(v_i_3956_, v___x_3971_);
v___x_3973_ = lean_array_uset(v_bs_x27_3970_, v_i_3956_, v_a_3968_);
v_i_3956_ = v___x_3972_;
v_bs_3957_ = v___x_3973_;
goto _start;
}
else
{
lean_object* v_a_3975_; lean_object* v___x_3977_; uint8_t v_isShared_3978_; uint8_t v_isSharedCheck_3982_; 
lean_dec_ref(v_bs_3957_);
lean_dec_ref(v_post_3951_);
lean_dec_ref(v_pre_3950_);
v_a_3975_ = lean_ctor_get(v___x_3967_, 0);
v_isSharedCheck_3982_ = !lean_is_exclusive(v___x_3967_);
if (v_isSharedCheck_3982_ == 0)
{
v___x_3977_ = v___x_3967_;
v_isShared_3978_ = v_isSharedCheck_3982_;
goto v_resetjp_3976_;
}
else
{
lean_inc(v_a_3975_);
lean_dec(v___x_3967_);
v___x_3977_ = lean_box(0);
v_isShared_3978_ = v_isSharedCheck_3982_;
goto v_resetjp_3976_;
}
v_resetjp_3976_:
{
lean_object* v___x_3980_; 
if (v_isShared_3978_ == 0)
{
v___x_3980_ = v___x_3977_;
goto v_reusejp_3979_;
}
else
{
lean_object* v_reuseFailAlloc_3981_; 
v_reuseFailAlloc_3981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3981_, 0, v_a_3975_);
v___x_3980_ = v_reuseFailAlloc_3981_;
goto v_reusejp_3979_;
}
v_reusejp_3979_:
{
return v___x_3980_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0(lean_object* v_pre_3983_, lean_object* v_post_3984_, uint8_t v_usedLetOnly_3985_, uint8_t v_skipConstInApp_3986_, uint8_t v_skipInstances_3987_, lean_object* v___x_3988_, lean_object* v___y_3989_, lean_object* v_b_3990_, lean_object* v_a_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_){
_start:
{
lean_object* v___x_3997_; 
v___x_3997_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3983_, v_post_3984_, v_usedLetOnly_3985_, v_skipConstInApp_3986_, v_skipInstances_3987_, v___x_3988_, v___y_3989_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_);
if (lean_obj_tag(v___x_3997_) == 0)
{
lean_object* v_a_3998_; lean_object* v___x_4000_; uint8_t v_isShared_4001_; uint8_t v_isSharedCheck_4007_; 
v_a_3998_ = lean_ctor_get(v___x_3997_, 0);
v_isSharedCheck_4007_ = !lean_is_exclusive(v___x_3997_);
if (v_isSharedCheck_4007_ == 0)
{
v___x_4000_ = v___x_3997_;
v_isShared_4001_ = v_isSharedCheck_4007_;
goto v_resetjp_3999_;
}
else
{
lean_inc(v_a_3998_);
lean_dec(v___x_3997_);
v___x_4000_ = lean_box(0);
v_isShared_4001_ = v_isSharedCheck_4007_;
goto v_resetjp_3999_;
}
v_resetjp_3999_:
{
lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4005_; 
v___x_4002_ = lean_array_fset(v_b_3990_, v_a_3991_, v_a_3998_);
v___x_4003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4003_, 0, v___x_4002_);
if (v_isShared_4001_ == 0)
{
lean_ctor_set(v___x_4000_, 0, v___x_4003_);
v___x_4005_ = v___x_4000_;
goto v_reusejp_4004_;
}
else
{
lean_object* v_reuseFailAlloc_4006_; 
v_reuseFailAlloc_4006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4006_, 0, v___x_4003_);
v___x_4005_ = v_reuseFailAlloc_4006_;
goto v_reusejp_4004_;
}
v_reusejp_4004_:
{
return v___x_4005_;
}
}
}
else
{
lean_object* v_a_4008_; lean_object* v___x_4010_; uint8_t v_isShared_4011_; uint8_t v_isSharedCheck_4015_; 
lean_dec_ref(v_b_3990_);
v_a_4008_ = lean_ctor_get(v___x_3997_, 0);
v_isSharedCheck_4015_ = !lean_is_exclusive(v___x_3997_);
if (v_isSharedCheck_4015_ == 0)
{
v___x_4010_ = v___x_3997_;
v_isShared_4011_ = v_isSharedCheck_4015_;
goto v_resetjp_4009_;
}
else
{
lean_inc(v_a_4008_);
lean_dec(v___x_3997_);
v___x_4010_ = lean_box(0);
v_isShared_4011_ = v_isSharedCheck_4015_;
goto v_resetjp_4009_;
}
v_resetjp_4009_:
{
lean_object* v___x_4013_; 
if (v_isShared_4011_ == 0)
{
v___x_4013_ = v___x_4010_;
goto v_reusejp_4012_;
}
else
{
lean_object* v_reuseFailAlloc_4014_; 
v_reuseFailAlloc_4014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4014_, 0, v_a_4008_);
v___x_4013_ = v_reuseFailAlloc_4014_;
goto v_reusejp_4012_;
}
v_reusejp_4012_:
{
return v___x_4013_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed(lean_object* v_pre_4016_, lean_object* v_post_4017_, lean_object* v_usedLetOnly_4018_, lean_object* v_skipConstInApp_4019_, lean_object* v_skipInstances_4020_, lean_object* v___x_4021_, lean_object* v___y_4022_, lean_object* v_b_4023_, lean_object* v_a_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_){
_start:
{
uint8_t v_usedLetOnly_boxed_4030_; uint8_t v_skipConstInApp_boxed_4031_; uint8_t v_skipInstances_boxed_4032_; lean_object* v_res_4033_; 
v_usedLetOnly_boxed_4030_ = lean_unbox(v_usedLetOnly_4018_);
v_skipConstInApp_boxed_4031_ = lean_unbox(v_skipConstInApp_4019_);
v_skipInstances_boxed_4032_ = lean_unbox(v_skipInstances_4020_);
v_res_4033_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0(v_pre_4016_, v_post_4017_, v_usedLetOnly_boxed_4030_, v_skipConstInApp_boxed_4031_, v_skipInstances_boxed_4032_, v___x_4021_, v___y_4022_, v_b_4023_, v_a_4024_, v___y_4025_, v___y_4026_, v___y_4027_, v___y_4028_);
lean_dec(v___y_4028_);
lean_dec_ref(v___y_4027_);
lean_dec(v___y_4026_);
lean_dec_ref(v___y_4025_);
lean_dec(v_a_4024_);
lean_dec(v___y_4022_);
return v_res_4033_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg(lean_object* v_upperBound_4034_, lean_object* v___x_4035_, lean_object* v_pre_4036_, lean_object* v_post_4037_, uint8_t v_usedLetOnly_4038_, uint8_t v_skipConstInApp_4039_, uint8_t v_skipInstances_4040_, lean_object* v_a_4041_, lean_object* v_b_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_){
_start:
{
lean_object* v___y_4050_; uint8_t v___x_4073_; 
v___x_4073_ = lean_nat_dec_lt(v_a_4041_, v_upperBound_4034_);
if (v___x_4073_ == 0)
{
lean_object* v___x_4074_; 
lean_dec(v_a_4041_);
lean_dec_ref(v_post_4037_);
lean_dec_ref(v_pre_4036_);
v___x_4074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4074_, 0, v_b_4042_);
return v___x_4074_;
}
else
{
lean_object* v___x_4075_; lean_object* v___x_4076_; uint8_t v___x_4077_; 
v___x_4075_ = lean_array_fget_borrowed(v_b_4042_, v_a_4041_);
v___x_4076_ = lean_array_get_size(v___x_4035_);
v___x_4077_ = lean_nat_dec_lt(v_a_4041_, v___x_4076_);
if (v___x_4077_ == 0)
{
lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___f_4081_; 
lean_inc(v___x_4075_);
v___x_4078_ = lean_box(v_usedLetOnly_4038_);
v___x_4079_ = lean_box(v_skipConstInApp_4039_);
v___x_4080_ = lean_box(v_skipInstances_4040_);
lean_inc(v_a_4041_);
lean_inc(v___y_4043_);
lean_inc_ref(v_post_4037_);
lean_inc_ref(v_pre_4036_);
v___f_4081_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_4081_, 0, v_pre_4036_);
lean_closure_set(v___f_4081_, 1, v_post_4037_);
lean_closure_set(v___f_4081_, 2, v___x_4078_);
lean_closure_set(v___f_4081_, 3, v___x_4079_);
lean_closure_set(v___f_4081_, 4, v___x_4080_);
lean_closure_set(v___f_4081_, 5, v___x_4075_);
lean_closure_set(v___f_4081_, 6, v___y_4043_);
lean_closure_set(v___f_4081_, 7, v_b_4042_);
lean_closure_set(v___f_4081_, 8, v_a_4041_);
v___y_4050_ = v___f_4081_;
goto v___jp_4049_;
}
else
{
lean_object* v___x_4082_; uint8_t v_isInstance_4083_; 
v___x_4082_ = lean_array_fget_borrowed(v___x_4035_, v_a_4041_);
v_isInstance_4083_ = lean_ctor_get_uint8(v___x_4082_, sizeof(void*)*1 + 4);
if (v_isInstance_4083_ == 0)
{
lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___f_4087_; 
lean_inc(v___x_4075_);
v___x_4084_ = lean_box(v_usedLetOnly_4038_);
v___x_4085_ = lean_box(v_skipConstInApp_4039_);
v___x_4086_ = lean_box(v_skipInstances_4040_);
lean_inc(v_a_4041_);
lean_inc(v___y_4043_);
lean_inc_ref(v_post_4037_);
lean_inc_ref(v_pre_4036_);
v___f_4087_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_4087_, 0, v_pre_4036_);
lean_closure_set(v___f_4087_, 1, v_post_4037_);
lean_closure_set(v___f_4087_, 2, v___x_4084_);
lean_closure_set(v___f_4087_, 3, v___x_4085_);
lean_closure_set(v___f_4087_, 4, v___x_4086_);
lean_closure_set(v___f_4087_, 5, v___x_4075_);
lean_closure_set(v___f_4087_, 6, v___y_4043_);
lean_closure_set(v___f_4087_, 7, v_b_4042_);
lean_closure_set(v___f_4087_, 8, v_a_4041_);
v___y_4050_ = v___f_4087_;
goto v___jp_4049_;
}
else
{
lean_object* v___x_4088_; lean_object* v___f_4089_; 
v___x_4088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4088_, 0, v_b_4042_);
v___f_4089_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_4089_, 0, v___x_4088_);
v___y_4050_ = v___f_4089_;
goto v___jp_4049_;
}
}
}
v___jp_4049_:
{
lean_object* v___x_4051_; 
lean_inc(v___y_4047_);
lean_inc_ref(v___y_4046_);
lean_inc(v___y_4045_);
lean_inc_ref(v___y_4044_);
v___x_4051_ = lean_apply_5(v___y_4050_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_, lean_box(0));
if (lean_obj_tag(v___x_4051_) == 0)
{
lean_object* v_a_4052_; lean_object* v___x_4054_; uint8_t v_isShared_4055_; uint8_t v_isSharedCheck_4064_; 
v_a_4052_ = lean_ctor_get(v___x_4051_, 0);
v_isSharedCheck_4064_ = !lean_is_exclusive(v___x_4051_);
if (v_isSharedCheck_4064_ == 0)
{
v___x_4054_ = v___x_4051_;
v_isShared_4055_ = v_isSharedCheck_4064_;
goto v_resetjp_4053_;
}
else
{
lean_inc(v_a_4052_);
lean_dec(v___x_4051_);
v___x_4054_ = lean_box(0);
v_isShared_4055_ = v_isSharedCheck_4064_;
goto v_resetjp_4053_;
}
v_resetjp_4053_:
{
if (lean_obj_tag(v_a_4052_) == 0)
{
lean_object* v_a_4056_; lean_object* v___x_4058_; 
lean_dec(v_a_4041_);
lean_dec_ref(v_post_4037_);
lean_dec_ref(v_pre_4036_);
v_a_4056_ = lean_ctor_get(v_a_4052_, 0);
lean_inc(v_a_4056_);
lean_dec_ref(v_a_4052_);
if (v_isShared_4055_ == 0)
{
lean_ctor_set(v___x_4054_, 0, v_a_4056_);
v___x_4058_ = v___x_4054_;
goto v_reusejp_4057_;
}
else
{
lean_object* v_reuseFailAlloc_4059_; 
v_reuseFailAlloc_4059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4059_, 0, v_a_4056_);
v___x_4058_ = v_reuseFailAlloc_4059_;
goto v_reusejp_4057_;
}
v_reusejp_4057_:
{
return v___x_4058_;
}
}
else
{
lean_object* v_a_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; 
lean_del_object(v___x_4054_);
v_a_4060_ = lean_ctor_get(v_a_4052_, 0);
lean_inc(v_a_4060_);
lean_dec_ref(v_a_4052_);
v___x_4061_ = lean_unsigned_to_nat(1u);
v___x_4062_ = lean_nat_add(v_a_4041_, v___x_4061_);
lean_dec(v_a_4041_);
v_a_4041_ = v___x_4062_;
v_b_4042_ = v_a_4060_;
goto _start;
}
}
}
else
{
lean_object* v_a_4065_; lean_object* v___x_4067_; uint8_t v_isShared_4068_; uint8_t v_isSharedCheck_4072_; 
lean_dec(v_a_4041_);
lean_dec_ref(v_post_4037_);
lean_dec_ref(v_pre_4036_);
v_a_4065_ = lean_ctor_get(v___x_4051_, 0);
v_isSharedCheck_4072_ = !lean_is_exclusive(v___x_4051_);
if (v_isSharedCheck_4072_ == 0)
{
v___x_4067_ = v___x_4051_;
v_isShared_4068_ = v_isSharedCheck_4072_;
goto v_resetjp_4066_;
}
else
{
lean_inc(v_a_4065_);
lean_dec(v___x_4051_);
v___x_4067_ = lean_box(0);
v_isShared_4068_ = v_isSharedCheck_4072_;
goto v_resetjp_4066_;
}
v_resetjp_4066_:
{
lean_object* v___x_4070_; 
if (v_isShared_4068_ == 0)
{
v___x_4070_ = v___x_4067_;
goto v_reusejp_4069_;
}
else
{
lean_object* v_reuseFailAlloc_4071_; 
v_reuseFailAlloc_4071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4071_, 0, v_a_4065_);
v___x_4070_ = v_reuseFailAlloc_4071_;
goto v_reusejp_4069_;
}
v_reusejp_4069_:
{
return v___x_4070_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__8(uint8_t v_skipInstances_4090_, lean_object* v_pre_4091_, lean_object* v_post_4092_, uint8_t v_usedLetOnly_4093_, uint8_t v_skipConstInApp_4094_, lean_object* v_x_4095_, lean_object* v_x_4096_, lean_object* v_x_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_){
_start:
{
lean_object* v_f_4105_; lean_object* v___y_4106_; lean_object* v___y_4107_; lean_object* v___y_4108_; lean_object* v___y_4109_; lean_object* v___y_4110_; 
if (lean_obj_tag(v_x_4095_) == 5)
{
lean_object* v_fn_4153_; lean_object* v_arg_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; 
v_fn_4153_ = lean_ctor_get(v_x_4095_, 0);
lean_inc_ref(v_fn_4153_);
v_arg_4154_ = lean_ctor_get(v_x_4095_, 1);
lean_inc_ref(v_arg_4154_);
lean_dec_ref(v_x_4095_);
v___x_4155_ = lean_array_set(v_x_4096_, v_x_4097_, v_arg_4154_);
v___x_4156_ = lean_unsigned_to_nat(1u);
v___x_4157_ = lean_nat_sub(v_x_4097_, v___x_4156_);
lean_dec(v_x_4097_);
v_x_4095_ = v_fn_4153_;
v_x_4096_ = v___x_4155_;
v_x_4097_ = v___x_4157_;
goto _start;
}
else
{
lean_dec(v_x_4097_);
if (v_skipConstInApp_4094_ == 0)
{
goto v___jp_4150_;
}
else
{
uint8_t v___x_4159_; 
v___x_4159_ = l_Lean_Expr_isConst(v_x_4095_);
if (v___x_4159_ == 0)
{
goto v___jp_4150_;
}
else
{
v_f_4105_ = v_x_4095_;
v___y_4106_ = v___y_4098_;
v___y_4107_ = v___y_4099_;
v___y_4108_ = v___y_4100_;
v___y_4109_ = v___y_4101_;
v___y_4110_ = v___y_4102_;
goto v___jp_4104_;
}
}
}
v___jp_4104_:
{
if (v_skipInstances_4090_ == 0)
{
size_t v_sz_4111_; size_t v___x_4112_; lean_object* v___x_4113_; 
v_sz_4111_ = lean_array_size(v_x_4096_);
v___x_4112_ = ((size_t)0ULL);
lean_inc_ref(v_post_4092_);
lean_inc_ref(v_pre_4091_);
v___x_4113_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__2(v_pre_4091_, v_post_4092_, v_usedLetOnly_4093_, v_skipConstInApp_4094_, v_skipInstances_4090_, v_sz_4111_, v___x_4112_, v_x_4096_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_);
if (lean_obj_tag(v___x_4113_) == 0)
{
lean_object* v_a_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; 
v_a_4114_ = lean_ctor_get(v___x_4113_, 0);
lean_inc(v_a_4114_);
lean_dec_ref(v___x_4113_);
v___x_4115_ = l_Lean_mkAppN(v_f_4105_, v_a_4114_);
lean_dec(v_a_4114_);
v___x_4116_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4091_, v_post_4092_, v_usedLetOnly_4093_, v_skipConstInApp_4094_, v_skipInstances_4090_, v___x_4115_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_);
return v___x_4116_;
}
else
{
lean_object* v_a_4117_; lean_object* v___x_4119_; uint8_t v_isShared_4120_; uint8_t v_isSharedCheck_4124_; 
lean_dec_ref(v_f_4105_);
lean_dec_ref(v_post_4092_);
lean_dec_ref(v_pre_4091_);
v_a_4117_ = lean_ctor_get(v___x_4113_, 0);
v_isSharedCheck_4124_ = !lean_is_exclusive(v___x_4113_);
if (v_isSharedCheck_4124_ == 0)
{
v___x_4119_ = v___x_4113_;
v_isShared_4120_ = v_isSharedCheck_4124_;
goto v_resetjp_4118_;
}
else
{
lean_inc(v_a_4117_);
lean_dec(v___x_4113_);
v___x_4119_ = lean_box(0);
v_isShared_4120_ = v_isSharedCheck_4124_;
goto v_resetjp_4118_;
}
v_resetjp_4118_:
{
lean_object* v___x_4122_; 
if (v_isShared_4120_ == 0)
{
v___x_4122_ = v___x_4119_;
goto v_reusejp_4121_;
}
else
{
lean_object* v_reuseFailAlloc_4123_; 
v_reuseFailAlloc_4123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4123_, 0, v_a_4117_);
v___x_4122_ = v_reuseFailAlloc_4123_;
goto v_reusejp_4121_;
}
v_reusejp_4121_:
{
return v___x_4122_;
}
}
}
}
else
{
lean_object* v___x_4125_; lean_object* v___x_4126_; 
v___x_4125_ = lean_array_get_size(v_x_4096_);
lean_inc_ref(v_f_4105_);
v___x_4126_ = l_Lean_Meta_getFunInfoNArgs(v_f_4105_, v___x_4125_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_);
if (lean_obj_tag(v___x_4126_) == 0)
{
lean_object* v_a_4127_; lean_object* v_paramInfo_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; 
v_a_4127_ = lean_ctor_get(v___x_4126_, 0);
lean_inc(v_a_4127_);
lean_dec_ref(v___x_4126_);
v_paramInfo_4128_ = lean_ctor_get(v_a_4127_, 0);
lean_inc_ref(v_paramInfo_4128_);
lean_dec(v_a_4127_);
v___x_4129_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_4092_);
lean_inc_ref(v_pre_4091_);
v___x_4130_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg(v___x_4125_, v_paramInfo_4128_, v_pre_4091_, v_post_4092_, v_usedLetOnly_4093_, v_skipConstInApp_4094_, v_skipInstances_4090_, v___x_4129_, v_x_4096_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_);
lean_dec_ref(v_paramInfo_4128_);
if (lean_obj_tag(v___x_4130_) == 0)
{
lean_object* v_a_4131_; lean_object* v___x_4132_; lean_object* v___x_4133_; 
v_a_4131_ = lean_ctor_get(v___x_4130_, 0);
lean_inc(v_a_4131_);
lean_dec_ref(v___x_4130_);
v___x_4132_ = l_Lean_mkAppN(v_f_4105_, v_a_4131_);
lean_dec(v_a_4131_);
v___x_4133_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4091_, v_post_4092_, v_usedLetOnly_4093_, v_skipConstInApp_4094_, v_skipInstances_4090_, v___x_4132_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_);
return v___x_4133_;
}
else
{
lean_object* v_a_4134_; lean_object* v___x_4136_; uint8_t v_isShared_4137_; uint8_t v_isSharedCheck_4141_; 
lean_dec_ref(v_f_4105_);
lean_dec_ref(v_post_4092_);
lean_dec_ref(v_pre_4091_);
v_a_4134_ = lean_ctor_get(v___x_4130_, 0);
v_isSharedCheck_4141_ = !lean_is_exclusive(v___x_4130_);
if (v_isSharedCheck_4141_ == 0)
{
v___x_4136_ = v___x_4130_;
v_isShared_4137_ = v_isSharedCheck_4141_;
goto v_resetjp_4135_;
}
else
{
lean_inc(v_a_4134_);
lean_dec(v___x_4130_);
v___x_4136_ = lean_box(0);
v_isShared_4137_ = v_isSharedCheck_4141_;
goto v_resetjp_4135_;
}
v_resetjp_4135_:
{
lean_object* v___x_4139_; 
if (v_isShared_4137_ == 0)
{
v___x_4139_ = v___x_4136_;
goto v_reusejp_4138_;
}
else
{
lean_object* v_reuseFailAlloc_4140_; 
v_reuseFailAlloc_4140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4140_, 0, v_a_4134_);
v___x_4139_ = v_reuseFailAlloc_4140_;
goto v_reusejp_4138_;
}
v_reusejp_4138_:
{
return v___x_4139_;
}
}
}
}
else
{
lean_object* v_a_4142_; lean_object* v___x_4144_; uint8_t v_isShared_4145_; uint8_t v_isSharedCheck_4149_; 
lean_dec_ref(v_f_4105_);
lean_dec_ref(v_x_4096_);
lean_dec_ref(v_post_4092_);
lean_dec_ref(v_pre_4091_);
v_a_4142_ = lean_ctor_get(v___x_4126_, 0);
v_isSharedCheck_4149_ = !lean_is_exclusive(v___x_4126_);
if (v_isSharedCheck_4149_ == 0)
{
v___x_4144_ = v___x_4126_;
v_isShared_4145_ = v_isSharedCheck_4149_;
goto v_resetjp_4143_;
}
else
{
lean_inc(v_a_4142_);
lean_dec(v___x_4126_);
v___x_4144_ = lean_box(0);
v_isShared_4145_ = v_isSharedCheck_4149_;
goto v_resetjp_4143_;
}
v_resetjp_4143_:
{
lean_object* v___x_4147_; 
if (v_isShared_4145_ == 0)
{
v___x_4147_ = v___x_4144_;
goto v_reusejp_4146_;
}
else
{
lean_object* v_reuseFailAlloc_4148_; 
v_reuseFailAlloc_4148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4148_, 0, v_a_4142_);
v___x_4147_ = v_reuseFailAlloc_4148_;
goto v_reusejp_4146_;
}
v_reusejp_4146_:
{
return v___x_4147_;
}
}
}
}
}
v___jp_4150_:
{
lean_object* v___x_4151_; 
lean_inc_ref(v_post_4092_);
lean_inc_ref(v_pre_4091_);
v___x_4151_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4091_, v_post_4092_, v_usedLetOnly_4093_, v_skipConstInApp_4094_, v_skipInstances_4090_, v_x_4095_, v___y_4098_, v___y_4099_, v___y_4100_, v___y_4101_, v___y_4102_);
if (lean_obj_tag(v___x_4151_) == 0)
{
lean_object* v_a_4152_; 
v_a_4152_ = lean_ctor_get(v___x_4151_, 0);
lean_inc(v_a_4152_);
lean_dec_ref(v___x_4151_);
v_f_4105_ = v_a_4152_;
v___y_4106_ = v___y_4098_;
v___y_4107_ = v___y_4099_;
v___y_4108_ = v___y_4100_;
v___y_4109_ = v___y_4101_;
v___y_4110_ = v___y_4102_;
goto v___jp_4104_;
}
else
{
lean_dec_ref(v_x_4096_);
lean_dec_ref(v_post_4092_);
lean_dec_ref(v_pre_4091_);
return v___x_4151_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1(lean_object* v___x_4160_, lean_object* v_pre_4161_, lean_object* v_e_4162_, lean_object* v_post_4163_, uint8_t v_usedLetOnly_4164_, uint8_t v_skipConstInApp_4165_, uint8_t v_skipInstances_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_){
_start:
{
lean_object* v___x_4173_; 
v___x_4173_ = l_Lean_Core_checkSystem(v___x_4160_, v___y_4170_, v___y_4171_);
if (lean_obj_tag(v___x_4173_) == 0)
{
lean_object* v___x_4174_; 
lean_dec_ref(v___x_4173_);
lean_inc_ref(v_pre_4161_);
lean_inc(v___y_4171_);
lean_inc_ref(v___y_4170_);
lean_inc(v___y_4169_);
lean_inc_ref(v___y_4168_);
lean_inc_ref(v_e_4162_);
v___x_4174_ = lean_apply_6(v_pre_4161_, v_e_4162_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_, lean_box(0));
if (lean_obj_tag(v___x_4174_) == 0)
{
lean_object* v_a_4175_; lean_object* v___x_4177_; uint8_t v_isShared_4178_; uint8_t v_isSharedCheck_4223_; 
v_a_4175_ = lean_ctor_get(v___x_4174_, 0);
v_isSharedCheck_4223_ = !lean_is_exclusive(v___x_4174_);
if (v_isSharedCheck_4223_ == 0)
{
v___x_4177_ = v___x_4174_;
v_isShared_4178_ = v_isSharedCheck_4223_;
goto v_resetjp_4176_;
}
else
{
lean_inc(v_a_4175_);
lean_dec(v___x_4174_);
v___x_4177_ = lean_box(0);
v_isShared_4178_ = v_isSharedCheck_4223_;
goto v_resetjp_4176_;
}
v_resetjp_4176_:
{
lean_object* v___y_4180_; 
switch(lean_obj_tag(v_a_4175_))
{
case 0:
{
lean_object* v_e_4215_; lean_object* v___x_4217_; 
lean_dec_ref(v_post_4163_);
lean_dec_ref(v_e_4162_);
lean_dec_ref(v_pre_4161_);
v_e_4215_ = lean_ctor_get(v_a_4175_, 0);
lean_inc_ref(v_e_4215_);
lean_dec_ref(v_a_4175_);
if (v_isShared_4178_ == 0)
{
lean_ctor_set(v___x_4177_, 0, v_e_4215_);
v___x_4217_ = v___x_4177_;
goto v_reusejp_4216_;
}
else
{
lean_object* v_reuseFailAlloc_4218_; 
v_reuseFailAlloc_4218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4218_, 0, v_e_4215_);
v___x_4217_ = v_reuseFailAlloc_4218_;
goto v_reusejp_4216_;
}
v_reusejp_4216_:
{
return v___x_4217_;
}
}
case 1:
{
lean_object* v_e_4219_; lean_object* v___x_4220_; 
lean_del_object(v___x_4177_);
lean_dec_ref(v_e_4162_);
v_e_4219_ = lean_ctor_get(v_a_4175_, 0);
lean_inc_ref(v_e_4219_);
lean_dec_ref(v_a_4175_);
v___x_4220_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4161_, v_post_4163_, v_usedLetOnly_4164_, v_skipConstInApp_4165_, v_skipInstances_4166_, v_e_4219_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_);
return v___x_4220_;
}
default: 
{
lean_object* v_e_x3f_4221_; 
lean_del_object(v___x_4177_);
v_e_x3f_4221_ = lean_ctor_get(v_a_4175_, 0);
lean_inc(v_e_x3f_4221_);
lean_dec_ref(v_a_4175_);
if (lean_obj_tag(v_e_x3f_4221_) == 0)
{
v___y_4180_ = v_e_4162_;
goto v___jp_4179_;
}
else
{
lean_object* v_val_4222_; 
lean_dec_ref(v_e_4162_);
v_val_4222_ = lean_ctor_get(v_e_x3f_4221_, 0);
lean_inc(v_val_4222_);
lean_dec_ref(v_e_x3f_4221_);
v___y_4180_ = v_val_4222_;
goto v___jp_4179_;
}
}
}
v___jp_4179_:
{
switch(lean_obj_tag(v___y_4180_))
{
case 7:
{
lean_object* v___x_4181_; lean_object* v___x_4182_; 
v___x_4181_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_4182_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5(v_pre_4161_, v_post_4163_, v_usedLetOnly_4164_, v_skipConstInApp_4165_, v_skipInstances_4166_, v___x_4181_, v___y_4180_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_);
return v___x_4182_;
}
case 6:
{
lean_object* v___x_4183_; lean_object* v___x_4184_; 
v___x_4183_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_4184_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6(v_pre_4161_, v_post_4163_, v_usedLetOnly_4164_, v_skipConstInApp_4165_, v_skipInstances_4166_, v___x_4183_, v___y_4180_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_);
return v___x_4184_;
}
case 8:
{
lean_object* v___x_4185_; lean_object* v___x_4186_; 
v___x_4185_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_4186_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7(v_pre_4161_, v_post_4163_, v_usedLetOnly_4164_, v_skipConstInApp_4165_, v_skipInstances_4166_, v___x_4185_, v___y_4180_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_);
return v___x_4186_;
}
case 5:
{
lean_object* v_dummy_4187_; lean_object* v_nargs_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; 
v_dummy_4187_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_4188_ = l_Lean_Expr_getAppNumArgs(v___y_4180_);
lean_inc(v_nargs_4188_);
v___x_4189_ = lean_mk_array(v_nargs_4188_, v_dummy_4187_);
v___x_4190_ = lean_unsigned_to_nat(1u);
v___x_4191_ = lean_nat_sub(v_nargs_4188_, v___x_4190_);
lean_dec(v_nargs_4188_);
v___x_4192_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__8(v_skipInstances_4166_, v_pre_4161_, v_post_4163_, v_usedLetOnly_4164_, v_skipConstInApp_4165_, v___y_4180_, v___x_4189_, v___x_4191_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_);
return v___x_4192_;
}
case 10:
{
lean_object* v_data_4193_; lean_object* v_expr_4194_; lean_object* v___x_4195_; 
v_data_4193_ = lean_ctor_get(v___y_4180_, 0);
v_expr_4194_ = lean_ctor_get(v___y_4180_, 1);
lean_inc_ref(v_expr_4194_);
lean_inc_ref(v_post_4163_);
lean_inc_ref(v_pre_4161_);
v___x_4195_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4161_, v_post_4163_, v_usedLetOnly_4164_, v_skipConstInApp_4165_, v_skipInstances_4166_, v_expr_4194_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_);
if (lean_obj_tag(v___x_4195_) == 0)
{
lean_object* v_a_4196_; size_t v___x_4197_; size_t v___x_4198_; uint8_t v___x_4199_; 
v_a_4196_ = lean_ctor_get(v___x_4195_, 0);
lean_inc(v_a_4196_);
lean_dec_ref(v___x_4195_);
v___x_4197_ = lean_ptr_addr(v_expr_4194_);
v___x_4198_ = lean_ptr_addr(v_a_4196_);
v___x_4199_ = lean_usize_dec_eq(v___x_4197_, v___x_4198_);
if (v___x_4199_ == 0)
{
lean_object* v___x_4200_; lean_object* v___x_4201_; 
lean_inc(v_data_4193_);
lean_dec_ref(v___y_4180_);
v___x_4200_ = l_Lean_Expr_mdata___override(v_data_4193_, v_a_4196_);
v___x_4201_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4161_, v_post_4163_, v_usedLetOnly_4164_, v_skipConstInApp_4165_, v_skipInstances_4166_, v___x_4200_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_);
return v___x_4201_;
}
else
{
lean_object* v___x_4202_; 
lean_dec(v_a_4196_);
v___x_4202_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4161_, v_post_4163_, v_usedLetOnly_4164_, v_skipConstInApp_4165_, v_skipInstances_4166_, v___y_4180_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_);
return v___x_4202_;
}
}
else
{
lean_dec_ref(v___y_4180_);
lean_dec_ref(v_post_4163_);
lean_dec_ref(v_pre_4161_);
return v___x_4195_;
}
}
case 11:
{
lean_object* v_typeName_4203_; lean_object* v_idx_4204_; lean_object* v_struct_4205_; lean_object* v___x_4206_; 
v_typeName_4203_ = lean_ctor_get(v___y_4180_, 0);
v_idx_4204_ = lean_ctor_get(v___y_4180_, 1);
v_struct_4205_ = lean_ctor_get(v___y_4180_, 2);
lean_inc_ref(v_struct_4205_);
lean_inc_ref(v_post_4163_);
lean_inc_ref(v_pre_4161_);
v___x_4206_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4161_, v_post_4163_, v_usedLetOnly_4164_, v_skipConstInApp_4165_, v_skipInstances_4166_, v_struct_4205_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_);
if (lean_obj_tag(v___x_4206_) == 0)
{
lean_object* v_a_4207_; size_t v___x_4208_; size_t v___x_4209_; uint8_t v___x_4210_; 
v_a_4207_ = lean_ctor_get(v___x_4206_, 0);
lean_inc(v_a_4207_);
lean_dec_ref(v___x_4206_);
v___x_4208_ = lean_ptr_addr(v_struct_4205_);
v___x_4209_ = lean_ptr_addr(v_a_4207_);
v___x_4210_ = lean_usize_dec_eq(v___x_4208_, v___x_4209_);
if (v___x_4210_ == 0)
{
lean_object* v___x_4211_; lean_object* v___x_4212_; 
lean_inc(v_idx_4204_);
lean_inc(v_typeName_4203_);
lean_dec_ref(v___y_4180_);
v___x_4211_ = l_Lean_Expr_proj___override(v_typeName_4203_, v_idx_4204_, v_a_4207_);
v___x_4212_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4161_, v_post_4163_, v_usedLetOnly_4164_, v_skipConstInApp_4165_, v_skipInstances_4166_, v___x_4211_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_);
return v___x_4212_;
}
else
{
lean_object* v___x_4213_; 
lean_dec(v_a_4207_);
v___x_4213_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4161_, v_post_4163_, v_usedLetOnly_4164_, v_skipConstInApp_4165_, v_skipInstances_4166_, v___y_4180_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_);
return v___x_4213_;
}
}
else
{
lean_dec_ref(v___y_4180_);
lean_dec_ref(v_post_4163_);
lean_dec_ref(v_pre_4161_);
return v___x_4206_;
}
}
default: 
{
lean_object* v___x_4214_; 
v___x_4214_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4161_, v_post_4163_, v_usedLetOnly_4164_, v_skipConstInApp_4165_, v_skipInstances_4166_, v___y_4180_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_);
return v___x_4214_;
}
}
}
}
}
else
{
lean_object* v_a_4224_; lean_object* v___x_4226_; uint8_t v_isShared_4227_; uint8_t v_isSharedCheck_4231_; 
lean_dec_ref(v_post_4163_);
lean_dec_ref(v_e_4162_);
lean_dec_ref(v_pre_4161_);
v_a_4224_ = lean_ctor_get(v___x_4174_, 0);
v_isSharedCheck_4231_ = !lean_is_exclusive(v___x_4174_);
if (v_isSharedCheck_4231_ == 0)
{
v___x_4226_ = v___x_4174_;
v_isShared_4227_ = v_isSharedCheck_4231_;
goto v_resetjp_4225_;
}
else
{
lean_inc(v_a_4224_);
lean_dec(v___x_4174_);
v___x_4226_ = lean_box(0);
v_isShared_4227_ = v_isSharedCheck_4231_;
goto v_resetjp_4225_;
}
v_resetjp_4225_:
{
lean_object* v___x_4229_; 
if (v_isShared_4227_ == 0)
{
v___x_4229_ = v___x_4226_;
goto v_reusejp_4228_;
}
else
{
lean_object* v_reuseFailAlloc_4230_; 
v_reuseFailAlloc_4230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4230_, 0, v_a_4224_);
v___x_4229_ = v_reuseFailAlloc_4230_;
goto v_reusejp_4228_;
}
v_reusejp_4228_:
{
return v___x_4229_;
}
}
}
}
else
{
lean_object* v_a_4232_; lean_object* v___x_4234_; uint8_t v_isShared_4235_; uint8_t v_isSharedCheck_4239_; 
lean_dec_ref(v_post_4163_);
lean_dec_ref(v_e_4162_);
lean_dec_ref(v_pre_4161_);
v_a_4232_ = lean_ctor_get(v___x_4173_, 0);
v_isSharedCheck_4239_ = !lean_is_exclusive(v___x_4173_);
if (v_isSharedCheck_4239_ == 0)
{
v___x_4234_ = v___x_4173_;
v_isShared_4235_ = v_isSharedCheck_4239_;
goto v_resetjp_4233_;
}
else
{
lean_inc(v_a_4232_);
lean_dec(v___x_4173_);
v___x_4234_ = lean_box(0);
v_isShared_4235_ = v_isSharedCheck_4239_;
goto v_resetjp_4233_;
}
v_resetjp_4233_:
{
lean_object* v___x_4237_; 
if (v_isShared_4235_ == 0)
{
v___x_4237_ = v___x_4234_;
goto v_reusejp_4236_;
}
else
{
lean_object* v_reuseFailAlloc_4238_; 
v_reuseFailAlloc_4238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4238_, 0, v_a_4232_);
v___x_4237_ = v_reuseFailAlloc_4238_;
goto v_reusejp_4236_;
}
v_reusejp_4236_:
{
return v___x_4237_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1___boxed(lean_object* v___x_4240_, lean_object* v_pre_4241_, lean_object* v_e_4242_, lean_object* v_post_4243_, lean_object* v_usedLetOnly_4244_, lean_object* v_skipConstInApp_4245_, lean_object* v_skipInstances_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_, lean_object* v___y_4252_){
_start:
{
uint8_t v_usedLetOnly_boxed_4253_; uint8_t v_skipConstInApp_boxed_4254_; uint8_t v_skipInstances_boxed_4255_; lean_object* v_res_4256_; 
v_usedLetOnly_boxed_4253_ = lean_unbox(v_usedLetOnly_4244_);
v_skipConstInApp_boxed_4254_ = lean_unbox(v_skipConstInApp_4245_);
v_skipInstances_boxed_4255_ = lean_unbox(v_skipInstances_4246_);
v_res_4256_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1(v___x_4240_, v_pre_4241_, v_e_4242_, v_post_4243_, v_usedLetOnly_boxed_4253_, v_skipConstInApp_boxed_4254_, v_skipInstances_boxed_4255_, v___y_4247_, v___y_4248_, v___y_4249_, v___y_4250_, v___y_4251_);
lean_dec(v___y_4251_);
lean_dec_ref(v___y_4250_);
lean_dec(v___y_4249_);
lean_dec_ref(v___y_4248_);
lean_dec(v___y_4247_);
return v_res_4256_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(lean_object* v_pre_4257_, lean_object* v_post_4258_, uint8_t v_usedLetOnly_4259_, uint8_t v_skipConstInApp_4260_, uint8_t v_skipInstances_4261_, lean_object* v_e_4262_, lean_object* v_a_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_){
_start:
{
lean_object* v___x_4269_; lean_object* v___x_4270_; 
lean_inc(v_a_4263_);
v___x_4269_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_4269_, 0, lean_box(0));
lean_closure_set(v___x_4269_, 1, lean_box(0));
lean_closure_set(v___x_4269_, 2, v_a_4263_);
v___x_4270_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0(lean_box(0), v___x_4269_, v___y_4264_, v___y_4265_, v___y_4266_, v___y_4267_);
if (lean_obj_tag(v___x_4270_) == 0)
{
lean_object* v_a_4271_; lean_object* v___x_4273_; uint8_t v_isShared_4274_; uint8_t v_isSharedCheck_4305_; 
v_a_4271_ = lean_ctor_get(v___x_4270_, 0);
v_isSharedCheck_4305_ = !lean_is_exclusive(v___x_4270_);
if (v_isSharedCheck_4305_ == 0)
{
v___x_4273_ = v___x_4270_;
v_isShared_4274_ = v_isSharedCheck_4305_;
goto v_resetjp_4272_;
}
else
{
lean_inc(v_a_4271_);
lean_dec(v___x_4270_);
v___x_4273_ = lean_box(0);
v_isShared_4274_ = v_isSharedCheck_4305_;
goto v_resetjp_4272_;
}
v_resetjp_4272_:
{
lean_object* v___x_4275_; 
v___x_4275_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg(v_a_4271_, v_e_4262_);
lean_dec(v_a_4271_);
if (lean_obj_tag(v___x_4275_) == 0)
{
lean_object* v___x_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; lean_object* v___f_4280_; lean_object* v___x_4281_; 
lean_del_object(v___x_4273_);
v___x_4276_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__19___closed__0));
v___x_4277_ = lean_box(v_usedLetOnly_4259_);
v___x_4278_ = lean_box(v_skipConstInApp_4260_);
v___x_4279_ = lean_box(v_skipInstances_4261_);
lean_inc_ref(v_e_4262_);
v___f_4280_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1___boxed), 13, 7);
lean_closure_set(v___f_4280_, 0, v___x_4276_);
lean_closure_set(v___f_4280_, 1, v_pre_4257_);
lean_closure_set(v___f_4280_, 2, v_e_4262_);
lean_closure_set(v___f_4280_, 3, v_post_4258_);
lean_closure_set(v___f_4280_, 4, v___x_4277_);
lean_closure_set(v___f_4280_, 5, v___x_4278_);
lean_closure_set(v___f_4280_, 6, v___x_4279_);
v___x_4281_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg(v___f_4280_, v_a_4263_, v___y_4264_, v___y_4265_, v___y_4266_, v___y_4267_);
if (lean_obj_tag(v___x_4281_) == 0)
{
lean_object* v_a_4282_; lean_object* v___f_4283_; lean_object* v___x_4284_; 
v_a_4282_ = lean_ctor_get(v___x_4281_, 0);
lean_inc_n(v_a_4282_, 2);
lean_dec_ref(v___x_4281_);
lean_inc(v_a_4263_);
v___f_4283_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_4283_, 0, v_a_4263_);
lean_closure_set(v___f_4283_, 1, v_e_4262_);
lean_closure_set(v___f_4283_, 2, v_a_4282_);
v___x_4284_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0(lean_box(0), v___f_4283_, v___y_4264_, v___y_4265_, v___y_4266_, v___y_4267_);
if (lean_obj_tag(v___x_4284_) == 0)
{
lean_object* v___x_4286_; uint8_t v_isShared_4287_; uint8_t v_isSharedCheck_4291_; 
v_isSharedCheck_4291_ = !lean_is_exclusive(v___x_4284_);
if (v_isSharedCheck_4291_ == 0)
{
lean_object* v_unused_4292_; 
v_unused_4292_ = lean_ctor_get(v___x_4284_, 0);
lean_dec(v_unused_4292_);
v___x_4286_ = v___x_4284_;
v_isShared_4287_ = v_isSharedCheck_4291_;
goto v_resetjp_4285_;
}
else
{
lean_dec(v___x_4284_);
v___x_4286_ = lean_box(0);
v_isShared_4287_ = v_isSharedCheck_4291_;
goto v_resetjp_4285_;
}
v_resetjp_4285_:
{
lean_object* v___x_4289_; 
if (v_isShared_4287_ == 0)
{
lean_ctor_set(v___x_4286_, 0, v_a_4282_);
v___x_4289_ = v___x_4286_;
goto v_reusejp_4288_;
}
else
{
lean_object* v_reuseFailAlloc_4290_; 
v_reuseFailAlloc_4290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4290_, 0, v_a_4282_);
v___x_4289_ = v_reuseFailAlloc_4290_;
goto v_reusejp_4288_;
}
v_reusejp_4288_:
{
return v___x_4289_;
}
}
}
else
{
lean_object* v_a_4293_; lean_object* v___x_4295_; uint8_t v_isShared_4296_; uint8_t v_isSharedCheck_4300_; 
lean_dec(v_a_4282_);
v_a_4293_ = lean_ctor_get(v___x_4284_, 0);
v_isSharedCheck_4300_ = !lean_is_exclusive(v___x_4284_);
if (v_isSharedCheck_4300_ == 0)
{
v___x_4295_ = v___x_4284_;
v_isShared_4296_ = v_isSharedCheck_4300_;
goto v_resetjp_4294_;
}
else
{
lean_inc(v_a_4293_);
lean_dec(v___x_4284_);
v___x_4295_ = lean_box(0);
v_isShared_4296_ = v_isSharedCheck_4300_;
goto v_resetjp_4294_;
}
v_resetjp_4294_:
{
lean_object* v___x_4298_; 
if (v_isShared_4296_ == 0)
{
v___x_4298_ = v___x_4295_;
goto v_reusejp_4297_;
}
else
{
lean_object* v_reuseFailAlloc_4299_; 
v_reuseFailAlloc_4299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4299_, 0, v_a_4293_);
v___x_4298_ = v_reuseFailAlloc_4299_;
goto v_reusejp_4297_;
}
v_reusejp_4297_:
{
return v___x_4298_;
}
}
}
}
else
{
lean_dec_ref(v_e_4262_);
return v___x_4281_;
}
}
else
{
lean_object* v_val_4301_; lean_object* v___x_4303_; 
lean_dec_ref(v_e_4262_);
lean_dec_ref(v_post_4258_);
lean_dec_ref(v_pre_4257_);
v_val_4301_ = lean_ctor_get(v___x_4275_, 0);
lean_inc(v_val_4301_);
lean_dec_ref(v___x_4275_);
if (v_isShared_4274_ == 0)
{
lean_ctor_set(v___x_4273_, 0, v_val_4301_);
v___x_4303_ = v___x_4273_;
goto v_reusejp_4302_;
}
else
{
lean_object* v_reuseFailAlloc_4304_; 
v_reuseFailAlloc_4304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4304_, 0, v_val_4301_);
v___x_4303_ = v_reuseFailAlloc_4304_;
goto v_reusejp_4302_;
}
v_reusejp_4302_:
{
return v___x_4303_;
}
}
}
}
else
{
lean_object* v_a_4306_; lean_object* v___x_4308_; uint8_t v_isShared_4309_; uint8_t v_isSharedCheck_4313_; 
lean_dec_ref(v_e_4262_);
lean_dec_ref(v_post_4258_);
lean_dec_ref(v_pre_4257_);
v_a_4306_ = lean_ctor_get(v___x_4270_, 0);
v_isSharedCheck_4313_ = !lean_is_exclusive(v___x_4270_);
if (v_isSharedCheck_4313_ == 0)
{
v___x_4308_ = v___x_4270_;
v_isShared_4309_ = v_isSharedCheck_4313_;
goto v_resetjp_4307_;
}
else
{
lean_inc(v_a_4306_);
lean_dec(v___x_4270_);
v___x_4308_ = lean_box(0);
v_isShared_4309_ = v_isSharedCheck_4313_;
goto v_resetjp_4307_;
}
v_resetjp_4307_:
{
lean_object* v___x_4311_; 
if (v_isShared_4309_ == 0)
{
v___x_4311_ = v___x_4308_;
goto v_reusejp_4310_;
}
else
{
lean_object* v_reuseFailAlloc_4312_; 
v_reuseFailAlloc_4312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4312_, 0, v_a_4306_);
v___x_4311_ = v_reuseFailAlloc_4312_;
goto v_reusejp_4310_;
}
v_reusejp_4310_:
{
return v___x_4311_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___lam__0___boxed(lean_object* v_fvars_4314_, lean_object* v_pre_4315_, lean_object* v_post_4316_, lean_object* v_usedLetOnly_4317_, lean_object* v_skipConstInApp_4318_, lean_object* v_skipInstances_4319_, lean_object* v_body_4320_, lean_object* v_x_4321_, lean_object* v___y_4322_, lean_object* v___y_4323_, lean_object* v___y_4324_, lean_object* v___y_4325_, lean_object* v___y_4326_, lean_object* v___y_4327_){
_start:
{
uint8_t v_usedLetOnly_boxed_4328_; uint8_t v_skipConstInApp_boxed_4329_; uint8_t v_skipInstances_boxed_4330_; lean_object* v_res_4331_; 
v_usedLetOnly_boxed_4328_ = lean_unbox(v_usedLetOnly_4317_);
v_skipConstInApp_boxed_4329_ = lean_unbox(v_skipConstInApp_4318_);
v_skipInstances_boxed_4330_ = lean_unbox(v_skipInstances_4319_);
v_res_4331_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___lam__0(v_fvars_4314_, v_pre_4315_, v_post_4316_, v_usedLetOnly_boxed_4328_, v_skipConstInApp_boxed_4329_, v_skipInstances_boxed_4330_, v_body_4320_, v_x_4321_, v___y_4322_, v___y_4323_, v___y_4324_, v___y_4325_, v___y_4326_);
lean_dec(v___y_4326_);
lean_dec_ref(v___y_4325_);
lean_dec(v___y_4324_);
lean_dec_ref(v___y_4323_);
lean_dec(v___y_4322_);
return v_res_4331_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5(lean_object* v_pre_4332_, lean_object* v_post_4333_, uint8_t v_usedLetOnly_4334_, uint8_t v_skipConstInApp_4335_, uint8_t v_skipInstances_4336_, lean_object* v_fvars_4337_, lean_object* v_e_4338_, lean_object* v_a_4339_, lean_object* v___y_4340_, lean_object* v___y_4341_, lean_object* v___y_4342_, lean_object* v___y_4343_){
_start:
{
if (lean_obj_tag(v_e_4338_) == 7)
{
lean_object* v_binderName_4345_; lean_object* v_binderType_4346_; lean_object* v_body_4347_; uint8_t v_binderInfo_4348_; lean_object* v___x_4349_; lean_object* v___x_4350_; 
v_binderName_4345_ = lean_ctor_get(v_e_4338_, 0);
lean_inc(v_binderName_4345_);
v_binderType_4346_ = lean_ctor_get(v_e_4338_, 1);
lean_inc_ref(v_binderType_4346_);
v_body_4347_ = lean_ctor_get(v_e_4338_, 2);
lean_inc_ref(v_body_4347_);
v_binderInfo_4348_ = lean_ctor_get_uint8(v_e_4338_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_4338_);
v___x_4349_ = lean_expr_instantiate_rev(v_binderType_4346_, v_fvars_4337_);
lean_dec_ref(v_binderType_4346_);
lean_inc_ref(v_post_4333_);
lean_inc_ref(v_pre_4332_);
v___x_4350_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4332_, v_post_4333_, v_usedLetOnly_4334_, v_skipConstInApp_4335_, v_skipInstances_4336_, v___x_4349_, v_a_4339_, v___y_4340_, v___y_4341_, v___y_4342_, v___y_4343_);
if (lean_obj_tag(v___x_4350_) == 0)
{
lean_object* v_a_4351_; lean_object* v___x_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; lean_object* v___f_4355_; uint8_t v___x_4356_; lean_object* v___x_4357_; 
v_a_4351_ = lean_ctor_get(v___x_4350_, 0);
lean_inc(v_a_4351_);
lean_dec_ref(v___x_4350_);
v___x_4352_ = lean_box(v_usedLetOnly_4334_);
v___x_4353_ = lean_box(v_skipConstInApp_4335_);
v___x_4354_ = lean_box(v_skipInstances_4336_);
v___f_4355_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___lam__0___boxed), 14, 7);
lean_closure_set(v___f_4355_, 0, v_fvars_4337_);
lean_closure_set(v___f_4355_, 1, v_pre_4332_);
lean_closure_set(v___f_4355_, 2, v_post_4333_);
lean_closure_set(v___f_4355_, 3, v___x_4352_);
lean_closure_set(v___f_4355_, 4, v___x_4353_);
lean_closure_set(v___f_4355_, 5, v___x_4354_);
lean_closure_set(v___f_4355_, 6, v_body_4347_);
v___x_4356_ = 0;
v___x_4357_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_binderName_4345_, v_binderInfo_4348_, v_a_4351_, v___f_4355_, v___x_4356_, v_a_4339_, v___y_4340_, v___y_4341_, v___y_4342_, v___y_4343_);
return v___x_4357_;
}
else
{
lean_dec_ref(v_body_4347_);
lean_dec(v_binderName_4345_);
lean_dec_ref(v_fvars_4337_);
lean_dec_ref(v_post_4333_);
lean_dec_ref(v_pre_4332_);
return v___x_4350_;
}
}
else
{
lean_object* v___x_4358_; lean_object* v___x_4359_; 
v___x_4358_ = lean_expr_instantiate_rev(v_e_4338_, v_fvars_4337_);
lean_dec_ref(v_e_4338_);
lean_inc_ref(v_post_4333_);
lean_inc_ref(v_pre_4332_);
v___x_4359_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4332_, v_post_4333_, v_usedLetOnly_4334_, v_skipConstInApp_4335_, v_skipInstances_4336_, v___x_4358_, v_a_4339_, v___y_4340_, v___y_4341_, v___y_4342_, v___y_4343_);
if (lean_obj_tag(v___x_4359_) == 0)
{
lean_object* v_a_4360_; uint8_t v___x_4361_; uint8_t v___x_4362_; uint8_t v___x_4363_; lean_object* v___x_4364_; 
v_a_4360_ = lean_ctor_get(v___x_4359_, 0);
lean_inc(v_a_4360_);
lean_dec_ref(v___x_4359_);
v___x_4361_ = 0;
v___x_4362_ = 1;
v___x_4363_ = 1;
v___x_4364_ = l_Lean_Meta_mkForallFVars(v_fvars_4337_, v_a_4360_, v___x_4361_, v_usedLetOnly_4334_, v___x_4362_, v___x_4363_, v___y_4340_, v___y_4341_, v___y_4342_, v___y_4343_);
lean_dec_ref(v_fvars_4337_);
if (lean_obj_tag(v___x_4364_) == 0)
{
lean_object* v_a_4365_; lean_object* v___x_4366_; 
v_a_4365_ = lean_ctor_get(v___x_4364_, 0);
lean_inc(v_a_4365_);
lean_dec_ref(v___x_4364_);
v___x_4366_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4332_, v_post_4333_, v_usedLetOnly_4334_, v_skipConstInApp_4335_, v_skipInstances_4336_, v_a_4365_, v_a_4339_, v___y_4340_, v___y_4341_, v___y_4342_, v___y_4343_);
return v___x_4366_;
}
else
{
lean_dec_ref(v_post_4333_);
lean_dec_ref(v_pre_4332_);
return v___x_4364_;
}
}
else
{
lean_dec_ref(v_fvars_4337_);
lean_dec_ref(v_post_4333_);
lean_dec_ref(v_pre_4332_);
return v___x_4359_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___lam__0(lean_object* v_fvars_4367_, lean_object* v_pre_4368_, lean_object* v_post_4369_, uint8_t v_usedLetOnly_4370_, uint8_t v_skipConstInApp_4371_, uint8_t v_skipInstances_4372_, lean_object* v_body_4373_, lean_object* v_x_4374_, lean_object* v___y_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_, lean_object* v___y_4379_){
_start:
{
lean_object* v___x_4381_; lean_object* v___x_4382_; 
v___x_4381_ = lean_array_push(v_fvars_4367_, v_x_4374_);
v___x_4382_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5(v_pre_4368_, v_post_4369_, v_usedLetOnly_4370_, v_skipConstInApp_4371_, v_skipInstances_4372_, v___x_4381_, v_body_4373_, v___y_4375_, v___y_4376_, v___y_4377_, v___y_4378_, v___y_4379_);
return v___x_4382_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3___boxed(lean_object* v_pre_4383_, lean_object* v_post_4384_, lean_object* v_usedLetOnly_4385_, lean_object* v_skipConstInApp_4386_, lean_object* v_skipInstances_4387_, lean_object* v_e_4388_, lean_object* v_a_4389_, lean_object* v___y_4390_, lean_object* v___y_4391_, lean_object* v___y_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_){
_start:
{
uint8_t v_usedLetOnly_boxed_4395_; uint8_t v_skipConstInApp_boxed_4396_; uint8_t v_skipInstances_boxed_4397_; lean_object* v_res_4398_; 
v_usedLetOnly_boxed_4395_ = lean_unbox(v_usedLetOnly_4385_);
v_skipConstInApp_boxed_4396_ = lean_unbox(v_skipConstInApp_4386_);
v_skipInstances_boxed_4397_ = lean_unbox(v_skipInstances_4387_);
v_res_4398_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4383_, v_post_4384_, v_usedLetOnly_boxed_4395_, v_skipConstInApp_boxed_4396_, v_skipInstances_boxed_4397_, v_e_4388_, v_a_4389_, v___y_4390_, v___y_4391_, v___y_4392_, v___y_4393_);
lean_dec(v___y_4393_);
lean_dec_ref(v___y_4392_);
lean_dec(v___y_4391_);
lean_dec_ref(v___y_4390_);
lean_dec(v_a_4389_);
return v_res_4398_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__2___boxed(lean_object* v_pre_4399_, lean_object* v_post_4400_, lean_object* v_usedLetOnly_4401_, lean_object* v_skipConstInApp_4402_, lean_object* v_skipInstances_4403_, lean_object* v_sz_4404_, lean_object* v_i_4405_, lean_object* v_bs_4406_, lean_object* v___y_4407_, lean_object* v___y_4408_, lean_object* v___y_4409_, lean_object* v___y_4410_, lean_object* v___y_4411_, lean_object* v___y_4412_){
_start:
{
uint8_t v_usedLetOnly_boxed_4413_; uint8_t v_skipConstInApp_boxed_4414_; uint8_t v_skipInstances_boxed_4415_; size_t v_sz_boxed_4416_; size_t v_i_boxed_4417_; lean_object* v_res_4418_; 
v_usedLetOnly_boxed_4413_ = lean_unbox(v_usedLetOnly_4401_);
v_skipConstInApp_boxed_4414_ = lean_unbox(v_skipConstInApp_4402_);
v_skipInstances_boxed_4415_ = lean_unbox(v_skipInstances_4403_);
v_sz_boxed_4416_ = lean_unbox_usize(v_sz_4404_);
lean_dec(v_sz_4404_);
v_i_boxed_4417_ = lean_unbox_usize(v_i_4405_);
lean_dec(v_i_4405_);
v_res_4418_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__2(v_pre_4399_, v_post_4400_, v_usedLetOnly_boxed_4413_, v_skipConstInApp_boxed_4414_, v_skipInstances_boxed_4415_, v_sz_boxed_4416_, v_i_boxed_4417_, v_bs_4406_, v___y_4407_, v___y_4408_, v___y_4409_, v___y_4410_, v___y_4411_);
lean_dec(v___y_4411_);
lean_dec_ref(v___y_4410_);
lean_dec(v___y_4409_);
lean_dec_ref(v___y_4408_);
lean_dec(v___y_4407_);
return v_res_4418_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___boxed(lean_object* v_pre_4419_, lean_object* v_post_4420_, lean_object* v_usedLetOnly_4421_, lean_object* v_skipConstInApp_4422_, lean_object* v_skipInstances_4423_, lean_object* v_e_4424_, lean_object* v_a_4425_, lean_object* v___y_4426_, lean_object* v___y_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_){
_start:
{
uint8_t v_usedLetOnly_boxed_4431_; uint8_t v_skipConstInApp_boxed_4432_; uint8_t v_skipInstances_boxed_4433_; lean_object* v_res_4434_; 
v_usedLetOnly_boxed_4431_ = lean_unbox(v_usedLetOnly_4421_);
v_skipConstInApp_boxed_4432_ = lean_unbox(v_skipConstInApp_4422_);
v_skipInstances_boxed_4433_ = lean_unbox(v_skipInstances_4423_);
v_res_4434_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4419_, v_post_4420_, v_usedLetOnly_boxed_4431_, v_skipConstInApp_boxed_4432_, v_skipInstances_boxed_4433_, v_e_4424_, v_a_4425_, v___y_4426_, v___y_4427_, v___y_4428_, v___y_4429_);
lean_dec(v___y_4429_);
lean_dec_ref(v___y_4428_);
lean_dec(v___y_4427_);
lean_dec_ref(v___y_4426_);
lean_dec(v_a_4425_);
return v_res_4434_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___boxed(lean_object* v_pre_4435_, lean_object* v_post_4436_, lean_object* v_usedLetOnly_4437_, lean_object* v_skipConstInApp_4438_, lean_object* v_skipInstances_4439_, lean_object* v_fvars_4440_, lean_object* v_e_4441_, lean_object* v_a_4442_, lean_object* v___y_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_){
_start:
{
uint8_t v_usedLetOnly_boxed_4448_; uint8_t v_skipConstInApp_boxed_4449_; uint8_t v_skipInstances_boxed_4450_; lean_object* v_res_4451_; 
v_usedLetOnly_boxed_4448_ = lean_unbox(v_usedLetOnly_4437_);
v_skipConstInApp_boxed_4449_ = lean_unbox(v_skipConstInApp_4438_);
v_skipInstances_boxed_4450_ = lean_unbox(v_skipInstances_4439_);
v_res_4451_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5(v_pre_4435_, v_post_4436_, v_usedLetOnly_boxed_4448_, v_skipConstInApp_boxed_4449_, v_skipInstances_boxed_4450_, v_fvars_4440_, v_e_4441_, v_a_4442_, v___y_4443_, v___y_4444_, v___y_4445_, v___y_4446_);
lean_dec(v___y_4446_);
lean_dec_ref(v___y_4445_);
lean_dec(v___y_4444_);
lean_dec_ref(v___y_4443_);
lean_dec(v_a_4442_);
return v_res_4451_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___boxed(lean_object* v_pre_4452_, lean_object* v_post_4453_, lean_object* v_usedLetOnly_4454_, lean_object* v_skipConstInApp_4455_, lean_object* v_skipInstances_4456_, lean_object* v_fvars_4457_, lean_object* v_e_4458_, lean_object* v_a_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_, lean_object* v___y_4463_, lean_object* v___y_4464_){
_start:
{
uint8_t v_usedLetOnly_boxed_4465_; uint8_t v_skipConstInApp_boxed_4466_; uint8_t v_skipInstances_boxed_4467_; lean_object* v_res_4468_; 
v_usedLetOnly_boxed_4465_ = lean_unbox(v_usedLetOnly_4454_);
v_skipConstInApp_boxed_4466_ = lean_unbox(v_skipConstInApp_4455_);
v_skipInstances_boxed_4467_ = lean_unbox(v_skipInstances_4456_);
v_res_4468_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6(v_pre_4452_, v_post_4453_, v_usedLetOnly_boxed_4465_, v_skipConstInApp_boxed_4466_, v_skipInstances_boxed_4467_, v_fvars_4457_, v_e_4458_, v_a_4459_, v___y_4460_, v___y_4461_, v___y_4462_, v___y_4463_);
lean_dec(v___y_4463_);
lean_dec_ref(v___y_4462_);
lean_dec(v___y_4461_);
lean_dec_ref(v___y_4460_);
lean_dec(v_a_4459_);
return v_res_4468_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___boxed(lean_object* v_pre_4469_, lean_object* v_post_4470_, lean_object* v_usedLetOnly_4471_, lean_object* v_skipConstInApp_4472_, lean_object* v_skipInstances_4473_, lean_object* v_fvars_4474_, lean_object* v_e_4475_, lean_object* v_a_4476_, lean_object* v___y_4477_, lean_object* v___y_4478_, lean_object* v___y_4479_, lean_object* v___y_4480_, lean_object* v___y_4481_){
_start:
{
uint8_t v_usedLetOnly_boxed_4482_; uint8_t v_skipConstInApp_boxed_4483_; uint8_t v_skipInstances_boxed_4484_; lean_object* v_res_4485_; 
v_usedLetOnly_boxed_4482_ = lean_unbox(v_usedLetOnly_4471_);
v_skipConstInApp_boxed_4483_ = lean_unbox(v_skipConstInApp_4472_);
v_skipInstances_boxed_4484_ = lean_unbox(v_skipInstances_4473_);
v_res_4485_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7(v_pre_4469_, v_post_4470_, v_usedLetOnly_boxed_4482_, v_skipConstInApp_boxed_4483_, v_skipInstances_boxed_4484_, v_fvars_4474_, v_e_4475_, v_a_4476_, v___y_4477_, v___y_4478_, v___y_4479_, v___y_4480_);
lean_dec(v___y_4480_);
lean_dec_ref(v___y_4479_);
lean_dec(v___y_4478_);
lean_dec_ref(v___y_4477_);
lean_dec(v_a_4476_);
return v_res_4485_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_upperBound_4486_, lean_object* v___x_4487_, lean_object* v_pre_4488_, lean_object* v_post_4489_, lean_object* v_usedLetOnly_4490_, lean_object* v_skipConstInApp_4491_, lean_object* v_skipInstances_4492_, lean_object* v_a_4493_, lean_object* v_b_4494_, lean_object* v___y_4495_, lean_object* v___y_4496_, lean_object* v___y_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_, lean_object* v___y_4500_){
_start:
{
uint8_t v_usedLetOnly_boxed_4501_; uint8_t v_skipConstInApp_boxed_4502_; uint8_t v_skipInstances_boxed_4503_; lean_object* v_res_4504_; 
v_usedLetOnly_boxed_4501_ = lean_unbox(v_usedLetOnly_4490_);
v_skipConstInApp_boxed_4502_ = lean_unbox(v_skipConstInApp_4491_);
v_skipInstances_boxed_4503_ = lean_unbox(v_skipInstances_4492_);
v_res_4504_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg(v_upperBound_4486_, v___x_4487_, v_pre_4488_, v_post_4489_, v_usedLetOnly_boxed_4501_, v_skipConstInApp_boxed_4502_, v_skipInstances_boxed_4503_, v_a_4493_, v_b_4494_, v___y_4495_, v___y_4496_, v___y_4497_, v___y_4498_, v___y_4499_);
lean_dec(v___y_4499_);
lean_dec_ref(v___y_4498_);
lean_dec(v___y_4497_);
lean_dec_ref(v___y_4496_);
lean_dec(v___y_4495_);
lean_dec_ref(v___x_4487_);
lean_dec(v_upperBound_4486_);
return v_res_4504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__8___boxed(lean_object* v_skipInstances_4505_, lean_object* v_pre_4506_, lean_object* v_post_4507_, lean_object* v_usedLetOnly_4508_, lean_object* v_skipConstInApp_4509_, lean_object* v_x_4510_, lean_object* v_x_4511_, lean_object* v_x_4512_, lean_object* v___y_4513_, lean_object* v___y_4514_, lean_object* v___y_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_){
_start:
{
uint8_t v_skipInstances_boxed_4519_; uint8_t v_usedLetOnly_boxed_4520_; uint8_t v_skipConstInApp_boxed_4521_; lean_object* v_res_4522_; 
v_skipInstances_boxed_4519_ = lean_unbox(v_skipInstances_4505_);
v_usedLetOnly_boxed_4520_ = lean_unbox(v_usedLetOnly_4508_);
v_skipConstInApp_boxed_4521_ = lean_unbox(v_skipConstInApp_4509_);
v_res_4522_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__8(v_skipInstances_boxed_4519_, v_pre_4506_, v_post_4507_, v_usedLetOnly_boxed_4520_, v_skipConstInApp_boxed_4521_, v_x_4510_, v_x_4511_, v_x_4512_, v___y_4513_, v___y_4514_, v___y_4515_, v___y_4516_, v___y_4517_);
lean_dec(v___y_4517_);
lean_dec_ref(v___y_4516_);
lean_dec(v___y_4515_);
lean_dec_ref(v___y_4514_);
lean_dec(v___y_4513_);
return v_res_4522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(lean_object* v_input_4523_, lean_object* v_pre_4524_, lean_object* v_post_4525_, uint8_t v_usedLetOnly_4526_, uint8_t v_skipConstInApp_4527_, lean_object* v___y_4528_, lean_object* v___y_4529_, lean_object* v___y_4530_, lean_object* v___y_4531_){
_start:
{
lean_object* v___x_4533_; lean_object* v___x_4534_; lean_object* v_a_4535_; uint8_t v___x_4536_; lean_object* v___x_4537_; 
v___x_4533_ = lean_obj_once(&l_Lean_Core_transform___redArg___closed__2, &l_Lean_Core_transform___redArg___closed__2_once, _init_l_Lean_Core_transform___redArg___closed__2);
v___x_4534_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0(lean_box(0), v___x_4533_, v___y_4528_, v___y_4529_, v___y_4530_, v___y_4531_);
v_a_4535_ = lean_ctor_get(v___x_4534_, 0);
lean_inc(v_a_4535_);
lean_dec_ref(v___x_4534_);
v___x_4536_ = 0;
v___x_4537_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4524_, v_post_4525_, v_usedLetOnly_4526_, v_skipConstInApp_4527_, v___x_4536_, v_input_4523_, v_a_4535_, v___y_4528_, v___y_4529_, v___y_4530_, v___y_4531_);
if (lean_obj_tag(v___x_4537_) == 0)
{
lean_object* v_a_4538_; lean_object* v___x_4539_; lean_object* v___x_4540_; lean_object* v___x_4542_; uint8_t v_isShared_4543_; uint8_t v_isSharedCheck_4547_; 
v_a_4538_ = lean_ctor_get(v___x_4537_, 0);
lean_inc(v_a_4538_);
lean_dec_ref(v___x_4537_);
v___x_4539_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_4539_, 0, lean_box(0));
lean_closure_set(v___x_4539_, 1, lean_box(0));
lean_closure_set(v___x_4539_, 2, v_a_4535_);
v___x_4540_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0(lean_box(0), v___x_4539_, v___y_4528_, v___y_4529_, v___y_4530_, v___y_4531_);
v_isSharedCheck_4547_ = !lean_is_exclusive(v___x_4540_);
if (v_isSharedCheck_4547_ == 0)
{
lean_object* v_unused_4548_; 
v_unused_4548_ = lean_ctor_get(v___x_4540_, 0);
lean_dec(v_unused_4548_);
v___x_4542_ = v___x_4540_;
v_isShared_4543_ = v_isSharedCheck_4547_;
goto v_resetjp_4541_;
}
else
{
lean_dec(v___x_4540_);
v___x_4542_ = lean_box(0);
v_isShared_4543_ = v_isSharedCheck_4547_;
goto v_resetjp_4541_;
}
v_resetjp_4541_:
{
lean_object* v___x_4545_; 
if (v_isShared_4543_ == 0)
{
lean_ctor_set(v___x_4542_, 0, v_a_4538_);
v___x_4545_ = v___x_4542_;
goto v_reusejp_4544_;
}
else
{
lean_object* v_reuseFailAlloc_4546_; 
v_reuseFailAlloc_4546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4546_, 0, v_a_4538_);
v___x_4545_ = v_reuseFailAlloc_4546_;
goto v_reusejp_4544_;
}
v_reusejp_4544_:
{
return v___x_4545_;
}
}
}
else
{
lean_dec(v_a_4535_);
return v___x_4537_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___boxed(lean_object* v_input_4549_, lean_object* v_pre_4550_, lean_object* v_post_4551_, lean_object* v_usedLetOnly_4552_, lean_object* v_skipConstInApp_4553_, lean_object* v___y_4554_, lean_object* v___y_4555_, lean_object* v___y_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_){
_start:
{
uint8_t v_usedLetOnly_boxed_4559_; uint8_t v_skipConstInApp_boxed_4560_; lean_object* v_res_4561_; 
v_usedLetOnly_boxed_4559_ = lean_unbox(v_usedLetOnly_4552_);
v_skipConstInApp_boxed_4560_ = lean_unbox(v_skipConstInApp_4553_);
v_res_4561_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(v_input_4549_, v_pre_4550_, v_post_4551_, v_usedLetOnly_boxed_4559_, v_skipConstInApp_boxed_4560_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_);
lean_dec(v___y_4557_);
lean_dec_ref(v___y_4556_);
lean_dec(v___y_4555_);
lean_dec_ref(v___y_4554_);
return v_res_4561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce(lean_object* v_e_4563_, uint8_t v_zetaDelta_4564_, uint8_t v_zetaHave_4565_, uint8_t v_beta_4566_, lean_object* v_a_4567_, lean_object* v_a_4568_, lean_object* v_a_4569_, lean_object* v_a_4570_){
_start:
{
lean_object* v_lctx_4572_; lean_object* v___x_4573_; lean_object* v___x_4574_; lean_object* v___x_4575_; lean_object* v___f_4576_; uint8_t v___x_4577_; 
v_lctx_4572_ = lean_ctor_get(v_a_4567_, 2);
lean_inc_ref(v_lctx_4572_);
v___x_4573_ = lean_local_ctx_num_indices(v_lctx_4572_);
v___x_4574_ = lean_box(v_zetaHave_4565_);
v___x_4575_ = lean_box(v_zetaDelta_4564_);
v___f_4576_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaReduce___lam__0___boxed), 9, 3);
lean_closure_set(v___f_4576_, 0, v___x_4574_);
lean_closure_set(v___f_4576_, 1, v___x_4573_);
lean_closure_set(v___f_4576_, 2, v___x_4575_);
v___x_4577_ = 1;
if (v_beta_4566_ == 0)
{
lean_object* v___f_4578_; lean_object* v___f_4579_; lean_object* v___x_4580_; 
v___f_4578_ = ((lean_object*)(l_Lean_Meta_zetaReduce___closed__0));
v___f_4579_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaReduce___lam__2___boxed), 7, 1);
lean_closure_set(v___f_4579_, 0, v___f_4576_);
v___x_4580_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(v_e_4563_, v___f_4579_, v___f_4578_, v___x_4577_, v_beta_4566_, v_a_4567_, v_a_4568_, v_a_4569_, v_a_4570_);
return v___x_4580_;
}
else
{
lean_object* v___f_4581_; lean_object* v___f_4582_; uint8_t v___x_4583_; lean_object* v___x_4584_; 
v___f_4581_ = ((lean_object*)(l_Lean_Meta_zetaReduce___closed__0));
v___f_4582_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaReduce___lam__4___boxed), 7, 1);
lean_closure_set(v___f_4582_, 0, v___f_4576_);
v___x_4583_ = 0;
v___x_4584_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(v_e_4563_, v___f_4582_, v___f_4581_, v___x_4577_, v___x_4583_, v_a_4567_, v_a_4568_, v_a_4569_, v_a_4570_);
return v___x_4584_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___boxed(lean_object* v_e_4585_, lean_object* v_zetaDelta_4586_, lean_object* v_zetaHave_4587_, lean_object* v_beta_4588_, lean_object* v_a_4589_, lean_object* v_a_4590_, lean_object* v_a_4591_, lean_object* v_a_4592_, lean_object* v_a_4593_){
_start:
{
uint8_t v_zetaDelta_boxed_4594_; uint8_t v_zetaHave_boxed_4595_; uint8_t v_beta_boxed_4596_; lean_object* v_res_4597_; 
v_zetaDelta_boxed_4594_ = lean_unbox(v_zetaDelta_4586_);
v_zetaHave_boxed_4595_ = lean_unbox(v_zetaHave_4587_);
v_beta_boxed_4596_ = lean_unbox(v_beta_4588_);
v_res_4597_ = l_Lean_Meta_zetaReduce(v_e_4585_, v_zetaDelta_boxed_4594_, v_zetaHave_boxed_4595_, v_beta_boxed_4596_, v_a_4589_, v_a_4590_, v_a_4591_, v_a_4592_);
lean_dec(v_a_4592_);
lean_dec_ref(v_a_4591_);
lean_dec(v_a_4590_);
lean_dec_ref(v_a_4589_);
return v_res_4597_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4(lean_object* v_upperBound_4598_, lean_object* v___x_4599_, lean_object* v_pre_4600_, lean_object* v_post_4601_, uint8_t v_usedLetOnly_4602_, uint8_t v_skipConstInApp_4603_, uint8_t v_skipInstances_4604_, lean_object* v___x_4605_, lean_object* v_inst_4606_, lean_object* v_R_4607_, lean_object* v_a_4608_, lean_object* v_b_4609_, lean_object* v_c_4610_, lean_object* v___y_4611_, lean_object* v___y_4612_, lean_object* v___y_4613_, lean_object* v___y_4614_, lean_object* v___y_4615_){
_start:
{
lean_object* v___x_4617_; 
v___x_4617_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg(v_upperBound_4598_, v___x_4599_, v_pre_4600_, v_post_4601_, v_usedLetOnly_4602_, v_skipConstInApp_4603_, v_skipInstances_4604_, v_a_4608_, v_b_4609_, v___y_4611_, v___y_4612_, v___y_4613_, v___y_4614_, v___y_4615_);
return v___x_4617_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___boxed(lean_object** _args){
lean_object* v_upperBound_4618_ = _args[0];
lean_object* v___x_4619_ = _args[1];
lean_object* v_pre_4620_ = _args[2];
lean_object* v_post_4621_ = _args[3];
lean_object* v_usedLetOnly_4622_ = _args[4];
lean_object* v_skipConstInApp_4623_ = _args[5];
lean_object* v_skipInstances_4624_ = _args[6];
lean_object* v___x_4625_ = _args[7];
lean_object* v_inst_4626_ = _args[8];
lean_object* v_R_4627_ = _args[9];
lean_object* v_a_4628_ = _args[10];
lean_object* v_b_4629_ = _args[11];
lean_object* v_c_4630_ = _args[12];
lean_object* v___y_4631_ = _args[13];
lean_object* v___y_4632_ = _args[14];
lean_object* v___y_4633_ = _args[15];
lean_object* v___y_4634_ = _args[16];
lean_object* v___y_4635_ = _args[17];
lean_object* v___y_4636_ = _args[18];
_start:
{
uint8_t v_usedLetOnly_boxed_4637_; uint8_t v_skipConstInApp_boxed_4638_; uint8_t v_skipInstances_boxed_4639_; lean_object* v_res_4640_; 
v_usedLetOnly_boxed_4637_ = lean_unbox(v_usedLetOnly_4622_);
v_skipConstInApp_boxed_4638_ = lean_unbox(v_skipConstInApp_4623_);
v_skipInstances_boxed_4639_ = lean_unbox(v_skipInstances_4624_);
v_res_4640_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4(v_upperBound_4618_, v___x_4619_, v_pre_4620_, v_post_4621_, v_usedLetOnly_boxed_4637_, v_skipConstInApp_boxed_4638_, v_skipInstances_boxed_4639_, v___x_4625_, v_inst_4626_, v_R_4627_, v_a_4628_, v_b_4629_, v_c_4630_, v___y_4631_, v___y_4632_, v___y_4633_, v___y_4634_, v___y_4635_);
lean_dec(v___y_4635_);
lean_dec_ref(v___y_4634_);
lean_dec(v___y_4633_);
lean_dec_ref(v___y_4632_);
lean_dec(v___y_4631_);
lean_dec(v___x_4625_);
lean_dec_ref(v___x_4619_);
lean_dec(v_upperBound_4618_);
return v_res_4640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6(lean_object* v_00_u03b1_4641_, lean_object* v_name_4642_, uint8_t v_bi_4643_, lean_object* v_type_4644_, lean_object* v_k_4645_, uint8_t v_kind_4646_, lean_object* v___y_4647_, lean_object* v___y_4648_, lean_object* v___y_4649_, lean_object* v___y_4650_, lean_object* v___y_4651_){
_start:
{
lean_object* v___x_4653_; 
v___x_4653_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_name_4642_, v_bi_4643_, v_type_4644_, v_k_4645_, v_kind_4646_, v___y_4647_, v___y_4648_, v___y_4649_, v___y_4650_, v___y_4651_);
return v___x_4653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___boxed(lean_object* v_00_u03b1_4654_, lean_object* v_name_4655_, lean_object* v_bi_4656_, lean_object* v_type_4657_, lean_object* v_k_4658_, lean_object* v_kind_4659_, lean_object* v___y_4660_, lean_object* v___y_4661_, lean_object* v___y_4662_, lean_object* v___y_4663_, lean_object* v___y_4664_, lean_object* v___y_4665_){
_start:
{
uint8_t v_bi_boxed_4666_; uint8_t v_kind_boxed_4667_; lean_object* v_res_4668_; 
v_bi_boxed_4666_ = lean_unbox(v_bi_4656_);
v_kind_boxed_4667_ = lean_unbox(v_kind_4659_);
v_res_4668_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6(v_00_u03b1_4654_, v_name_4655_, v_bi_boxed_4666_, v_type_4657_, v_k_4658_, v_kind_boxed_4667_, v___y_4660_, v___y_4661_, v___y_4662_, v___y_4663_, v___y_4664_);
lean_dec(v___y_4664_);
lean_dec_ref(v___y_4663_);
lean_dec(v___y_4662_);
lean_dec_ref(v___y_4661_);
lean_dec(v___y_4660_);
return v_res_4668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9(lean_object* v_00_u03b1_4669_, lean_object* v_name_4670_, lean_object* v_type_4671_, lean_object* v_val_4672_, lean_object* v_k_4673_, uint8_t v_nondep_4674_, uint8_t v_kind_4675_, lean_object* v___y_4676_, lean_object* v___y_4677_, lean_object* v___y_4678_, lean_object* v___y_4679_, lean_object* v___y_4680_){
_start:
{
lean_object* v___x_4682_; 
v___x_4682_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg(v_name_4670_, v_type_4671_, v_val_4672_, v_k_4673_, v_nondep_4674_, v_kind_4675_, v___y_4676_, v___y_4677_, v___y_4678_, v___y_4679_, v___y_4680_);
return v___x_4682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___boxed(lean_object* v_00_u03b1_4683_, lean_object* v_name_4684_, lean_object* v_type_4685_, lean_object* v_val_4686_, lean_object* v_k_4687_, lean_object* v_nondep_4688_, lean_object* v_kind_4689_, lean_object* v___y_4690_, lean_object* v___y_4691_, lean_object* v___y_4692_, lean_object* v___y_4693_, lean_object* v___y_4694_, lean_object* v___y_4695_){
_start:
{
uint8_t v_nondep_boxed_4696_; uint8_t v_kind_boxed_4697_; lean_object* v_res_4698_; 
v_nondep_boxed_4696_ = lean_unbox(v_nondep_4688_);
v_kind_boxed_4697_ = lean_unbox(v_kind_4689_);
v_res_4698_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9(v_00_u03b1_4683_, v_name_4684_, v_type_4685_, v_val_4686_, v_k_4687_, v_nondep_boxed_4696_, v_kind_boxed_4697_, v___y_4690_, v___y_4691_, v___y_4692_, v___y_4693_, v___y_4694_);
lean_dec(v___y_4694_);
lean_dec_ref(v___y_4693_);
lean_dec(v___y_4692_);
lean_dec_ref(v___y_4691_);
lean_dec(v___y_4690_);
return v_res_4698_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12(lean_object* v_00_u03b1_4699_, lean_object* v_ref_4700_, lean_object* v___y_4701_, lean_object* v___y_4702_, lean_object* v___y_4703_, lean_object* v___y_4704_){
_start:
{
lean_object* v___x_4706_; 
v___x_4706_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg(v_ref_4700_);
return v___x_4706_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___boxed(lean_object* v_00_u03b1_4707_, lean_object* v_ref_4708_, lean_object* v___y_4709_, lean_object* v___y_4710_, lean_object* v___y_4711_, lean_object* v___y_4712_, lean_object* v___y_4713_){
_start:
{
lean_object* v_res_4714_; 
v_res_4714_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12(v_00_u03b1_4707_, v_ref_4708_, v___y_4709_, v___y_4710_, v___y_4711_, v___y_4712_);
lean_dec(v___y_4712_);
lean_dec_ref(v___y_4711_);
lean_dec(v___y_4710_);
lean_dec_ref(v___y_4709_);
return v_res_4714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9(lean_object* v_00_u03b1_4715_, lean_object* v_x_4716_, lean_object* v___y_4717_, lean_object* v___y_4718_, lean_object* v___y_4719_, lean_object* v___y_4720_, lean_object* v___y_4721_){
_start:
{
lean_object* v___x_4723_; 
v___x_4723_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg(v_x_4716_, v___y_4717_, v___y_4718_, v___y_4719_, v___y_4720_, v___y_4721_);
return v___x_4723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___boxed(lean_object* v_00_u03b1_4724_, lean_object* v_x_4725_, lean_object* v___y_4726_, lean_object* v___y_4727_, lean_object* v___y_4728_, lean_object* v___y_4729_, lean_object* v___y_4730_, lean_object* v___y_4731_){
_start:
{
lean_object* v_res_4732_; 
v_res_4732_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9(v_00_u03b1_4724_, v_x_4725_, v___y_4726_, v___y_4727_, v___y_4728_, v___y_4729_, v___y_4730_);
lean_dec(v___y_4730_);
lean_dec_ref(v___y_4729_);
lean_dec(v___y_4728_);
lean_dec_ref(v___y_4727_);
lean_dec(v___y_4726_);
return v_res_4732_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0_spec__0(lean_object* v_a_4733_, lean_object* v_as_4734_, size_t v_i_4735_, size_t v_stop_4736_){
_start:
{
uint8_t v___x_4737_; 
v___x_4737_ = lean_usize_dec_eq(v_i_4735_, v_stop_4736_);
if (v___x_4737_ == 0)
{
lean_object* v___x_4738_; uint8_t v___x_4739_; 
v___x_4738_ = lean_array_uget_borrowed(v_as_4734_, v_i_4735_);
v___x_4739_ = l_Lean_instBEqFVarId_beq(v_a_4733_, v___x_4738_);
if (v___x_4739_ == 0)
{
size_t v___x_4740_; size_t v___x_4741_; 
v___x_4740_ = ((size_t)1ULL);
v___x_4741_ = lean_usize_add(v_i_4735_, v___x_4740_);
v_i_4735_ = v___x_4741_;
goto _start;
}
else
{
return v___x_4739_;
}
}
else
{
uint8_t v___x_4743_; 
v___x_4743_ = 0;
return v___x_4743_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0_spec__0___boxed(lean_object* v_a_4744_, lean_object* v_as_4745_, lean_object* v_i_4746_, lean_object* v_stop_4747_){
_start:
{
size_t v_i_boxed_4748_; size_t v_stop_boxed_4749_; uint8_t v_res_4750_; lean_object* v_r_4751_; 
v_i_boxed_4748_ = lean_unbox_usize(v_i_4746_);
lean_dec(v_i_4746_);
v_stop_boxed_4749_ = lean_unbox_usize(v_stop_4747_);
lean_dec(v_stop_4747_);
v_res_4750_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0_spec__0(v_a_4744_, v_as_4745_, v_i_boxed_4748_, v_stop_boxed_4749_);
lean_dec_ref(v_as_4745_);
lean_dec(v_a_4744_);
v_r_4751_ = lean_box(v_res_4750_);
return v_r_4751_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0(lean_object* v_as_4752_, lean_object* v_a_4753_){
_start:
{
lean_object* v___x_4754_; lean_object* v___x_4755_; uint8_t v___x_4756_; 
v___x_4754_ = lean_unsigned_to_nat(0u);
v___x_4755_ = lean_array_get_size(v_as_4752_);
v___x_4756_ = lean_nat_dec_lt(v___x_4754_, v___x_4755_);
if (v___x_4756_ == 0)
{
return v___x_4756_;
}
else
{
if (v___x_4756_ == 0)
{
return v___x_4756_;
}
else
{
size_t v___x_4757_; size_t v___x_4758_; uint8_t v___x_4759_; 
v___x_4757_ = ((size_t)0ULL);
v___x_4758_ = lean_usize_of_nat(v___x_4755_);
v___x_4759_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0_spec__0(v_a_4753_, v_as_4752_, v___x_4757_, v___x_4758_);
return v___x_4759_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0___boxed(lean_object* v_as_4760_, lean_object* v_a_4761_){
_start:
{
uint8_t v_res_4762_; lean_object* v_r_4763_; 
v_res_4762_ = l_Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0(v_as_4760_, v_a_4761_);
lean_dec(v_a_4761_);
lean_dec_ref(v_as_4760_);
v_r_4763_ = lean_box(v_res_4762_);
return v_r_4763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaFVars___lam__1(lean_object* v_fvars_4764_, lean_object* v_e_4765_, lean_object* v___y_4766_, lean_object* v___y_4767_, lean_object* v___y_4768_, lean_object* v___y_4769_){
_start:
{
lean_object* v___x_4774_; 
v___x_4774_ = l_Lean_Expr_getAppFn(v_e_4765_);
if (lean_obj_tag(v___x_4774_) == 1)
{
lean_object* v_fvarId_4775_; uint8_t v___x_4776_; 
v_fvarId_4775_ = lean_ctor_get(v___x_4774_, 0);
lean_inc(v_fvarId_4775_);
lean_dec_ref(v___x_4774_);
v___x_4776_ = l_Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0(v_fvars_4764_, v_fvarId_4775_);
if (v___x_4776_ == 0)
{
lean_dec(v_fvarId_4775_);
lean_dec_ref(v_e_4765_);
goto v___jp_4771_;
}
else
{
uint8_t v___x_4777_; lean_object* v___x_4778_; 
v___x_4777_ = 0;
v___x_4778_ = l_Lean_FVarId_getValue_x3f___redArg(v_fvarId_4775_, v___x_4777_, v___y_4766_, v___y_4768_, v___y_4769_);
if (lean_obj_tag(v___x_4778_) == 0)
{
lean_object* v_a_4779_; 
v_a_4779_ = lean_ctor_get(v___x_4778_, 0);
lean_inc(v_a_4779_);
lean_dec_ref(v___x_4778_);
if (lean_obj_tag(v_a_4779_) == 1)
{
lean_object* v_val_4780_; lean_object* v___x_4782_; uint8_t v_isShared_4783_; uint8_t v_isSharedCheck_4803_; 
v_val_4780_ = lean_ctor_get(v_a_4779_, 0);
v_isSharedCheck_4803_ = !lean_is_exclusive(v_a_4779_);
if (v_isSharedCheck_4803_ == 0)
{
v___x_4782_ = v_a_4779_;
v_isShared_4783_ = v_isSharedCheck_4803_;
goto v_resetjp_4781_;
}
else
{
lean_inc(v_val_4780_);
lean_dec(v_a_4779_);
v___x_4782_ = lean_box(0);
v_isShared_4783_ = v_isSharedCheck_4803_;
goto v_resetjp_4781_;
}
v_resetjp_4781_:
{
lean_object* v___x_4784_; lean_object* v_a_4785_; lean_object* v___x_4787_; uint8_t v_isShared_4788_; uint8_t v_isSharedCheck_4802_; 
v___x_4784_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(v_val_4780_, v___y_4767_);
v_a_4785_ = lean_ctor_get(v___x_4784_, 0);
v_isSharedCheck_4802_ = !lean_is_exclusive(v___x_4784_);
if (v_isSharedCheck_4802_ == 0)
{
v___x_4787_ = v___x_4784_;
v_isShared_4788_ = v_isSharedCheck_4802_;
goto v_resetjp_4786_;
}
else
{
lean_inc(v_a_4785_);
lean_dec(v___x_4784_);
v___x_4787_ = lean_box(0);
v_isShared_4788_ = v_isSharedCheck_4802_;
goto v_resetjp_4786_;
}
v_resetjp_4786_:
{
lean_object* v_dummy_4789_; lean_object* v_nargs_4790_; lean_object* v___x_4791_; lean_object* v___x_4792_; lean_object* v___x_4793_; lean_object* v___x_4794_; lean_object* v___x_4795_; lean_object* v___x_4797_; 
v_dummy_4789_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_4790_ = l_Lean_Expr_getAppNumArgs(v_e_4765_);
lean_inc(v_nargs_4790_);
v___x_4791_ = lean_mk_array(v_nargs_4790_, v_dummy_4789_);
v___x_4792_ = lean_unsigned_to_nat(1u);
v___x_4793_ = lean_nat_sub(v_nargs_4790_, v___x_4792_);
lean_dec(v_nargs_4790_);
v___x_4794_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_4765_, v___x_4791_, v___x_4793_);
v___x_4795_ = l_Lean_Expr_beta(v_a_4785_, v___x_4794_);
if (v_isShared_4783_ == 0)
{
lean_ctor_set(v___x_4782_, 0, v___x_4795_);
v___x_4797_ = v___x_4782_;
goto v_reusejp_4796_;
}
else
{
lean_object* v_reuseFailAlloc_4801_; 
v_reuseFailAlloc_4801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4801_, 0, v___x_4795_);
v___x_4797_ = v_reuseFailAlloc_4801_;
goto v_reusejp_4796_;
}
v_reusejp_4796_:
{
lean_object* v___x_4799_; 
if (v_isShared_4788_ == 0)
{
lean_ctor_set(v___x_4787_, 0, v___x_4797_);
v___x_4799_ = v___x_4787_;
goto v_reusejp_4798_;
}
else
{
lean_object* v_reuseFailAlloc_4800_; 
v_reuseFailAlloc_4800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4800_, 0, v___x_4797_);
v___x_4799_ = v_reuseFailAlloc_4800_;
goto v_reusejp_4798_;
}
v_reusejp_4798_:
{
return v___x_4799_;
}
}
}
}
}
else
{
lean_dec(v_a_4779_);
lean_dec_ref(v_e_4765_);
goto v___jp_4771_;
}
}
else
{
lean_object* v_a_4804_; lean_object* v___x_4806_; uint8_t v_isShared_4807_; uint8_t v_isSharedCheck_4811_; 
lean_dec_ref(v_e_4765_);
v_a_4804_ = lean_ctor_get(v___x_4778_, 0);
v_isSharedCheck_4811_ = !lean_is_exclusive(v___x_4778_);
if (v_isSharedCheck_4811_ == 0)
{
v___x_4806_ = v___x_4778_;
v_isShared_4807_ = v_isSharedCheck_4811_;
goto v_resetjp_4805_;
}
else
{
lean_inc(v_a_4804_);
lean_dec(v___x_4778_);
v___x_4806_ = lean_box(0);
v_isShared_4807_ = v_isSharedCheck_4811_;
goto v_resetjp_4805_;
}
v_resetjp_4805_:
{
lean_object* v___x_4809_; 
if (v_isShared_4807_ == 0)
{
v___x_4809_ = v___x_4806_;
goto v_reusejp_4808_;
}
else
{
lean_object* v_reuseFailAlloc_4810_; 
v_reuseFailAlloc_4810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4810_, 0, v_a_4804_);
v___x_4809_ = v_reuseFailAlloc_4810_;
goto v_reusejp_4808_;
}
v_reusejp_4808_:
{
return v___x_4809_;
}
}
}
}
}
else
{
lean_object* v___x_4812_; lean_object* v___x_4813_; 
lean_dec_ref(v___x_4774_);
lean_dec_ref(v_e_4765_);
v___x_4812_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_4813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4813_, 0, v___x_4812_);
return v___x_4813_;
}
v___jp_4771_:
{
lean_object* v___x_4772_; lean_object* v___x_4773_; 
v___x_4772_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_4773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4773_, 0, v___x_4772_);
return v___x_4773_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaFVars___lam__1___boxed(lean_object* v_fvars_4814_, lean_object* v_e_4815_, lean_object* v___y_4816_, lean_object* v___y_4817_, lean_object* v___y_4818_, lean_object* v___y_4819_, lean_object* v___y_4820_){
_start:
{
lean_object* v_res_4821_; 
v_res_4821_ = l_Lean_Meta_zetaDeltaFVars___lam__1(v_fvars_4814_, v_e_4815_, v___y_4816_, v___y_4817_, v___y_4818_, v___y_4819_);
lean_dec(v___y_4819_);
lean_dec_ref(v___y_4818_);
lean_dec(v___y_4817_);
lean_dec_ref(v___y_4816_);
lean_dec_ref(v_fvars_4814_);
return v_res_4821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaFVars(lean_object* v_e_4822_, lean_object* v_fvars_4823_, lean_object* v_a_4824_, lean_object* v_a_4825_, lean_object* v_a_4826_, lean_object* v_a_4827_){
_start:
{
lean_object* v___f_4829_; lean_object* v_pre_4830_; uint8_t v___x_4831_; lean_object* v___x_4832_; 
v___f_4829_ = ((lean_object*)(l_Lean_Meta_zetaReduce___closed__0));
v_pre_4830_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaDeltaFVars___lam__1___boxed), 7, 1);
lean_closure_set(v_pre_4830_, 0, v_fvars_4823_);
v___x_4831_ = 0;
v___x_4832_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(v_e_4822_, v_pre_4830_, v___f_4829_, v___x_4831_, v___x_4831_, v_a_4824_, v_a_4825_, v_a_4826_, v_a_4827_);
return v___x_4832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaFVars___boxed(lean_object* v_e_4833_, lean_object* v_fvars_4834_, lean_object* v_a_4835_, lean_object* v_a_4836_, lean_object* v_a_4837_, lean_object* v_a_4838_, lean_object* v_a_4839_){
_start:
{
lean_object* v_res_4840_; 
v_res_4840_ = l_Lean_Meta_zetaDeltaFVars(v_e_4833_, v_fvars_4834_, v_a_4835_, v_a_4836_, v_a_4837_, v_a_4838_);
lean_dec(v_a_4838_);
lean_dec_ref(v_a_4837_);
lean_dec(v_a_4836_);
lean_dec_ref(v_a_4835_);
return v_res_4840_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_4841_; 
v___x_4841_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4841_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_4842_; lean_object* v___x_4843_; 
v___x_4842_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__0, &l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__0);
v___x_4843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4843_, 0, v___x_4842_);
return v___x_4843_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_4844_; lean_object* v___x_4845_; 
v___x_4844_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__1, &l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__1);
v___x_4845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4845_, 0, v___x_4844_);
lean_ctor_set(v___x_4845_, 1, v___x_4844_);
return v___x_4845_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(lean_object* v_env_4846_, lean_object* v___y_4847_){
_start:
{
lean_object* v___x_4849_; lean_object* v_nextMacroScope_4850_; lean_object* v_ngen_4851_; lean_object* v_auxDeclNGen_4852_; lean_object* v_traceState_4853_; lean_object* v_messages_4854_; lean_object* v_infoState_4855_; lean_object* v_snapshotTasks_4856_; lean_object* v___x_4858_; uint8_t v_isShared_4859_; uint8_t v_isSharedCheck_4867_; 
v___x_4849_ = lean_st_ref_take(v___y_4847_);
v_nextMacroScope_4850_ = lean_ctor_get(v___x_4849_, 1);
v_ngen_4851_ = lean_ctor_get(v___x_4849_, 2);
v_auxDeclNGen_4852_ = lean_ctor_get(v___x_4849_, 3);
v_traceState_4853_ = lean_ctor_get(v___x_4849_, 4);
v_messages_4854_ = lean_ctor_get(v___x_4849_, 6);
v_infoState_4855_ = lean_ctor_get(v___x_4849_, 7);
v_snapshotTasks_4856_ = lean_ctor_get(v___x_4849_, 8);
v_isSharedCheck_4867_ = !lean_is_exclusive(v___x_4849_);
if (v_isSharedCheck_4867_ == 0)
{
lean_object* v_unused_4868_; lean_object* v_unused_4869_; 
v_unused_4868_ = lean_ctor_get(v___x_4849_, 5);
lean_dec(v_unused_4868_);
v_unused_4869_ = lean_ctor_get(v___x_4849_, 0);
lean_dec(v_unused_4869_);
v___x_4858_ = v___x_4849_;
v_isShared_4859_ = v_isSharedCheck_4867_;
goto v_resetjp_4857_;
}
else
{
lean_inc(v_snapshotTasks_4856_);
lean_inc(v_infoState_4855_);
lean_inc(v_messages_4854_);
lean_inc(v_traceState_4853_);
lean_inc(v_auxDeclNGen_4852_);
lean_inc(v_ngen_4851_);
lean_inc(v_nextMacroScope_4850_);
lean_dec(v___x_4849_);
v___x_4858_ = lean_box(0);
v_isShared_4859_ = v_isSharedCheck_4867_;
goto v_resetjp_4857_;
}
v_resetjp_4857_:
{
lean_object* v___x_4860_; lean_object* v___x_4862_; 
v___x_4860_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2, &l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2);
if (v_isShared_4859_ == 0)
{
lean_ctor_set(v___x_4858_, 5, v___x_4860_);
lean_ctor_set(v___x_4858_, 0, v_env_4846_);
v___x_4862_ = v___x_4858_;
goto v_reusejp_4861_;
}
else
{
lean_object* v_reuseFailAlloc_4866_; 
v_reuseFailAlloc_4866_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4866_, 0, v_env_4846_);
lean_ctor_set(v_reuseFailAlloc_4866_, 1, v_nextMacroScope_4850_);
lean_ctor_set(v_reuseFailAlloc_4866_, 2, v_ngen_4851_);
lean_ctor_set(v_reuseFailAlloc_4866_, 3, v_auxDeclNGen_4852_);
lean_ctor_set(v_reuseFailAlloc_4866_, 4, v_traceState_4853_);
lean_ctor_set(v_reuseFailAlloc_4866_, 5, v___x_4860_);
lean_ctor_set(v_reuseFailAlloc_4866_, 6, v_messages_4854_);
lean_ctor_set(v_reuseFailAlloc_4866_, 7, v_infoState_4855_);
lean_ctor_set(v_reuseFailAlloc_4866_, 8, v_snapshotTasks_4856_);
v___x_4862_ = v_reuseFailAlloc_4866_;
goto v_reusejp_4861_;
}
v_reusejp_4861_:
{
lean_object* v___x_4863_; lean_object* v___x_4864_; lean_object* v___x_4865_; 
v___x_4863_ = lean_st_ref_set(v___y_4847_, v___x_4862_);
v___x_4864_ = lean_box(0);
v___x_4865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4865_, 0, v___x_4864_);
return v___x_4865_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___boxed(lean_object* v_env_4870_, lean_object* v___y_4871_, lean_object* v___y_4872_){
_start:
{
lean_object* v_res_4873_; 
v_res_4873_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_4870_, v___y_4871_);
lean_dec(v___y_4871_);
return v_res_4873_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0(lean_object* v_env_4874_, lean_object* v___y_4875_, lean_object* v___y_4876_){
_start:
{
lean_object* v___x_4878_; 
v___x_4878_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_4874_, v___y_4876_);
return v___x_4878_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___boxed(lean_object* v_env_4879_, lean_object* v___y_4880_, lean_object* v___y_4881_, lean_object* v___y_4882_){
_start:
{
lean_object* v_res_4883_; 
v_res_4883_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0(v_env_4879_, v___y_4880_, v___y_4881_);
lean_dec(v___y_4881_);
lean_dec_ref(v___y_4880_);
return v_res_4883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___lam__1(lean_object* v_env_4884_, lean_object* v___x_4885_, uint8_t v___x_4886_, lean_object* v_e_4887_, lean_object* v___y_4888_, lean_object* v___y_4889_){
_start:
{
if (lean_obj_tag(v_e_4887_) == 4)
{
lean_object* v_declName_4891_; lean_object* v_us_4892_; uint8_t v___x_4893_; uint8_t v___x_4894_; 
v_declName_4891_ = lean_ctor_get(v_e_4887_, 0);
v_us_4892_ = lean_ctor_get(v_e_4887_, 1);
v___x_4893_ = 1;
lean_inc(v_declName_4891_);
v___x_4894_ = l_Lean_Environment_contains(v_env_4884_, v_declName_4891_, v___x_4893_);
if (v___x_4894_ == 0)
{
lean_object* v___x_4895_; 
lean_inc(v_declName_4891_);
v___x_4895_ = l_Lean_Environment_find_x3f(v___x_4885_, v_declName_4891_, v___x_4886_);
if (lean_obj_tag(v___x_4895_) == 1)
{
lean_object* v_val_4896_; lean_object* v___x_4898_; uint8_t v_isShared_4899_; uint8_t v_isSharedCheck_4925_; 
v_val_4896_ = lean_ctor_get(v___x_4895_, 0);
v_isSharedCheck_4925_ = !lean_is_exclusive(v___x_4895_);
if (v_isSharedCheck_4925_ == 0)
{
v___x_4898_ = v___x_4895_;
v_isShared_4899_ = v_isSharedCheck_4925_;
goto v_resetjp_4897_;
}
else
{
lean_inc(v_val_4896_);
lean_dec(v___x_4895_);
v___x_4898_ = lean_box(0);
v_isShared_4899_ = v_isSharedCheck_4925_;
goto v_resetjp_4897_;
}
v_resetjp_4897_:
{
uint8_t v___x_4900_; 
v___x_4900_ = l_Lean_ConstantInfo_hasValue(v_val_4896_, v___x_4893_);
if (v___x_4900_ == 0)
{
lean_object* v___x_4902_; 
lean_dec(v_val_4896_);
if (v_isShared_4899_ == 0)
{
lean_ctor_set_tag(v___x_4898_, 0);
lean_ctor_set(v___x_4898_, 0, v_e_4887_);
v___x_4902_ = v___x_4898_;
goto v_reusejp_4901_;
}
else
{
lean_object* v_reuseFailAlloc_4904_; 
v_reuseFailAlloc_4904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4904_, 0, v_e_4887_);
v___x_4902_ = v_reuseFailAlloc_4904_;
goto v_reusejp_4901_;
}
v_reusejp_4901_:
{
lean_object* v___x_4903_; 
v___x_4903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4903_, 0, v___x_4902_);
return v___x_4903_;
}
}
else
{
lean_object* v___x_4905_; 
lean_inc(v_us_4892_);
lean_dec_ref(v_e_4887_);
v___x_4905_ = l_Lean_Core_instantiateValueLevelParams(v_val_4896_, v_us_4892_, v___x_4893_, v___y_4888_, v___y_4889_);
lean_dec(v_val_4896_);
if (lean_obj_tag(v___x_4905_) == 0)
{
lean_object* v_a_4906_; lean_object* v___x_4908_; uint8_t v_isShared_4909_; uint8_t v_isSharedCheck_4916_; 
v_a_4906_ = lean_ctor_get(v___x_4905_, 0);
v_isSharedCheck_4916_ = !lean_is_exclusive(v___x_4905_);
if (v_isSharedCheck_4916_ == 0)
{
v___x_4908_ = v___x_4905_;
v_isShared_4909_ = v_isSharedCheck_4916_;
goto v_resetjp_4907_;
}
else
{
lean_inc(v_a_4906_);
lean_dec(v___x_4905_);
v___x_4908_ = lean_box(0);
v_isShared_4909_ = v_isSharedCheck_4916_;
goto v_resetjp_4907_;
}
v_resetjp_4907_:
{
lean_object* v___x_4911_; 
if (v_isShared_4899_ == 0)
{
lean_ctor_set(v___x_4898_, 0, v_a_4906_);
v___x_4911_ = v___x_4898_;
goto v_reusejp_4910_;
}
else
{
lean_object* v_reuseFailAlloc_4915_; 
v_reuseFailAlloc_4915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4915_, 0, v_a_4906_);
v___x_4911_ = v_reuseFailAlloc_4915_;
goto v_reusejp_4910_;
}
v_reusejp_4910_:
{
lean_object* v___x_4913_; 
if (v_isShared_4909_ == 0)
{
lean_ctor_set(v___x_4908_, 0, v___x_4911_);
v___x_4913_ = v___x_4908_;
goto v_reusejp_4912_;
}
else
{
lean_object* v_reuseFailAlloc_4914_; 
v_reuseFailAlloc_4914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4914_, 0, v___x_4911_);
v___x_4913_ = v_reuseFailAlloc_4914_;
goto v_reusejp_4912_;
}
v_reusejp_4912_:
{
return v___x_4913_;
}
}
}
}
else
{
lean_object* v_a_4917_; lean_object* v___x_4919_; uint8_t v_isShared_4920_; uint8_t v_isSharedCheck_4924_; 
lean_del_object(v___x_4898_);
v_a_4917_ = lean_ctor_get(v___x_4905_, 0);
v_isSharedCheck_4924_ = !lean_is_exclusive(v___x_4905_);
if (v_isSharedCheck_4924_ == 0)
{
v___x_4919_ = v___x_4905_;
v_isShared_4920_ = v_isSharedCheck_4924_;
goto v_resetjp_4918_;
}
else
{
lean_inc(v_a_4917_);
lean_dec(v___x_4905_);
v___x_4919_ = lean_box(0);
v_isShared_4920_ = v_isSharedCheck_4924_;
goto v_resetjp_4918_;
}
v_resetjp_4918_:
{
lean_object* v___x_4922_; 
if (v_isShared_4920_ == 0)
{
v___x_4922_ = v___x_4919_;
goto v_reusejp_4921_;
}
else
{
lean_object* v_reuseFailAlloc_4923_; 
v_reuseFailAlloc_4923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4923_, 0, v_a_4917_);
v___x_4922_ = v_reuseFailAlloc_4923_;
goto v_reusejp_4921_;
}
v_reusejp_4921_:
{
return v___x_4922_;
}
}
}
}
}
}
else
{
lean_object* v___x_4926_; lean_object* v___x_4927_; 
lean_dec(v___x_4895_);
v___x_4926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4926_, 0, v_e_4887_);
v___x_4927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4927_, 0, v___x_4926_);
return v___x_4927_;
}
}
else
{
lean_object* v___x_4928_; lean_object* v___x_4929_; 
lean_dec_ref(v___x_4885_);
v___x_4928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4928_, 0, v_e_4887_);
v___x_4929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4929_, 0, v___x_4928_);
return v___x_4929_;
}
}
else
{
lean_object* v___x_4930_; lean_object* v___x_4931_; 
lean_dec_ref(v_e_4887_);
lean_dec_ref(v___x_4885_);
lean_dec_ref(v_env_4884_);
v___x_4930_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_4931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4931_, 0, v___x_4930_);
return v___x_4931_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___lam__1___boxed(lean_object* v_env_4932_, lean_object* v___x_4933_, lean_object* v___x_4934_, lean_object* v_e_4935_, lean_object* v___y_4936_, lean_object* v___y_4937_, lean_object* v___y_4938_){
_start:
{
uint8_t v___x_2152__boxed_4939_; lean_object* v_res_4940_; 
v___x_2152__boxed_4939_ = lean_unbox(v___x_4934_);
v_res_4940_ = l_Lean_Meta_unfoldDeclsFrom___lam__1(v_env_4932_, v___x_4933_, v___x_2152__boxed_4939_, v_e_4935_, v___y_4936_, v___y_4937_);
lean_dec(v___y_4937_);
lean_dec_ref(v___y_4936_);
return v_res_4940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___lam__0(lean_object* v_biggerEnv_4941_, lean_object* v_e_4942_, lean_object* v___f_4943_, lean_object* v___y_4944_, lean_object* v___y_4945_){
_start:
{
lean_object* v___x_4947_; uint8_t v___x_4948_; lean_object* v___x_4949_; lean_object* v___x_4950_; lean_object* v_env_4951_; lean_object* v___x_4952_; lean_object* v___f_4953_; lean_object* v___x_4954_; 
v___x_4947_ = lean_st_ref_get(v___y_4945_);
v___x_4948_ = 0;
v___x_4949_ = l_Lean_Environment_setExporting(v_biggerEnv_4941_, v___x_4948_);
lean_inc_ref(v___x_4949_);
v___x_4950_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v___x_4949_, v___y_4945_);
lean_dec_ref(v___x_4950_);
v_env_4951_ = lean_ctor_get(v___x_4947_, 0);
lean_inc_ref(v_env_4951_);
lean_dec(v___x_4947_);
v___x_4952_ = lean_box(v___x_4948_);
v___f_4953_ = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDeclsFrom___lam__1___boxed), 7, 3);
lean_closure_set(v___f_4953_, 0, v_env_4951_);
lean_closure_set(v___f_4953_, 1, v___x_4949_);
lean_closure_set(v___f_4953_, 2, v___x_4952_);
v___x_4954_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_4942_, v___f_4953_, v___f_4943_, v___y_4944_, v___y_4945_);
return v___x_4954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___lam__0___boxed(lean_object* v_biggerEnv_4955_, lean_object* v_e_4956_, lean_object* v___f_4957_, lean_object* v___y_4958_, lean_object* v___y_4959_, lean_object* v___y_4960_){
_start:
{
lean_object* v_res_4961_; 
v_res_4961_ = l_Lean_Meta_unfoldDeclsFrom___lam__0(v_biggerEnv_4955_, v_e_4956_, v___f_4957_, v___y_4958_, v___y_4959_);
lean_dec(v___y_4959_);
lean_dec_ref(v___y_4958_);
return v_res_4961_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg(lean_object* v_env_4962_, lean_object* v_x_4963_, lean_object* v___y_4964_, lean_object* v___y_4965_){
_start:
{
lean_object* v___x_4967_; lean_object* v_env_4968_; lean_object* v_a_4970_; lean_object* v___x_4980_; lean_object* v___x_4981_; 
v___x_4967_ = lean_st_ref_get(v___y_4965_);
v_env_4968_ = lean_ctor_get(v___x_4967_, 0);
lean_inc_ref(v_env_4968_);
lean_dec(v___x_4967_);
v___x_4980_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_4962_, v___y_4965_);
lean_dec_ref(v___x_4980_);
lean_inc(v___y_4965_);
lean_inc_ref(v___y_4964_);
v___x_4981_ = lean_apply_3(v_x_4963_, v___y_4964_, v___y_4965_, lean_box(0));
if (lean_obj_tag(v___x_4981_) == 0)
{
lean_object* v_a_4982_; lean_object* v___x_4983_; lean_object* v___x_4985_; uint8_t v_isShared_4986_; uint8_t v_isSharedCheck_4990_; 
v_a_4982_ = lean_ctor_get(v___x_4981_, 0);
lean_inc(v_a_4982_);
lean_dec_ref(v___x_4981_);
v___x_4983_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_4968_, v___y_4965_);
v_isSharedCheck_4990_ = !lean_is_exclusive(v___x_4983_);
if (v_isSharedCheck_4990_ == 0)
{
lean_object* v_unused_4991_; 
v_unused_4991_ = lean_ctor_get(v___x_4983_, 0);
lean_dec(v_unused_4991_);
v___x_4985_ = v___x_4983_;
v_isShared_4986_ = v_isSharedCheck_4990_;
goto v_resetjp_4984_;
}
else
{
lean_dec(v___x_4983_);
v___x_4985_ = lean_box(0);
v_isShared_4986_ = v_isSharedCheck_4990_;
goto v_resetjp_4984_;
}
v_resetjp_4984_:
{
lean_object* v___x_4988_; 
if (v_isShared_4986_ == 0)
{
lean_ctor_set(v___x_4985_, 0, v_a_4982_);
v___x_4988_ = v___x_4985_;
goto v_reusejp_4987_;
}
else
{
lean_object* v_reuseFailAlloc_4989_; 
v_reuseFailAlloc_4989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4989_, 0, v_a_4982_);
v___x_4988_ = v_reuseFailAlloc_4989_;
goto v_reusejp_4987_;
}
v_reusejp_4987_:
{
return v___x_4988_;
}
}
}
else
{
lean_object* v_a_4992_; 
v_a_4992_ = lean_ctor_get(v___x_4981_, 0);
lean_inc(v_a_4992_);
lean_dec_ref(v___x_4981_);
v_a_4970_ = v_a_4992_;
goto v___jp_4969_;
}
v___jp_4969_:
{
lean_object* v___x_4971_; lean_object* v___x_4973_; uint8_t v_isShared_4974_; uint8_t v_isSharedCheck_4978_; 
v___x_4971_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_4968_, v___y_4965_);
v_isSharedCheck_4978_ = !lean_is_exclusive(v___x_4971_);
if (v_isSharedCheck_4978_ == 0)
{
lean_object* v_unused_4979_; 
v_unused_4979_ = lean_ctor_get(v___x_4971_, 0);
lean_dec(v_unused_4979_);
v___x_4973_ = v___x_4971_;
v_isShared_4974_ = v_isSharedCheck_4978_;
goto v_resetjp_4972_;
}
else
{
lean_dec(v___x_4971_);
v___x_4973_ = lean_box(0);
v_isShared_4974_ = v_isSharedCheck_4978_;
goto v_resetjp_4972_;
}
v_resetjp_4972_:
{
lean_object* v___x_4976_; 
if (v_isShared_4974_ == 0)
{
lean_ctor_set_tag(v___x_4973_, 1);
lean_ctor_set(v___x_4973_, 0, v_a_4970_);
v___x_4976_ = v___x_4973_;
goto v_reusejp_4975_;
}
else
{
lean_object* v_reuseFailAlloc_4977_; 
v_reuseFailAlloc_4977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4977_, 0, v_a_4970_);
v___x_4976_ = v_reuseFailAlloc_4977_;
goto v_reusejp_4975_;
}
v_reusejp_4975_:
{
return v___x_4976_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg___boxed(lean_object* v_env_4993_, lean_object* v_x_4994_, lean_object* v___y_4995_, lean_object* v___y_4996_, lean_object* v___y_4997_){
_start:
{
lean_object* v_res_4998_; 
v_res_4998_ = l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg(v_env_4993_, v_x_4994_, v___y_4995_, v___y_4996_);
lean_dec(v___y_4996_);
lean_dec_ref(v___y_4995_);
return v_res_4998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom(lean_object* v_biggerEnv_4999_, lean_object* v_e_5000_, lean_object* v_a_5001_, lean_object* v_a_5002_){
_start:
{
lean_object* v___x_5004_; lean_object* v_env_5005_; lean_object* v___f_5006_; lean_object* v___f_5007_; lean_object* v___x_5008_; lean_object* v___x_5009_; 
v___x_5004_ = lean_st_ref_get(v_a_5002_);
v_env_5005_ = lean_ctor_get(v___x_5004_, 0);
lean_inc_ref(v_env_5005_);
lean_dec(v___x_5004_);
v___f_5006_ = ((lean_object*)(l_Lean_Core_betaReduce___closed__1));
v___f_5007_ = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDeclsFrom___lam__0___boxed), 6, 3);
lean_closure_set(v___f_5007_, 0, v_biggerEnv_4999_);
lean_closure_set(v___f_5007_, 1, v_e_5000_);
lean_closure_set(v___f_5007_, 2, v___f_5006_);
v___x_5008_ = l_Lean_Environment_unlockAsync(v_env_5005_);
v___x_5009_ = l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg(v___x_5008_, v___f_5007_, v_a_5001_, v_a_5002_);
return v___x_5009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___boxed(lean_object* v_biggerEnv_5010_, lean_object* v_e_5011_, lean_object* v_a_5012_, lean_object* v_a_5013_, lean_object* v_a_5014_){
_start:
{
lean_object* v_res_5015_; 
v_res_5015_ = l_Lean_Meta_unfoldDeclsFrom(v_biggerEnv_5010_, v_e_5011_, v_a_5012_, v_a_5013_);
lean_dec(v_a_5013_);
lean_dec_ref(v_a_5012_);
return v_res_5015_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1(lean_object* v_00_u03b1_5016_, lean_object* v_env_5017_, lean_object* v_x_5018_, lean_object* v___y_5019_, lean_object* v___y_5020_){
_start:
{
lean_object* v___x_5022_; 
v___x_5022_ = l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg(v_env_5017_, v_x_5018_, v___y_5019_, v___y_5020_);
return v___x_5022_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___boxed(lean_object* v_00_u03b1_5023_, lean_object* v_env_5024_, lean_object* v_x_5025_, lean_object* v___y_5026_, lean_object* v___y_5027_, lean_object* v___y_5028_){
_start:
{
lean_object* v_res_5029_; 
v_res_5029_ = l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1(v_00_u03b1_5023_, v_env_5024_, v_x_5025_, v___y_5026_, v___y_5027_);
lean_dec(v___y_5027_);
lean_dec_ref(v___y_5026_);
return v_res_5029_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0(lean_object* v_af_5030_, lean_object* v_axs_5031_, lean_object* v_numSectionVars_5032_, lean_object* v_as_5033_, size_t v_i_5034_, size_t v_stop_5035_){
_start:
{
uint8_t v___x_5036_; 
v___x_5036_ = lean_usize_dec_eq(v_i_5034_, v_stop_5035_);
if (v___x_5036_ == 0)
{
uint8_t v___x_5037_; uint8_t v___y_5039_; lean_object* v___x_5043_; lean_object* v___x_5044_; uint8_t v___x_5045_; 
v___x_5037_ = 1;
v___x_5043_ = lean_array_uget_borrowed(v_as_5033_, v_i_5034_);
v___x_5044_ = l_Lean_Expr_constName_x21(v_af_5030_);
v___x_5045_ = lean_name_eq(v___x_5044_, v___x_5043_);
lean_dec(v___x_5044_);
if (v___x_5045_ == 0)
{
v___y_5039_ = v___x_5045_;
goto v___jp_5038_;
}
else
{
lean_object* v___x_5046_; uint8_t v___x_5047_; 
v___x_5046_ = lean_array_get_size(v_axs_5031_);
v___x_5047_ = lean_nat_dec_le(v___x_5046_, v_numSectionVars_5032_);
v___y_5039_ = v___x_5047_;
goto v___jp_5038_;
}
v___jp_5038_:
{
if (v___y_5039_ == 0)
{
size_t v___x_5040_; size_t v___x_5041_; 
v___x_5040_ = ((size_t)1ULL);
v___x_5041_ = lean_usize_add(v_i_5034_, v___x_5040_);
v_i_5034_ = v___x_5041_;
goto _start;
}
else
{
return v___x_5037_;
}
}
}
else
{
uint8_t v___x_5048_; 
v___x_5048_ = 0;
return v___x_5048_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0___boxed(lean_object* v_af_5049_, lean_object* v_axs_5050_, lean_object* v_numSectionVars_5051_, lean_object* v_as_5052_, lean_object* v_i_5053_, lean_object* v_stop_5054_){
_start:
{
size_t v_i_boxed_5055_; size_t v_stop_boxed_5056_; uint8_t v_res_5057_; lean_object* v_r_5058_; 
v_i_boxed_5055_ = lean_unbox_usize(v_i_5053_);
lean_dec(v_i_5053_);
v_stop_boxed_5056_ = lean_unbox_usize(v_stop_5054_);
lean_dec(v_stop_5054_);
v_res_5057_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0(v_af_5049_, v_axs_5050_, v_numSectionVars_5051_, v_as_5052_, v_i_boxed_5055_, v_stop_boxed_5056_);
lean_dec_ref(v_as_5052_);
lean_dec(v_numSectionVars_5051_);
lean_dec_ref(v_axs_5050_);
lean_dec_ref(v_af_5049_);
v_r_5058_ = lean_box(v_res_5057_);
return v_r_5058_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1_spec__1(lean_object* v_fnNames_5059_, lean_object* v_numSectionVars_5060_, lean_object* v_x_5061_, lean_object* v_x_5062_, lean_object* v_x_5063_){
_start:
{
if (lean_obj_tag(v_x_5061_) == 5)
{
lean_object* v_fn_5064_; lean_object* v_arg_5065_; lean_object* v___x_5066_; lean_object* v___x_5067_; lean_object* v___x_5068_; 
v_fn_5064_ = lean_ctor_get(v_x_5061_, 0);
lean_inc_ref(v_fn_5064_);
v_arg_5065_ = lean_ctor_get(v_x_5061_, 1);
lean_inc_ref(v_arg_5065_);
lean_dec_ref(v_x_5061_);
v___x_5066_ = lean_array_set(v_x_5062_, v_x_5063_, v_arg_5065_);
v___x_5067_ = lean_unsigned_to_nat(1u);
v___x_5068_ = lean_nat_sub(v_x_5063_, v___x_5067_);
lean_dec(v_x_5063_);
v_x_5061_ = v_fn_5064_;
v_x_5062_ = v___x_5066_;
v_x_5063_ = v___x_5068_;
goto _start;
}
else
{
uint8_t v___x_5070_; 
lean_dec(v_x_5063_);
v___x_5070_ = l_Lean_Expr_isConst(v_x_5061_);
if (v___x_5070_ == 0)
{
lean_dec_ref(v_x_5062_);
lean_dec_ref(v_x_5061_);
return v___x_5070_;
}
else
{
lean_object* v___x_5071_; lean_object* v___x_5072_; uint8_t v___x_5073_; 
v___x_5071_ = lean_unsigned_to_nat(0u);
v___x_5072_ = lean_array_get_size(v_fnNames_5059_);
v___x_5073_ = lean_nat_dec_lt(v___x_5071_, v___x_5072_);
if (v___x_5073_ == 0)
{
lean_dec_ref(v_x_5062_);
lean_dec_ref(v_x_5061_);
return v___x_5073_;
}
else
{
if (v___x_5073_ == 0)
{
lean_dec_ref(v_x_5062_);
lean_dec_ref(v_x_5061_);
return v___x_5073_;
}
else
{
size_t v___x_5074_; size_t v___x_5075_; uint8_t v___x_5076_; 
v___x_5074_ = ((size_t)0ULL);
v___x_5075_ = lean_usize_of_nat(v___x_5072_);
v___x_5076_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0(v_x_5061_, v_x_5062_, v_numSectionVars_5060_, v_fnNames_5059_, v___x_5074_, v___x_5075_);
lean_dec_ref(v_x_5062_);
lean_dec_ref(v_x_5061_);
return v___x_5076_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1_spec__1___boxed(lean_object* v_fnNames_5077_, lean_object* v_numSectionVars_5078_, lean_object* v_x_5079_, lean_object* v_x_5080_, lean_object* v_x_5081_){
_start:
{
uint8_t v_res_5082_; lean_object* v_r_5083_; 
v_res_5082_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1_spec__1(v_fnNames_5077_, v_numSectionVars_5078_, v_x_5079_, v_x_5080_, v_x_5081_);
lean_dec(v_numSectionVars_5078_);
lean_dec_ref(v_fnNames_5077_);
v_r_5083_ = lean_box(v_res_5082_);
return v_r_5083_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1(lean_object* v_numSectionVars_5084_, lean_object* v_fnNames_5085_, lean_object* v_x_5086_, lean_object* v_x_5087_, lean_object* v_x_5088_){
_start:
{
if (lean_obj_tag(v_x_5086_) == 5)
{
lean_object* v_fn_5089_; lean_object* v_arg_5090_; lean_object* v___x_5091_; lean_object* v___x_5092_; lean_object* v___x_5093_; uint8_t v___x_5094_; 
v_fn_5089_ = lean_ctor_get(v_x_5086_, 0);
lean_inc_ref(v_fn_5089_);
v_arg_5090_ = lean_ctor_get(v_x_5086_, 1);
lean_inc_ref(v_arg_5090_);
lean_dec_ref(v_x_5086_);
v___x_5091_ = lean_array_set(v_x_5087_, v_x_5088_, v_arg_5090_);
v___x_5092_ = lean_unsigned_to_nat(1u);
v___x_5093_ = lean_nat_sub(v_x_5088_, v___x_5092_);
v___x_5094_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1_spec__1(v_fnNames_5085_, v_numSectionVars_5084_, v_fn_5089_, v___x_5091_, v___x_5093_);
return v___x_5094_;
}
else
{
uint8_t v___x_5095_; 
v___x_5095_ = l_Lean_Expr_isConst(v_x_5086_);
if (v___x_5095_ == 0)
{
lean_dec_ref(v_x_5087_);
lean_dec_ref(v_x_5086_);
return v___x_5095_;
}
else
{
lean_object* v___x_5096_; lean_object* v___x_5097_; uint8_t v___x_5098_; 
v___x_5096_ = lean_unsigned_to_nat(0u);
v___x_5097_ = lean_array_get_size(v_fnNames_5085_);
v___x_5098_ = lean_nat_dec_lt(v___x_5096_, v___x_5097_);
if (v___x_5098_ == 0)
{
lean_dec_ref(v_x_5087_);
lean_dec_ref(v_x_5086_);
return v___x_5098_;
}
else
{
if (v___x_5098_ == 0)
{
lean_dec_ref(v_x_5087_);
lean_dec_ref(v_x_5086_);
return v___x_5098_;
}
else
{
size_t v___x_5099_; size_t v___x_5100_; uint8_t v___x_5101_; 
v___x_5099_ = ((size_t)0ULL);
v___x_5100_ = lean_usize_of_nat(v___x_5097_);
v___x_5101_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0(v_x_5086_, v_x_5087_, v_numSectionVars_5084_, v_fnNames_5085_, v___x_5099_, v___x_5100_);
lean_dec_ref(v_x_5087_);
lean_dec_ref(v_x_5086_);
return v___x_5101_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1___boxed(lean_object* v_numSectionVars_5102_, lean_object* v_fnNames_5103_, lean_object* v_x_5104_, lean_object* v_x_5105_, lean_object* v_x_5106_){
_start:
{
uint8_t v_res_5107_; lean_object* v_r_5108_; 
v_res_5107_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1(v_numSectionVars_5102_, v_fnNames_5103_, v_x_5104_, v_x_5105_, v_x_5106_);
lean_dec(v_x_5106_);
lean_dec_ref(v_fnNames_5103_);
lean_dec(v_numSectionVars_5102_);
v_r_5108_ = lean_box(v_res_5107_);
return v_r_5108_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg(lean_object* v_fnNames_5109_, lean_object* v_numSectionVars_5110_, lean_object* v_a_5111_){
_start:
{
lean_object* v_dummy_5112_; lean_object* v_nargs_5113_; lean_object* v___x_5114_; lean_object* v___x_5115_; lean_object* v___x_5116_; uint8_t v___x_5117_; 
v_dummy_5112_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_5113_ = l_Lean_Expr_getAppNumArgs(v_a_5111_);
lean_inc(v_nargs_5113_);
v___x_5114_ = lean_mk_array(v_nargs_5113_, v_dummy_5112_);
v___x_5115_ = lean_unsigned_to_nat(1u);
v___x_5116_ = lean_nat_sub(v_nargs_5113_, v___x_5115_);
lean_dec(v_nargs_5113_);
v___x_5117_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1(v_numSectionVars_5110_, v_fnNames_5109_, v_a_5111_, v___x_5114_, v___x_5116_);
lean_dec(v___x_5116_);
return v___x_5117_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg___boxed(lean_object* v_fnNames_5118_, lean_object* v_numSectionVars_5119_, lean_object* v_a_5120_){
_start:
{
uint8_t v_res_5121_; lean_object* v_r_5122_; 
v_res_5121_ = l___private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg(v_fnNames_5118_, v_numSectionVars_5119_, v_a_5120_);
lean_dec(v_numSectionVars_5119_);
lean_dec_ref(v_fnNames_5118_);
v_r_5122_ = lean_box(v_res_5121_);
return v_r_5122_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__0(lean_object* v_fnNames_5123_, lean_object* v_numSectionVars_5124_, lean_object* v_as_5125_, size_t v_i_5126_, size_t v_stop_5127_){
_start:
{
uint8_t v___x_5128_; 
v___x_5128_ = lean_usize_dec_eq(v_i_5126_, v_stop_5127_);
if (v___x_5128_ == 0)
{
lean_object* v___x_5129_; uint8_t v___x_5130_; 
v___x_5129_ = lean_array_uget_borrowed(v_as_5125_, v_i_5126_);
lean_inc(v___x_5129_);
v___x_5130_ = l___private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg(v_fnNames_5123_, v_numSectionVars_5124_, v___x_5129_);
if (v___x_5130_ == 0)
{
size_t v___x_5131_; size_t v___x_5132_; 
v___x_5131_ = ((size_t)1ULL);
v___x_5132_ = lean_usize_add(v_i_5126_, v___x_5131_);
v_i_5126_ = v___x_5132_;
goto _start;
}
else
{
return v___x_5130_;
}
}
else
{
uint8_t v___x_5134_; 
v___x_5134_ = 0;
return v___x_5134_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__0___boxed(lean_object* v_fnNames_5135_, lean_object* v_numSectionVars_5136_, lean_object* v_as_5137_, lean_object* v_i_5138_, lean_object* v_stop_5139_){
_start:
{
size_t v_i_boxed_5140_; size_t v_stop_boxed_5141_; uint8_t v_res_5142_; lean_object* v_r_5143_; 
v_i_boxed_5140_ = lean_unbox_usize(v_i_5138_);
lean_dec(v_i_5138_);
v_stop_boxed_5141_ = lean_unbox_usize(v_stop_5139_);
lean_dec(v_stop_5139_);
v_res_5142_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__0(v_fnNames_5135_, v_numSectionVars_5136_, v_as_5137_, v_i_boxed_5140_, v_stop_boxed_5141_);
lean_dec_ref(v_as_5137_);
lean_dec(v_numSectionVars_5136_);
lean_dec_ref(v_fnNames_5135_);
v_r_5143_ = lean_box(v_res_5142_);
return v_r_5143_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__1(lean_object* v_fnNames_5144_, lean_object* v_numSectionVars_5145_, lean_object* v___x_5146_, lean_object* v_x_5147_, lean_object* v_x_5148_, lean_object* v___y_5149_, lean_object* v___y_5150_){
_start:
{
if (lean_obj_tag(v_x_5147_) == 5)
{
lean_object* v_fn_5155_; lean_object* v_arg_5156_; lean_object* v___x_5157_; 
v_fn_5155_ = lean_ctor_get(v_x_5147_, 0);
lean_inc_ref(v_fn_5155_);
v_arg_5156_ = lean_ctor_get(v_x_5147_, 1);
lean_inc_ref(v_arg_5156_);
lean_dec_ref(v_x_5147_);
v___x_5157_ = lean_array_push(v_x_5148_, v_arg_5156_);
v_x_5147_ = v_fn_5155_;
v_x_5148_ = v___x_5157_;
goto _start;
}
else
{
uint8_t v___x_5159_; 
v___x_5159_ = l_Lean_Expr_isConst(v_x_5147_);
if (v___x_5159_ == 0)
{
lean_dec_ref(v_x_5148_);
lean_dec_ref(v_x_5147_);
lean_dec_ref(v___x_5146_);
goto v___jp_5152_;
}
else
{
lean_object* v___x_5160_; lean_object* v___x_5161_; uint8_t v___x_5162_; 
v___x_5160_ = lean_unsigned_to_nat(0u);
v___x_5161_ = lean_array_get_size(v_x_5148_);
v___x_5162_ = lean_nat_dec_lt(v___x_5160_, v___x_5161_);
if (v___x_5162_ == 0)
{
lean_dec_ref(v_x_5148_);
lean_dec_ref(v_x_5147_);
lean_dec_ref(v___x_5146_);
goto v___jp_5152_;
}
else
{
if (v___x_5162_ == 0)
{
lean_dec_ref(v_x_5148_);
lean_dec_ref(v_x_5147_);
lean_dec_ref(v___x_5146_);
goto v___jp_5152_;
}
else
{
size_t v___x_5163_; size_t v___x_5164_; uint8_t v___x_5165_; 
v___x_5163_ = ((size_t)0ULL);
v___x_5164_ = lean_usize_of_nat(v___x_5161_);
v___x_5165_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__0(v_fnNames_5144_, v_numSectionVars_5145_, v_x_5148_, v___x_5163_, v___x_5164_);
if (v___x_5165_ == 0)
{
lean_dec_ref(v_x_5148_);
lean_dec_ref(v_x_5147_);
lean_dec_ref(v___x_5146_);
goto v___jp_5152_;
}
else
{
lean_object* v___x_5166_; uint8_t v___x_5167_; lean_object* v___x_5168_; 
v___x_5166_ = l_Lean_Expr_constName_x21(v_x_5147_);
v___x_5167_ = 0;
v___x_5168_ = l_Lean_Environment_find_x3f(v___x_5146_, v___x_5166_, v___x_5167_);
if (lean_obj_tag(v___x_5168_) == 1)
{
lean_object* v_val_5169_; 
v_val_5169_ = lean_ctor_get(v___x_5168_, 0);
lean_inc(v_val_5169_);
lean_dec_ref(v___x_5168_);
if (lean_obj_tag(v_val_5169_) == 2)
{
lean_object* v___x_5170_; lean_object* v___x_5171_; lean_object* v___x_5173_; uint8_t v_isShared_5174_; uint8_t v_isSharedCheck_5195_; 
v___x_5170_ = l_Lean_Expr_constLevels_x21(v_x_5147_);
lean_dec_ref(v_x_5147_);
v___x_5171_ = l_Lean_Core_instantiateValueLevelParams(v_val_5169_, v___x_5170_, v___x_5159_, v___y_5149_, v___y_5150_);
v_isSharedCheck_5195_ = !lean_is_exclusive(v_val_5169_);
if (v_isSharedCheck_5195_ == 0)
{
lean_object* v_unused_5196_; 
v_unused_5196_ = lean_ctor_get(v_val_5169_, 0);
lean_dec(v_unused_5196_);
v___x_5173_ = v_val_5169_;
v_isShared_5174_ = v_isSharedCheck_5195_;
goto v_resetjp_5172_;
}
else
{
lean_dec(v_val_5169_);
v___x_5173_ = lean_box(0);
v_isShared_5174_ = v_isSharedCheck_5195_;
goto v_resetjp_5172_;
}
v_resetjp_5172_:
{
if (lean_obj_tag(v___x_5171_) == 0)
{
lean_object* v_a_5175_; lean_object* v___x_5177_; uint8_t v_isShared_5178_; uint8_t v_isSharedCheck_5186_; 
v_a_5175_ = lean_ctor_get(v___x_5171_, 0);
v_isSharedCheck_5186_ = !lean_is_exclusive(v___x_5171_);
if (v_isSharedCheck_5186_ == 0)
{
v___x_5177_ = v___x_5171_;
v_isShared_5178_ = v_isSharedCheck_5186_;
goto v_resetjp_5176_;
}
else
{
lean_inc(v_a_5175_);
lean_dec(v___x_5171_);
v___x_5177_ = lean_box(0);
v_isShared_5178_ = v_isSharedCheck_5186_;
goto v_resetjp_5176_;
}
v_resetjp_5176_:
{
lean_object* v___x_5179_; lean_object* v___x_5181_; 
v___x_5179_ = l_Lean_Expr_betaRev(v_a_5175_, v_x_5148_, v___x_5167_, v___x_5167_);
lean_dec_ref(v_x_5148_);
if (v_isShared_5174_ == 0)
{
lean_ctor_set_tag(v___x_5173_, 1);
lean_ctor_set(v___x_5173_, 0, v___x_5179_);
v___x_5181_ = v___x_5173_;
goto v_reusejp_5180_;
}
else
{
lean_object* v_reuseFailAlloc_5185_; 
v_reuseFailAlloc_5185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5185_, 0, v___x_5179_);
v___x_5181_ = v_reuseFailAlloc_5185_;
goto v_reusejp_5180_;
}
v_reusejp_5180_:
{
lean_object* v___x_5183_; 
if (v_isShared_5178_ == 0)
{
lean_ctor_set(v___x_5177_, 0, v___x_5181_);
v___x_5183_ = v___x_5177_;
goto v_reusejp_5182_;
}
else
{
lean_object* v_reuseFailAlloc_5184_; 
v_reuseFailAlloc_5184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5184_, 0, v___x_5181_);
v___x_5183_ = v_reuseFailAlloc_5184_;
goto v_reusejp_5182_;
}
v_reusejp_5182_:
{
return v___x_5183_;
}
}
}
}
else
{
lean_object* v_a_5187_; lean_object* v___x_5189_; uint8_t v_isShared_5190_; uint8_t v_isSharedCheck_5194_; 
lean_del_object(v___x_5173_);
lean_dec_ref(v_x_5148_);
v_a_5187_ = lean_ctor_get(v___x_5171_, 0);
v_isSharedCheck_5194_ = !lean_is_exclusive(v___x_5171_);
if (v_isSharedCheck_5194_ == 0)
{
v___x_5189_ = v___x_5171_;
v_isShared_5190_ = v_isSharedCheck_5194_;
goto v_resetjp_5188_;
}
else
{
lean_inc(v_a_5187_);
lean_dec(v___x_5171_);
v___x_5189_ = lean_box(0);
v_isShared_5190_ = v_isSharedCheck_5194_;
goto v_resetjp_5188_;
}
v_resetjp_5188_:
{
lean_object* v___x_5192_; 
if (v_isShared_5190_ == 0)
{
v___x_5192_ = v___x_5189_;
goto v_reusejp_5191_;
}
else
{
lean_object* v_reuseFailAlloc_5193_; 
v_reuseFailAlloc_5193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5193_, 0, v_a_5187_);
v___x_5192_ = v_reuseFailAlloc_5193_;
goto v_reusejp_5191_;
}
v_reusejp_5191_:
{
return v___x_5192_;
}
}
}
}
}
else
{
lean_dec(v_val_5169_);
lean_dec_ref(v_x_5148_);
lean_dec_ref(v_x_5147_);
goto v___jp_5152_;
}
}
else
{
lean_dec(v___x_5168_);
lean_dec_ref(v_x_5148_);
lean_dec_ref(v_x_5147_);
goto v___jp_5152_;
}
}
}
}
}
}
v___jp_5152_:
{
lean_object* v___x_5153_; lean_object* v___x_5154_; 
v___x_5153_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_5154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5154_, 0, v___x_5153_);
return v___x_5154_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__1___boxed(lean_object* v_fnNames_5197_, lean_object* v_numSectionVars_5198_, lean_object* v___x_5199_, lean_object* v_x_5200_, lean_object* v_x_5201_, lean_object* v___y_5202_, lean_object* v___y_5203_, lean_object* v___y_5204_){
_start:
{
lean_object* v_res_5205_; 
v_res_5205_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__1(v_fnNames_5197_, v_numSectionVars_5198_, v___x_5199_, v_x_5200_, v_x_5201_, v___y_5202_, v___y_5203_);
lean_dec(v___y_5203_);
lean_dec_ref(v___y_5202_);
lean_dec(v_numSectionVars_5198_);
lean_dec_ref(v_fnNames_5197_);
return v_res_5205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___lam__1(lean_object* v_fnNames_5206_, lean_object* v_numSectionVars_5207_, lean_object* v_env_5208_, lean_object* v_e_5209_, lean_object* v___y_5210_, lean_object* v___y_5211_){
_start:
{
lean_object* v___x_5213_; lean_object* v___x_5214_; lean_object* v___x_5215_; 
v___x_5213_ = l_Lean_Expr_getAppNumArgs(v_e_5209_);
v___x_5214_ = lean_mk_empty_array_with_capacity(v___x_5213_);
lean_dec(v___x_5213_);
v___x_5215_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__1(v_fnNames_5206_, v_numSectionVars_5207_, v_env_5208_, v_e_5209_, v___x_5214_, v___y_5210_, v___y_5211_);
return v___x_5215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___lam__1___boxed(lean_object* v_fnNames_5216_, lean_object* v_numSectionVars_5217_, lean_object* v_env_5218_, lean_object* v_e_5219_, lean_object* v___y_5220_, lean_object* v___y_5221_, lean_object* v___y_5222_){
_start:
{
lean_object* v_res_5223_; 
v_res_5223_ = l_Lean_Meta_unfoldIfArgIsAppOf___lam__1(v_fnNames_5216_, v_numSectionVars_5217_, v_env_5218_, v_e_5219_, v___y_5220_, v___y_5221_);
lean_dec(v___y_5221_);
lean_dec_ref(v___y_5220_);
lean_dec(v_numSectionVars_5217_);
lean_dec_ref(v_fnNames_5216_);
return v_res_5223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___lam__0(lean_object* v_fnNames_5224_, lean_object* v_numSectionVars_5225_, lean_object* v_e_5226_, lean_object* v___f_5227_, lean_object* v___y_5228_, lean_object* v___y_5229_){
_start:
{
lean_object* v___x_5231_; lean_object* v_env_5232_; lean_object* v___f_5233_; lean_object* v___x_5234_; 
v___x_5231_ = lean_st_ref_get(v___y_5229_);
v_env_5232_ = lean_ctor_get(v___x_5231_, 0);
lean_inc_ref(v_env_5232_);
lean_dec(v___x_5231_);
v___f_5233_ = lean_alloc_closure((void*)(l_Lean_Meta_unfoldIfArgIsAppOf___lam__1___boxed), 7, 3);
lean_closure_set(v___f_5233_, 0, v_fnNames_5224_);
lean_closure_set(v___f_5233_, 1, v_numSectionVars_5225_);
lean_closure_set(v___f_5233_, 2, v_env_5232_);
v___x_5234_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_5226_, v___f_5233_, v___f_5227_, v___y_5228_, v___y_5229_);
return v___x_5234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___lam__0___boxed(lean_object* v_fnNames_5235_, lean_object* v_numSectionVars_5236_, lean_object* v_e_5237_, lean_object* v___f_5238_, lean_object* v___y_5239_, lean_object* v___y_5240_, lean_object* v___y_5241_){
_start:
{
lean_object* v_res_5242_; 
v_res_5242_ = l_Lean_Meta_unfoldIfArgIsAppOf___lam__0(v_fnNames_5235_, v_numSectionVars_5236_, v_e_5237_, v___f_5238_, v___y_5239_, v___y_5240_);
lean_dec(v___y_5240_);
lean_dec_ref(v___y_5239_);
return v_res_5242_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0(lean_object* v___y_5243_, uint8_t v_isExporting_5244_, lean_object* v___x_5245_, lean_object* v_a_x3f_5246_){
_start:
{
lean_object* v___x_5248_; lean_object* v_env_5249_; lean_object* v_nextMacroScope_5250_; lean_object* v_ngen_5251_; lean_object* v_auxDeclNGen_5252_; lean_object* v_traceState_5253_; lean_object* v_messages_5254_; lean_object* v_infoState_5255_; lean_object* v_snapshotTasks_5256_; lean_object* v___x_5258_; uint8_t v_isShared_5259_; uint8_t v_isSharedCheck_5267_; 
v___x_5248_ = lean_st_ref_take(v___y_5243_);
v_env_5249_ = lean_ctor_get(v___x_5248_, 0);
v_nextMacroScope_5250_ = lean_ctor_get(v___x_5248_, 1);
v_ngen_5251_ = lean_ctor_get(v___x_5248_, 2);
v_auxDeclNGen_5252_ = lean_ctor_get(v___x_5248_, 3);
v_traceState_5253_ = lean_ctor_get(v___x_5248_, 4);
v_messages_5254_ = lean_ctor_get(v___x_5248_, 6);
v_infoState_5255_ = lean_ctor_get(v___x_5248_, 7);
v_snapshotTasks_5256_ = lean_ctor_get(v___x_5248_, 8);
v_isSharedCheck_5267_ = !lean_is_exclusive(v___x_5248_);
if (v_isSharedCheck_5267_ == 0)
{
lean_object* v_unused_5268_; 
v_unused_5268_ = lean_ctor_get(v___x_5248_, 5);
lean_dec(v_unused_5268_);
v___x_5258_ = v___x_5248_;
v_isShared_5259_ = v_isSharedCheck_5267_;
goto v_resetjp_5257_;
}
else
{
lean_inc(v_snapshotTasks_5256_);
lean_inc(v_infoState_5255_);
lean_inc(v_messages_5254_);
lean_inc(v_traceState_5253_);
lean_inc(v_auxDeclNGen_5252_);
lean_inc(v_ngen_5251_);
lean_inc(v_nextMacroScope_5250_);
lean_inc(v_env_5249_);
lean_dec(v___x_5248_);
v___x_5258_ = lean_box(0);
v_isShared_5259_ = v_isSharedCheck_5267_;
goto v_resetjp_5257_;
}
v_resetjp_5257_:
{
lean_object* v___x_5260_; lean_object* v___x_5262_; 
v___x_5260_ = l_Lean_Environment_setExporting(v_env_5249_, v_isExporting_5244_);
if (v_isShared_5259_ == 0)
{
lean_ctor_set(v___x_5258_, 5, v___x_5245_);
lean_ctor_set(v___x_5258_, 0, v___x_5260_);
v___x_5262_ = v___x_5258_;
goto v_reusejp_5261_;
}
else
{
lean_object* v_reuseFailAlloc_5266_; 
v_reuseFailAlloc_5266_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5266_, 0, v___x_5260_);
lean_ctor_set(v_reuseFailAlloc_5266_, 1, v_nextMacroScope_5250_);
lean_ctor_set(v_reuseFailAlloc_5266_, 2, v_ngen_5251_);
lean_ctor_set(v_reuseFailAlloc_5266_, 3, v_auxDeclNGen_5252_);
lean_ctor_set(v_reuseFailAlloc_5266_, 4, v_traceState_5253_);
lean_ctor_set(v_reuseFailAlloc_5266_, 5, v___x_5245_);
lean_ctor_set(v_reuseFailAlloc_5266_, 6, v_messages_5254_);
lean_ctor_set(v_reuseFailAlloc_5266_, 7, v_infoState_5255_);
lean_ctor_set(v_reuseFailAlloc_5266_, 8, v_snapshotTasks_5256_);
v___x_5262_ = v_reuseFailAlloc_5266_;
goto v_reusejp_5261_;
}
v_reusejp_5261_:
{
lean_object* v___x_5263_; lean_object* v___x_5264_; lean_object* v___x_5265_; 
v___x_5263_ = lean_st_ref_set(v___y_5243_, v___x_5262_);
v___x_5264_ = lean_box(0);
v___x_5265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5265_, 0, v___x_5264_);
return v___x_5265_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0___boxed(lean_object* v___y_5269_, lean_object* v_isExporting_5270_, lean_object* v___x_5271_, lean_object* v_a_x3f_5272_, lean_object* v___y_5273_){
_start:
{
uint8_t v_isExporting_boxed_5274_; lean_object* v_res_5275_; 
v_isExporting_boxed_5274_ = lean_unbox(v_isExporting_5270_);
v_res_5275_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0(v___y_5269_, v_isExporting_boxed_5274_, v___x_5271_, v_a_x3f_5272_);
lean_dec(v_a_x3f_5272_);
lean_dec(v___y_5269_);
return v_res_5275_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg(lean_object* v_x_5276_, uint8_t v_isExporting_5277_, lean_object* v___y_5278_, lean_object* v___y_5279_){
_start:
{
lean_object* v___x_5281_; lean_object* v_env_5282_; uint8_t v_isExporting_5283_; lean_object* v___x_5284_; lean_object* v_env_5285_; lean_object* v_nextMacroScope_5286_; lean_object* v_ngen_5287_; lean_object* v_auxDeclNGen_5288_; lean_object* v_traceState_5289_; lean_object* v_messages_5290_; lean_object* v_infoState_5291_; lean_object* v_snapshotTasks_5292_; lean_object* v___x_5294_; uint8_t v_isShared_5295_; uint8_t v_isSharedCheck_5331_; 
v___x_5281_ = lean_st_ref_get(v___y_5279_);
v_env_5282_ = lean_ctor_get(v___x_5281_, 0);
lean_inc_ref(v_env_5282_);
lean_dec(v___x_5281_);
v_isExporting_5283_ = lean_ctor_get_uint8(v_env_5282_, sizeof(void*)*8);
lean_dec_ref(v_env_5282_);
v___x_5284_ = lean_st_ref_take(v___y_5279_);
v_env_5285_ = lean_ctor_get(v___x_5284_, 0);
v_nextMacroScope_5286_ = lean_ctor_get(v___x_5284_, 1);
v_ngen_5287_ = lean_ctor_get(v___x_5284_, 2);
v_auxDeclNGen_5288_ = lean_ctor_get(v___x_5284_, 3);
v_traceState_5289_ = lean_ctor_get(v___x_5284_, 4);
v_messages_5290_ = lean_ctor_get(v___x_5284_, 6);
v_infoState_5291_ = lean_ctor_get(v___x_5284_, 7);
v_snapshotTasks_5292_ = lean_ctor_get(v___x_5284_, 8);
v_isSharedCheck_5331_ = !lean_is_exclusive(v___x_5284_);
if (v_isSharedCheck_5331_ == 0)
{
lean_object* v_unused_5332_; 
v_unused_5332_ = lean_ctor_get(v___x_5284_, 5);
lean_dec(v_unused_5332_);
v___x_5294_ = v___x_5284_;
v_isShared_5295_ = v_isSharedCheck_5331_;
goto v_resetjp_5293_;
}
else
{
lean_inc(v_snapshotTasks_5292_);
lean_inc(v_infoState_5291_);
lean_inc(v_messages_5290_);
lean_inc(v_traceState_5289_);
lean_inc(v_auxDeclNGen_5288_);
lean_inc(v_ngen_5287_);
lean_inc(v_nextMacroScope_5286_);
lean_inc(v_env_5285_);
lean_dec(v___x_5284_);
v___x_5294_ = lean_box(0);
v_isShared_5295_ = v_isSharedCheck_5331_;
goto v_resetjp_5293_;
}
v_resetjp_5293_:
{
lean_object* v___x_5296_; lean_object* v___x_5297_; lean_object* v___x_5299_; 
v___x_5296_ = l_Lean_Environment_setExporting(v_env_5285_, v_isExporting_5277_);
v___x_5297_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2, &l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2);
if (v_isShared_5295_ == 0)
{
lean_ctor_set(v___x_5294_, 5, v___x_5297_);
lean_ctor_set(v___x_5294_, 0, v___x_5296_);
v___x_5299_ = v___x_5294_;
goto v_reusejp_5298_;
}
else
{
lean_object* v_reuseFailAlloc_5330_; 
v_reuseFailAlloc_5330_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5330_, 0, v___x_5296_);
lean_ctor_set(v_reuseFailAlloc_5330_, 1, v_nextMacroScope_5286_);
lean_ctor_set(v_reuseFailAlloc_5330_, 2, v_ngen_5287_);
lean_ctor_set(v_reuseFailAlloc_5330_, 3, v_auxDeclNGen_5288_);
lean_ctor_set(v_reuseFailAlloc_5330_, 4, v_traceState_5289_);
lean_ctor_set(v_reuseFailAlloc_5330_, 5, v___x_5297_);
lean_ctor_set(v_reuseFailAlloc_5330_, 6, v_messages_5290_);
lean_ctor_set(v_reuseFailAlloc_5330_, 7, v_infoState_5291_);
lean_ctor_set(v_reuseFailAlloc_5330_, 8, v_snapshotTasks_5292_);
v___x_5299_ = v_reuseFailAlloc_5330_;
goto v_reusejp_5298_;
}
v_reusejp_5298_:
{
lean_object* v___x_5300_; lean_object* v_r_5301_; 
v___x_5300_ = lean_st_ref_set(v___y_5279_, v___x_5299_);
lean_inc(v___y_5279_);
lean_inc_ref(v___y_5278_);
v_r_5301_ = lean_apply_3(v_x_5276_, v___y_5278_, v___y_5279_, lean_box(0));
if (lean_obj_tag(v_r_5301_) == 0)
{
lean_object* v_a_5302_; lean_object* v___x_5304_; uint8_t v_isShared_5305_; uint8_t v_isSharedCheck_5318_; 
v_a_5302_ = lean_ctor_get(v_r_5301_, 0);
v_isSharedCheck_5318_ = !lean_is_exclusive(v_r_5301_);
if (v_isSharedCheck_5318_ == 0)
{
v___x_5304_ = v_r_5301_;
v_isShared_5305_ = v_isSharedCheck_5318_;
goto v_resetjp_5303_;
}
else
{
lean_inc(v_a_5302_);
lean_dec(v_r_5301_);
v___x_5304_ = lean_box(0);
v_isShared_5305_ = v_isSharedCheck_5318_;
goto v_resetjp_5303_;
}
v_resetjp_5303_:
{
lean_object* v___x_5307_; 
lean_inc(v_a_5302_);
if (v_isShared_5305_ == 0)
{
lean_ctor_set_tag(v___x_5304_, 1);
v___x_5307_ = v___x_5304_;
goto v_reusejp_5306_;
}
else
{
lean_object* v_reuseFailAlloc_5317_; 
v_reuseFailAlloc_5317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5317_, 0, v_a_5302_);
v___x_5307_ = v_reuseFailAlloc_5317_;
goto v_reusejp_5306_;
}
v_reusejp_5306_:
{
lean_object* v___x_5308_; lean_object* v___x_5310_; uint8_t v_isShared_5311_; uint8_t v_isSharedCheck_5315_; 
v___x_5308_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0(v___y_5279_, v_isExporting_5283_, v___x_5297_, v___x_5307_);
lean_dec_ref(v___x_5307_);
v_isSharedCheck_5315_ = !lean_is_exclusive(v___x_5308_);
if (v_isSharedCheck_5315_ == 0)
{
lean_object* v_unused_5316_; 
v_unused_5316_ = lean_ctor_get(v___x_5308_, 0);
lean_dec(v_unused_5316_);
v___x_5310_ = v___x_5308_;
v_isShared_5311_ = v_isSharedCheck_5315_;
goto v_resetjp_5309_;
}
else
{
lean_dec(v___x_5308_);
v___x_5310_ = lean_box(0);
v_isShared_5311_ = v_isSharedCheck_5315_;
goto v_resetjp_5309_;
}
v_resetjp_5309_:
{
lean_object* v___x_5313_; 
if (v_isShared_5311_ == 0)
{
lean_ctor_set(v___x_5310_, 0, v_a_5302_);
v___x_5313_ = v___x_5310_;
goto v_reusejp_5312_;
}
else
{
lean_object* v_reuseFailAlloc_5314_; 
v_reuseFailAlloc_5314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5314_, 0, v_a_5302_);
v___x_5313_ = v_reuseFailAlloc_5314_;
goto v_reusejp_5312_;
}
v_reusejp_5312_:
{
return v___x_5313_;
}
}
}
}
}
else
{
lean_object* v_a_5319_; lean_object* v___x_5320_; lean_object* v___x_5321_; lean_object* v___x_5323_; uint8_t v_isShared_5324_; uint8_t v_isSharedCheck_5328_; 
v_a_5319_ = lean_ctor_get(v_r_5301_, 0);
lean_inc(v_a_5319_);
lean_dec_ref(v_r_5301_);
v___x_5320_ = lean_box(0);
v___x_5321_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0(v___y_5279_, v_isExporting_5283_, v___x_5297_, v___x_5320_);
v_isSharedCheck_5328_ = !lean_is_exclusive(v___x_5321_);
if (v_isSharedCheck_5328_ == 0)
{
lean_object* v_unused_5329_; 
v_unused_5329_ = lean_ctor_get(v___x_5321_, 0);
lean_dec(v_unused_5329_);
v___x_5323_ = v___x_5321_;
v_isShared_5324_ = v_isSharedCheck_5328_;
goto v_resetjp_5322_;
}
else
{
lean_dec(v___x_5321_);
v___x_5323_ = lean_box(0);
v_isShared_5324_ = v_isSharedCheck_5328_;
goto v_resetjp_5322_;
}
v_resetjp_5322_:
{
lean_object* v___x_5326_; 
if (v_isShared_5324_ == 0)
{
lean_ctor_set_tag(v___x_5323_, 1);
lean_ctor_set(v___x_5323_, 0, v_a_5319_);
v___x_5326_ = v___x_5323_;
goto v_reusejp_5325_;
}
else
{
lean_object* v_reuseFailAlloc_5327_; 
v_reuseFailAlloc_5327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5327_, 0, v_a_5319_);
v___x_5326_ = v_reuseFailAlloc_5327_;
goto v_reusejp_5325_;
}
v_reusejp_5325_:
{
return v___x_5326_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___boxed(lean_object* v_x_5333_, lean_object* v_isExporting_5334_, lean_object* v___y_5335_, lean_object* v___y_5336_, lean_object* v___y_5337_){
_start:
{
uint8_t v_isExporting_boxed_5338_; lean_object* v_res_5339_; 
v_isExporting_boxed_5338_ = lean_unbox(v_isExporting_5334_);
v_res_5339_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg(v_x_5333_, v_isExporting_boxed_5338_, v___y_5335_, v___y_5336_);
lean_dec(v___y_5336_);
lean_dec_ref(v___y_5335_);
return v_res_5339_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg(lean_object* v_x_5340_, uint8_t v_when_5341_, lean_object* v___y_5342_, lean_object* v___y_5343_){
_start:
{
if (v_when_5341_ == 0)
{
lean_object* v___x_5345_; 
lean_inc(v___y_5343_);
lean_inc_ref(v___y_5342_);
v___x_5345_ = lean_apply_3(v_x_5340_, v___y_5342_, v___y_5343_, lean_box(0));
return v___x_5345_;
}
else
{
uint8_t v___x_5346_; lean_object* v___x_5347_; 
v___x_5346_ = 0;
v___x_5347_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg(v_x_5340_, v___x_5346_, v___y_5342_, v___y_5343_);
return v___x_5347_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg___boxed(lean_object* v_x_5348_, lean_object* v_when_5349_, lean_object* v___y_5350_, lean_object* v___y_5351_, lean_object* v___y_5352_){
_start:
{
uint8_t v_when_boxed_5353_; lean_object* v_res_5354_; 
v_when_boxed_5353_ = lean_unbox(v_when_5349_);
v_res_5354_ = l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg(v_x_5348_, v_when_boxed_5353_, v___y_5350_, v___y_5351_);
lean_dec(v___y_5351_);
lean_dec_ref(v___y_5350_);
return v_res_5354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf(lean_object* v_fnNames_5355_, lean_object* v_numSectionVars_5356_, lean_object* v_e_5357_, lean_object* v_a_5358_, lean_object* v_a_5359_){
_start:
{
lean_object* v___f_5361_; lean_object* v___f_5362_; uint8_t v___x_5363_; lean_object* v___x_5364_; 
v___f_5361_ = ((lean_object*)(l_Lean_Core_betaReduce___closed__1));
v___f_5362_ = lean_alloc_closure((void*)(l_Lean_Meta_unfoldIfArgIsAppOf___lam__0___boxed), 7, 4);
lean_closure_set(v___f_5362_, 0, v_fnNames_5355_);
lean_closure_set(v___f_5362_, 1, v_numSectionVars_5356_);
lean_closure_set(v___f_5362_, 2, v_e_5357_);
lean_closure_set(v___f_5362_, 3, v___f_5361_);
v___x_5363_ = 1;
v___x_5364_ = l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg(v___f_5362_, v___x_5363_, v_a_5358_, v_a_5359_);
return v___x_5364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___boxed(lean_object* v_fnNames_5365_, lean_object* v_numSectionVars_5366_, lean_object* v_e_5367_, lean_object* v_a_5368_, lean_object* v_a_5369_, lean_object* v_a_5370_){
_start:
{
lean_object* v_res_5371_; 
v_res_5371_ = l_Lean_Meta_unfoldIfArgIsAppOf(v_fnNames_5365_, v_numSectionVars_5366_, v_e_5367_, v_a_5368_, v_a_5369_);
lean_dec(v_a_5369_);
lean_dec_ref(v_a_5368_);
return v_res_5371_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2(lean_object* v_00_u03b1_5372_, lean_object* v_x_5373_, uint8_t v_isExporting_5374_, lean_object* v___y_5375_, lean_object* v___y_5376_){
_start:
{
lean_object* v___x_5378_; 
v___x_5378_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg(v_x_5373_, v_isExporting_5374_, v___y_5375_, v___y_5376_);
return v___x_5378_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___boxed(lean_object* v_00_u03b1_5379_, lean_object* v_x_5380_, lean_object* v_isExporting_5381_, lean_object* v___y_5382_, lean_object* v___y_5383_, lean_object* v___y_5384_){
_start:
{
uint8_t v_isExporting_boxed_5385_; lean_object* v_res_5386_; 
v_isExporting_boxed_5385_ = lean_unbox(v_isExporting_5381_);
v_res_5386_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2(v_00_u03b1_5379_, v_x_5380_, v_isExporting_boxed_5385_, v___y_5382_, v___y_5383_);
lean_dec(v___y_5383_);
lean_dec_ref(v___y_5382_);
return v_res_5386_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2(lean_object* v_00_u03b1_5387_, lean_object* v_x_5388_, uint8_t v_when_5389_, lean_object* v___y_5390_, lean_object* v___y_5391_){
_start:
{
lean_object* v___x_5393_; 
v___x_5393_ = l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg(v_x_5388_, v_when_5389_, v___y_5390_, v___y_5391_);
return v___x_5393_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___boxed(lean_object* v_00_u03b1_5394_, lean_object* v_x_5395_, lean_object* v_when_5396_, lean_object* v___y_5397_, lean_object* v___y_5398_, lean_object* v___y_5399_){
_start:
{
uint8_t v_when_boxed_5400_; lean_object* v_res_5401_; 
v_when_boxed_5400_ = lean_unbox(v_when_5396_);
v_res_5401_ = l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2(v_00_u03b1_5394_, v_x_5395_, v_when_boxed_5400_, v___y_5397_, v___y_5398_);
lean_dec(v___y_5398_);
lean_dec_ref(v___y_5397_);
return v_res_5401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___lam__0(lean_object* v_x_5402_, lean_object* v___y_5403_, lean_object* v___y_5404_){
_start:
{
lean_object* v___x_5406_; lean_object* v___x_5407_; 
v___x_5406_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_5407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5407_, 0, v___x_5406_);
return v___x_5407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___lam__0___boxed(lean_object* v_x_5408_, lean_object* v___y_5409_, lean_object* v___y_5410_, lean_object* v___y_5411_){
_start:
{
lean_object* v_res_5412_; 
v_res_5412_ = l_Lean_Meta_eraseInaccessibleAnnotations___lam__0(v_x_5408_, v___y_5409_, v___y_5410_);
lean_dec(v___y_5410_);
lean_dec_ref(v___y_5409_);
lean_dec_ref(v_x_5408_);
return v_res_5412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___lam__1(lean_object* v_e_5413_, lean_object* v___y_5414_, lean_object* v___y_5415_){
_start:
{
lean_object* v___y_5418_; lean_object* v___x_5421_; 
v___x_5421_ = l_Lean_inaccessible_x3f(v_e_5413_);
if (lean_obj_tag(v___x_5421_) == 1)
{
lean_object* v_val_5422_; 
lean_dec_ref(v_e_5413_);
v_val_5422_ = lean_ctor_get(v___x_5421_, 0);
lean_inc(v_val_5422_);
lean_dec_ref(v___x_5421_);
v___y_5418_ = v_val_5422_;
goto v___jp_5417_;
}
else
{
lean_dec(v___x_5421_);
v___y_5418_ = v_e_5413_;
goto v___jp_5417_;
}
v___jp_5417_:
{
lean_object* v___x_5419_; lean_object* v___x_5420_; 
v___x_5419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5419_, 0, v___y_5418_);
v___x_5420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5420_, 0, v___x_5419_);
return v___x_5420_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___lam__1___boxed(lean_object* v_e_5423_, lean_object* v___y_5424_, lean_object* v___y_5425_, lean_object* v___y_5426_){
_start:
{
lean_object* v_res_5427_; 
v_res_5427_ = l_Lean_Meta_eraseInaccessibleAnnotations___lam__1(v_e_5423_, v___y_5424_, v___y_5425_);
lean_dec(v___y_5425_);
lean_dec_ref(v___y_5424_);
return v_res_5427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations(lean_object* v_e_5430_, lean_object* v_a_5431_, lean_object* v_a_5432_){
_start:
{
lean_object* v___f_5434_; lean_object* v___f_5435_; lean_object* v___x_5436_; 
v___f_5434_ = ((lean_object*)(l_Lean_Meta_eraseInaccessibleAnnotations___closed__0));
v___f_5435_ = ((lean_object*)(l_Lean_Meta_eraseInaccessibleAnnotations___closed__1));
v___x_5436_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_5430_, v___f_5434_, v___f_5435_, v_a_5431_, v_a_5432_);
return v___x_5436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___boxed(lean_object* v_e_5437_, lean_object* v_a_5438_, lean_object* v_a_5439_, lean_object* v_a_5440_){
_start:
{
lean_object* v_res_5441_; 
v_res_5441_ = l_Lean_Meta_eraseInaccessibleAnnotations(v_e_5437_, v_a_5438_, v_a_5439_);
lean_dec(v_a_5439_);
lean_dec_ref(v_a_5438_);
return v_res_5441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_erasePatternRefAnnotations___lam__1(lean_object* v_e_5442_, lean_object* v___y_5443_, lean_object* v___y_5444_){
_start:
{
lean_object* v___y_5447_; lean_object* v___x_5450_; 
v___x_5450_ = l_Lean_patternWithRef_x3f(v_e_5442_);
if (lean_obj_tag(v___x_5450_) == 1)
{
lean_object* v_val_5451_; lean_object* v_snd_5452_; 
lean_dec_ref(v_e_5442_);
v_val_5451_ = lean_ctor_get(v___x_5450_, 0);
lean_inc(v_val_5451_);
lean_dec_ref(v___x_5450_);
v_snd_5452_ = lean_ctor_get(v_val_5451_, 1);
lean_inc(v_snd_5452_);
lean_dec(v_val_5451_);
v___y_5447_ = v_snd_5452_;
goto v___jp_5446_;
}
else
{
lean_dec(v___x_5450_);
v___y_5447_ = v_e_5442_;
goto v___jp_5446_;
}
v___jp_5446_:
{
lean_object* v___x_5448_; lean_object* v___x_5449_; 
v___x_5448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5448_, 0, v___y_5447_);
v___x_5449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5449_, 0, v___x_5448_);
return v___x_5449_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_erasePatternRefAnnotations___lam__1___boxed(lean_object* v_e_5453_, lean_object* v___y_5454_, lean_object* v___y_5455_, lean_object* v___y_5456_){
_start:
{
lean_object* v_res_5457_; 
v_res_5457_ = l_Lean_Meta_erasePatternRefAnnotations___lam__1(v_e_5453_, v___y_5454_, v___y_5455_);
lean_dec(v___y_5455_);
lean_dec_ref(v___y_5454_);
return v_res_5457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_erasePatternRefAnnotations(lean_object* v_e_5459_, lean_object* v_a_5460_, lean_object* v_a_5461_){
_start:
{
lean_object* v___f_5463_; lean_object* v___f_5464_; lean_object* v___x_5465_; 
v___f_5463_ = ((lean_object*)(l_Lean_Meta_eraseInaccessibleAnnotations___closed__0));
v___f_5464_ = ((lean_object*)(l_Lean_Meta_erasePatternRefAnnotations___closed__0));
v___x_5465_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_5459_, v___f_5463_, v___f_5464_, v_a_5460_, v_a_5461_);
return v___x_5465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_erasePatternRefAnnotations___boxed(lean_object* v_e_5466_, lean_object* v_a_5467_, lean_object* v_a_5468_, lean_object* v_a_5469_){
_start:
{
lean_object* v_res_5470_; 
v_res_5470_ = l_Lean_Meta_erasePatternRefAnnotations(v_e_5466_, v_a_5467_, v_a_5468_);
lean_dec(v_a_5468_);
lean_dec_ref(v_a_5467_);
return v_res_5470_;
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
