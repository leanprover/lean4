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
uint8_t l_IO_CancelToken_isSet(lean_object*);
extern lean_object* l_Lean_interruptExceptionId;
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
static lean_once_cell_t l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___redArg();
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___redArg___boxed(lean_object*);
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__12___redArg(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13(lean_object*, lean_object*, lean_object*);
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
static lean_object* _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1065_ = lean_box(0);
v___x_1066_ = l_Lean_interruptExceptionId;
v___x_1067_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1066_);
lean_ctor_set(v___x_1067_, 1, v___x_1065_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___redArg(){
_start:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1069_ = lean_obj_once(&l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___redArg___closed__0, &l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___redArg___closed__0);
v___x_1070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1069_);
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___redArg___boxed(lean_object* v___y_1071_){
_start:
{
lean_object* v_res_1072_; 
v_res_1072_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___redArg();
return v_res_1072_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1078_ = l_Lean_maxRecDepthErrorMessage;
v___x_1079_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1078_);
return v___x_1079_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; 
v___x_1080_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__3);
v___x_1081_ = l_Lean_MessageData_ofFormat(v___x_1080_);
return v___x_1081_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1082_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__4);
v___x_1083_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__2));
v___x_1084_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1083_);
lean_ctor_set(v___x_1084_, 1, v___x_1082_);
return v___x_1084_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg(lean_object* v_ref_1085_){
_start:
{
lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; 
v___x_1087_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5);
v___x_1088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1088_, 0, v_ref_1085_);
lean_ctor_set(v___x_1088_, 1, v___x_1087_);
v___x_1089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1088_);
return v___x_1089_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object* v_ref_1090_, lean_object* v___y_1091_){
_start:
{
lean_object* v_res_1092_; 
v_res_1092_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_1090_);
return v_res_1092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___redArg(lean_object* v_x_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_){
_start:
{
lean_object* v___y_1099_; lean_object* v___y_1109_; lean_object* v___y_1110_; uint8_t v___y_1111_; lean_object* v___y_1112_; lean_object* v___y_1113_; lean_object* v___y_1114_; lean_object* v___y_1115_; lean_object* v___y_1116_; lean_object* v___y_1117_; lean_object* v___y_1118_; lean_object* v___y_1119_; lean_object* v___y_1120_; lean_object* v___y_1121_; lean_object* v___y_1122_; uint8_t v___y_1123_; lean_object* v___y_1124_; lean_object* v_fileName_1129_; lean_object* v_fileMap_1130_; lean_object* v_options_1131_; lean_object* v_currRecDepth_1132_; lean_object* v_maxRecDepth_1133_; lean_object* v_ref_1134_; lean_object* v_currNamespace_1135_; lean_object* v_openDecls_1136_; lean_object* v_initHeartbeats_1137_; lean_object* v_maxHeartbeats_1138_; lean_object* v_quotContext_1139_; lean_object* v_currMacroScope_1140_; uint8_t v_diag_1141_; lean_object* v_cancelTk_x3f_1142_; uint8_t v_suppressElabErrors_1143_; lean_object* v_inheritedTraceOptions_1144_; 
v_fileName_1129_ = lean_ctor_get(v___y_1095_, 0);
v_fileMap_1130_ = lean_ctor_get(v___y_1095_, 1);
v_options_1131_ = lean_ctor_get(v___y_1095_, 2);
v_currRecDepth_1132_ = lean_ctor_get(v___y_1095_, 3);
v_maxRecDepth_1133_ = lean_ctor_get(v___y_1095_, 4);
v_ref_1134_ = lean_ctor_get(v___y_1095_, 5);
v_currNamespace_1135_ = lean_ctor_get(v___y_1095_, 6);
v_openDecls_1136_ = lean_ctor_get(v___y_1095_, 7);
v_initHeartbeats_1137_ = lean_ctor_get(v___y_1095_, 8);
v_maxHeartbeats_1138_ = lean_ctor_get(v___y_1095_, 9);
v_quotContext_1139_ = lean_ctor_get(v___y_1095_, 10);
v_currMacroScope_1140_ = lean_ctor_get(v___y_1095_, 11);
v_diag_1141_ = lean_ctor_get_uint8(v___y_1095_, sizeof(void*)*14);
v_cancelTk_x3f_1142_ = lean_ctor_get(v___y_1095_, 12);
v_suppressElabErrors_1143_ = lean_ctor_get_uint8(v___y_1095_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1144_ = lean_ctor_get(v___y_1095_, 13);
if (lean_obj_tag(v_cancelTk_x3f_1142_) == 1)
{
lean_object* v_val_1150_; uint8_t v___x_1151_; 
v_val_1150_ = lean_ctor_get(v_cancelTk_x3f_1142_, 0);
v___x_1151_ = l_IO_CancelToken_isSet(v_val_1150_);
if (v___x_1151_ == 0)
{
goto v___jp_1145_;
}
else
{
lean_object* v___x_1152_; lean_object* v_a_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1160_; 
lean_dec_ref(v_x_1093_);
v___x_1152_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___redArg();
v_a_1153_ = lean_ctor_get(v___x_1152_, 0);
v_isSharedCheck_1160_ = !lean_is_exclusive(v___x_1152_);
if (v_isSharedCheck_1160_ == 0)
{
v___x_1155_ = v___x_1152_;
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_a_1153_);
lean_dec(v___x_1152_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v___x_1158_; 
if (v_isShared_1156_ == 0)
{
v___x_1158_ = v___x_1155_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_a_1153_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
return v___x_1158_;
}
}
}
}
else
{
goto v___jp_1145_;
}
v___jp_1098_:
{
if (lean_obj_tag(v___y_1099_) == 0)
{
return v___y_1099_;
}
else
{
lean_object* v_a_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1107_; 
v_a_1100_ = lean_ctor_get(v___y_1099_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___y_1099_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1102_ = v___y_1099_;
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_a_1100_);
lean_dec(v___y_1099_);
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
v_reuseFailAlloc_1106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_a_1100_);
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
v___jp_1108_:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; 
v___x_1125_ = lean_unsigned_to_nat(1u);
v___x_1126_ = lean_nat_add(v___y_1113_, v___x_1125_);
lean_inc_ref(v___y_1117_);
lean_inc(v___y_1118_);
lean_inc(v___y_1116_);
lean_inc(v___y_1120_);
lean_inc(v___y_1121_);
lean_inc(v___y_1115_);
lean_inc(v___y_1109_);
lean_inc(v___y_1119_);
lean_inc(v___y_1112_);
lean_inc_ref(v___y_1122_);
lean_inc_ref(v___y_1114_);
lean_inc_ref(v___y_1124_);
v___x_1127_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1127_, 0, v___y_1124_);
lean_ctor_set(v___x_1127_, 1, v___y_1114_);
lean_ctor_set(v___x_1127_, 2, v___y_1122_);
lean_ctor_set(v___x_1127_, 3, v___x_1126_);
lean_ctor_set(v___x_1127_, 4, v___y_1112_);
lean_ctor_set(v___x_1127_, 5, v___y_1110_);
lean_ctor_set(v___x_1127_, 6, v___y_1119_);
lean_ctor_set(v___x_1127_, 7, v___y_1109_);
lean_ctor_set(v___x_1127_, 8, v___y_1115_);
lean_ctor_set(v___x_1127_, 9, v___y_1121_);
lean_ctor_set(v___x_1127_, 10, v___y_1120_);
lean_ctor_set(v___x_1127_, 11, v___y_1116_);
lean_ctor_set(v___x_1127_, 12, v___y_1118_);
lean_ctor_set(v___x_1127_, 13, v___y_1117_);
lean_ctor_set_uint8(v___x_1127_, sizeof(void*)*14, v___y_1111_);
lean_ctor_set_uint8(v___x_1127_, sizeof(void*)*14 + 1, v___y_1123_);
lean_inc(v___y_1096_);
lean_inc(v___y_1094_);
v___x_1128_ = lean_apply_4(v_x_1093_, v___y_1094_, v___x_1127_, v___y_1096_, lean_box(0));
v___y_1099_ = v___x_1128_;
goto v___jp_1098_;
}
v___jp_1145_:
{
lean_object* v___x_1146_; uint8_t v___x_1147_; 
v___x_1146_ = lean_unsigned_to_nat(0u);
v___x_1147_ = lean_nat_dec_eq(v_maxRecDepth_1133_, v___x_1146_);
if (v___x_1147_ == 0)
{
uint8_t v___x_1148_; 
v___x_1148_ = lean_nat_dec_eq(v_currRecDepth_1132_, v_maxRecDepth_1133_);
if (v___x_1148_ == 0)
{
lean_inc(v_ref_1134_);
v___y_1109_ = v_openDecls_1136_;
v___y_1110_ = v_ref_1134_;
v___y_1111_ = v_diag_1141_;
v___y_1112_ = v_maxRecDepth_1133_;
v___y_1113_ = v_currRecDepth_1132_;
v___y_1114_ = v_fileMap_1130_;
v___y_1115_ = v_initHeartbeats_1137_;
v___y_1116_ = v_currMacroScope_1140_;
v___y_1117_ = v_inheritedTraceOptions_1144_;
v___y_1118_ = v_cancelTk_x3f_1142_;
v___y_1119_ = v_currNamespace_1135_;
v___y_1120_ = v_quotContext_1139_;
v___y_1121_ = v_maxHeartbeats_1138_;
v___y_1122_ = v_options_1131_;
v___y_1123_ = v_suppressElabErrors_1143_;
v___y_1124_ = v_fileName_1129_;
goto v___jp_1108_;
}
else
{
lean_object* v___x_1149_; 
lean_dec_ref(v_x_1093_);
lean_inc(v_ref_1134_);
v___x_1149_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_1134_);
v___y_1099_ = v___x_1149_;
goto v___jp_1098_;
}
}
else
{
lean_inc(v_ref_1134_);
v___y_1109_ = v_openDecls_1136_;
v___y_1110_ = v_ref_1134_;
v___y_1111_ = v_diag_1141_;
v___y_1112_ = v_maxRecDepth_1133_;
v___y_1113_ = v_currRecDepth_1132_;
v___y_1114_ = v_fileMap_1130_;
v___y_1115_ = v_initHeartbeats_1137_;
v___y_1116_ = v_currMacroScope_1140_;
v___y_1117_ = v_inheritedTraceOptions_1144_;
v___y_1118_ = v_cancelTk_x3f_1142_;
v___y_1119_ = v_currNamespace_1135_;
v___y_1120_ = v_quotContext_1139_;
v___y_1121_ = v_maxHeartbeats_1138_;
v___y_1122_ = v_options_1131_;
v___y_1123_ = v_suppressElabErrors_1143_;
v___y_1124_ = v_fileName_1129_;
goto v___jp_1108_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___redArg___boxed(lean_object* v_x_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_){
_start:
{
lean_object* v_res_1166_; 
v_res_1166_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___redArg(v_x_1161_, v___y_1162_, v___y_1163_, v___y_1164_);
lean_dec(v___y_1164_);
lean_dec_ref(v___y_1163_);
lean_dec(v___y_1162_);
return v_res_1166_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_1167_, lean_object* v_x_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_){
_start:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; 
v___x_1172_ = lean_apply_1(v_x_1168_, lean_box(0));
v___x_1173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1172_);
return v___x_1173_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_1174_, lean_object* v_x_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_){
_start:
{
lean_object* v_res_1179_; 
v_res_1179_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__0(v_00_u03b1_1174_, v_x_1175_, v___y_1176_, v___y_1177_);
lean_dec(v___y_1177_);
lean_dec_ref(v___y_1176_);
return v_res_1179_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___redArg(lean_object* v_a_1180_, lean_object* v_x_1181_){
_start:
{
if (lean_obj_tag(v_x_1181_) == 0)
{
uint8_t v___x_1182_; 
v___x_1182_ = 0;
return v___x_1182_;
}
else
{
lean_object* v_key_1183_; lean_object* v_tail_1184_; uint8_t v___x_1185_; 
v_key_1183_ = lean_ctor_get(v_x_1181_, 0);
v_tail_1184_ = lean_ctor_get(v_x_1181_, 2);
v___x_1185_ = l_Lean_ExprStructEq_beq(v_key_1183_, v_a_1180_);
if (v___x_1185_ == 0)
{
v_x_1181_ = v_tail_1184_;
goto _start;
}
else
{
return v___x_1185_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___redArg___boxed(lean_object* v_a_1187_, lean_object* v_x_1188_){
_start:
{
uint8_t v_res_1189_; lean_object* v_r_1190_; 
v_res_1189_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___redArg(v_a_1187_, v_x_1188_);
lean_dec(v_x_1188_);
lean_dec_ref(v_a_1187_);
v_r_1190_ = lean_box(v_res_1189_);
return v_r_1190_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(lean_object* v_x_1191_, lean_object* v_x_1192_){
_start:
{
if (lean_obj_tag(v_x_1192_) == 0)
{
return v_x_1191_;
}
else
{
lean_object* v_key_1193_; lean_object* v_value_1194_; lean_object* v_tail_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1218_; 
v_key_1193_ = lean_ctor_get(v_x_1192_, 0);
v_value_1194_ = lean_ctor_get(v_x_1192_, 1);
v_tail_1195_ = lean_ctor_get(v_x_1192_, 2);
v_isSharedCheck_1218_ = !lean_is_exclusive(v_x_1192_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1197_ = v_x_1192_;
v_isShared_1198_ = v_isSharedCheck_1218_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_tail_1195_);
lean_inc(v_value_1194_);
lean_inc(v_key_1193_);
lean_dec(v_x_1192_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1218_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
lean_object* v___x_1199_; uint64_t v___x_1200_; uint64_t v___x_1201_; uint64_t v___x_1202_; uint64_t v_fold_1203_; uint64_t v___x_1204_; uint64_t v___x_1205_; uint64_t v___x_1206_; size_t v___x_1207_; size_t v___x_1208_; size_t v___x_1209_; size_t v___x_1210_; size_t v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1214_; 
v___x_1199_ = lean_array_get_size(v_x_1191_);
v___x_1200_ = l_Lean_ExprStructEq_hash(v_key_1193_);
v___x_1201_ = 32ULL;
v___x_1202_ = lean_uint64_shift_right(v___x_1200_, v___x_1201_);
v_fold_1203_ = lean_uint64_xor(v___x_1200_, v___x_1202_);
v___x_1204_ = 16ULL;
v___x_1205_ = lean_uint64_shift_right(v_fold_1203_, v___x_1204_);
v___x_1206_ = lean_uint64_xor(v_fold_1203_, v___x_1205_);
v___x_1207_ = lean_uint64_to_usize(v___x_1206_);
v___x_1208_ = lean_usize_of_nat(v___x_1199_);
v___x_1209_ = ((size_t)1ULL);
v___x_1210_ = lean_usize_sub(v___x_1208_, v___x_1209_);
v___x_1211_ = lean_usize_land(v___x_1207_, v___x_1210_);
v___x_1212_ = lean_array_uget_borrowed(v_x_1191_, v___x_1211_);
lean_inc(v___x_1212_);
if (v_isShared_1198_ == 0)
{
lean_ctor_set(v___x_1197_, 2, v___x_1212_);
v___x_1214_ = v___x_1197_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v_key_1193_);
lean_ctor_set(v_reuseFailAlloc_1217_, 1, v_value_1194_);
lean_ctor_set(v_reuseFailAlloc_1217_, 2, v___x_1212_);
v___x_1214_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
lean_object* v___x_1215_; 
v___x_1215_ = lean_array_uset(v_x_1191_, v___x_1211_, v___x_1214_);
v_x_1191_ = v___x_1215_;
v_x_1192_ = v_tail_1195_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(lean_object* v_i_1219_, lean_object* v_source_1220_, lean_object* v_target_1221_){
_start:
{
lean_object* v___x_1222_; uint8_t v___x_1223_; 
v___x_1222_ = lean_array_get_size(v_source_1220_);
v___x_1223_ = lean_nat_dec_lt(v_i_1219_, v___x_1222_);
if (v___x_1223_ == 0)
{
lean_dec_ref(v_source_1220_);
lean_dec(v_i_1219_);
return v_target_1221_;
}
else
{
lean_object* v_es_1224_; lean_object* v___x_1225_; lean_object* v_source_1226_; lean_object* v_target_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
v_es_1224_ = lean_array_fget(v_source_1220_, v_i_1219_);
v___x_1225_ = lean_box(0);
v_source_1226_ = lean_array_fset(v_source_1220_, v_i_1219_, v___x_1225_);
v_target_1227_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_target_1221_, v_es_1224_);
v___x_1228_ = lean_unsigned_to_nat(1u);
v___x_1229_ = lean_nat_add(v_i_1219_, v___x_1228_);
lean_dec(v_i_1219_);
v_i_1219_ = v___x_1229_;
v_source_1220_ = v_source_1226_;
v_target_1221_ = v_target_1227_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11___redArg(lean_object* v_data_1231_){
_start:
{
lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v_nbuckets_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; 
v___x_1232_ = lean_array_get_size(v_data_1231_);
v___x_1233_ = lean_unsigned_to_nat(2u);
v_nbuckets_1234_ = lean_nat_mul(v___x_1232_, v___x_1233_);
v___x_1235_ = lean_unsigned_to_nat(0u);
v___x_1236_ = lean_box(0);
v___x_1237_ = lean_mk_array(v_nbuckets_1234_, v___x_1236_);
v___x_1238_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v___x_1235_, v_data_1231_, v___x_1237_);
return v___x_1238_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__12___redArg(lean_object* v_a_1239_, lean_object* v_b_1240_, lean_object* v_x_1241_){
_start:
{
if (lean_obj_tag(v_x_1241_) == 0)
{
lean_dec(v_b_1240_);
lean_dec_ref(v_a_1239_);
return v_x_1241_;
}
else
{
lean_object* v_key_1242_; lean_object* v_value_1243_; lean_object* v_tail_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1256_; 
v_key_1242_ = lean_ctor_get(v_x_1241_, 0);
v_value_1243_ = lean_ctor_get(v_x_1241_, 1);
v_tail_1244_ = lean_ctor_get(v_x_1241_, 2);
v_isSharedCheck_1256_ = !lean_is_exclusive(v_x_1241_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1246_ = v_x_1241_;
v_isShared_1247_ = v_isSharedCheck_1256_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_tail_1244_);
lean_inc(v_value_1243_);
lean_inc(v_key_1242_);
lean_dec(v_x_1241_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1256_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
uint8_t v___x_1248_; 
v___x_1248_ = l_Lean_ExprStructEq_beq(v_key_1242_, v_a_1239_);
if (v___x_1248_ == 0)
{
lean_object* v___x_1249_; lean_object* v___x_1251_; 
v___x_1249_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__12___redArg(v_a_1239_, v_b_1240_, v_tail_1244_);
if (v_isShared_1247_ == 0)
{
lean_ctor_set(v___x_1246_, 2, v___x_1249_);
v___x_1251_ = v___x_1246_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v_key_1242_);
lean_ctor_set(v_reuseFailAlloc_1252_, 1, v_value_1243_);
lean_ctor_set(v_reuseFailAlloc_1252_, 2, v___x_1249_);
v___x_1251_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
return v___x_1251_;
}
}
else
{
lean_object* v___x_1254_; 
lean_dec(v_value_1243_);
lean_dec(v_key_1242_);
if (v_isShared_1247_ == 0)
{
lean_ctor_set(v___x_1246_, 1, v_b_1240_);
lean_ctor_set(v___x_1246_, 0, v_a_1239_);
v___x_1254_ = v___x_1246_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v_a_1239_);
lean_ctor_set(v_reuseFailAlloc_1255_, 1, v_b_1240_);
lean_ctor_set(v_reuseFailAlloc_1255_, 2, v_tail_1244_);
v___x_1254_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
return v___x_1254_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6___redArg(lean_object* v_m_1257_, lean_object* v_a_1258_, lean_object* v_b_1259_){
_start:
{
lean_object* v_size_1260_; lean_object* v_buckets_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1304_; 
v_size_1260_ = lean_ctor_get(v_m_1257_, 0);
v_buckets_1261_ = lean_ctor_get(v_m_1257_, 1);
v_isSharedCheck_1304_ = !lean_is_exclusive(v_m_1257_);
if (v_isSharedCheck_1304_ == 0)
{
v___x_1263_ = v_m_1257_;
v_isShared_1264_ = v_isSharedCheck_1304_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_buckets_1261_);
lean_inc(v_size_1260_);
lean_dec(v_m_1257_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1304_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___x_1265_; uint64_t v___x_1266_; uint64_t v___x_1267_; uint64_t v___x_1268_; uint64_t v_fold_1269_; uint64_t v___x_1270_; uint64_t v___x_1271_; uint64_t v___x_1272_; size_t v___x_1273_; size_t v___x_1274_; size_t v___x_1275_; size_t v___x_1276_; size_t v___x_1277_; lean_object* v_bkt_1278_; uint8_t v___x_1279_; 
v___x_1265_ = lean_array_get_size(v_buckets_1261_);
v___x_1266_ = l_Lean_ExprStructEq_hash(v_a_1258_);
v___x_1267_ = 32ULL;
v___x_1268_ = lean_uint64_shift_right(v___x_1266_, v___x_1267_);
v_fold_1269_ = lean_uint64_xor(v___x_1266_, v___x_1268_);
v___x_1270_ = 16ULL;
v___x_1271_ = lean_uint64_shift_right(v_fold_1269_, v___x_1270_);
v___x_1272_ = lean_uint64_xor(v_fold_1269_, v___x_1271_);
v___x_1273_ = lean_uint64_to_usize(v___x_1272_);
v___x_1274_ = lean_usize_of_nat(v___x_1265_);
v___x_1275_ = ((size_t)1ULL);
v___x_1276_ = lean_usize_sub(v___x_1274_, v___x_1275_);
v___x_1277_ = lean_usize_land(v___x_1273_, v___x_1276_);
v_bkt_1278_ = lean_array_uget_borrowed(v_buckets_1261_, v___x_1277_);
v___x_1279_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___redArg(v_a_1258_, v_bkt_1278_);
if (v___x_1279_ == 0)
{
lean_object* v___x_1280_; lean_object* v_size_x27_1281_; lean_object* v___x_1282_; lean_object* v_buckets_x27_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; uint8_t v___x_1289_; 
v___x_1280_ = lean_unsigned_to_nat(1u);
v_size_x27_1281_ = lean_nat_add(v_size_1260_, v___x_1280_);
lean_dec(v_size_1260_);
lean_inc(v_bkt_1278_);
v___x_1282_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1282_, 0, v_a_1258_);
lean_ctor_set(v___x_1282_, 1, v_b_1259_);
lean_ctor_set(v___x_1282_, 2, v_bkt_1278_);
v_buckets_x27_1283_ = lean_array_uset(v_buckets_1261_, v___x_1277_, v___x_1282_);
v___x_1284_ = lean_unsigned_to_nat(4u);
v___x_1285_ = lean_nat_mul(v_size_x27_1281_, v___x_1284_);
v___x_1286_ = lean_unsigned_to_nat(3u);
v___x_1287_ = lean_nat_div(v___x_1285_, v___x_1286_);
lean_dec(v___x_1285_);
v___x_1288_ = lean_array_get_size(v_buckets_x27_1283_);
v___x_1289_ = lean_nat_dec_le(v___x_1287_, v___x_1288_);
lean_dec(v___x_1287_);
if (v___x_1289_ == 0)
{
lean_object* v_val_1290_; lean_object* v___x_1292_; 
v_val_1290_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11___redArg(v_buckets_x27_1283_);
if (v_isShared_1264_ == 0)
{
lean_ctor_set(v___x_1263_, 1, v_val_1290_);
lean_ctor_set(v___x_1263_, 0, v_size_x27_1281_);
v___x_1292_ = v___x_1263_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_size_x27_1281_);
lean_ctor_set(v_reuseFailAlloc_1293_, 1, v_val_1290_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
return v___x_1292_;
}
}
else
{
lean_object* v___x_1295_; 
if (v_isShared_1264_ == 0)
{
lean_ctor_set(v___x_1263_, 1, v_buckets_x27_1283_);
lean_ctor_set(v___x_1263_, 0, v_size_x27_1281_);
v___x_1295_ = v___x_1263_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v_size_x27_1281_);
lean_ctor_set(v_reuseFailAlloc_1296_, 1, v_buckets_x27_1283_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
return v___x_1295_;
}
}
}
else
{
lean_object* v___x_1297_; lean_object* v_buckets_x27_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1302_; 
lean_inc(v_bkt_1278_);
v___x_1297_ = lean_box(0);
v_buckets_x27_1298_ = lean_array_uset(v_buckets_1261_, v___x_1277_, v___x_1297_);
v___x_1299_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__12___redArg(v_a_1258_, v_b_1259_, v_bkt_1278_);
v___x_1300_ = lean_array_uset(v_buckets_x27_1298_, v___x_1277_, v___x_1299_);
if (v_isShared_1264_ == 0)
{
lean_ctor_set(v___x_1263_, 1, v___x_1300_);
v___x_1302_ = v___x_1263_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v_size_1260_);
lean_ctor_set(v_reuseFailAlloc_1303_, 1, v___x_1300_);
v___x_1302_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
return v___x_1302_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__2(lean_object* v_a_1305_, lean_object* v_e_1306_, lean_object* v_a_1307_){
_start:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1309_ = lean_st_ref_take(v_a_1305_);
v___x_1310_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6___redArg(v___x_1309_, v_e_1306_, v_a_1307_);
v___x_1311_ = lean_st_ref_set(v_a_1305_, v___x_1310_);
v___x_1312_ = lean_box(0);
return v___x_1312_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__2___boxed(lean_object* v_a_1313_, lean_object* v_e_1314_, lean_object* v_a_1315_, lean_object* v___y_1316_){
_start:
{
lean_object* v_res_1317_; 
v_res_1317_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__2(v_a_1313_, v_e_1314_, v_a_1315_);
lean_dec(v_a_1313_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___redArg(lean_object* v_a_1318_, lean_object* v_x_1319_){
_start:
{
if (lean_obj_tag(v_x_1319_) == 0)
{
lean_object* v___x_1320_; 
v___x_1320_ = lean_box(0);
return v___x_1320_;
}
else
{
lean_object* v_key_1321_; lean_object* v_value_1322_; lean_object* v_tail_1323_; uint8_t v___x_1324_; 
v_key_1321_ = lean_ctor_get(v_x_1319_, 0);
v_value_1322_ = lean_ctor_get(v_x_1319_, 1);
v_tail_1323_ = lean_ctor_get(v_x_1319_, 2);
v___x_1324_ = l_Lean_ExprStructEq_beq(v_key_1321_, v_a_1318_);
if (v___x_1324_ == 0)
{
v_x_1319_ = v_tail_1323_;
goto _start;
}
else
{
lean_object* v___x_1326_; 
lean_inc(v_value_1322_);
v___x_1326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1326_, 0, v_value_1322_);
return v___x_1326_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___redArg___boxed(lean_object* v_a_1327_, lean_object* v_x_1328_){
_start:
{
lean_object* v_res_1329_; 
v_res_1329_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___redArg(v_a_1327_, v_x_1328_);
lean_dec(v_x_1328_);
lean_dec_ref(v_a_1327_);
return v_res_1329_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg(lean_object* v_m_1330_, lean_object* v_a_1331_){
_start:
{
lean_object* v_buckets_1332_; lean_object* v___x_1333_; uint64_t v___x_1334_; uint64_t v___x_1335_; uint64_t v___x_1336_; uint64_t v_fold_1337_; uint64_t v___x_1338_; uint64_t v___x_1339_; uint64_t v___x_1340_; size_t v___x_1341_; size_t v___x_1342_; size_t v___x_1343_; size_t v___x_1344_; size_t v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; 
v_buckets_1332_ = lean_ctor_get(v_m_1330_, 1);
v___x_1333_ = lean_array_get_size(v_buckets_1332_);
v___x_1334_ = l_Lean_ExprStructEq_hash(v_a_1331_);
v___x_1335_ = 32ULL;
v___x_1336_ = lean_uint64_shift_right(v___x_1334_, v___x_1335_);
v_fold_1337_ = lean_uint64_xor(v___x_1334_, v___x_1336_);
v___x_1338_ = 16ULL;
v___x_1339_ = lean_uint64_shift_right(v_fold_1337_, v___x_1338_);
v___x_1340_ = lean_uint64_xor(v_fold_1337_, v___x_1339_);
v___x_1341_ = lean_uint64_to_usize(v___x_1340_);
v___x_1342_ = lean_usize_of_nat(v___x_1333_);
v___x_1343_ = ((size_t)1ULL);
v___x_1344_ = lean_usize_sub(v___x_1342_, v___x_1343_);
v___x_1345_ = lean_usize_land(v___x_1341_, v___x_1344_);
v___x_1346_ = lean_array_uget_borrowed(v_buckets_1332_, v___x_1345_);
v___x_1347_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___redArg(v_a_1331_, v___x_1346_);
return v___x_1347_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_m_1348_, lean_object* v_a_1349_){
_start:
{
lean_object* v_res_1350_; 
v_res_1350_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg(v_m_1348_, v_a_1349_);
lean_dec_ref(v_a_1349_);
lean_dec_ref(v_m_1348_);
return v_res_1350_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1(lean_object* v_pre_1351_, lean_object* v_post_1352_, size_t v_sz_1353_, size_t v_i_1354_, lean_object* v_bs_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_){
_start:
{
uint8_t v___x_1360_; 
v___x_1360_ = lean_usize_dec_lt(v_i_1354_, v_sz_1353_);
if (v___x_1360_ == 0)
{
lean_object* v___x_1361_; 
lean_dec_ref(v_post_1352_);
lean_dec_ref(v_pre_1351_);
v___x_1361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1361_, 0, v_bs_1355_);
return v___x_1361_;
}
else
{
lean_object* v_v_1362_; lean_object* v___x_1363_; 
v_v_1362_ = lean_array_uget_borrowed(v_bs_1355_, v_i_1354_);
lean_inc(v_v_1362_);
lean_inc_ref(v_post_1352_);
lean_inc_ref(v_pre_1351_);
v___x_1363_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1351_, v_post_1352_, v_v_1362_, v___y_1356_, v___y_1357_, v___y_1358_);
if (lean_obj_tag(v___x_1363_) == 0)
{
lean_object* v_a_1364_; lean_object* v___x_1365_; lean_object* v_bs_x27_1366_; size_t v___x_1367_; size_t v___x_1368_; lean_object* v___x_1369_; 
v_a_1364_ = lean_ctor_get(v___x_1363_, 0);
lean_inc(v_a_1364_);
lean_dec_ref(v___x_1363_);
v___x_1365_ = lean_unsigned_to_nat(0u);
v_bs_x27_1366_ = lean_array_uset(v_bs_1355_, v_i_1354_, v___x_1365_);
v___x_1367_ = ((size_t)1ULL);
v___x_1368_ = lean_usize_add(v_i_1354_, v___x_1367_);
v___x_1369_ = lean_array_uset(v_bs_x27_1366_, v_i_1354_, v_a_1364_);
v_i_1354_ = v___x_1368_;
v_bs_1355_ = v___x_1369_;
goto _start;
}
else
{
lean_object* v_a_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1378_; 
lean_dec_ref(v_bs_1355_);
lean_dec_ref(v_post_1352_);
lean_dec_ref(v_pre_1351_);
v_a_1371_ = lean_ctor_get(v___x_1363_, 0);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1363_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1373_ = v___x_1363_;
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_a_1371_);
lean_dec(v___x_1363_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1376_; 
if (v_isShared_1374_ == 0)
{
v___x_1376_ = v___x_1373_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_a_1371_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__4(lean_object* v_pre_1379_, lean_object* v_post_1380_, lean_object* v_x_1381_, lean_object* v_x_1382_, lean_object* v_x_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_){
_start:
{
if (lean_obj_tag(v_x_1381_) == 5)
{
lean_object* v_fn_1388_; lean_object* v_arg_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; 
v_fn_1388_ = lean_ctor_get(v_x_1381_, 0);
lean_inc_ref(v_fn_1388_);
v_arg_1389_ = lean_ctor_get(v_x_1381_, 1);
lean_inc_ref(v_arg_1389_);
lean_dec_ref(v_x_1381_);
v___x_1390_ = lean_array_set(v_x_1382_, v_x_1383_, v_arg_1389_);
v___x_1391_ = lean_unsigned_to_nat(1u);
v___x_1392_ = lean_nat_sub(v_x_1383_, v___x_1391_);
lean_dec(v_x_1383_);
v_x_1381_ = v_fn_1388_;
v_x_1382_ = v___x_1390_;
v_x_1383_ = v___x_1392_;
goto _start;
}
else
{
lean_object* v___x_1394_; 
lean_dec(v_x_1383_);
lean_inc_ref(v_post_1380_);
lean_inc_ref(v_pre_1379_);
v___x_1394_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1379_, v_post_1380_, v_x_1381_, v___y_1384_, v___y_1385_, v___y_1386_);
if (lean_obj_tag(v___x_1394_) == 0)
{
lean_object* v_a_1395_; size_t v_sz_1396_; size_t v___x_1397_; lean_object* v___x_1398_; 
v_a_1395_ = lean_ctor_get(v___x_1394_, 0);
lean_inc(v_a_1395_);
lean_dec_ref(v___x_1394_);
v_sz_1396_ = lean_array_size(v_x_1382_);
v___x_1397_ = ((size_t)0ULL);
lean_inc_ref(v_post_1380_);
lean_inc_ref(v_pre_1379_);
v___x_1398_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1(v_pre_1379_, v_post_1380_, v_sz_1396_, v___x_1397_, v_x_1382_, v___y_1384_, v___y_1385_, v___y_1386_);
if (lean_obj_tag(v___x_1398_) == 0)
{
lean_object* v_a_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; 
v_a_1399_ = lean_ctor_get(v___x_1398_, 0);
lean_inc(v_a_1399_);
lean_dec_ref(v___x_1398_);
v___x_1400_ = l_Lean_mkAppN(v_a_1395_, v_a_1399_);
lean_dec(v_a_1399_);
v___x_1401_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1379_, v_post_1380_, v___x_1400_, v___y_1384_, v___y_1385_, v___y_1386_);
return v___x_1401_;
}
else
{
lean_object* v_a_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1409_; 
lean_dec(v_a_1395_);
lean_dec_ref(v_post_1380_);
lean_dec_ref(v_pre_1379_);
v_a_1402_ = lean_ctor_get(v___x_1398_, 0);
v_isSharedCheck_1409_ = !lean_is_exclusive(v___x_1398_);
if (v_isSharedCheck_1409_ == 0)
{
v___x_1404_ = v___x_1398_;
v_isShared_1405_ = v_isSharedCheck_1409_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_a_1402_);
lean_dec(v___x_1398_);
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
v_reuseFailAlloc_1408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v_a_1402_);
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
else
{
lean_dec_ref(v_x_1382_);
lean_dec_ref(v_post_1380_);
lean_dec_ref(v_pre_1379_);
return v___x_1394_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__1(lean_object* v___x_1410_, lean_object* v_pre_1411_, lean_object* v_e_1412_, lean_object* v_post_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_){
_start:
{
lean_object* v___y_1419_; lean_object* v___y_1420_; uint8_t v___y_1421_; lean_object* v___y_1422_; lean_object* v___y_1423_; lean_object* v___y_1424_; lean_object* v___y_1425_; uint8_t v___y_1426_; uint8_t v___y_1436_; lean_object* v___y_1437_; lean_object* v___y_1438_; lean_object* v___y_1439_; lean_object* v___y_1440_; uint8_t v___y_1441_; uint8_t v___y_1449_; lean_object* v___y_1450_; lean_object* v___y_1451_; lean_object* v___y_1452_; lean_object* v___y_1453_; uint8_t v___y_1454_; lean_object* v___x_1461_; 
v___x_1461_ = l_Lean_Core_checkSystem(v___x_1410_, v___y_1415_, v___y_1416_);
if (lean_obj_tag(v___x_1461_) == 0)
{
lean_object* v___x_1462_; 
lean_dec_ref(v___x_1461_);
lean_inc_ref(v_pre_1411_);
lean_inc(v___y_1416_);
lean_inc_ref(v___y_1415_);
lean_inc_ref(v_e_1412_);
v___x_1462_ = lean_apply_4(v_pre_1411_, v_e_1412_, v___y_1415_, v___y_1416_, lean_box(0));
if (lean_obj_tag(v___x_1462_) == 0)
{
lean_object* v_a_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1552_; 
v_a_1463_ = lean_ctor_get(v___x_1462_, 0);
v_isSharedCheck_1552_ = !lean_is_exclusive(v___x_1462_);
if (v_isSharedCheck_1552_ == 0)
{
v___x_1465_ = v___x_1462_;
v_isShared_1466_ = v_isSharedCheck_1552_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_a_1463_);
lean_dec(v___x_1462_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1552_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
lean_object* v___y_1468_; 
switch(lean_obj_tag(v_a_1463_))
{
case 0:
{
lean_object* v_e_1542_; lean_object* v___x_1544_; 
lean_dec_ref(v_post_1413_);
lean_dec_ref(v_e_1412_);
lean_dec_ref(v_pre_1411_);
v_e_1542_ = lean_ctor_get(v_a_1463_, 0);
lean_inc_ref(v_e_1542_);
lean_dec_ref(v_a_1463_);
if (v_isShared_1466_ == 0)
{
lean_ctor_set(v___x_1465_, 0, v_e_1542_);
v___x_1544_ = v___x_1465_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v_e_1542_);
v___x_1544_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
return v___x_1544_;
}
}
case 1:
{
lean_object* v_e_1546_; lean_object* v___x_1547_; 
lean_del_object(v___x_1465_);
lean_dec_ref(v_e_1412_);
v_e_1546_ = lean_ctor_get(v_a_1463_, 0);
lean_inc_ref(v_e_1546_);
lean_dec_ref(v_a_1463_);
lean_inc_ref(v_post_1413_);
lean_inc_ref(v_pre_1411_);
v___x_1547_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1411_, v_post_1413_, v_e_1546_, v___y_1414_, v___y_1415_, v___y_1416_);
if (lean_obj_tag(v___x_1547_) == 0)
{
lean_object* v_a_1548_; lean_object* v___x_1549_; 
v_a_1548_ = lean_ctor_get(v___x_1547_, 0);
lean_inc(v_a_1548_);
lean_dec_ref(v___x_1547_);
v___x_1549_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1411_, v_post_1413_, v_a_1548_, v___y_1414_, v___y_1415_, v___y_1416_);
return v___x_1549_;
}
else
{
lean_dec_ref(v_post_1413_);
lean_dec_ref(v_pre_1411_);
return v___x_1547_;
}
}
default: 
{
lean_object* v_e_x3f_1550_; 
lean_del_object(v___x_1465_);
v_e_x3f_1550_ = lean_ctor_get(v_a_1463_, 0);
lean_inc(v_e_x3f_1550_);
lean_dec_ref(v_a_1463_);
if (lean_obj_tag(v_e_x3f_1550_) == 0)
{
v___y_1468_ = v_e_1412_;
goto v___jp_1467_;
}
else
{
lean_object* v_val_1551_; 
lean_dec_ref(v_e_1412_);
v_val_1551_ = lean_ctor_get(v_e_x3f_1550_, 0);
lean_inc(v_val_1551_);
lean_dec_ref(v_e_x3f_1550_);
v___y_1468_ = v_val_1551_;
goto v___jp_1467_;
}
}
}
v___jp_1467_:
{
switch(lean_obj_tag(v___y_1468_))
{
case 7:
{
lean_object* v_binderName_1469_; lean_object* v_binderType_1470_; lean_object* v_body_1471_; uint8_t v_binderInfo_1472_; lean_object* v___x_1473_; 
v_binderName_1469_ = lean_ctor_get(v___y_1468_, 0);
lean_inc(v_binderName_1469_);
v_binderType_1470_ = lean_ctor_get(v___y_1468_, 1);
v_body_1471_ = lean_ctor_get(v___y_1468_, 2);
v_binderInfo_1472_ = lean_ctor_get_uint8(v___y_1468_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1470_);
lean_inc_ref(v_post_1413_);
lean_inc_ref(v_pre_1411_);
v___x_1473_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1411_, v_post_1413_, v_binderType_1470_, v___y_1414_, v___y_1415_, v___y_1416_);
if (lean_obj_tag(v___x_1473_) == 0)
{
lean_object* v_a_1474_; lean_object* v___x_1475_; 
v_a_1474_ = lean_ctor_get(v___x_1473_, 0);
lean_inc(v_a_1474_);
lean_dec_ref(v___x_1473_);
lean_inc_ref(v_body_1471_);
lean_inc_ref(v_post_1413_);
lean_inc_ref(v_pre_1411_);
v___x_1475_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1411_, v_post_1413_, v_body_1471_, v___y_1414_, v___y_1415_, v___y_1416_);
if (lean_obj_tag(v___x_1475_) == 0)
{
lean_object* v_a_1476_; size_t v___x_1477_; size_t v___x_1478_; uint8_t v___x_1479_; 
v_a_1476_ = lean_ctor_get(v___x_1475_, 0);
lean_inc(v_a_1476_);
lean_dec_ref(v___x_1475_);
v___x_1477_ = lean_ptr_addr(v_binderType_1470_);
v___x_1478_ = lean_ptr_addr(v_a_1474_);
v___x_1479_ = lean_usize_dec_eq(v___x_1477_, v___x_1478_);
if (v___x_1479_ == 0)
{
v___y_1449_ = v_binderInfo_1472_;
v___y_1450_ = v_binderName_1469_;
v___y_1451_ = v_a_1476_;
v___y_1452_ = v_a_1474_;
v___y_1453_ = v___y_1468_;
v___y_1454_ = v___x_1479_;
goto v___jp_1448_;
}
else
{
size_t v___x_1480_; size_t v___x_1481_; uint8_t v___x_1482_; 
v___x_1480_ = lean_ptr_addr(v_body_1471_);
v___x_1481_ = lean_ptr_addr(v_a_1476_);
v___x_1482_ = lean_usize_dec_eq(v___x_1480_, v___x_1481_);
v___y_1449_ = v_binderInfo_1472_;
v___y_1450_ = v_binderName_1469_;
v___y_1451_ = v_a_1476_;
v___y_1452_ = v_a_1474_;
v___y_1453_ = v___y_1468_;
v___y_1454_ = v___x_1482_;
goto v___jp_1448_;
}
}
else
{
lean_dec(v_a_1474_);
lean_dec(v_binderName_1469_);
lean_dec_ref(v___y_1468_);
lean_dec_ref(v_post_1413_);
lean_dec_ref(v_pre_1411_);
return v___x_1475_;
}
}
else
{
lean_dec_ref(v___y_1468_);
lean_dec(v_binderName_1469_);
lean_dec_ref(v_post_1413_);
lean_dec_ref(v_pre_1411_);
return v___x_1473_;
}
}
case 6:
{
lean_object* v_binderName_1483_; lean_object* v_binderType_1484_; lean_object* v_body_1485_; uint8_t v_binderInfo_1486_; lean_object* v___x_1487_; 
v_binderName_1483_ = lean_ctor_get(v___y_1468_, 0);
lean_inc(v_binderName_1483_);
v_binderType_1484_ = lean_ctor_get(v___y_1468_, 1);
v_body_1485_ = lean_ctor_get(v___y_1468_, 2);
v_binderInfo_1486_ = lean_ctor_get_uint8(v___y_1468_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1484_);
lean_inc_ref(v_post_1413_);
lean_inc_ref(v_pre_1411_);
v___x_1487_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1411_, v_post_1413_, v_binderType_1484_, v___y_1414_, v___y_1415_, v___y_1416_);
if (lean_obj_tag(v___x_1487_) == 0)
{
lean_object* v_a_1488_; lean_object* v___x_1489_; 
v_a_1488_ = lean_ctor_get(v___x_1487_, 0);
lean_inc(v_a_1488_);
lean_dec_ref(v___x_1487_);
lean_inc_ref(v_body_1485_);
lean_inc_ref(v_post_1413_);
lean_inc_ref(v_pre_1411_);
v___x_1489_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1411_, v_post_1413_, v_body_1485_, v___y_1414_, v___y_1415_, v___y_1416_);
if (lean_obj_tag(v___x_1489_) == 0)
{
lean_object* v_a_1490_; size_t v___x_1491_; size_t v___x_1492_; uint8_t v___x_1493_; 
v_a_1490_ = lean_ctor_get(v___x_1489_, 0);
lean_inc(v_a_1490_);
lean_dec_ref(v___x_1489_);
v___x_1491_ = lean_ptr_addr(v_binderType_1484_);
v___x_1492_ = lean_ptr_addr(v_a_1488_);
v___x_1493_ = lean_usize_dec_eq(v___x_1491_, v___x_1492_);
if (v___x_1493_ == 0)
{
v___y_1436_ = v_binderInfo_1486_;
v___y_1437_ = v___y_1468_;
v___y_1438_ = v_a_1488_;
v___y_1439_ = v_a_1490_;
v___y_1440_ = v_binderName_1483_;
v___y_1441_ = v___x_1493_;
goto v___jp_1435_;
}
else
{
size_t v___x_1494_; size_t v___x_1495_; uint8_t v___x_1496_; 
v___x_1494_ = lean_ptr_addr(v_body_1485_);
v___x_1495_ = lean_ptr_addr(v_a_1490_);
v___x_1496_ = lean_usize_dec_eq(v___x_1494_, v___x_1495_);
v___y_1436_ = v_binderInfo_1486_;
v___y_1437_ = v___y_1468_;
v___y_1438_ = v_a_1488_;
v___y_1439_ = v_a_1490_;
v___y_1440_ = v_binderName_1483_;
v___y_1441_ = v___x_1496_;
goto v___jp_1435_;
}
}
else
{
lean_dec(v_a_1488_);
lean_dec_ref(v___y_1468_);
lean_dec(v_binderName_1483_);
lean_dec_ref(v_post_1413_);
lean_dec_ref(v_pre_1411_);
return v___x_1489_;
}
}
else
{
lean_dec_ref(v___y_1468_);
lean_dec(v_binderName_1483_);
lean_dec_ref(v_post_1413_);
lean_dec_ref(v_pre_1411_);
return v___x_1487_;
}
}
case 8:
{
lean_object* v_declName_1497_; lean_object* v_type_1498_; lean_object* v_value_1499_; lean_object* v_body_1500_; uint8_t v_nondep_1501_; lean_object* v___x_1502_; 
v_declName_1497_ = lean_ctor_get(v___y_1468_, 0);
lean_inc(v_declName_1497_);
v_type_1498_ = lean_ctor_get(v___y_1468_, 1);
v_value_1499_ = lean_ctor_get(v___y_1468_, 2);
v_body_1500_ = lean_ctor_get(v___y_1468_, 3);
lean_inc_ref(v_body_1500_);
v_nondep_1501_ = lean_ctor_get_uint8(v___y_1468_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_1498_);
lean_inc_ref(v_post_1413_);
lean_inc_ref(v_pre_1411_);
v___x_1502_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1411_, v_post_1413_, v_type_1498_, v___y_1414_, v___y_1415_, v___y_1416_);
if (lean_obj_tag(v___x_1502_) == 0)
{
lean_object* v_a_1503_; lean_object* v___x_1504_; 
v_a_1503_ = lean_ctor_get(v___x_1502_, 0);
lean_inc(v_a_1503_);
lean_dec_ref(v___x_1502_);
lean_inc_ref(v_value_1499_);
lean_inc_ref(v_post_1413_);
lean_inc_ref(v_pre_1411_);
v___x_1504_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1411_, v_post_1413_, v_value_1499_, v___y_1414_, v___y_1415_, v___y_1416_);
if (lean_obj_tag(v___x_1504_) == 0)
{
lean_object* v_a_1505_; lean_object* v___x_1506_; 
v_a_1505_ = lean_ctor_get(v___x_1504_, 0);
lean_inc(v_a_1505_);
lean_dec_ref(v___x_1504_);
lean_inc_ref(v_body_1500_);
lean_inc_ref(v_post_1413_);
lean_inc_ref(v_pre_1411_);
v___x_1506_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1411_, v_post_1413_, v_body_1500_, v___y_1414_, v___y_1415_, v___y_1416_);
if (lean_obj_tag(v___x_1506_) == 0)
{
lean_object* v_a_1507_; size_t v___x_1508_; size_t v___x_1509_; uint8_t v___x_1510_; 
v_a_1507_ = lean_ctor_get(v___x_1506_, 0);
lean_inc(v_a_1507_);
lean_dec_ref(v___x_1506_);
v___x_1508_ = lean_ptr_addr(v_type_1498_);
v___x_1509_ = lean_ptr_addr(v_a_1503_);
v___x_1510_ = lean_usize_dec_eq(v___x_1508_, v___x_1509_);
if (v___x_1510_ == 0)
{
v___y_1419_ = v_declName_1497_;
v___y_1420_ = v___y_1468_;
v___y_1421_ = v_nondep_1501_;
v___y_1422_ = v_body_1500_;
v___y_1423_ = v_a_1505_;
v___y_1424_ = v_a_1507_;
v___y_1425_ = v_a_1503_;
v___y_1426_ = v___x_1510_;
goto v___jp_1418_;
}
else
{
size_t v___x_1511_; size_t v___x_1512_; uint8_t v___x_1513_; 
v___x_1511_ = lean_ptr_addr(v_value_1499_);
v___x_1512_ = lean_ptr_addr(v_a_1505_);
v___x_1513_ = lean_usize_dec_eq(v___x_1511_, v___x_1512_);
v___y_1419_ = v_declName_1497_;
v___y_1420_ = v___y_1468_;
v___y_1421_ = v_nondep_1501_;
v___y_1422_ = v_body_1500_;
v___y_1423_ = v_a_1505_;
v___y_1424_ = v_a_1507_;
v___y_1425_ = v_a_1503_;
v___y_1426_ = v___x_1513_;
goto v___jp_1418_;
}
}
else
{
lean_dec(v_a_1505_);
lean_dec(v_a_1503_);
lean_dec_ref(v_body_1500_);
lean_dec_ref(v___y_1468_);
lean_dec(v_declName_1497_);
lean_dec_ref(v_post_1413_);
lean_dec_ref(v_pre_1411_);
return v___x_1506_;
}
}
else
{
lean_dec(v_a_1503_);
lean_dec_ref(v_body_1500_);
lean_dec_ref(v___y_1468_);
lean_dec(v_declName_1497_);
lean_dec_ref(v_post_1413_);
lean_dec_ref(v_pre_1411_);
return v___x_1504_;
}
}
else
{
lean_dec_ref(v_body_1500_);
lean_dec_ref(v___y_1468_);
lean_dec(v_declName_1497_);
lean_dec_ref(v_post_1413_);
lean_dec_ref(v_pre_1411_);
return v___x_1502_;
}
}
case 5:
{
lean_object* v_dummy_1514_; lean_object* v_nargs_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; 
v_dummy_1514_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_1515_ = l_Lean_Expr_getAppNumArgs(v___y_1468_);
lean_inc(v_nargs_1515_);
v___x_1516_ = lean_mk_array(v_nargs_1515_, v_dummy_1514_);
v___x_1517_ = lean_unsigned_to_nat(1u);
v___x_1518_ = lean_nat_sub(v_nargs_1515_, v___x_1517_);
lean_dec(v_nargs_1515_);
v___x_1519_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__4(v_pre_1411_, v_post_1413_, v___y_1468_, v___x_1516_, v___x_1518_, v___y_1414_, v___y_1415_, v___y_1416_);
return v___x_1519_;
}
case 10:
{
lean_object* v_data_1520_; lean_object* v_expr_1521_; lean_object* v___x_1522_; 
v_data_1520_ = lean_ctor_get(v___y_1468_, 0);
v_expr_1521_ = lean_ctor_get(v___y_1468_, 1);
lean_inc_ref(v_expr_1521_);
lean_inc_ref(v_post_1413_);
lean_inc_ref(v_pre_1411_);
v___x_1522_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1411_, v_post_1413_, v_expr_1521_, v___y_1414_, v___y_1415_, v___y_1416_);
if (lean_obj_tag(v___x_1522_) == 0)
{
lean_object* v_a_1523_; size_t v___x_1524_; size_t v___x_1525_; uint8_t v___x_1526_; 
v_a_1523_ = lean_ctor_get(v___x_1522_, 0);
lean_inc(v_a_1523_);
lean_dec_ref(v___x_1522_);
v___x_1524_ = lean_ptr_addr(v_expr_1521_);
v___x_1525_ = lean_ptr_addr(v_a_1523_);
v___x_1526_ = lean_usize_dec_eq(v___x_1524_, v___x_1525_);
if (v___x_1526_ == 0)
{
lean_object* v___x_1527_; lean_object* v___x_1528_; 
lean_inc(v_data_1520_);
lean_dec_ref(v___y_1468_);
v___x_1527_ = l_Lean_Expr_mdata___override(v_data_1520_, v_a_1523_);
v___x_1528_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1411_, v_post_1413_, v___x_1527_, v___y_1414_, v___y_1415_, v___y_1416_);
return v___x_1528_;
}
else
{
lean_object* v___x_1529_; 
lean_dec(v_a_1523_);
v___x_1529_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1411_, v_post_1413_, v___y_1468_, v___y_1414_, v___y_1415_, v___y_1416_);
return v___x_1529_;
}
}
else
{
lean_dec_ref(v___y_1468_);
lean_dec_ref(v_post_1413_);
lean_dec_ref(v_pre_1411_);
return v___x_1522_;
}
}
case 11:
{
lean_object* v_typeName_1530_; lean_object* v_idx_1531_; lean_object* v_struct_1532_; lean_object* v___x_1533_; 
v_typeName_1530_ = lean_ctor_get(v___y_1468_, 0);
v_idx_1531_ = lean_ctor_get(v___y_1468_, 1);
v_struct_1532_ = lean_ctor_get(v___y_1468_, 2);
lean_inc_ref(v_struct_1532_);
lean_inc_ref(v_post_1413_);
lean_inc_ref(v_pre_1411_);
v___x_1533_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1411_, v_post_1413_, v_struct_1532_, v___y_1414_, v___y_1415_, v___y_1416_);
if (lean_obj_tag(v___x_1533_) == 0)
{
lean_object* v_a_1534_; size_t v___x_1535_; size_t v___x_1536_; uint8_t v___x_1537_; 
v_a_1534_ = lean_ctor_get(v___x_1533_, 0);
lean_inc(v_a_1534_);
lean_dec_ref(v___x_1533_);
v___x_1535_ = lean_ptr_addr(v_struct_1532_);
v___x_1536_ = lean_ptr_addr(v_a_1534_);
v___x_1537_ = lean_usize_dec_eq(v___x_1535_, v___x_1536_);
if (v___x_1537_ == 0)
{
lean_object* v___x_1538_; lean_object* v___x_1539_; 
lean_inc(v_idx_1531_);
lean_inc(v_typeName_1530_);
lean_dec_ref(v___y_1468_);
v___x_1538_ = l_Lean_Expr_proj___override(v_typeName_1530_, v_idx_1531_, v_a_1534_);
v___x_1539_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1411_, v_post_1413_, v___x_1538_, v___y_1414_, v___y_1415_, v___y_1416_);
return v___x_1539_;
}
else
{
lean_object* v___x_1540_; 
lean_dec(v_a_1534_);
v___x_1540_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1411_, v_post_1413_, v___y_1468_, v___y_1414_, v___y_1415_, v___y_1416_);
return v___x_1540_;
}
}
else
{
lean_dec_ref(v___y_1468_);
lean_dec_ref(v_post_1413_);
lean_dec_ref(v_pre_1411_);
return v___x_1533_;
}
}
default: 
{
lean_object* v___x_1541_; 
v___x_1541_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1411_, v_post_1413_, v___y_1468_, v___y_1414_, v___y_1415_, v___y_1416_);
return v___x_1541_;
}
}
}
}
}
else
{
lean_object* v_a_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1560_; 
lean_dec_ref(v_post_1413_);
lean_dec_ref(v_e_1412_);
lean_dec_ref(v_pre_1411_);
v_a_1553_ = lean_ctor_get(v___x_1462_, 0);
v_isSharedCheck_1560_ = !lean_is_exclusive(v___x_1462_);
if (v_isSharedCheck_1560_ == 0)
{
v___x_1555_ = v___x_1462_;
v_isShared_1556_ = v_isSharedCheck_1560_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_a_1553_);
lean_dec(v___x_1462_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1560_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v___x_1558_; 
if (v_isShared_1556_ == 0)
{
v___x_1558_ = v___x_1555_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v_a_1553_);
v___x_1558_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
return v___x_1558_;
}
}
}
}
else
{
lean_object* v_a_1561_; lean_object* v___x_1563_; uint8_t v_isShared_1564_; uint8_t v_isSharedCheck_1568_; 
lean_dec_ref(v_post_1413_);
lean_dec_ref(v_e_1412_);
lean_dec_ref(v_pre_1411_);
v_a_1561_ = lean_ctor_get(v___x_1461_, 0);
v_isSharedCheck_1568_ = !lean_is_exclusive(v___x_1461_);
if (v_isSharedCheck_1568_ == 0)
{
v___x_1563_ = v___x_1461_;
v_isShared_1564_ = v_isSharedCheck_1568_;
goto v_resetjp_1562_;
}
else
{
lean_inc(v_a_1561_);
lean_dec(v___x_1461_);
v___x_1563_ = lean_box(0);
v_isShared_1564_ = v_isSharedCheck_1568_;
goto v_resetjp_1562_;
}
v_resetjp_1562_:
{
lean_object* v___x_1566_; 
if (v_isShared_1564_ == 0)
{
v___x_1566_ = v___x_1563_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v_a_1561_);
v___x_1566_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
return v___x_1566_;
}
}
}
v___jp_1418_:
{
if (v___y_1426_ == 0)
{
lean_object* v___x_1427_; lean_object* v___x_1428_; 
lean_dec_ref(v___y_1422_);
lean_dec_ref(v___y_1420_);
v___x_1427_ = l_Lean_Expr_letE___override(v___y_1419_, v___y_1425_, v___y_1423_, v___y_1424_, v___y_1421_);
v___x_1428_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1411_, v_post_1413_, v___x_1427_, v___y_1414_, v___y_1415_, v___y_1416_);
return v___x_1428_;
}
else
{
size_t v___x_1429_; size_t v___x_1430_; uint8_t v___x_1431_; 
v___x_1429_ = lean_ptr_addr(v___y_1422_);
lean_dec_ref(v___y_1422_);
v___x_1430_ = lean_ptr_addr(v___y_1424_);
v___x_1431_ = lean_usize_dec_eq(v___x_1429_, v___x_1430_);
if (v___x_1431_ == 0)
{
lean_object* v___x_1432_; lean_object* v___x_1433_; 
lean_dec_ref(v___y_1420_);
v___x_1432_ = l_Lean_Expr_letE___override(v___y_1419_, v___y_1425_, v___y_1423_, v___y_1424_, v___y_1421_);
v___x_1433_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1411_, v_post_1413_, v___x_1432_, v___y_1414_, v___y_1415_, v___y_1416_);
return v___x_1433_;
}
else
{
lean_object* v___x_1434_; 
lean_dec_ref(v___y_1425_);
lean_dec_ref(v___y_1424_);
lean_dec_ref(v___y_1423_);
lean_dec(v___y_1419_);
v___x_1434_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1411_, v_post_1413_, v___y_1420_, v___y_1414_, v___y_1415_, v___y_1416_);
return v___x_1434_;
}
}
}
v___jp_1435_:
{
if (v___y_1441_ == 0)
{
lean_object* v___x_1442_; lean_object* v___x_1443_; 
lean_dec_ref(v___y_1437_);
v___x_1442_ = l_Lean_Expr_lam___override(v___y_1440_, v___y_1438_, v___y_1439_, v___y_1436_);
v___x_1443_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1411_, v_post_1413_, v___x_1442_, v___y_1414_, v___y_1415_, v___y_1416_);
return v___x_1443_;
}
else
{
uint8_t v___x_1444_; 
v___x_1444_ = l_Lean_instBEqBinderInfo_beq(v___y_1436_, v___y_1436_);
if (v___x_1444_ == 0)
{
lean_object* v___x_1445_; lean_object* v___x_1446_; 
lean_dec_ref(v___y_1437_);
v___x_1445_ = l_Lean_Expr_lam___override(v___y_1440_, v___y_1438_, v___y_1439_, v___y_1436_);
v___x_1446_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1411_, v_post_1413_, v___x_1445_, v___y_1414_, v___y_1415_, v___y_1416_);
return v___x_1446_;
}
else
{
lean_object* v___x_1447_; 
lean_dec(v___y_1440_);
lean_dec_ref(v___y_1439_);
lean_dec_ref(v___y_1438_);
v___x_1447_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1411_, v_post_1413_, v___y_1437_, v___y_1414_, v___y_1415_, v___y_1416_);
return v___x_1447_;
}
}
}
v___jp_1448_:
{
if (v___y_1454_ == 0)
{
lean_object* v___x_1455_; lean_object* v___x_1456_; 
lean_dec_ref(v___y_1453_);
v___x_1455_ = l_Lean_Expr_forallE___override(v___y_1450_, v___y_1452_, v___y_1451_, v___y_1449_);
v___x_1456_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1411_, v_post_1413_, v___x_1455_, v___y_1414_, v___y_1415_, v___y_1416_);
return v___x_1456_;
}
else
{
uint8_t v___x_1457_; 
v___x_1457_ = l_Lean_instBEqBinderInfo_beq(v___y_1449_, v___y_1449_);
if (v___x_1457_ == 0)
{
lean_object* v___x_1458_; lean_object* v___x_1459_; 
lean_dec_ref(v___y_1453_);
v___x_1458_ = l_Lean_Expr_forallE___override(v___y_1450_, v___y_1452_, v___y_1451_, v___y_1449_);
v___x_1459_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1411_, v_post_1413_, v___x_1458_, v___y_1414_, v___y_1415_, v___y_1416_);
return v___x_1459_;
}
else
{
lean_object* v___x_1460_; 
lean_dec_ref(v___y_1452_);
lean_dec_ref(v___y_1451_);
lean_dec(v___y_1450_);
v___x_1460_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1411_, v_post_1413_, v___y_1453_, v___y_1414_, v___y_1415_, v___y_1416_);
return v___x_1460_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__1___boxed(lean_object* v___x_1569_, lean_object* v_pre_1570_, lean_object* v_e_1571_, lean_object* v_post_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_){
_start:
{
lean_object* v_res_1577_; 
v_res_1577_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__1(v___x_1569_, v_pre_1570_, v_e_1571_, v_post_1572_, v___y_1573_, v___y_1574_, v___y_1575_);
lean_dec(v___y_1575_);
lean_dec_ref(v___y_1574_);
lean_dec(v___y_1573_);
return v_res_1577_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(lean_object* v_pre_1578_, lean_object* v_post_1579_, lean_object* v_e_1580_, lean_object* v_a_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_){
_start:
{
lean_object* v___x_1585_; lean_object* v___x_1586_; 
lean_inc(v_a_1581_);
v___x_1585_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1585_, 0, lean_box(0));
lean_closure_set(v___x_1585_, 1, lean_box(0));
lean_closure_set(v___x_1585_, 2, v_a_1581_);
v___x_1586_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__0(lean_box(0), v___x_1585_, v___y_1582_, v___y_1583_);
if (lean_obj_tag(v___x_1586_) == 0)
{
lean_object* v_a_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1618_; 
v_a_1587_ = lean_ctor_get(v___x_1586_, 0);
v_isSharedCheck_1618_ = !lean_is_exclusive(v___x_1586_);
if (v_isSharedCheck_1618_ == 0)
{
v___x_1589_ = v___x_1586_;
v_isShared_1590_ = v_isSharedCheck_1618_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_a_1587_);
lean_dec(v___x_1586_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1618_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
lean_object* v___x_1591_; 
v___x_1591_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg(v_a_1587_, v_e_1580_);
lean_dec(v_a_1587_);
if (lean_obj_tag(v___x_1591_) == 0)
{
lean_object* v___x_1592_; lean_object* v___f_1593_; lean_object* v___x_1594_; 
lean_del_object(v___x_1589_);
v___x_1592_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__19___closed__0));
lean_inc_ref(v_e_1580_);
v___f_1593_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__1___boxed), 8, 4);
lean_closure_set(v___f_1593_, 0, v___x_1592_);
lean_closure_set(v___f_1593_, 1, v_pre_1578_);
lean_closure_set(v___f_1593_, 2, v_e_1580_);
lean_closure_set(v___f_1593_, 3, v_post_1579_);
v___x_1594_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___redArg(v___f_1593_, v_a_1581_, v___y_1582_, v___y_1583_);
if (lean_obj_tag(v___x_1594_) == 0)
{
lean_object* v_a_1595_; lean_object* v___f_1596_; lean_object* v___x_1597_; 
v_a_1595_ = lean_ctor_get(v___x_1594_, 0);
lean_inc_n(v_a_1595_, 2);
lean_dec_ref(v___x_1594_);
lean_inc(v_a_1581_);
v___f_1596_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1596_, 0, v_a_1581_);
lean_closure_set(v___f_1596_, 1, v_e_1580_);
lean_closure_set(v___f_1596_, 2, v_a_1595_);
v___x_1597_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__0(lean_box(0), v___f_1596_, v___y_1582_, v___y_1583_);
if (lean_obj_tag(v___x_1597_) == 0)
{
lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1604_; 
v_isSharedCheck_1604_ = !lean_is_exclusive(v___x_1597_);
if (v_isSharedCheck_1604_ == 0)
{
lean_object* v_unused_1605_; 
v_unused_1605_ = lean_ctor_get(v___x_1597_, 0);
lean_dec(v_unused_1605_);
v___x_1599_ = v___x_1597_;
v_isShared_1600_ = v_isSharedCheck_1604_;
goto v_resetjp_1598_;
}
else
{
lean_dec(v___x_1597_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1604_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v___x_1602_; 
if (v_isShared_1600_ == 0)
{
lean_ctor_set(v___x_1599_, 0, v_a_1595_);
v___x_1602_ = v___x_1599_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v_a_1595_);
v___x_1602_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
return v___x_1602_;
}
}
}
else
{
lean_object* v_a_1606_; lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1613_; 
lean_dec(v_a_1595_);
v_a_1606_ = lean_ctor_get(v___x_1597_, 0);
v_isSharedCheck_1613_ = !lean_is_exclusive(v___x_1597_);
if (v_isSharedCheck_1613_ == 0)
{
v___x_1608_ = v___x_1597_;
v_isShared_1609_ = v_isSharedCheck_1613_;
goto v_resetjp_1607_;
}
else
{
lean_inc(v_a_1606_);
lean_dec(v___x_1597_);
v___x_1608_ = lean_box(0);
v_isShared_1609_ = v_isSharedCheck_1613_;
goto v_resetjp_1607_;
}
v_resetjp_1607_:
{
lean_object* v___x_1611_; 
if (v_isShared_1609_ == 0)
{
v___x_1611_ = v___x_1608_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v_a_1606_);
v___x_1611_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
return v___x_1611_;
}
}
}
}
else
{
lean_dec_ref(v_e_1580_);
return v___x_1594_;
}
}
else
{
lean_object* v_val_1614_; lean_object* v___x_1616_; 
lean_dec_ref(v_e_1580_);
lean_dec_ref(v_post_1579_);
lean_dec_ref(v_pre_1578_);
v_val_1614_ = lean_ctor_get(v___x_1591_, 0);
lean_inc(v_val_1614_);
lean_dec_ref(v___x_1591_);
if (v_isShared_1590_ == 0)
{
lean_ctor_set(v___x_1589_, 0, v_val_1614_);
v___x_1616_ = v___x_1589_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v_val_1614_);
v___x_1616_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
return v___x_1616_;
}
}
}
}
else
{
lean_object* v_a_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1626_; 
lean_dec_ref(v_e_1580_);
lean_dec_ref(v_post_1579_);
lean_dec_ref(v_pre_1578_);
v_a_1619_ = lean_ctor_get(v___x_1586_, 0);
v_isSharedCheck_1626_ = !lean_is_exclusive(v___x_1586_);
if (v_isSharedCheck_1626_ == 0)
{
v___x_1621_ = v___x_1586_;
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_a_1619_);
lean_dec(v___x_1586_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v___x_1624_; 
if (v_isShared_1622_ == 0)
{
v___x_1624_ = v___x_1621_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v_a_1619_);
v___x_1624_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
return v___x_1624_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(lean_object* v_pre_1627_, lean_object* v_post_1628_, lean_object* v_e_1629_, lean_object* v_a_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_){
_start:
{
lean_object* v___x_1634_; 
lean_inc_ref(v_post_1628_);
lean_inc(v___y_1632_);
lean_inc_ref(v___y_1631_);
lean_inc_ref(v_e_1629_);
v___x_1634_ = lean_apply_4(v_post_1628_, v_e_1629_, v___y_1631_, v___y_1632_, lean_box(0));
if (lean_obj_tag(v___x_1634_) == 0)
{
lean_object* v_a_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1653_; 
v_a_1635_ = lean_ctor_get(v___x_1634_, 0);
v_isSharedCheck_1653_ = !lean_is_exclusive(v___x_1634_);
if (v_isSharedCheck_1653_ == 0)
{
v___x_1637_ = v___x_1634_;
v_isShared_1638_ = v_isSharedCheck_1653_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_a_1635_);
lean_dec(v___x_1634_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1653_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
switch(lean_obj_tag(v_a_1635_))
{
case 0:
{
lean_object* v_e_1639_; lean_object* v___x_1641_; 
lean_dec_ref(v_e_1629_);
lean_dec_ref(v_post_1628_);
lean_dec_ref(v_pre_1627_);
v_e_1639_ = lean_ctor_get(v_a_1635_, 0);
lean_inc_ref(v_e_1639_);
lean_dec_ref(v_a_1635_);
if (v_isShared_1638_ == 0)
{
lean_ctor_set(v___x_1637_, 0, v_e_1639_);
v___x_1641_ = v___x_1637_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v_e_1639_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
return v___x_1641_;
}
}
case 1:
{
lean_object* v_e_1643_; lean_object* v___x_1644_; 
lean_del_object(v___x_1637_);
lean_dec_ref(v_e_1629_);
v_e_1643_ = lean_ctor_get(v_a_1635_, 0);
lean_inc_ref(v_e_1643_);
lean_dec_ref(v_a_1635_);
v___x_1644_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1627_, v_post_1628_, v_e_1643_, v_a_1630_, v___y_1631_, v___y_1632_);
return v___x_1644_;
}
default: 
{
lean_object* v_e_x3f_1645_; 
lean_dec_ref(v_post_1628_);
lean_dec_ref(v_pre_1627_);
v_e_x3f_1645_ = lean_ctor_get(v_a_1635_, 0);
lean_inc(v_e_x3f_1645_);
lean_dec_ref(v_a_1635_);
if (lean_obj_tag(v_e_x3f_1645_) == 0)
{
lean_object* v___x_1647_; 
if (v_isShared_1638_ == 0)
{
lean_ctor_set(v___x_1637_, 0, v_e_1629_);
v___x_1647_ = v___x_1637_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v_e_1629_);
v___x_1647_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
return v___x_1647_;
}
}
else
{
lean_object* v_val_1649_; lean_object* v___x_1651_; 
lean_dec_ref(v_e_1629_);
v_val_1649_ = lean_ctor_get(v_e_x3f_1645_, 0);
lean_inc(v_val_1649_);
lean_dec_ref(v_e_x3f_1645_);
if (v_isShared_1638_ == 0)
{
lean_ctor_set(v___x_1637_, 0, v_val_1649_);
v___x_1651_ = v___x_1637_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v_val_1649_);
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
lean_object* v_a_1654_; lean_object* v___x_1656_; uint8_t v_isShared_1657_; uint8_t v_isSharedCheck_1661_; 
lean_dec_ref(v_e_1629_);
lean_dec_ref(v_post_1628_);
lean_dec_ref(v_pre_1627_);
v_a_1654_ = lean_ctor_get(v___x_1634_, 0);
v_isSharedCheck_1661_ = !lean_is_exclusive(v___x_1634_);
if (v_isSharedCheck_1661_ == 0)
{
v___x_1656_ = v___x_1634_;
v_isShared_1657_ = v_isSharedCheck_1661_;
goto v_resetjp_1655_;
}
else
{
lean_inc(v_a_1654_);
lean_dec(v___x_1634_);
v___x_1656_ = lean_box(0);
v_isShared_1657_ = v_isSharedCheck_1661_;
goto v_resetjp_1655_;
}
v_resetjp_1655_:
{
lean_object* v___x_1659_; 
if (v_isShared_1657_ == 0)
{
v___x_1659_ = v___x_1656_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v_a_1654_);
v___x_1659_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
return v___x_1659_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_1662_, lean_object* v_post_1663_, lean_object* v_e_1664_, lean_object* v_a_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_){
_start:
{
lean_object* v_res_1669_; 
v_res_1669_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1662_, v_post_1663_, v_e_1664_, v_a_1665_, v___y_1666_, v___y_1667_);
lean_dec(v___y_1667_);
lean_dec_ref(v___y_1666_);
lean_dec(v_a_1665_);
return v_res_1669_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_1670_, lean_object* v_post_1671_, lean_object* v_sz_1672_, lean_object* v_i_1673_, lean_object* v_bs_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_){
_start:
{
size_t v_sz_boxed_1679_; size_t v_i_boxed_1680_; lean_object* v_res_1681_; 
v_sz_boxed_1679_ = lean_unbox_usize(v_sz_1672_);
lean_dec(v_sz_1672_);
v_i_boxed_1680_ = lean_unbox_usize(v_i_1673_);
lean_dec(v_i_1673_);
v_res_1681_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1(v_pre_1670_, v_post_1671_, v_sz_boxed_1679_, v_i_boxed_1680_, v_bs_1674_, v___y_1675_, v___y_1676_, v___y_1677_);
lean_dec(v___y_1677_);
lean_dec_ref(v___y_1676_);
lean_dec(v___y_1675_);
return v_res_1681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__4___boxed(lean_object* v_pre_1682_, lean_object* v_post_1683_, lean_object* v_x_1684_, lean_object* v_x_1685_, lean_object* v_x_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_){
_start:
{
lean_object* v_res_1691_; 
v_res_1691_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__4(v_pre_1682_, v_post_1683_, v_x_1684_, v_x_1685_, v_x_1686_, v___y_1687_, v___y_1688_, v___y_1689_);
lean_dec(v___y_1689_);
lean_dec_ref(v___y_1688_);
lean_dec(v___y_1687_);
return v_res_1691_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___boxed(lean_object* v_pre_1692_, lean_object* v_post_1693_, lean_object* v_e_1694_, lean_object* v_a_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_){
_start:
{
lean_object* v_res_1699_; 
v_res_1699_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1692_, v_post_1693_, v_e_1694_, v_a_1695_, v___y_1696_, v___y_1697_);
lean_dec(v___y_1697_);
lean_dec_ref(v___y_1696_);
lean_dec(v_a_1695_);
return v_res_1699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___lam__0(lean_object* v_00_u03b1_1700_, lean_object* v_x_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_){
_start:
{
lean_object* v___x_1705_; lean_object* v___x_1706_; 
v___x_1705_ = lean_apply_1(v_x_1701_, lean_box(0));
v___x_1706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1706_, 0, v___x_1705_);
return v___x_1706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___lam__0___boxed(lean_object* v_00_u03b1_1707_, lean_object* v_x_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_){
_start:
{
lean_object* v_res_1712_; 
v_res_1712_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___lam__0(v_00_u03b1_1707_, v_x_1708_, v___y_1709_, v___y_1710_);
lean_dec(v___y_1710_);
lean_dec_ref(v___y_1709_);
return v_res_1712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(lean_object* v_input_1713_, lean_object* v_pre_1714_, lean_object* v_post_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_){
_start:
{
lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v_a_1721_; lean_object* v___x_1722_; 
v___x_1719_ = lean_obj_once(&l_Lean_Core_transform___redArg___closed__2, &l_Lean_Core_transform___redArg___closed__2_once, _init_l_Lean_Core_transform___redArg___closed__2);
v___x_1720_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___lam__0(lean_box(0), v___x_1719_, v___y_1716_, v___y_1717_);
v_a_1721_ = lean_ctor_get(v___x_1720_, 0);
lean_inc(v_a_1721_);
lean_dec_ref(v___x_1720_);
v___x_1722_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1714_, v_post_1715_, v_input_1713_, v_a_1721_, v___y_1716_, v___y_1717_);
if (lean_obj_tag(v___x_1722_) == 0)
{
lean_object* v_a_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1732_; 
v_a_1723_ = lean_ctor_get(v___x_1722_, 0);
lean_inc(v_a_1723_);
lean_dec_ref(v___x_1722_);
v___x_1724_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1724_, 0, lean_box(0));
lean_closure_set(v___x_1724_, 1, lean_box(0));
lean_closure_set(v___x_1724_, 2, v_a_1721_);
v___x_1725_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___lam__0(lean_box(0), v___x_1724_, v___y_1716_, v___y_1717_);
v_isSharedCheck_1732_ = !lean_is_exclusive(v___x_1725_);
if (v_isSharedCheck_1732_ == 0)
{
lean_object* v_unused_1733_; 
v_unused_1733_ = lean_ctor_get(v___x_1725_, 0);
lean_dec(v_unused_1733_);
v___x_1727_ = v___x_1725_;
v_isShared_1728_ = v_isSharedCheck_1732_;
goto v_resetjp_1726_;
}
else
{
lean_dec(v___x_1725_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1732_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v___x_1730_; 
if (v_isShared_1728_ == 0)
{
lean_ctor_set(v___x_1727_, 0, v_a_1723_);
v___x_1730_ = v___x_1727_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v_a_1723_);
v___x_1730_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
return v___x_1730_;
}
}
}
else
{
lean_dec(v_a_1721_);
return v___x_1722_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___boxed(lean_object* v_input_1734_, lean_object* v_pre_1735_, lean_object* v_post_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_){
_start:
{
lean_object* v_res_1740_; 
v_res_1740_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_input_1734_, v_pre_1735_, v_post_1736_, v___y_1737_, v___y_1738_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
return v_res_1740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_betaReduce(lean_object* v_e_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_){
_start:
{
lean_object* v___f_1747_; lean_object* v___f_1748_; lean_object* v___x_1749_; 
v___f_1747_ = ((lean_object*)(l_Lean_Core_betaReduce___closed__0));
v___f_1748_ = ((lean_object*)(l_Lean_Core_betaReduce___closed__1));
v___x_1749_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_1743_, v___f_1747_, v___f_1748_, v_a_1744_, v_a_1745_);
return v___x_1749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_betaReduce___boxed(lean_object* v_e_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_){
_start:
{
lean_object* v_res_1754_; 
v_res_1754_ = l_Lean_Core_betaReduce(v_e_1750_, v_a_1751_, v_a_1752_);
lean_dec(v_a_1752_);
lean_dec_ref(v_a_1751_);
return v_res_1754_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_1755_, lean_object* v_m_1756_, lean_object* v_a_1757_){
_start:
{
lean_object* v___x_1758_; 
v___x_1758_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg(v_m_1756_, v_a_1757_);
return v___x_1758_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_1759_, lean_object* v_m_1760_, lean_object* v_a_1761_){
_start:
{
lean_object* v_res_1762_; 
v_res_1762_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3(v_00_u03b2_1759_, v_m_1760_, v_a_1761_);
lean_dec_ref(v_a_1761_);
lean_dec_ref(v_m_1760_);
return v_res_1762_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_1763_, lean_object* v_ref_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_){
_start:
{
lean_object* v___x_1768_; 
v___x_1768_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_1764_);
return v___x_1768_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1769_, lean_object* v_ref_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_){
_start:
{
lean_object* v_res_1774_; 
v_res_1774_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_1769_, v_ref_1770_, v___y_1771_, v___y_1772_);
lean_dec(v___y_1772_);
lean_dec_ref(v___y_1771_);
return v_res_1774_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8(lean_object* v_00_u03b1_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_){
_start:
{
lean_object* v___x_1779_; 
v___x_1779_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___redArg();
return v___x_1779_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___boxed(lean_object* v_00_u03b1_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_){
_start:
{
lean_object* v_res_1784_; 
v_res_1784_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8(v_00_u03b1_1780_, v___y_1781_, v___y_1782_);
lean_dec(v___y_1782_);
lean_dec_ref(v___y_1781_);
return v_res_1784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5(lean_object* v_00_u03b1_1785_, lean_object* v_x_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_){
_start:
{
lean_object* v___x_1791_; 
v___x_1791_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___redArg(v_x_1786_, v___y_1787_, v___y_1788_, v___y_1789_);
return v___x_1791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b1_1792_, lean_object* v_x_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_){
_start:
{
lean_object* v_res_1798_; 
v_res_1798_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5(v_00_u03b1_1792_, v_x_1793_, v___y_1794_, v___y_1795_, v___y_1796_);
lean_dec(v___y_1796_);
lean_dec_ref(v___y_1795_);
lean_dec(v___y_1794_);
return v_res_1798_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6(lean_object* v_00_u03b2_1799_, lean_object* v_m_1800_, lean_object* v_a_1801_, lean_object* v_b_1802_){
_start:
{
lean_object* v___x_1803_; 
v___x_1803_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6___redArg(v_m_1800_, v_a_1801_, v_b_1802_);
return v___x_1803_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4(lean_object* v_00_u03b2_1804_, lean_object* v_a_1805_, lean_object* v_x_1806_){
_start:
{
lean_object* v___x_1807_; 
v___x_1807_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___redArg(v_a_1805_, v_x_1806_);
return v___x_1807_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___boxed(lean_object* v_00_u03b2_1808_, lean_object* v_a_1809_, lean_object* v_x_1810_){
_start:
{
lean_object* v_res_1811_; 
v_res_1811_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4(v_00_u03b2_1808_, v_a_1809_, v_x_1810_);
lean_dec(v_x_1810_);
lean_dec_ref(v_a_1809_);
return v_res_1811_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10(lean_object* v_00_u03b2_1812_, lean_object* v_a_1813_, lean_object* v_x_1814_){
_start:
{
uint8_t v___x_1815_; 
v___x_1815_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___redArg(v_a_1813_, v_x_1814_);
return v___x_1815_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___boxed(lean_object* v_00_u03b2_1816_, lean_object* v_a_1817_, lean_object* v_x_1818_){
_start:
{
uint8_t v_res_1819_; lean_object* v_r_1820_; 
v_res_1819_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10(v_00_u03b2_1816_, v_a_1817_, v_x_1818_);
lean_dec(v_x_1818_);
lean_dec_ref(v_a_1817_);
v_r_1820_ = lean_box(v_res_1819_);
return v_r_1820_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11(lean_object* v_00_u03b2_1821_, lean_object* v_data_1822_){
_start:
{
lean_object* v___x_1823_; 
v___x_1823_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11___redArg(v_data_1822_);
return v___x_1823_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__12(lean_object* v_00_u03b2_1824_, lean_object* v_a_1825_, lean_object* v_b_1826_, lean_object* v_x_1827_){
_start:
{
lean_object* v___x_1828_; 
v___x_1828_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__12___redArg(v_a_1825_, v_b_1826_, v_x_1827_);
return v___x_1828_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12(lean_object* v_00_u03b2_1829_, lean_object* v_i_1830_, lean_object* v_source_1831_, lean_object* v_target_1832_){
_start:
{
lean_object* v___x_1833_; 
v___x_1833_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v_i_1830_, v_source_1831_, v_target_1832_);
return v___x_1833_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13(lean_object* v_00_u03b2_1834_, lean_object* v_x_1835_, lean_object* v_x_1836_){
_start:
{
lean_object* v___x_1837_; 
v___x_1837_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_x_1835_, v_x_1836_);
return v___x_1837_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__0(lean_object* v_toApplicative_1838_, lean_object* v_a_1839_){
_start:
{
lean_object* v_toPure_1840_; lean_object* v___x_1841_; 
v_toPure_1840_ = lean_ctor_get(v_toApplicative_1838_, 1);
lean_inc(v_toPure_1840_);
lean_dec_ref(v_toApplicative_1838_);
v___x_1841_ = lean_apply_2(v_toPure_1840_, lean_box(0), v_a_1839_);
return v___x_1841_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__13(lean_object* v___x_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_){
_start:
{
lean_object* v___x_1848_; 
v___x_1848_ = l_Lean_Core_checkSystem(v___x_1842_, v___y_1845_, v___y_1846_);
return v___x_1848_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__13___boxed(lean_object* v___x_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_){
_start:
{
lean_object* v_res_1855_; 
v_res_1855_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__13(v___x_1849_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_);
lean_dec(v___y_1853_);
lean_dec_ref(v___y_1852_);
lean_dec(v___y_1851_);
lean_dec_ref(v___y_1850_);
return v_res_1855_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14(lean_object* v_inst_1858_, lean_object* v_x_1859_, lean_object* v___x_1860_, lean_object* v___x_1861_, lean_object* v_inst_1862_, lean_object* v___f_1863_, lean_object* v___x_1864_, lean_object* v___x_1865_, lean_object* v_a_1866_, lean_object* v_toBind_1867_, lean_object* v___f_1868_, lean_object* v_toApplicative_1869_, lean_object* v_a_1870_){
_start:
{
if (lean_obj_tag(v_a_1870_) == 0)
{
lean_object* v___f_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_3801__overap_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; 
lean_dec_ref(v_toApplicative_1869_);
v___f_1871_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14___closed__0));
v___x_1872_ = lean_apply_2(v_inst_1858_, lean_box(0), v___f_1871_);
lean_inc_ref(v___x_1861_);
lean_inc_ref(v___x_1860_);
v___x_1873_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonadLift___aux__1___boxed), 10, 9);
lean_closure_set(v___x_1873_, 0, lean_box(0));
lean_closure_set(v___x_1873_, 1, lean_box(0));
lean_closure_set(v___x_1873_, 2, lean_box(0));
lean_closure_set(v___x_1873_, 3, lean_box(0));
lean_closure_set(v___x_1873_, 4, v_x_1859_);
lean_closure_set(v___x_1873_, 5, v___x_1860_);
lean_closure_set(v___x_1873_, 6, v___x_1861_);
lean_closure_set(v___x_1873_, 7, lean_box(0));
lean_closure_set(v___x_1873_, 8, v___x_1872_);
v___x_1874_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonad___aux__13___boxed), 13, 12);
lean_closure_set(v___x_1874_, 0, lean_box(0));
lean_closure_set(v___x_1874_, 1, lean_box(0));
lean_closure_set(v___x_1874_, 2, lean_box(0));
lean_closure_set(v___x_1874_, 3, lean_box(0));
lean_closure_set(v___x_1874_, 4, v_x_1859_);
lean_closure_set(v___x_1874_, 5, v___x_1860_);
lean_closure_set(v___x_1874_, 6, v___x_1861_);
lean_closure_set(v___x_1874_, 7, v_inst_1862_);
lean_closure_set(v___x_1874_, 8, lean_box(0));
lean_closure_set(v___x_1874_, 9, lean_box(0));
lean_closure_set(v___x_1874_, 10, v___x_1873_);
lean_closure_set(v___x_1874_, 11, v___f_1863_);
v___x_3801__overap_1875_ = l_Lean_Meta_withIncRecDepth___redArg(v___x_1864_, v___x_1865_, v___x_1874_);
lean_inc(v_a_1866_);
v___x_1876_ = lean_apply_1(v___x_3801__overap_1875_, v_a_1866_);
v___x_1877_ = lean_apply_4(v_toBind_1867_, lean_box(0), lean_box(0), v___x_1876_, v___f_1868_);
return v___x_1877_;
}
else
{
lean_object* v_val_1878_; lean_object* v_toPure_1879_; lean_object* v___x_1880_; 
lean_dec(v___f_1868_);
lean_dec(v_toBind_1867_);
lean_dec_ref(v___x_1865_);
lean_dec_ref(v___x_1864_);
lean_dec(v___f_1863_);
lean_dec_ref(v_inst_1862_);
lean_dec_ref(v___x_1861_);
lean_dec_ref(v___x_1860_);
lean_dec(v_inst_1858_);
v_val_1878_ = lean_ctor_get(v_a_1870_, 0);
lean_inc(v_val_1878_);
lean_dec_ref(v_a_1870_);
v_toPure_1879_ = lean_ctor_get(v_toApplicative_1869_, 1);
lean_inc(v_toPure_1879_);
lean_dec_ref(v_toApplicative_1869_);
v___x_1880_ = lean_apply_2(v_toPure_1879_, lean_box(0), v_val_1878_);
return v___x_1880_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14___boxed(lean_object* v_inst_1881_, lean_object* v_x_1882_, lean_object* v___x_1883_, lean_object* v___x_1884_, lean_object* v_inst_1885_, lean_object* v___f_1886_, lean_object* v___x_1887_, lean_object* v___x_1888_, lean_object* v_a_1889_, lean_object* v_toBind_1890_, lean_object* v___f_1891_, lean_object* v_toApplicative_1892_, lean_object* v_a_1893_){
_start:
{
lean_object* v_res_1894_; 
v_res_1894_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14(v_inst_1881_, v_x_1882_, v___x_1883_, v___x_1884_, v_inst_1885_, v___f_1886_, v___x_1887_, v___x_1888_, v_a_1889_, v_toBind_1890_, v___f_1891_, v_toApplicative_1892_, v_a_1893_);
lean_dec(v_a_1889_);
return v_res_1894_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__1(lean_object* v___x_1895_, lean_object* v___x_1896_, lean_object* v_declName_1897_, lean_object* v_a_1898_, lean_object* v___f_1899_, uint8_t v_nondep_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_){
_start:
{
uint8_t v___x_1903_; lean_object* v___x_3820__overap_1904_; lean_object* v___x_1905_; 
v___x_1903_ = 0;
v___x_3820__overap_1904_ = l_Lean_Meta_withLetDecl___redArg(v___x_1895_, v___x_1896_, v_declName_1897_, v_a_1898_, v_a_1902_, v___f_1899_, v_nondep_1900_, v___x_1903_);
lean_inc(v_a_1901_);
v___x_1905_ = lean_apply_1(v___x_3820__overap_1904_, v_a_1901_);
return v___x_1905_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__1___boxed(lean_object* v___x_1906_, lean_object* v___x_1907_, lean_object* v_declName_1908_, lean_object* v_a_1909_, lean_object* v___f_1910_, lean_object* v_nondep_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_){
_start:
{
uint8_t v_nondep_3999__boxed_1914_; lean_object* v_res_1915_; 
v_nondep_3999__boxed_1914_ = lean_unbox(v_nondep_1911_);
v_res_1915_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__1(v___x_1906_, v___x_1907_, v_declName_1908_, v_a_1909_, v___f_1910_, v_nondep_3999__boxed_1914_, v_a_1912_, v_a_1913_);
lean_dec(v_a_1912_);
return v_res_1915_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__4(lean_object* v_fvars_1916_, uint8_t v_usedLetOnly_1917_, lean_object* v_inst_1918_, lean_object* v_toBind_1919_, lean_object* v___f_1920_, lean_object* v_a_1921_){
_start:
{
uint8_t v___x_1922_; uint8_t v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; 
v___x_1922_ = 0;
v___x_1923_ = 1;
v___x_1924_ = lean_box(v_usedLetOnly_1917_);
v___x_1925_ = lean_box(v___x_1922_);
v___x_1926_ = lean_box(v___x_1923_);
v___x_1927_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLetFVars___boxed), 10, 5);
lean_closure_set(v___x_1927_, 0, v_fvars_1916_);
lean_closure_set(v___x_1927_, 1, v_a_1921_);
lean_closure_set(v___x_1927_, 2, v___x_1924_);
lean_closure_set(v___x_1927_, 3, v___x_1925_);
lean_closure_set(v___x_1927_, 4, v___x_1926_);
v___x_1928_ = lean_apply_2(v_inst_1918_, lean_box(0), v___x_1927_);
v___x_1929_ = lean_apply_4(v_toBind_1919_, lean_box(0), lean_box(0), v___x_1928_, v___f_1920_);
return v___x_1929_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__4___boxed(lean_object* v_fvars_1930_, lean_object* v_usedLetOnly_1931_, lean_object* v_inst_1932_, lean_object* v_toBind_1933_, lean_object* v___f_1934_, lean_object* v_a_1935_){
_start:
{
uint8_t v_usedLetOnly_boxed_1936_; lean_object* v_res_1937_; 
v_usedLetOnly_boxed_1936_ = lean_unbox(v_usedLetOnly_1931_);
v_res_1937_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__4(v_fvars_1930_, v_usedLetOnly_boxed_1936_, v_inst_1932_, v_toBind_1933_, v___f_1934_, v_a_1935_);
return v_res_1937_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__3(lean_object* v_fvars_1938_, uint8_t v_usedLetOnly_1939_, lean_object* v_inst_1940_, lean_object* v_toBind_1941_, lean_object* v___f_1942_, lean_object* v_a_1943_){
_start:
{
uint8_t v___x_1944_; uint8_t v___x_1945_; uint8_t v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; 
v___x_1944_ = 0;
v___x_1945_ = 1;
v___x_1946_ = 1;
v___x_1947_ = lean_box(v___x_1944_);
v___x_1948_ = lean_box(v_usedLetOnly_1939_);
v___x_1949_ = lean_box(v___x_1944_);
v___x_1950_ = lean_box(v___x_1945_);
v___x_1951_ = lean_box(v___x_1946_);
v___x_1952_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(v___x_1952_, 0, v_fvars_1938_);
lean_closure_set(v___x_1952_, 1, v_a_1943_);
lean_closure_set(v___x_1952_, 2, v___x_1947_);
lean_closure_set(v___x_1952_, 3, v___x_1948_);
lean_closure_set(v___x_1952_, 4, v___x_1949_);
lean_closure_set(v___x_1952_, 5, v___x_1950_);
lean_closure_set(v___x_1952_, 6, v___x_1951_);
v___x_1953_ = lean_apply_2(v_inst_1940_, lean_box(0), v___x_1952_);
v___x_1954_ = lean_apply_4(v_toBind_1941_, lean_box(0), lean_box(0), v___x_1953_, v___f_1942_);
return v___x_1954_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__3___boxed(lean_object* v_fvars_1955_, lean_object* v_usedLetOnly_1956_, lean_object* v_inst_1957_, lean_object* v_toBind_1958_, lean_object* v___f_1959_, lean_object* v_a_1960_){
_start:
{
uint8_t v_usedLetOnly_boxed_1961_; lean_object* v_res_1962_; 
v_usedLetOnly_boxed_1961_ = lean_unbox(v_usedLetOnly_1956_);
v_res_1962_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__3(v_fvars_1955_, v_usedLetOnly_boxed_1961_, v_inst_1957_, v_toBind_1958_, v___f_1959_, v_a_1960_);
return v_res_1962_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1(lean_object* v___x_1963_, lean_object* v___x_1964_, lean_object* v_binderName_1965_, uint8_t v_binderInfo_1966_, lean_object* v___f_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_){
_start:
{
uint8_t v___x_1970_; lean_object* v___x_3878__overap_1971_; lean_object* v___x_1972_; 
v___x_1970_ = 0;
v___x_3878__overap_1971_ = l_Lean_Meta_withLocalDecl___redArg(v___x_1963_, v___x_1964_, v_binderName_1965_, v_binderInfo_1966_, v_a_1969_, v___f_1967_, v___x_1970_);
lean_inc(v_a_1968_);
v___x_1972_ = lean_apply_1(v___x_3878__overap_1971_, v_a_1968_);
return v___x_1972_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1___boxed(lean_object* v___x_1973_, lean_object* v___x_1974_, lean_object* v_binderName_1975_, lean_object* v_binderInfo_1976_, lean_object* v___f_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_){
_start:
{
uint8_t v_binderInfo_4067__boxed_1980_; lean_object* v_res_1981_; 
v_binderInfo_4067__boxed_1980_ = lean_unbox(v_binderInfo_1976_);
v_res_1981_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1(v___x_1973_, v___x_1974_, v_binderName_1975_, v_binderInfo_4067__boxed_1980_, v___f_1977_, v_a_1978_, v_a_1979_);
lean_dec(v_a_1978_);
return v_res_1981_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__3(lean_object* v_fvars_1982_, uint8_t v_usedLetOnly_1983_, lean_object* v_inst_1984_, lean_object* v_toBind_1985_, lean_object* v___f_1986_, lean_object* v_a_1987_){
_start:
{
uint8_t v___x_1988_; uint8_t v___x_1989_; uint8_t v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; 
v___x_1988_ = 0;
v___x_1989_ = 1;
v___x_1990_ = 1;
v___x_1991_ = lean_box(v___x_1988_);
v___x_1992_ = lean_box(v_usedLetOnly_1983_);
v___x_1993_ = lean_box(v___x_1989_);
v___x_1994_ = lean_box(v___x_1990_);
v___x_1995_ = lean_alloc_closure((void*)(l_Lean_Meta_mkForallFVars___boxed), 11, 6);
lean_closure_set(v___x_1995_, 0, v_fvars_1982_);
lean_closure_set(v___x_1995_, 1, v_a_1987_);
lean_closure_set(v___x_1995_, 2, v___x_1991_);
lean_closure_set(v___x_1995_, 3, v___x_1992_);
lean_closure_set(v___x_1995_, 4, v___x_1993_);
lean_closure_set(v___x_1995_, 5, v___x_1994_);
v___x_1996_ = lean_apply_2(v_inst_1984_, lean_box(0), v___x_1995_);
v___x_1997_ = lean_apply_4(v_toBind_1985_, lean_box(0), lean_box(0), v___x_1996_, v___f_1986_);
return v___x_1997_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__3___boxed(lean_object* v_fvars_1998_, lean_object* v_usedLetOnly_1999_, lean_object* v_inst_2000_, lean_object* v_toBind_2001_, lean_object* v___f_2002_, lean_object* v_a_2003_){
_start:
{
uint8_t v_usedLetOnly_boxed_2004_; lean_object* v_res_2005_; 
v_usedLetOnly_boxed_2004_ = lean_unbox(v_usedLetOnly_1999_);
v_res_2005_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__3(v_fvars_1998_, v_usedLetOnly_boxed_2004_, v_inst_2000_, v_toBind_2001_, v___f_2002_, v_a_2003_);
return v_res_2005_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__7(lean_object* v___f_2006_, lean_object* v___y_2007_, lean_object* v_a_2008_){
_start:
{
lean_object* v___x_2009_; 
lean_inc(v___y_2007_);
v___x_2009_ = lean_apply_2(v___f_2006_, v_a_2008_, v___y_2007_);
return v___x_2009_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__7___boxed(lean_object* v___f_2010_, lean_object* v___y_2011_, lean_object* v_a_2012_){
_start:
{
lean_object* v_res_2013_; 
v_res_2013_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__7(v___f_2010_, v___y_2011_, v_a_2012_);
lean_dec(v___y_2011_);
return v_res_2013_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1(lean_object* v_toApplicative_2014_, lean_object* v_acc_2015_, lean_object* v_next_2016_, lean_object* v_a_2017_){
_start:
{
lean_object* v_toPure_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; 
v_toPure_2018_ = lean_ctor_get(v_toApplicative_2014_, 1);
lean_inc(v_toPure_2018_);
lean_dec_ref(v_toApplicative_2014_);
v___x_2019_ = lean_array_fset(v_acc_2015_, v_next_2016_, v_a_2017_);
v___x_2020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2020_, 0, v___x_2019_);
v___x_2021_ = lean_apply_2(v_toPure_2018_, lean_box(0), v___x_2020_);
return v___x_2021_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1___boxed(lean_object* v_toApplicative_2022_, lean_object* v_acc_2023_, lean_object* v_next_2024_, lean_object* v_a_2025_){
_start:
{
lean_object* v_res_2026_; 
v_res_2026_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1(v_toApplicative_2022_, v_acc_2023_, v_next_2024_, v_a_2025_);
lean_dec(v_next_2024_);
return v_res_2026_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__2(lean_object* v_toApplicative_2027_, lean_object* v_next_2028_, lean_object* v_G_2029_, lean_object* v___y_2030_, lean_object* v_a_2031_){
_start:
{
if (lean_obj_tag(v_a_2031_) == 0)
{
lean_object* v_a_2032_; lean_object* v_toPure_2033_; lean_object* v___x_2034_; 
lean_dec(v_G_2029_);
v_a_2032_ = lean_ctor_get(v_a_2031_, 0);
lean_inc(v_a_2032_);
lean_dec_ref(v_a_2031_);
v_toPure_2033_ = lean_ctor_get(v_toApplicative_2027_, 1);
lean_inc(v_toPure_2033_);
lean_dec_ref(v_toApplicative_2027_);
v___x_2034_ = lean_apply_2(v_toPure_2033_, lean_box(0), v_a_2032_);
return v___x_2034_;
}
else
{
lean_object* v_a_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; 
lean_dec_ref(v_toApplicative_2027_);
v_a_2035_ = lean_ctor_get(v_a_2031_, 0);
lean_inc(v_a_2035_);
lean_dec_ref(v_a_2031_);
v___x_2036_ = lean_unsigned_to_nat(1u);
v___x_2037_ = lean_nat_add(v_next_2028_, v___x_2036_);
lean_inc(v___y_2030_);
v___x_2038_ = lean_apply_5(v_G_2029_, v___x_2037_, v_a_2035_, lean_box(0), lean_box(0), v___y_2030_);
return v___x_2038_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__2___boxed(lean_object* v_toApplicative_2039_, lean_object* v_next_2040_, lean_object* v_G_2041_, lean_object* v___y_2042_, lean_object* v_a_2043_){
_start:
{
lean_object* v_res_2044_; 
v_res_2044_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__2(v_toApplicative_2039_, v_next_2040_, v_G_2041_, v___y_2042_, v_a_2043_);
lean_dec(v___y_2042_);
lean_dec(v_next_2040_);
return v_res_2044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5(lean_object* v_f_2045_, lean_object* v_inst_2046_, lean_object* v_inst_2047_, lean_object* v_inst_2048_, lean_object* v_pre_2049_, lean_object* v_post_2050_, uint8_t v_usedLetOnly_2051_, uint8_t v_skipConstInApp_2052_, uint8_t v_skipInstances_2053_, lean_object* v_x_2054_, lean_object* v_x_2055_, lean_object* v___y_2056_, lean_object* v_a_2057_){
_start:
{
lean_object* v___x_2058_; lean_object* v___x_2059_; 
v___x_2058_ = l_Lean_mkAppN(v_f_2045_, v_a_2057_);
v___x_2059_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2046_, v_inst_2047_, v_inst_2048_, v_pre_2049_, v_post_2050_, v_usedLetOnly_2051_, v_skipConstInApp_2052_, v_skipInstances_2053_, v_x_2054_, v_x_2055_, v___x_2058_, v___y_2056_);
return v___x_2059_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5___boxed(lean_object* v_f_2060_, lean_object* v_inst_2061_, lean_object* v_inst_2062_, lean_object* v_inst_2063_, lean_object* v_pre_2064_, lean_object* v_post_2065_, lean_object* v_usedLetOnly_2066_, lean_object* v_skipConstInApp_2067_, lean_object* v_skipInstances_2068_, lean_object* v_x_2069_, lean_object* v_x_2070_, lean_object* v___y_2071_, lean_object* v_a_2072_){
_start:
{
uint8_t v_usedLetOnly_boxed_2073_; uint8_t v_skipConstInApp_boxed_2074_; uint8_t v_skipInstances_boxed_2075_; lean_object* v_res_2076_; 
v_usedLetOnly_boxed_2073_ = lean_unbox(v_usedLetOnly_2066_);
v_skipConstInApp_boxed_2074_ = lean_unbox(v_skipConstInApp_2067_);
v_skipInstances_boxed_2075_ = lean_unbox(v_skipInstances_2068_);
v_res_2076_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5(v_f_2060_, v_inst_2061_, v_inst_2062_, v_inst_2063_, v_pre_2064_, v_post_2065_, v_usedLetOnly_boxed_2073_, v_skipConstInApp_boxed_2074_, v_skipInstances_boxed_2075_, v_x_2069_, v_x_2070_, v___y_2071_, v_a_2072_);
lean_dec_ref(v_a_2072_);
lean_dec(v___y_2071_);
return v_res_2076_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___boxed(lean_object* v_inst_2077_, lean_object* v_inst_2078_, lean_object* v_inst_2079_, lean_object* v_pre_2080_, lean_object* v_post_2081_, lean_object* v_usedLetOnly_2082_, lean_object* v_skipConstInApp_2083_, lean_object* v_skipInstances_2084_, lean_object* v_x_2085_, lean_object* v_x_2086_, lean_object* v_e_2087_, lean_object* v_a_2088_){
_start:
{
uint8_t v_usedLetOnly_boxed_2089_; uint8_t v_skipConstInApp_boxed_2090_; uint8_t v_skipInstances_boxed_2091_; lean_object* v_res_2092_; 
v_usedLetOnly_boxed_2089_ = lean_unbox(v_usedLetOnly_2082_);
v_skipConstInApp_boxed_2090_ = lean_unbox(v_skipConstInApp_2083_);
v_skipInstances_boxed_2091_ = lean_unbox(v_skipInstances_2084_);
v_res_2092_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2077_, v_inst_2078_, v_inst_2079_, v_pre_2080_, v_post_2081_, v_usedLetOnly_boxed_2089_, v_skipConstInApp_boxed_2090_, v_skipInstances_boxed_2091_, v_x_2085_, v_x_2086_, v_e_2087_, v_a_2088_);
lean_dec(v_a_2088_);
return v_res_2092_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__4(lean_object* v___x_2093_, lean_object* v_toApplicative_2094_, lean_object* v_toBind_2095_, lean_object* v___f_2096_, lean_object* v_paramInfo_2097_, lean_object* v_inst_2098_, lean_object* v_inst_2099_, lean_object* v_inst_2100_, lean_object* v_pre_2101_, lean_object* v_post_2102_, uint8_t v_usedLetOnly_2103_, uint8_t v_skipConstInApp_2104_, uint8_t v_skipInstances_2105_, lean_object* v_x_2106_, lean_object* v_x_2107_, lean_object* v_next_2108_, lean_object* v_acc_2109_, lean_object* v_h_2110_, lean_object* v_G_2111_, lean_object* v___y_2112_){
_start:
{
uint8_t v___x_2113_; 
v___x_2113_ = lean_nat_dec_lt(v_next_2108_, v___x_2093_);
if (v___x_2113_ == 0)
{
lean_object* v_toPure_2114_; lean_object* v___x_2115_; 
lean_dec(v_G_2111_);
lean_dec(v_next_2108_);
lean_dec(v_x_2107_);
lean_dec(v_post_2102_);
lean_dec(v_pre_2101_);
lean_dec_ref(v_inst_2100_);
lean_dec(v_inst_2099_);
lean_dec_ref(v_inst_2098_);
lean_dec(v___f_2096_);
lean_dec(v_toBind_2095_);
v_toPure_2114_ = lean_ctor_get(v_toApplicative_2094_, 1);
lean_inc(v_toPure_2114_);
lean_dec_ref(v_toApplicative_2094_);
v___x_2115_ = lean_apply_2(v_toPure_2114_, lean_box(0), v_acc_2109_);
return v___x_2115_;
}
else
{
lean_object* v___f_2116_; lean_object* v___y_2118_; lean_object* v___x_2121_; lean_object* v___x_2122_; uint8_t v___x_2123_; 
lean_inc(v___y_2112_);
lean_inc(v_next_2108_);
lean_inc_ref(v_toApplicative_2094_);
v___f_2116_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__2___boxed), 5, 4);
lean_closure_set(v___f_2116_, 0, v_toApplicative_2094_);
lean_closure_set(v___f_2116_, 1, v_next_2108_);
lean_closure_set(v___f_2116_, 2, v_G_2111_);
lean_closure_set(v___f_2116_, 3, v___y_2112_);
v___x_2121_ = lean_array_fget_borrowed(v_acc_2109_, v_next_2108_);
v___x_2122_ = lean_array_get_size(v_paramInfo_2097_);
v___x_2123_ = lean_nat_dec_lt(v_next_2108_, v___x_2122_);
if (v___x_2123_ == 0)
{
lean_object* v___f_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; 
lean_inc(v___x_2121_);
v___f_2124_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2124_, 0, v_toApplicative_2094_);
lean_closure_set(v___f_2124_, 1, v_acc_2109_);
lean_closure_set(v___f_2124_, 2, v_next_2108_);
v___x_2125_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2098_, v_inst_2099_, v_inst_2100_, v_pre_2101_, v_post_2102_, v_usedLetOnly_2103_, v_skipConstInApp_2104_, v_skipInstances_2105_, v_x_2106_, v_x_2107_, v___x_2121_, v___y_2112_);
lean_inc(v_toBind_2095_);
v___x_2126_ = lean_apply_4(v_toBind_2095_, lean_box(0), lean_box(0), v___x_2125_, v___f_2124_);
v___y_2118_ = v___x_2126_;
goto v___jp_2117_;
}
else
{
lean_object* v___x_2127_; uint8_t v_isInstance_2128_; 
v___x_2127_ = lean_array_fget_borrowed(v_paramInfo_2097_, v_next_2108_);
v_isInstance_2128_ = lean_ctor_get_uint8(v___x_2127_, sizeof(void*)*1 + 4);
if (v_isInstance_2128_ == 0)
{
lean_object* v___f_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; 
lean_inc(v___x_2121_);
v___f_2129_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2129_, 0, v_toApplicative_2094_);
lean_closure_set(v___f_2129_, 1, v_acc_2109_);
lean_closure_set(v___f_2129_, 2, v_next_2108_);
v___x_2130_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2098_, v_inst_2099_, v_inst_2100_, v_pre_2101_, v_post_2102_, v_usedLetOnly_2103_, v_skipConstInApp_2104_, v_skipInstances_2105_, v_x_2106_, v_x_2107_, v___x_2121_, v___y_2112_);
lean_inc(v_toBind_2095_);
v___x_2131_ = lean_apply_4(v_toBind_2095_, lean_box(0), lean_box(0), v___x_2130_, v___f_2129_);
v___y_2118_ = v___x_2131_;
goto v___jp_2117_;
}
else
{
lean_object* v_toPure_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; 
lean_dec(v_next_2108_);
lean_dec(v_x_2107_);
lean_dec(v_post_2102_);
lean_dec(v_pre_2101_);
lean_dec_ref(v_inst_2100_);
lean_dec(v_inst_2099_);
lean_dec_ref(v_inst_2098_);
v_toPure_2132_ = lean_ctor_get(v_toApplicative_2094_, 1);
lean_inc(v_toPure_2132_);
lean_dec_ref(v_toApplicative_2094_);
v___x_2133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2133_, 0, v_acc_2109_);
v___x_2134_ = lean_apply_2(v_toPure_2132_, lean_box(0), v___x_2133_);
v___y_2118_ = v___x_2134_;
goto v___jp_2117_;
}
}
v___jp_2117_:
{
lean_object* v___x_2119_; lean_object* v___x_2120_; 
lean_inc(v_toBind_2095_);
v___x_2119_ = lean_apply_4(v_toBind_2095_, lean_box(0), lean_box(0), v___y_2118_, v___f_2096_);
v___x_2120_ = lean_apply_4(v_toBind_2095_, lean_box(0), lean_box(0), v___x_2119_, v___f_2116_);
return v___x_2120_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__4___boxed(lean_object** _args){
lean_object* v___x_2135_ = _args[0];
lean_object* v_toApplicative_2136_ = _args[1];
lean_object* v_toBind_2137_ = _args[2];
lean_object* v___f_2138_ = _args[3];
lean_object* v_paramInfo_2139_ = _args[4];
lean_object* v_inst_2140_ = _args[5];
lean_object* v_inst_2141_ = _args[6];
lean_object* v_inst_2142_ = _args[7];
lean_object* v_pre_2143_ = _args[8];
lean_object* v_post_2144_ = _args[9];
lean_object* v_usedLetOnly_2145_ = _args[10];
lean_object* v_skipConstInApp_2146_ = _args[11];
lean_object* v_skipInstances_2147_ = _args[12];
lean_object* v_x_2148_ = _args[13];
lean_object* v_x_2149_ = _args[14];
lean_object* v_next_2150_ = _args[15];
lean_object* v_acc_2151_ = _args[16];
lean_object* v_h_2152_ = _args[17];
lean_object* v_G_2153_ = _args[18];
lean_object* v___y_2154_ = _args[19];
_start:
{
uint8_t v_usedLetOnly_boxed_2155_; uint8_t v_skipConstInApp_boxed_2156_; uint8_t v_skipInstances_boxed_2157_; lean_object* v_res_2158_; 
v_usedLetOnly_boxed_2155_ = lean_unbox(v_usedLetOnly_2145_);
v_skipConstInApp_boxed_2156_ = lean_unbox(v_skipConstInApp_2146_);
v_skipInstances_boxed_2157_ = lean_unbox(v_skipInstances_2147_);
v_res_2158_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__4(v___x_2135_, v_toApplicative_2136_, v_toBind_2137_, v___f_2138_, v_paramInfo_2139_, v_inst_2140_, v_inst_2141_, v_inst_2142_, v_pre_2143_, v_post_2144_, v_usedLetOnly_boxed_2155_, v_skipConstInApp_boxed_2156_, v_skipInstances_boxed_2157_, v_x_2148_, v_x_2149_, v_next_2150_, v_acc_2151_, v_h_2152_, v_G_2153_, v___y_2154_);
lean_dec(v___y_2154_);
lean_dec_ref(v_paramInfo_2139_);
lean_dec(v___x_2135_);
return v_res_2158_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__3(lean_object* v___x_2159_, lean_object* v_toApplicative_2160_, lean_object* v_toBind_2161_, lean_object* v___f_2162_, lean_object* v_inst_2163_, lean_object* v_inst_2164_, lean_object* v_inst_2165_, lean_object* v_pre_2166_, lean_object* v_post_2167_, uint8_t v_usedLetOnly_2168_, uint8_t v_skipConstInApp_2169_, uint8_t v_skipInstances_2170_, lean_object* v_x_2171_, lean_object* v_x_2172_, lean_object* v_args_2173_, lean_object* v___y_2174_, lean_object* v___f_2175_, lean_object* v_a_2176_){
_start:
{
lean_object* v_paramInfo_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___f_2182_; lean_object* v___x_3638__overap_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; 
v_paramInfo_2177_ = lean_ctor_get(v_a_2176_, 0);
lean_inc_ref(v_paramInfo_2177_);
lean_dec_ref(v_a_2176_);
v___x_2178_ = lean_unsigned_to_nat(0u);
v___x_2179_ = lean_box(v_usedLetOnly_2168_);
v___x_2180_ = lean_box(v_skipConstInApp_2169_);
v___x_2181_ = lean_box(v_skipInstances_2170_);
lean_inc(v_toBind_2161_);
v___f_2182_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__4___boxed), 20, 15);
lean_closure_set(v___f_2182_, 0, v___x_2159_);
lean_closure_set(v___f_2182_, 1, v_toApplicative_2160_);
lean_closure_set(v___f_2182_, 2, v_toBind_2161_);
lean_closure_set(v___f_2182_, 3, v___f_2162_);
lean_closure_set(v___f_2182_, 4, v_paramInfo_2177_);
lean_closure_set(v___f_2182_, 5, v_inst_2163_);
lean_closure_set(v___f_2182_, 6, v_inst_2164_);
lean_closure_set(v___f_2182_, 7, v_inst_2165_);
lean_closure_set(v___f_2182_, 8, v_pre_2166_);
lean_closure_set(v___f_2182_, 9, v_post_2167_);
lean_closure_set(v___f_2182_, 10, v___x_2179_);
lean_closure_set(v___f_2182_, 11, v___x_2180_);
lean_closure_set(v___f_2182_, 12, v___x_2181_);
lean_closure_set(v___f_2182_, 13, v_x_2171_);
lean_closure_set(v___f_2182_, 14, v_x_2172_);
v___x_3638__overap_2183_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_2182_, v___x_2178_, v_args_2173_, lean_box(0));
lean_inc(v___y_2174_);
v___x_2184_ = lean_apply_1(v___x_3638__overap_2183_, v___y_2174_);
v___x_2185_ = lean_apply_4(v_toBind_2161_, lean_box(0), lean_box(0), v___x_2184_, v___f_2175_);
return v___x_2185_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__3___boxed(lean_object** _args){
lean_object* v___x_2186_ = _args[0];
lean_object* v_toApplicative_2187_ = _args[1];
lean_object* v_toBind_2188_ = _args[2];
lean_object* v___f_2189_ = _args[3];
lean_object* v_inst_2190_ = _args[4];
lean_object* v_inst_2191_ = _args[5];
lean_object* v_inst_2192_ = _args[6];
lean_object* v_pre_2193_ = _args[7];
lean_object* v_post_2194_ = _args[8];
lean_object* v_usedLetOnly_2195_ = _args[9];
lean_object* v_skipConstInApp_2196_ = _args[10];
lean_object* v_skipInstances_2197_ = _args[11];
lean_object* v_x_2198_ = _args[12];
lean_object* v_x_2199_ = _args[13];
lean_object* v_args_2200_ = _args[14];
lean_object* v___y_2201_ = _args[15];
lean_object* v___f_2202_ = _args[16];
lean_object* v_a_2203_ = _args[17];
_start:
{
uint8_t v_usedLetOnly_boxed_2204_; uint8_t v_skipConstInApp_boxed_2205_; uint8_t v_skipInstances_boxed_2206_; lean_object* v_res_2207_; 
v_usedLetOnly_boxed_2204_ = lean_unbox(v_usedLetOnly_2195_);
v_skipConstInApp_boxed_2205_ = lean_unbox(v_skipConstInApp_2196_);
v_skipInstances_boxed_2206_ = lean_unbox(v_skipInstances_2197_);
v_res_2207_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__3(v___x_2186_, v_toApplicative_2187_, v_toBind_2188_, v___f_2189_, v_inst_2190_, v_inst_2191_, v_inst_2192_, v_pre_2193_, v_post_2194_, v_usedLetOnly_boxed_2204_, v_skipConstInApp_boxed_2205_, v_skipInstances_boxed_2206_, v_x_2198_, v_x_2199_, v_args_2200_, v___y_2201_, v___f_2202_, v_a_2203_);
lean_dec(v___y_2201_);
return v_res_2207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__6(uint8_t v_skipInstances_2208_, lean_object* v_inst_2209_, lean_object* v_inst_2210_, lean_object* v_inst_2211_, lean_object* v_pre_2212_, lean_object* v_post_2213_, uint8_t v_usedLetOnly_2214_, uint8_t v_skipConstInApp_2215_, lean_object* v_x_2216_, lean_object* v_x_2217_, lean_object* v_args_2218_, lean_object* v___x_2219_, lean_object* v_toBind_2220_, lean_object* v_toApplicative_2221_, lean_object* v___f_2222_, lean_object* v_f_2223_, lean_object* v___y_2224_){
_start:
{
if (v_skipInstances_2208_ == 0)
{
lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___f_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; size_t v_sz_2233_; size_t v___x_2234_; lean_object* v___x_3651__overap_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; 
lean_dec(v___f_2222_);
lean_dec_ref(v_toApplicative_2221_);
v___x_2225_ = lean_box(v_usedLetOnly_2214_);
v___x_2226_ = lean_box(v_skipConstInApp_2215_);
v___x_2227_ = lean_box(v_skipInstances_2208_);
lean_inc_n(v___y_2224_, 2);
lean_inc(v_x_2217_);
lean_inc(v_post_2213_);
lean_inc(v_pre_2212_);
lean_inc_ref(v_inst_2211_);
lean_inc(v_inst_2210_);
lean_inc_ref(v_inst_2209_);
v___f_2228_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5___boxed), 13, 12);
lean_closure_set(v___f_2228_, 0, v_f_2223_);
lean_closure_set(v___f_2228_, 1, v_inst_2209_);
lean_closure_set(v___f_2228_, 2, v_inst_2210_);
lean_closure_set(v___f_2228_, 3, v_inst_2211_);
lean_closure_set(v___f_2228_, 4, v_pre_2212_);
lean_closure_set(v___f_2228_, 5, v_post_2213_);
lean_closure_set(v___f_2228_, 6, v___x_2225_);
lean_closure_set(v___f_2228_, 7, v___x_2226_);
lean_closure_set(v___f_2228_, 8, v___x_2227_);
lean_closure_set(v___f_2228_, 9, v_x_2216_);
lean_closure_set(v___f_2228_, 10, v_x_2217_);
lean_closure_set(v___f_2228_, 11, v___y_2224_);
v___x_2229_ = lean_box(v_usedLetOnly_2214_);
v___x_2230_ = lean_box(v_skipConstInApp_2215_);
v___x_2231_ = lean_box(v_skipInstances_2208_);
v___x_2232_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___boxed), 12, 10);
lean_closure_set(v___x_2232_, 0, v_inst_2209_);
lean_closure_set(v___x_2232_, 1, v_inst_2210_);
lean_closure_set(v___x_2232_, 2, v_inst_2211_);
lean_closure_set(v___x_2232_, 3, v_pre_2212_);
lean_closure_set(v___x_2232_, 4, v_post_2213_);
lean_closure_set(v___x_2232_, 5, v___x_2229_);
lean_closure_set(v___x_2232_, 6, v___x_2230_);
lean_closure_set(v___x_2232_, 7, v___x_2231_);
lean_closure_set(v___x_2232_, 8, v_x_2216_);
lean_closure_set(v___x_2232_, 9, v_x_2217_);
v_sz_2233_ = lean_array_size(v_args_2218_);
v___x_2234_ = ((size_t)0ULL);
v___x_3651__overap_2235_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2219_, v___x_2232_, v_sz_2233_, v___x_2234_, v_args_2218_);
v___x_2236_ = lean_apply_1(v___x_3651__overap_2235_, v___y_2224_);
v___x_2237_ = lean_apply_4(v_toBind_2220_, lean_box(0), lean_box(0), v___x_2236_, v___f_2228_);
return v___x_2237_;
}
else
{
lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___f_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___f_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; 
lean_dec_ref(v___x_2219_);
v___x_2238_ = lean_box(v_usedLetOnly_2214_);
v___x_2239_ = lean_box(v_skipConstInApp_2215_);
v___x_2240_ = lean_box(v_skipInstances_2208_);
lean_inc_n(v___y_2224_, 2);
lean_inc(v_x_2217_);
lean_inc(v_post_2213_);
lean_inc(v_pre_2212_);
lean_inc_ref(v_inst_2211_);
lean_inc_n(v_inst_2210_, 2);
lean_inc_ref(v_inst_2209_);
lean_inc_ref(v_f_2223_);
v___f_2241_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5___boxed), 13, 12);
lean_closure_set(v___f_2241_, 0, v_f_2223_);
lean_closure_set(v___f_2241_, 1, v_inst_2209_);
lean_closure_set(v___f_2241_, 2, v_inst_2210_);
lean_closure_set(v___f_2241_, 3, v_inst_2211_);
lean_closure_set(v___f_2241_, 4, v_pre_2212_);
lean_closure_set(v___f_2241_, 5, v_post_2213_);
lean_closure_set(v___f_2241_, 6, v___x_2238_);
lean_closure_set(v___f_2241_, 7, v___x_2239_);
lean_closure_set(v___f_2241_, 8, v___x_2240_);
lean_closure_set(v___f_2241_, 9, v_x_2216_);
lean_closure_set(v___f_2241_, 10, v_x_2217_);
lean_closure_set(v___f_2241_, 11, v___y_2224_);
v___x_2242_ = lean_array_get_size(v_args_2218_);
v___x_2243_ = lean_box(v_usedLetOnly_2214_);
v___x_2244_ = lean_box(v_skipConstInApp_2215_);
v___x_2245_ = lean_box(v_skipInstances_2208_);
lean_inc(v_toBind_2220_);
v___f_2246_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__3___boxed), 18, 17);
lean_closure_set(v___f_2246_, 0, v___x_2242_);
lean_closure_set(v___f_2246_, 1, v_toApplicative_2221_);
lean_closure_set(v___f_2246_, 2, v_toBind_2220_);
lean_closure_set(v___f_2246_, 3, v___f_2222_);
lean_closure_set(v___f_2246_, 4, v_inst_2209_);
lean_closure_set(v___f_2246_, 5, v_inst_2210_);
lean_closure_set(v___f_2246_, 6, v_inst_2211_);
lean_closure_set(v___f_2246_, 7, v_pre_2212_);
lean_closure_set(v___f_2246_, 8, v_post_2213_);
lean_closure_set(v___f_2246_, 9, v___x_2243_);
lean_closure_set(v___f_2246_, 10, v___x_2244_);
lean_closure_set(v___f_2246_, 11, v___x_2245_);
lean_closure_set(v___f_2246_, 12, v_x_2216_);
lean_closure_set(v___f_2246_, 13, v_x_2217_);
lean_closure_set(v___f_2246_, 14, v_args_2218_);
lean_closure_set(v___f_2246_, 15, v___y_2224_);
lean_closure_set(v___f_2246_, 16, v___f_2241_);
v___x_2247_ = lean_alloc_closure((void*)(l_Lean_Meta_getFunInfoNArgs___boxed), 7, 2);
lean_closure_set(v___x_2247_, 0, v_f_2223_);
lean_closure_set(v___x_2247_, 1, v___x_2242_);
v___x_2248_ = lean_apply_2(v_inst_2210_, lean_box(0), v___x_2247_);
v___x_2249_ = lean_apply_4(v_toBind_2220_, lean_box(0), lean_box(0), v___x_2248_, v___f_2246_);
return v___x_2249_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__6___boxed(lean_object** _args){
lean_object* v_skipInstances_2250_ = _args[0];
lean_object* v_inst_2251_ = _args[1];
lean_object* v_inst_2252_ = _args[2];
lean_object* v_inst_2253_ = _args[3];
lean_object* v_pre_2254_ = _args[4];
lean_object* v_post_2255_ = _args[5];
lean_object* v_usedLetOnly_2256_ = _args[6];
lean_object* v_skipConstInApp_2257_ = _args[7];
lean_object* v_x_2258_ = _args[8];
lean_object* v_x_2259_ = _args[9];
lean_object* v_args_2260_ = _args[10];
lean_object* v___x_2261_ = _args[11];
lean_object* v_toBind_2262_ = _args[12];
lean_object* v_toApplicative_2263_ = _args[13];
lean_object* v___f_2264_ = _args[14];
lean_object* v_f_2265_ = _args[15];
lean_object* v___y_2266_ = _args[16];
_start:
{
uint8_t v_skipInstances_boxed_2267_; uint8_t v_usedLetOnly_boxed_2268_; uint8_t v_skipConstInApp_boxed_2269_; lean_object* v_res_2270_; 
v_skipInstances_boxed_2267_ = lean_unbox(v_skipInstances_2250_);
v_usedLetOnly_boxed_2268_ = lean_unbox(v_usedLetOnly_2256_);
v_skipConstInApp_boxed_2269_ = lean_unbox(v_skipConstInApp_2257_);
v_res_2270_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__6(v_skipInstances_boxed_2267_, v_inst_2251_, v_inst_2252_, v_inst_2253_, v_pre_2254_, v_post_2255_, v_usedLetOnly_boxed_2268_, v_skipConstInApp_boxed_2269_, v_x_2258_, v_x_2259_, v_args_2260_, v___x_2261_, v_toBind_2262_, v_toApplicative_2263_, v___f_2264_, v_f_2265_, v___y_2266_);
lean_dec(v___y_2266_);
return v_res_2270_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__9(uint8_t v_skipInstances_2271_, lean_object* v_inst_2272_, lean_object* v_inst_2273_, lean_object* v_inst_2274_, lean_object* v_pre_2275_, lean_object* v_post_2276_, uint8_t v_usedLetOnly_2277_, uint8_t v_skipConstInApp_2278_, lean_object* v_x_2279_, lean_object* v_x_2280_, lean_object* v___x_2281_, lean_object* v_toBind_2282_, lean_object* v_toApplicative_2283_, lean_object* v___f_2284_, lean_object* v_f_2285_, lean_object* v_args_2286_, lean_object* v___y_2287_){
_start:
{
lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___f_2291_; lean_object* v___f_2292_; 
v___x_2288_ = lean_box(v_skipInstances_2271_);
v___x_2289_ = lean_box(v_usedLetOnly_2277_);
v___x_2290_ = lean_box(v_skipConstInApp_2278_);
lean_inc_ref(v_toApplicative_2283_);
lean_inc(v_toBind_2282_);
lean_inc(v_x_2280_);
lean_inc(v_post_2276_);
lean_inc(v_pre_2275_);
lean_inc_ref(v_inst_2274_);
lean_inc(v_inst_2273_);
lean_inc_ref(v_inst_2272_);
v___f_2291_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__6___boxed), 17, 15);
lean_closure_set(v___f_2291_, 0, v___x_2288_);
lean_closure_set(v___f_2291_, 1, v_inst_2272_);
lean_closure_set(v___f_2291_, 2, v_inst_2273_);
lean_closure_set(v___f_2291_, 3, v_inst_2274_);
lean_closure_set(v___f_2291_, 4, v_pre_2275_);
lean_closure_set(v___f_2291_, 5, v_post_2276_);
lean_closure_set(v___f_2291_, 6, v___x_2289_);
lean_closure_set(v___f_2291_, 7, v___x_2290_);
lean_closure_set(v___f_2291_, 8, v_x_2279_);
lean_closure_set(v___f_2291_, 9, v_x_2280_);
lean_closure_set(v___f_2291_, 10, v_args_2286_);
lean_closure_set(v___f_2291_, 11, v___x_2281_);
lean_closure_set(v___f_2291_, 12, v_toBind_2282_);
lean_closure_set(v___f_2291_, 13, v_toApplicative_2283_);
lean_closure_set(v___f_2291_, 14, v___f_2284_);
lean_inc(v___y_2287_);
v___f_2292_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__7___boxed), 3, 2);
lean_closure_set(v___f_2292_, 0, v___f_2291_);
lean_closure_set(v___f_2292_, 1, v___y_2287_);
if (v_skipConstInApp_2278_ == 0)
{
lean_dec_ref(v_toApplicative_2283_);
goto v___jp_2293_;
}
else
{
uint8_t v___x_2296_; 
v___x_2296_ = l_Lean_Expr_isConst(v_f_2285_);
if (v___x_2296_ == 0)
{
lean_dec_ref(v_toApplicative_2283_);
goto v___jp_2293_;
}
else
{
lean_object* v_toPure_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; 
lean_dec(v_x_2280_);
lean_dec(v_post_2276_);
lean_dec(v_pre_2275_);
lean_dec_ref(v_inst_2274_);
lean_dec(v_inst_2273_);
lean_dec_ref(v_inst_2272_);
v_toPure_2297_ = lean_ctor_get(v_toApplicative_2283_, 1);
lean_inc(v_toPure_2297_);
lean_dec_ref(v_toApplicative_2283_);
v___x_2298_ = lean_apply_2(v_toPure_2297_, lean_box(0), v_f_2285_);
v___x_2299_ = lean_apply_4(v_toBind_2282_, lean_box(0), lean_box(0), v___x_2298_, v___f_2292_);
return v___x_2299_;
}
}
v___jp_2293_:
{
lean_object* v___x_2294_; lean_object* v___x_2295_; 
v___x_2294_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2272_, v_inst_2273_, v_inst_2274_, v_pre_2275_, v_post_2276_, v_usedLetOnly_2277_, v_skipConstInApp_2278_, v_skipInstances_2271_, v_x_2279_, v_x_2280_, v_f_2285_, v___y_2287_);
v___x_2295_ = lean_apply_4(v_toBind_2282_, lean_box(0), lean_box(0), v___x_2294_, v___f_2292_);
return v___x_2295_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__9___boxed(lean_object** _args){
lean_object* v_skipInstances_2300_ = _args[0];
lean_object* v_inst_2301_ = _args[1];
lean_object* v_inst_2302_ = _args[2];
lean_object* v_inst_2303_ = _args[3];
lean_object* v_pre_2304_ = _args[4];
lean_object* v_post_2305_ = _args[5];
lean_object* v_usedLetOnly_2306_ = _args[6];
lean_object* v_skipConstInApp_2307_ = _args[7];
lean_object* v_x_2308_ = _args[8];
lean_object* v_x_2309_ = _args[9];
lean_object* v___x_2310_ = _args[10];
lean_object* v_toBind_2311_ = _args[11];
lean_object* v_toApplicative_2312_ = _args[12];
lean_object* v___f_2313_ = _args[13];
lean_object* v_f_2314_ = _args[14];
lean_object* v_args_2315_ = _args[15];
lean_object* v___y_2316_ = _args[16];
_start:
{
uint8_t v_skipInstances_boxed_2317_; uint8_t v_usedLetOnly_boxed_2318_; uint8_t v_skipConstInApp_boxed_2319_; lean_object* v_res_2320_; 
v_skipInstances_boxed_2317_ = lean_unbox(v_skipInstances_2300_);
v_usedLetOnly_boxed_2318_ = lean_unbox(v_usedLetOnly_2306_);
v_skipConstInApp_boxed_2319_ = lean_unbox(v_skipConstInApp_2307_);
v_res_2320_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__9(v_skipInstances_boxed_2317_, v_inst_2301_, v_inst_2302_, v_inst_2303_, v_pre_2304_, v_post_2305_, v_usedLetOnly_boxed_2318_, v_skipConstInApp_boxed_2319_, v_x_2308_, v_x_2309_, v___x_2310_, v_toBind_2311_, v_toApplicative_2312_, v___f_2313_, v_f_2314_, v_args_2315_, v___y_2316_);
lean_dec(v___y_2316_);
return v_res_2320_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__0(lean_object* v_fvars_2323_, lean_object* v_inst_2324_, lean_object* v_inst_2325_, lean_object* v_inst_2326_, lean_object* v_pre_2327_, lean_object* v_post_2328_, uint8_t v_usedLetOnly_2329_, uint8_t v_skipConstInApp_2330_, uint8_t v_skipInstances_2331_, lean_object* v_x_2332_, lean_object* v_x_2333_, lean_object* v_body_2334_, lean_object* v_x_2335_, lean_object* v___y_2336_){
_start:
{
lean_object* v___x_2337_; lean_object* v___x_2338_; 
v___x_2337_ = lean_array_push(v_fvars_2323_, v_x_2335_);
v___x_2338_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(v_inst_2324_, v_inst_2325_, v_inst_2326_, v_pre_2327_, v_post_2328_, v_usedLetOnly_2329_, v_skipConstInApp_2330_, v_skipInstances_2331_, v_x_2332_, v_x_2333_, v___x_2337_, v_body_2334_, v___y_2336_);
return v___x_2338_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__0___boxed(lean_object* v_fvars_2339_, lean_object* v_inst_2340_, lean_object* v_inst_2341_, lean_object* v_inst_2342_, lean_object* v_pre_2343_, lean_object* v_post_2344_, lean_object* v_usedLetOnly_2345_, lean_object* v_skipConstInApp_2346_, lean_object* v_skipInstances_2347_, lean_object* v_x_2348_, lean_object* v_x_2349_, lean_object* v_body_2350_, lean_object* v_x_2351_, lean_object* v___y_2352_){
_start:
{
uint8_t v_usedLetOnly_boxed_2353_; uint8_t v_skipConstInApp_boxed_2354_; uint8_t v_skipInstances_boxed_2355_; lean_object* v_res_2356_; 
v_usedLetOnly_boxed_2353_ = lean_unbox(v_usedLetOnly_2345_);
v_skipConstInApp_boxed_2354_ = lean_unbox(v_skipConstInApp_2346_);
v_skipInstances_boxed_2355_ = lean_unbox(v_skipInstances_2347_);
v_res_2356_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__0(v_fvars_2339_, v_inst_2340_, v_inst_2341_, v_inst_2342_, v_pre_2343_, v_post_2344_, v_usedLetOnly_boxed_2353_, v_skipConstInApp_boxed_2354_, v_skipInstances_boxed_2355_, v_x_2348_, v_x_2349_, v_body_2350_, v_x_2351_, v___y_2352_);
lean_dec(v___y_2352_);
return v_res_2356_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3___boxed(lean_object* v_inst_2357_, lean_object* v_inst_2358_, lean_object* v_inst_2359_, lean_object* v_pre_2360_, lean_object* v_post_2361_, lean_object* v_usedLetOnly_2362_, lean_object* v_skipConstInApp_2363_, lean_object* v_skipInstances_2364_, lean_object* v_x_2365_, lean_object* v_x_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_){
_start:
{
uint8_t v_usedLetOnly_boxed_2369_; uint8_t v_skipConstInApp_boxed_2370_; uint8_t v_skipInstances_boxed_2371_; lean_object* v_res_2372_; 
v_usedLetOnly_boxed_2369_ = lean_unbox(v_usedLetOnly_2362_);
v_skipConstInApp_boxed_2370_ = lean_unbox(v_skipConstInApp_2363_);
v_skipInstances_boxed_2371_ = lean_unbox(v_skipInstances_2364_);
v_res_2372_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3(v_inst_2357_, v_inst_2358_, v_inst_2359_, v_pre_2360_, v_post_2361_, v_usedLetOnly_boxed_2369_, v_skipConstInApp_boxed_2370_, v_skipInstances_boxed_2371_, v_x_2365_, v_x_2366_, v_a_2367_, v_a_2368_);
lean_dec(v_a_2367_);
return v_res_2372_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(lean_object* v_inst_2373_, lean_object* v_inst_2374_, lean_object* v_inst_2375_, lean_object* v_pre_2376_, lean_object* v_post_2377_, uint8_t v_usedLetOnly_2378_, uint8_t v_skipConstInApp_2379_, uint8_t v_skipInstances_2380_, lean_object* v_x_2381_, lean_object* v_x_2382_, lean_object* v_fvars_2383_, lean_object* v_e_2384_, lean_object* v_a_2385_){
_start:
{
lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___f_2390_; lean_object* v___f_2391_; lean_object* v___x_2392_; 
v___x_2386_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0));
v___x_2387_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1));
lean_inc_ref(v_inst_2373_);
v___x_2388_ = l_Lean_MonadCacheT_instMonad___redArg(v_x_2381_, v___x_2386_, v___x_2387_, v_inst_2373_);
v___x_2389_ = l_Lean_MonadCacheT_instMonadControl___redArg(v_x_2381_, v___x_2386_, v___x_2387_);
lean_inc_ref_n(v_inst_2375_, 2);
lean_inc_ref(v___x_2389_);
v___f_2390_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_2390_, 0, v___x_2389_);
lean_closure_set(v___f_2390_, 1, v_inst_2375_);
v___f_2391_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_2391_, 0, v___x_2389_);
lean_closure_set(v___f_2391_, 1, v_inst_2375_);
v___x_2392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2392_, 0, v___f_2390_);
lean_ctor_set(v___x_2392_, 1, v___f_2391_);
if (lean_obj_tag(v_e_2384_) == 7)
{
lean_object* v_binderName_2393_; lean_object* v_binderType_2394_; lean_object* v_body_2395_; uint8_t v_binderInfo_2396_; lean_object* v_toBind_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___f_2401_; lean_object* v___x_2402_; lean_object* v___f_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; 
v_binderName_2393_ = lean_ctor_get(v_e_2384_, 0);
lean_inc(v_binderName_2393_);
v_binderType_2394_ = lean_ctor_get(v_e_2384_, 1);
lean_inc_ref(v_binderType_2394_);
v_body_2395_ = lean_ctor_get(v_e_2384_, 2);
lean_inc_ref(v_body_2395_);
v_binderInfo_2396_ = lean_ctor_get_uint8(v_e_2384_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_2384_);
v_toBind_2397_ = lean_ctor_get(v_inst_2373_, 1);
lean_inc(v_toBind_2397_);
v___x_2398_ = lean_box(v_usedLetOnly_2378_);
v___x_2399_ = lean_box(v_skipConstInApp_2379_);
v___x_2400_ = lean_box(v_skipInstances_2380_);
lean_inc(v_x_2382_);
lean_inc(v_post_2377_);
lean_inc(v_pre_2376_);
lean_inc_ref(v_inst_2375_);
lean_inc(v_inst_2374_);
lean_inc_ref(v_inst_2373_);
lean_inc_ref(v_fvars_2383_);
v___f_2401_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__0___boxed), 14, 12);
lean_closure_set(v___f_2401_, 0, v_fvars_2383_);
lean_closure_set(v___f_2401_, 1, v_inst_2373_);
lean_closure_set(v___f_2401_, 2, v_inst_2374_);
lean_closure_set(v___f_2401_, 3, v_inst_2375_);
lean_closure_set(v___f_2401_, 4, v_pre_2376_);
lean_closure_set(v___f_2401_, 5, v_post_2377_);
lean_closure_set(v___f_2401_, 6, v___x_2398_);
lean_closure_set(v___f_2401_, 7, v___x_2399_);
lean_closure_set(v___f_2401_, 8, v___x_2400_);
lean_closure_set(v___f_2401_, 9, v_x_2381_);
lean_closure_set(v___f_2401_, 10, v_x_2382_);
lean_closure_set(v___f_2401_, 11, v_body_2395_);
v___x_2402_ = lean_box(v_binderInfo_2396_);
lean_inc(v_a_2385_);
v___f_2403_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_2403_, 0, v___x_2392_);
lean_closure_set(v___f_2403_, 1, v___x_2388_);
lean_closure_set(v___f_2403_, 2, v_binderName_2393_);
lean_closure_set(v___f_2403_, 3, v___x_2402_);
lean_closure_set(v___f_2403_, 4, v___f_2401_);
lean_closure_set(v___f_2403_, 5, v_a_2385_);
v___x_2404_ = lean_expr_instantiate_rev(v_binderType_2394_, v_fvars_2383_);
lean_dec_ref(v_fvars_2383_);
lean_dec_ref(v_binderType_2394_);
v___x_2405_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2373_, v_inst_2374_, v_inst_2375_, v_pre_2376_, v_post_2377_, v_usedLetOnly_2378_, v_skipConstInApp_2379_, v_skipInstances_2380_, v_x_2381_, v_x_2382_, v___x_2404_, v_a_2385_);
v___x_2406_ = lean_apply_4(v_toBind_2397_, lean_box(0), lean_box(0), v___x_2405_, v___f_2403_);
return v___x_2406_;
}
else
{
lean_object* v_toBind_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___f_2411_; lean_object* v___x_2412_; lean_object* v___f_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; 
lean_dec_ref(v___x_2392_);
lean_dec_ref(v___x_2388_);
v_toBind_2407_ = lean_ctor_get(v_inst_2373_, 1);
lean_inc_n(v_toBind_2407_, 2);
v___x_2408_ = lean_box(v_usedLetOnly_2378_);
v___x_2409_ = lean_box(v_skipConstInApp_2379_);
v___x_2410_ = lean_box(v_skipInstances_2380_);
lean_inc(v_a_2385_);
lean_inc(v_x_2382_);
lean_inc(v_post_2377_);
lean_inc(v_pre_2376_);
lean_inc_ref(v_inst_2375_);
lean_inc_n(v_inst_2374_, 2);
lean_inc_ref(v_inst_2373_);
v___f_2411_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3___boxed), 12, 11);
lean_closure_set(v___f_2411_, 0, v_inst_2373_);
lean_closure_set(v___f_2411_, 1, v_inst_2374_);
lean_closure_set(v___f_2411_, 2, v_inst_2375_);
lean_closure_set(v___f_2411_, 3, v_pre_2376_);
lean_closure_set(v___f_2411_, 4, v_post_2377_);
lean_closure_set(v___f_2411_, 5, v___x_2408_);
lean_closure_set(v___f_2411_, 6, v___x_2409_);
lean_closure_set(v___f_2411_, 7, v___x_2410_);
lean_closure_set(v___f_2411_, 8, v_x_2381_);
lean_closure_set(v___f_2411_, 9, v_x_2382_);
lean_closure_set(v___f_2411_, 10, v_a_2385_);
v___x_2412_ = lean_box(v_usedLetOnly_2378_);
lean_inc_ref(v_fvars_2383_);
v___f_2413_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__3___boxed), 6, 5);
lean_closure_set(v___f_2413_, 0, v_fvars_2383_);
lean_closure_set(v___f_2413_, 1, v___x_2412_);
lean_closure_set(v___f_2413_, 2, v_inst_2374_);
lean_closure_set(v___f_2413_, 3, v_toBind_2407_);
lean_closure_set(v___f_2413_, 4, v___f_2411_);
v___x_2414_ = lean_expr_instantiate_rev(v_e_2384_, v_fvars_2383_);
lean_dec_ref(v_fvars_2383_);
lean_dec_ref(v_e_2384_);
v___x_2415_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2373_, v_inst_2374_, v_inst_2375_, v_pre_2376_, v_post_2377_, v_usedLetOnly_2378_, v_skipConstInApp_2379_, v_skipInstances_2380_, v_x_2381_, v_x_2382_, v___x_2414_, v_a_2385_);
v___x_2416_ = lean_apply_4(v_toBind_2407_, lean_box(0), lean_box(0), v___x_2415_, v___f_2413_);
return v___x_2416_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__0(lean_object* v_fvars_2417_, lean_object* v_inst_2418_, lean_object* v_inst_2419_, lean_object* v_inst_2420_, lean_object* v_pre_2421_, lean_object* v_post_2422_, uint8_t v_usedLetOnly_2423_, uint8_t v_skipConstInApp_2424_, uint8_t v_skipInstances_2425_, lean_object* v_x_2426_, lean_object* v_x_2427_, lean_object* v_body_2428_, lean_object* v_x_2429_, lean_object* v___y_2430_){
_start:
{
lean_object* v___x_2431_; lean_object* v___x_2432_; 
v___x_2431_ = lean_array_push(v_fvars_2417_, v_x_2429_);
v___x_2432_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(v_inst_2418_, v_inst_2419_, v_inst_2420_, v_pre_2421_, v_post_2422_, v_usedLetOnly_2423_, v_skipConstInApp_2424_, v_skipInstances_2425_, v_x_2426_, v_x_2427_, v___x_2431_, v_body_2428_, v___y_2430_);
return v___x_2432_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__0___boxed(lean_object* v_fvars_2433_, lean_object* v_inst_2434_, lean_object* v_inst_2435_, lean_object* v_inst_2436_, lean_object* v_pre_2437_, lean_object* v_post_2438_, lean_object* v_usedLetOnly_2439_, lean_object* v_skipConstInApp_2440_, lean_object* v_skipInstances_2441_, lean_object* v_x_2442_, lean_object* v_x_2443_, lean_object* v_body_2444_, lean_object* v_x_2445_, lean_object* v___y_2446_){
_start:
{
uint8_t v_usedLetOnly_boxed_2447_; uint8_t v_skipConstInApp_boxed_2448_; uint8_t v_skipInstances_boxed_2449_; lean_object* v_res_2450_; 
v_usedLetOnly_boxed_2447_ = lean_unbox(v_usedLetOnly_2439_);
v_skipConstInApp_boxed_2448_ = lean_unbox(v_skipConstInApp_2440_);
v_skipInstances_boxed_2449_ = lean_unbox(v_skipInstances_2441_);
v_res_2450_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__0(v_fvars_2433_, v_inst_2434_, v_inst_2435_, v_inst_2436_, v_pre_2437_, v_post_2438_, v_usedLetOnly_boxed_2447_, v_skipConstInApp_boxed_2448_, v_skipInstances_boxed_2449_, v_x_2442_, v_x_2443_, v_body_2444_, v_x_2445_, v___y_2446_);
lean_dec(v___y_2446_);
return v_res_2450_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(lean_object* v_inst_2451_, lean_object* v_inst_2452_, lean_object* v_inst_2453_, lean_object* v_pre_2454_, lean_object* v_post_2455_, uint8_t v_usedLetOnly_2456_, uint8_t v_skipConstInApp_2457_, uint8_t v_skipInstances_2458_, lean_object* v_x_2459_, lean_object* v_x_2460_, lean_object* v_fvars_2461_, lean_object* v_e_2462_, lean_object* v_a_2463_){
_start:
{
lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___f_2468_; lean_object* v___f_2469_; lean_object* v___x_2470_; 
v___x_2464_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0));
v___x_2465_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1));
lean_inc_ref(v_inst_2451_);
v___x_2466_ = l_Lean_MonadCacheT_instMonad___redArg(v_x_2459_, v___x_2464_, v___x_2465_, v_inst_2451_);
v___x_2467_ = l_Lean_MonadCacheT_instMonadControl___redArg(v_x_2459_, v___x_2464_, v___x_2465_);
lean_inc_ref_n(v_inst_2453_, 2);
lean_inc_ref(v___x_2467_);
v___f_2468_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_2468_, 0, v___x_2467_);
lean_closure_set(v___f_2468_, 1, v_inst_2453_);
v___f_2469_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_2469_, 0, v___x_2467_);
lean_closure_set(v___f_2469_, 1, v_inst_2453_);
v___x_2470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2470_, 0, v___f_2468_);
lean_ctor_set(v___x_2470_, 1, v___f_2469_);
if (lean_obj_tag(v_e_2462_) == 6)
{
lean_object* v_binderName_2471_; lean_object* v_binderType_2472_; lean_object* v_body_2473_; uint8_t v_binderInfo_2474_; lean_object* v_toBind_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___f_2479_; lean_object* v___x_2480_; lean_object* v___f_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; 
v_binderName_2471_ = lean_ctor_get(v_e_2462_, 0);
lean_inc(v_binderName_2471_);
v_binderType_2472_ = lean_ctor_get(v_e_2462_, 1);
lean_inc_ref(v_binderType_2472_);
v_body_2473_ = lean_ctor_get(v_e_2462_, 2);
lean_inc_ref(v_body_2473_);
v_binderInfo_2474_ = lean_ctor_get_uint8(v_e_2462_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_2462_);
v_toBind_2475_ = lean_ctor_get(v_inst_2451_, 1);
lean_inc(v_toBind_2475_);
v___x_2476_ = lean_box(v_usedLetOnly_2456_);
v___x_2477_ = lean_box(v_skipConstInApp_2457_);
v___x_2478_ = lean_box(v_skipInstances_2458_);
lean_inc(v_x_2460_);
lean_inc(v_post_2455_);
lean_inc(v_pre_2454_);
lean_inc_ref(v_inst_2453_);
lean_inc(v_inst_2452_);
lean_inc_ref(v_inst_2451_);
lean_inc_ref(v_fvars_2461_);
v___f_2479_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__0___boxed), 14, 12);
lean_closure_set(v___f_2479_, 0, v_fvars_2461_);
lean_closure_set(v___f_2479_, 1, v_inst_2451_);
lean_closure_set(v___f_2479_, 2, v_inst_2452_);
lean_closure_set(v___f_2479_, 3, v_inst_2453_);
lean_closure_set(v___f_2479_, 4, v_pre_2454_);
lean_closure_set(v___f_2479_, 5, v_post_2455_);
lean_closure_set(v___f_2479_, 6, v___x_2476_);
lean_closure_set(v___f_2479_, 7, v___x_2477_);
lean_closure_set(v___f_2479_, 8, v___x_2478_);
lean_closure_set(v___f_2479_, 9, v_x_2459_);
lean_closure_set(v___f_2479_, 10, v_x_2460_);
lean_closure_set(v___f_2479_, 11, v_body_2473_);
v___x_2480_ = lean_box(v_binderInfo_2474_);
lean_inc(v_a_2463_);
v___f_2481_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_2481_, 0, v___x_2470_);
lean_closure_set(v___f_2481_, 1, v___x_2466_);
lean_closure_set(v___f_2481_, 2, v_binderName_2471_);
lean_closure_set(v___f_2481_, 3, v___x_2480_);
lean_closure_set(v___f_2481_, 4, v___f_2479_);
lean_closure_set(v___f_2481_, 5, v_a_2463_);
v___x_2482_ = lean_expr_instantiate_rev(v_binderType_2472_, v_fvars_2461_);
lean_dec_ref(v_fvars_2461_);
lean_dec_ref(v_binderType_2472_);
v___x_2483_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2451_, v_inst_2452_, v_inst_2453_, v_pre_2454_, v_post_2455_, v_usedLetOnly_2456_, v_skipConstInApp_2457_, v_skipInstances_2458_, v_x_2459_, v_x_2460_, v___x_2482_, v_a_2463_);
v___x_2484_ = lean_apply_4(v_toBind_2475_, lean_box(0), lean_box(0), v___x_2483_, v___f_2481_);
return v___x_2484_;
}
else
{
lean_object* v_toBind_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___f_2489_; lean_object* v___x_2490_; lean_object* v___f_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; 
lean_dec_ref(v___x_2470_);
lean_dec_ref(v___x_2466_);
v_toBind_2485_ = lean_ctor_get(v_inst_2451_, 1);
lean_inc_n(v_toBind_2485_, 2);
v___x_2486_ = lean_box(v_usedLetOnly_2456_);
v___x_2487_ = lean_box(v_skipConstInApp_2457_);
v___x_2488_ = lean_box(v_skipInstances_2458_);
lean_inc(v_a_2463_);
lean_inc(v_x_2460_);
lean_inc(v_post_2455_);
lean_inc(v_pre_2454_);
lean_inc_ref(v_inst_2453_);
lean_inc_n(v_inst_2452_, 2);
lean_inc_ref(v_inst_2451_);
v___f_2489_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3___boxed), 12, 11);
lean_closure_set(v___f_2489_, 0, v_inst_2451_);
lean_closure_set(v___f_2489_, 1, v_inst_2452_);
lean_closure_set(v___f_2489_, 2, v_inst_2453_);
lean_closure_set(v___f_2489_, 3, v_pre_2454_);
lean_closure_set(v___f_2489_, 4, v_post_2455_);
lean_closure_set(v___f_2489_, 5, v___x_2486_);
lean_closure_set(v___f_2489_, 6, v___x_2487_);
lean_closure_set(v___f_2489_, 7, v___x_2488_);
lean_closure_set(v___f_2489_, 8, v_x_2459_);
lean_closure_set(v___f_2489_, 9, v_x_2460_);
lean_closure_set(v___f_2489_, 10, v_a_2463_);
v___x_2490_ = lean_box(v_usedLetOnly_2456_);
lean_inc_ref(v_fvars_2461_);
v___f_2491_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__3___boxed), 6, 5);
lean_closure_set(v___f_2491_, 0, v_fvars_2461_);
lean_closure_set(v___f_2491_, 1, v___x_2490_);
lean_closure_set(v___f_2491_, 2, v_inst_2452_);
lean_closure_set(v___f_2491_, 3, v_toBind_2485_);
lean_closure_set(v___f_2491_, 4, v___f_2489_);
v___x_2492_ = lean_expr_instantiate_rev(v_e_2462_, v_fvars_2461_);
lean_dec_ref(v_fvars_2461_);
lean_dec_ref(v_e_2462_);
v___x_2493_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2451_, v_inst_2452_, v_inst_2453_, v_pre_2454_, v_post_2455_, v_usedLetOnly_2456_, v_skipConstInApp_2457_, v_skipInstances_2458_, v_x_2459_, v_x_2460_, v___x_2492_, v_a_2463_);
v___x_2494_ = lean_apply_4(v_toBind_2485_, lean_box(0), lean_box(0), v___x_2493_, v___f_2491_);
return v___x_2494_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__0(lean_object* v_fvars_2495_, lean_object* v_inst_2496_, lean_object* v_inst_2497_, lean_object* v_inst_2498_, lean_object* v_pre_2499_, lean_object* v_post_2500_, uint8_t v_usedLetOnly_2501_, uint8_t v_skipConstInApp_2502_, uint8_t v_skipInstances_2503_, lean_object* v_x_2504_, lean_object* v_x_2505_, lean_object* v_body_2506_, lean_object* v_x_2507_, lean_object* v___y_2508_){
_start:
{
lean_object* v___x_2509_; lean_object* v___x_2510_; 
v___x_2509_ = lean_array_push(v_fvars_2495_, v_x_2507_);
v___x_2510_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(v_inst_2496_, v_inst_2497_, v_inst_2498_, v_pre_2499_, v_post_2500_, v_usedLetOnly_2501_, v_skipConstInApp_2502_, v_skipInstances_2503_, v_x_2504_, v_x_2505_, v___x_2509_, v_body_2506_, v___y_2508_);
return v___x_2510_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__0___boxed(lean_object* v_fvars_2511_, lean_object* v_inst_2512_, lean_object* v_inst_2513_, lean_object* v_inst_2514_, lean_object* v_pre_2515_, lean_object* v_post_2516_, lean_object* v_usedLetOnly_2517_, lean_object* v_skipConstInApp_2518_, lean_object* v_skipInstances_2519_, lean_object* v_x_2520_, lean_object* v_x_2521_, lean_object* v_body_2522_, lean_object* v_x_2523_, lean_object* v___y_2524_){
_start:
{
uint8_t v_usedLetOnly_boxed_2525_; uint8_t v_skipConstInApp_boxed_2526_; uint8_t v_skipInstances_boxed_2527_; lean_object* v_res_2528_; 
v_usedLetOnly_boxed_2525_ = lean_unbox(v_usedLetOnly_2517_);
v_skipConstInApp_boxed_2526_ = lean_unbox(v_skipConstInApp_2518_);
v_skipInstances_boxed_2527_ = lean_unbox(v_skipInstances_2519_);
v_res_2528_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__0(v_fvars_2511_, v_inst_2512_, v_inst_2513_, v_inst_2514_, v_pre_2515_, v_post_2516_, v_usedLetOnly_boxed_2525_, v_skipConstInApp_boxed_2526_, v_skipInstances_boxed_2527_, v_x_2520_, v_x_2521_, v_body_2522_, v_x_2523_, v___y_2524_);
lean_dec(v___y_2524_);
return v_res_2528_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__2(lean_object* v___x_2529_, lean_object* v___x_2530_, lean_object* v_declName_2531_, lean_object* v___f_2532_, uint8_t v_nondep_2533_, lean_object* v_a_2534_, lean_object* v_value_2535_, lean_object* v_fvars_2536_, lean_object* v_inst_2537_, lean_object* v_inst_2538_, lean_object* v_inst_2539_, lean_object* v_pre_2540_, lean_object* v_post_2541_, uint8_t v_usedLetOnly_2542_, uint8_t v_skipConstInApp_2543_, uint8_t v_skipInstances_2544_, lean_object* v_x_2545_, lean_object* v_x_2546_, lean_object* v_toBind_2547_, lean_object* v_a_2548_){
_start:
{
lean_object* v___x_2549_; lean_object* v___f_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; 
v___x_2549_ = lean_box(v_nondep_2533_);
lean_inc(v_a_2534_);
v___f_2550_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_2550_, 0, v___x_2529_);
lean_closure_set(v___f_2550_, 1, v___x_2530_);
lean_closure_set(v___f_2550_, 2, v_declName_2531_);
lean_closure_set(v___f_2550_, 3, v_a_2548_);
lean_closure_set(v___f_2550_, 4, v___f_2532_);
lean_closure_set(v___f_2550_, 5, v___x_2549_);
lean_closure_set(v___f_2550_, 6, v_a_2534_);
v___x_2551_ = lean_expr_instantiate_rev(v_value_2535_, v_fvars_2536_);
v___x_2552_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2537_, v_inst_2538_, v_inst_2539_, v_pre_2540_, v_post_2541_, v_usedLetOnly_2542_, v_skipConstInApp_2543_, v_skipInstances_2544_, v_x_2545_, v_x_2546_, v___x_2551_, v_a_2534_);
v___x_2553_ = lean_apply_4(v_toBind_2547_, lean_box(0), lean_box(0), v___x_2552_, v___f_2550_);
return v___x_2553_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__2___boxed(lean_object** _args){
lean_object* v___x_2554_ = _args[0];
lean_object* v___x_2555_ = _args[1];
lean_object* v_declName_2556_ = _args[2];
lean_object* v___f_2557_ = _args[3];
lean_object* v_nondep_2558_ = _args[4];
lean_object* v_a_2559_ = _args[5];
lean_object* v_value_2560_ = _args[6];
lean_object* v_fvars_2561_ = _args[7];
lean_object* v_inst_2562_ = _args[8];
lean_object* v_inst_2563_ = _args[9];
lean_object* v_inst_2564_ = _args[10];
lean_object* v_pre_2565_ = _args[11];
lean_object* v_post_2566_ = _args[12];
lean_object* v_usedLetOnly_2567_ = _args[13];
lean_object* v_skipConstInApp_2568_ = _args[14];
lean_object* v_skipInstances_2569_ = _args[15];
lean_object* v_x_2570_ = _args[16];
lean_object* v_x_2571_ = _args[17];
lean_object* v_toBind_2572_ = _args[18];
lean_object* v_a_2573_ = _args[19];
_start:
{
uint8_t v_nondep_4209__boxed_2574_; uint8_t v_usedLetOnly_boxed_2575_; uint8_t v_skipConstInApp_boxed_2576_; uint8_t v_skipInstances_boxed_2577_; lean_object* v_res_2578_; 
v_nondep_4209__boxed_2574_ = lean_unbox(v_nondep_2558_);
v_usedLetOnly_boxed_2575_ = lean_unbox(v_usedLetOnly_2567_);
v_skipConstInApp_boxed_2576_ = lean_unbox(v_skipConstInApp_2568_);
v_skipInstances_boxed_2577_ = lean_unbox(v_skipInstances_2569_);
v_res_2578_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__2(v___x_2554_, v___x_2555_, v_declName_2556_, v___f_2557_, v_nondep_4209__boxed_2574_, v_a_2559_, v_value_2560_, v_fvars_2561_, v_inst_2562_, v_inst_2563_, v_inst_2564_, v_pre_2565_, v_post_2566_, v_usedLetOnly_boxed_2575_, v_skipConstInApp_boxed_2576_, v_skipInstances_boxed_2577_, v_x_2570_, v_x_2571_, v_toBind_2572_, v_a_2573_);
lean_dec_ref(v_fvars_2561_);
lean_dec_ref(v_value_2560_);
lean_dec(v_a_2559_);
return v_res_2578_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(lean_object* v_inst_2579_, lean_object* v_inst_2580_, lean_object* v_inst_2581_, lean_object* v_pre_2582_, lean_object* v_post_2583_, uint8_t v_usedLetOnly_2584_, uint8_t v_skipConstInApp_2585_, uint8_t v_skipInstances_2586_, lean_object* v_x_2587_, lean_object* v_x_2588_, lean_object* v_fvars_2589_, lean_object* v_e_2590_, lean_object* v_a_2591_){
_start:
{
lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___f_2596_; lean_object* v___f_2597_; lean_object* v___x_2598_; 
v___x_2592_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0));
v___x_2593_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1));
lean_inc_ref(v_inst_2579_);
v___x_2594_ = l_Lean_MonadCacheT_instMonad___redArg(v_x_2587_, v___x_2592_, v___x_2593_, v_inst_2579_);
v___x_2595_ = l_Lean_MonadCacheT_instMonadControl___redArg(v_x_2587_, v___x_2592_, v___x_2593_);
lean_inc_ref_n(v_inst_2581_, 2);
lean_inc_ref(v___x_2595_);
v___f_2596_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_2596_, 0, v___x_2595_);
lean_closure_set(v___f_2596_, 1, v_inst_2581_);
v___f_2597_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_2597_, 0, v___x_2595_);
lean_closure_set(v___f_2597_, 1, v_inst_2581_);
v___x_2598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2598_, 0, v___f_2596_);
lean_ctor_set(v___x_2598_, 1, v___f_2597_);
if (lean_obj_tag(v_e_2590_) == 8)
{
lean_object* v_declName_2599_; lean_object* v_type_2600_; lean_object* v_value_2601_; lean_object* v_body_2602_; uint8_t v_nondep_2603_; lean_object* v_toBind_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___f_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___f_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; 
v_declName_2599_ = lean_ctor_get(v_e_2590_, 0);
lean_inc(v_declName_2599_);
v_type_2600_ = lean_ctor_get(v_e_2590_, 1);
lean_inc_ref(v_type_2600_);
v_value_2601_ = lean_ctor_get(v_e_2590_, 2);
lean_inc_ref(v_value_2601_);
v_body_2602_ = lean_ctor_get(v_e_2590_, 3);
lean_inc_ref(v_body_2602_);
v_nondep_2603_ = lean_ctor_get_uint8(v_e_2590_, sizeof(void*)*4 + 8);
lean_dec_ref(v_e_2590_);
v_toBind_2604_ = lean_ctor_get(v_inst_2579_, 1);
lean_inc_n(v_toBind_2604_, 2);
v___x_2605_ = lean_box(v_usedLetOnly_2584_);
v___x_2606_ = lean_box(v_skipConstInApp_2585_);
v___x_2607_ = lean_box(v_skipInstances_2586_);
lean_inc_n(v_x_2588_, 2);
lean_inc_n(v_post_2583_, 2);
lean_inc_n(v_pre_2582_, 2);
lean_inc_ref_n(v_inst_2581_, 2);
lean_inc_n(v_inst_2580_, 2);
lean_inc_ref_n(v_inst_2579_, 2);
lean_inc_ref_n(v_fvars_2589_, 2);
v___f_2608_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__0___boxed), 14, 12);
lean_closure_set(v___f_2608_, 0, v_fvars_2589_);
lean_closure_set(v___f_2608_, 1, v_inst_2579_);
lean_closure_set(v___f_2608_, 2, v_inst_2580_);
lean_closure_set(v___f_2608_, 3, v_inst_2581_);
lean_closure_set(v___f_2608_, 4, v_pre_2582_);
lean_closure_set(v___f_2608_, 5, v_post_2583_);
lean_closure_set(v___f_2608_, 6, v___x_2605_);
lean_closure_set(v___f_2608_, 7, v___x_2606_);
lean_closure_set(v___f_2608_, 8, v___x_2607_);
lean_closure_set(v___f_2608_, 9, v_x_2587_);
lean_closure_set(v___f_2608_, 10, v_x_2588_);
lean_closure_set(v___f_2608_, 11, v_body_2602_);
v___x_2609_ = lean_box(v_nondep_2603_);
v___x_2610_ = lean_box(v_usedLetOnly_2584_);
v___x_2611_ = lean_box(v_skipConstInApp_2585_);
v___x_2612_ = lean_box(v_skipInstances_2586_);
lean_inc(v_a_2591_);
v___f_2613_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__2___boxed), 20, 19);
lean_closure_set(v___f_2613_, 0, v___x_2598_);
lean_closure_set(v___f_2613_, 1, v___x_2594_);
lean_closure_set(v___f_2613_, 2, v_declName_2599_);
lean_closure_set(v___f_2613_, 3, v___f_2608_);
lean_closure_set(v___f_2613_, 4, v___x_2609_);
lean_closure_set(v___f_2613_, 5, v_a_2591_);
lean_closure_set(v___f_2613_, 6, v_value_2601_);
lean_closure_set(v___f_2613_, 7, v_fvars_2589_);
lean_closure_set(v___f_2613_, 8, v_inst_2579_);
lean_closure_set(v___f_2613_, 9, v_inst_2580_);
lean_closure_set(v___f_2613_, 10, v_inst_2581_);
lean_closure_set(v___f_2613_, 11, v_pre_2582_);
lean_closure_set(v___f_2613_, 12, v_post_2583_);
lean_closure_set(v___f_2613_, 13, v___x_2610_);
lean_closure_set(v___f_2613_, 14, v___x_2611_);
lean_closure_set(v___f_2613_, 15, v___x_2612_);
lean_closure_set(v___f_2613_, 16, v_x_2587_);
lean_closure_set(v___f_2613_, 17, v_x_2588_);
lean_closure_set(v___f_2613_, 18, v_toBind_2604_);
v___x_2614_ = lean_expr_instantiate_rev(v_type_2600_, v_fvars_2589_);
lean_dec_ref(v_fvars_2589_);
lean_dec_ref(v_type_2600_);
v___x_2615_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2579_, v_inst_2580_, v_inst_2581_, v_pre_2582_, v_post_2583_, v_usedLetOnly_2584_, v_skipConstInApp_2585_, v_skipInstances_2586_, v_x_2587_, v_x_2588_, v___x_2614_, v_a_2591_);
v___x_2616_ = lean_apply_4(v_toBind_2604_, lean_box(0), lean_box(0), v___x_2615_, v___f_2613_);
return v___x_2616_;
}
else
{
lean_object* v_toBind_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___f_2621_; lean_object* v___x_2622_; lean_object* v___f_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; 
lean_dec_ref(v___x_2598_);
lean_dec_ref(v___x_2594_);
v_toBind_2617_ = lean_ctor_get(v_inst_2579_, 1);
lean_inc_n(v_toBind_2617_, 2);
v___x_2618_ = lean_box(v_usedLetOnly_2584_);
v___x_2619_ = lean_box(v_skipConstInApp_2585_);
v___x_2620_ = lean_box(v_skipInstances_2586_);
lean_inc(v_a_2591_);
lean_inc(v_x_2588_);
lean_inc(v_post_2583_);
lean_inc(v_pre_2582_);
lean_inc_ref(v_inst_2581_);
lean_inc_n(v_inst_2580_, 2);
lean_inc_ref(v_inst_2579_);
v___f_2621_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3___boxed), 12, 11);
lean_closure_set(v___f_2621_, 0, v_inst_2579_);
lean_closure_set(v___f_2621_, 1, v_inst_2580_);
lean_closure_set(v___f_2621_, 2, v_inst_2581_);
lean_closure_set(v___f_2621_, 3, v_pre_2582_);
lean_closure_set(v___f_2621_, 4, v_post_2583_);
lean_closure_set(v___f_2621_, 5, v___x_2618_);
lean_closure_set(v___f_2621_, 6, v___x_2619_);
lean_closure_set(v___f_2621_, 7, v___x_2620_);
lean_closure_set(v___f_2621_, 8, v_x_2587_);
lean_closure_set(v___f_2621_, 9, v_x_2588_);
lean_closure_set(v___f_2621_, 10, v_a_2591_);
v___x_2622_ = lean_box(v_usedLetOnly_2584_);
lean_inc_ref(v_fvars_2589_);
v___f_2623_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__4___boxed), 6, 5);
lean_closure_set(v___f_2623_, 0, v_fvars_2589_);
lean_closure_set(v___f_2623_, 1, v___x_2622_);
lean_closure_set(v___f_2623_, 2, v_inst_2580_);
lean_closure_set(v___f_2623_, 3, v_toBind_2617_);
lean_closure_set(v___f_2623_, 4, v___f_2621_);
v___x_2624_ = lean_expr_instantiate_rev(v_e_2590_, v_fvars_2589_);
lean_dec_ref(v_fvars_2589_);
lean_dec_ref(v_e_2590_);
v___x_2625_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2579_, v_inst_2580_, v_inst_2581_, v_pre_2582_, v_post_2583_, v_usedLetOnly_2584_, v_skipConstInApp_2585_, v_skipInstances_2586_, v_x_2587_, v_x_2588_, v___x_2624_, v_a_2591_);
v___x_2626_ = lean_apply_4(v_toBind_2617_, lean_box(0), lean_box(0), v___x_2625_, v___f_2623_);
return v___x_2626_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__8(lean_object* v_expr_2627_, lean_object* v_data_2628_, lean_object* v_inst_2629_, lean_object* v_inst_2630_, lean_object* v_inst_2631_, lean_object* v_pre_2632_, lean_object* v_post_2633_, uint8_t v_usedLetOnly_2634_, uint8_t v_skipConstInApp_2635_, uint8_t v_skipInstances_2636_, lean_object* v_x_2637_, lean_object* v_x_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v_a_2641_){
_start:
{
size_t v___x_2642_; size_t v___x_2643_; uint8_t v___x_2644_; 
v___x_2642_ = lean_ptr_addr(v_expr_2627_);
v___x_2643_ = lean_ptr_addr(v_a_2641_);
v___x_2644_ = lean_usize_dec_eq(v___x_2642_, v___x_2643_);
if (v___x_2644_ == 0)
{
lean_object* v___x_2645_; lean_object* v___x_2646_; 
lean_dec_ref(v___y_2640_);
v___x_2645_ = l_Lean_Expr_mdata___override(v_data_2628_, v_a_2641_);
v___x_2646_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2629_, v_inst_2630_, v_inst_2631_, v_pre_2632_, v_post_2633_, v_usedLetOnly_2634_, v_skipConstInApp_2635_, v_skipInstances_2636_, v_x_2637_, v_x_2638_, v___x_2645_, v___y_2639_);
return v___x_2646_;
}
else
{
lean_object* v___x_2647_; 
lean_dec_ref(v_a_2641_);
lean_dec(v_data_2628_);
v___x_2647_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2629_, v_inst_2630_, v_inst_2631_, v_pre_2632_, v_post_2633_, v_usedLetOnly_2634_, v_skipConstInApp_2635_, v_skipInstances_2636_, v_x_2637_, v_x_2638_, v___y_2640_, v___y_2639_);
return v___x_2647_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__8___boxed(lean_object* v_expr_2648_, lean_object* v_data_2649_, lean_object* v_inst_2650_, lean_object* v_inst_2651_, lean_object* v_inst_2652_, lean_object* v_pre_2653_, lean_object* v_post_2654_, lean_object* v_usedLetOnly_2655_, lean_object* v_skipConstInApp_2656_, lean_object* v_skipInstances_2657_, lean_object* v_x_2658_, lean_object* v_x_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v_a_2662_){
_start:
{
uint8_t v_usedLetOnly_boxed_2663_; uint8_t v_skipConstInApp_boxed_2664_; uint8_t v_skipInstances_boxed_2665_; lean_object* v_res_2666_; 
v_usedLetOnly_boxed_2663_ = lean_unbox(v_usedLetOnly_2655_);
v_skipConstInApp_boxed_2664_ = lean_unbox(v_skipConstInApp_2656_);
v_skipInstances_boxed_2665_ = lean_unbox(v_skipInstances_2657_);
v_res_2666_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__8(v_expr_2648_, v_data_2649_, v_inst_2650_, v_inst_2651_, v_inst_2652_, v_pre_2653_, v_post_2654_, v_usedLetOnly_boxed_2663_, v_skipConstInApp_boxed_2664_, v_skipInstances_boxed_2665_, v_x_2658_, v_x_2659_, v___y_2660_, v___y_2661_, v_a_2662_);
lean_dec(v___y_2660_);
lean_dec_ref(v_expr_2648_);
return v_res_2666_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__10(lean_object* v_struct_2667_, lean_object* v_typeName_2668_, lean_object* v_idx_2669_, lean_object* v_inst_2670_, lean_object* v_inst_2671_, lean_object* v_inst_2672_, lean_object* v_pre_2673_, lean_object* v_post_2674_, uint8_t v_usedLetOnly_2675_, uint8_t v_skipConstInApp_2676_, uint8_t v_skipInstances_2677_, lean_object* v_x_2678_, lean_object* v_x_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v_a_2682_){
_start:
{
size_t v___x_2683_; size_t v___x_2684_; uint8_t v___x_2685_; 
v___x_2683_ = lean_ptr_addr(v_struct_2667_);
v___x_2684_ = lean_ptr_addr(v_a_2682_);
v___x_2685_ = lean_usize_dec_eq(v___x_2683_, v___x_2684_);
if (v___x_2685_ == 0)
{
lean_object* v___x_2686_; lean_object* v___x_2687_; 
lean_dec_ref(v___y_2681_);
v___x_2686_ = l_Lean_Expr_proj___override(v_typeName_2668_, v_idx_2669_, v_a_2682_);
v___x_2687_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2670_, v_inst_2671_, v_inst_2672_, v_pre_2673_, v_post_2674_, v_usedLetOnly_2675_, v_skipConstInApp_2676_, v_skipInstances_2677_, v_x_2678_, v_x_2679_, v___x_2686_, v___y_2680_);
return v___x_2687_;
}
else
{
lean_object* v___x_2688_; 
lean_dec_ref(v_a_2682_);
lean_dec(v_idx_2669_);
lean_dec(v_typeName_2668_);
v___x_2688_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2670_, v_inst_2671_, v_inst_2672_, v_pre_2673_, v_post_2674_, v_usedLetOnly_2675_, v_skipConstInApp_2676_, v_skipInstances_2677_, v_x_2678_, v_x_2679_, v___y_2681_, v___y_2680_);
return v___x_2688_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__10___boxed(lean_object* v_struct_2689_, lean_object* v_typeName_2690_, lean_object* v_idx_2691_, lean_object* v_inst_2692_, lean_object* v_inst_2693_, lean_object* v_inst_2694_, lean_object* v_pre_2695_, lean_object* v_post_2696_, lean_object* v_usedLetOnly_2697_, lean_object* v_skipConstInApp_2698_, lean_object* v_skipInstances_2699_, lean_object* v_x_2700_, lean_object* v_x_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v_a_2704_){
_start:
{
uint8_t v_usedLetOnly_boxed_2705_; uint8_t v_skipConstInApp_boxed_2706_; uint8_t v_skipInstances_boxed_2707_; lean_object* v_res_2708_; 
v_usedLetOnly_boxed_2705_ = lean_unbox(v_usedLetOnly_2697_);
v_skipConstInApp_boxed_2706_ = lean_unbox(v_skipConstInApp_2698_);
v_skipInstances_boxed_2707_ = lean_unbox(v_skipInstances_2699_);
v_res_2708_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__10(v_struct_2689_, v_typeName_2690_, v_idx_2691_, v_inst_2692_, v_inst_2693_, v_inst_2694_, v_pre_2695_, v_post_2696_, v_usedLetOnly_boxed_2705_, v_skipConstInApp_boxed_2706_, v_skipInstances_boxed_2707_, v_x_2700_, v_x_2701_, v___y_2702_, v___y_2703_, v_a_2704_);
lean_dec(v___y_2702_);
lean_dec_ref(v_struct_2689_);
return v_res_2708_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11(lean_object* v_toApplicative_2709_, lean_object* v_inst_2710_, lean_object* v_inst_2711_, lean_object* v_inst_2712_, lean_object* v_pre_2713_, lean_object* v_post_2714_, uint8_t v_usedLetOnly_2715_, uint8_t v_skipConstInApp_2716_, uint8_t v_skipInstances_2717_, lean_object* v_x_2718_, lean_object* v_x_2719_, lean_object* v___y_2720_, lean_object* v___f_2721_, lean_object* v_toBind_2722_, lean_object* v_e_2723_, lean_object* v_a_2724_){
_start:
{
lean_object* v___y_2726_; 
switch(lean_obj_tag(v_a_2724_))
{
case 0:
{
lean_object* v_e_2758_; lean_object* v_toPure_2759_; lean_object* v___x_2760_; 
lean_dec_ref(v_e_2723_);
lean_dec(v_toBind_2722_);
lean_dec(v___f_2721_);
lean_dec(v_x_2719_);
lean_dec(v_post_2714_);
lean_dec(v_pre_2713_);
lean_dec_ref(v_inst_2712_);
lean_dec(v_inst_2711_);
lean_dec_ref(v_inst_2710_);
v_e_2758_ = lean_ctor_get(v_a_2724_, 0);
lean_inc_ref(v_e_2758_);
lean_dec_ref(v_a_2724_);
v_toPure_2759_ = lean_ctor_get(v_toApplicative_2709_, 1);
lean_inc(v_toPure_2759_);
lean_dec_ref(v_toApplicative_2709_);
v___x_2760_ = lean_apply_2(v_toPure_2759_, lean_box(0), v_e_2758_);
return v___x_2760_;
}
case 1:
{
lean_object* v_e_2761_; lean_object* v___x_2762_; 
lean_dec_ref(v_e_2723_);
lean_dec(v_toBind_2722_);
lean_dec(v___f_2721_);
lean_dec_ref(v_toApplicative_2709_);
v_e_2761_ = lean_ctor_get(v_a_2724_, 0);
lean_inc_ref(v_e_2761_);
lean_dec_ref(v_a_2724_);
v___x_2762_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2710_, v_inst_2711_, v_inst_2712_, v_pre_2713_, v_post_2714_, v_usedLetOnly_2715_, v_skipConstInApp_2716_, v_skipInstances_2717_, v_x_2718_, v_x_2719_, v_e_2761_, v___y_2720_);
return v___x_2762_;
}
default: 
{
lean_object* v_e_x3f_2763_; 
lean_dec_ref(v_toApplicative_2709_);
v_e_x3f_2763_ = lean_ctor_get(v_a_2724_, 0);
lean_inc(v_e_x3f_2763_);
lean_dec_ref(v_a_2724_);
if (lean_obj_tag(v_e_x3f_2763_) == 0)
{
v___y_2726_ = v_e_2723_;
goto v___jp_2725_;
}
else
{
lean_object* v_val_2764_; 
lean_dec_ref(v_e_2723_);
v_val_2764_ = lean_ctor_get(v_e_x3f_2763_, 0);
lean_inc(v_val_2764_);
lean_dec_ref(v_e_x3f_2763_);
v___y_2726_ = v_val_2764_;
goto v___jp_2725_;
}
}
}
v___jp_2725_:
{
switch(lean_obj_tag(v___y_2726_))
{
case 7:
{
lean_object* v___x_2727_; lean_object* v___x_2728_; 
lean_dec(v_toBind_2722_);
lean_dec(v___f_2721_);
v___x_2727_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_2728_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(v_inst_2710_, v_inst_2711_, v_inst_2712_, v_pre_2713_, v_post_2714_, v_usedLetOnly_2715_, v_skipConstInApp_2716_, v_skipInstances_2717_, v_x_2718_, v_x_2719_, v___x_2727_, v___y_2726_, v___y_2720_);
return v___x_2728_;
}
case 6:
{
lean_object* v___x_2729_; lean_object* v___x_2730_; 
lean_dec(v_toBind_2722_);
lean_dec(v___f_2721_);
v___x_2729_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_2730_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(v_inst_2710_, v_inst_2711_, v_inst_2712_, v_pre_2713_, v_post_2714_, v_usedLetOnly_2715_, v_skipConstInApp_2716_, v_skipInstances_2717_, v_x_2718_, v_x_2719_, v___x_2729_, v___y_2726_, v___y_2720_);
return v___x_2730_;
}
case 8:
{
lean_object* v___x_2731_; lean_object* v___x_2732_; 
lean_dec(v_toBind_2722_);
lean_dec(v___f_2721_);
v___x_2731_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_2732_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(v_inst_2710_, v_inst_2711_, v_inst_2712_, v_pre_2713_, v_post_2714_, v_usedLetOnly_2715_, v_skipConstInApp_2716_, v_skipInstances_2717_, v_x_2718_, v_x_2719_, v___x_2731_, v___y_2726_, v___y_2720_);
return v___x_2732_;
}
case 5:
{
lean_object* v_dummy_2733_; lean_object* v_nargs_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_3755__overap_2738_; lean_object* v___x_2739_; 
lean_dec(v_toBind_2722_);
lean_dec(v_x_2719_);
lean_dec(v_post_2714_);
lean_dec(v_pre_2713_);
lean_dec_ref(v_inst_2712_);
lean_dec(v_inst_2711_);
lean_dec_ref(v_inst_2710_);
v_dummy_2733_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_2734_ = l_Lean_Expr_getAppNumArgs(v___y_2726_);
lean_inc(v_nargs_2734_);
v___x_2735_ = lean_mk_array(v_nargs_2734_, v_dummy_2733_);
v___x_2736_ = lean_unsigned_to_nat(1u);
v___x_2737_ = lean_nat_sub(v_nargs_2734_, v___x_2736_);
lean_dec(v_nargs_2734_);
v___x_3755__overap_2738_ = l_Lean_Expr_withAppAux___redArg(v___f_2721_, v___y_2726_, v___x_2735_, v___x_2737_);
lean_inc(v___y_2720_);
v___x_2739_ = lean_apply_1(v___x_3755__overap_2738_, v___y_2720_);
return v___x_2739_;
}
case 10:
{
lean_object* v_data_2740_; lean_object* v_expr_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___f_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; 
lean_dec(v___f_2721_);
v_data_2740_ = lean_ctor_get(v___y_2726_, 0);
lean_inc(v_data_2740_);
v_expr_2741_ = lean_ctor_get(v___y_2726_, 1);
lean_inc_ref_n(v_expr_2741_, 2);
v___x_2742_ = lean_box(v_usedLetOnly_2715_);
v___x_2743_ = lean_box(v_skipConstInApp_2716_);
v___x_2744_ = lean_box(v_skipInstances_2717_);
lean_inc(v___y_2720_);
lean_inc(v_x_2719_);
lean_inc(v_post_2714_);
lean_inc(v_pre_2713_);
lean_inc_ref(v_inst_2712_);
lean_inc(v_inst_2711_);
lean_inc_ref(v_inst_2710_);
v___f_2745_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__8___boxed), 15, 14);
lean_closure_set(v___f_2745_, 0, v_expr_2741_);
lean_closure_set(v___f_2745_, 1, v_data_2740_);
lean_closure_set(v___f_2745_, 2, v_inst_2710_);
lean_closure_set(v___f_2745_, 3, v_inst_2711_);
lean_closure_set(v___f_2745_, 4, v_inst_2712_);
lean_closure_set(v___f_2745_, 5, v_pre_2713_);
lean_closure_set(v___f_2745_, 6, v_post_2714_);
lean_closure_set(v___f_2745_, 7, v___x_2742_);
lean_closure_set(v___f_2745_, 8, v___x_2743_);
lean_closure_set(v___f_2745_, 9, v___x_2744_);
lean_closure_set(v___f_2745_, 10, v_x_2718_);
lean_closure_set(v___f_2745_, 11, v_x_2719_);
lean_closure_set(v___f_2745_, 12, v___y_2720_);
lean_closure_set(v___f_2745_, 13, v___y_2726_);
v___x_2746_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2710_, v_inst_2711_, v_inst_2712_, v_pre_2713_, v_post_2714_, v_usedLetOnly_2715_, v_skipConstInApp_2716_, v_skipInstances_2717_, v_x_2718_, v_x_2719_, v_expr_2741_, v___y_2720_);
v___x_2747_ = lean_apply_4(v_toBind_2722_, lean_box(0), lean_box(0), v___x_2746_, v___f_2745_);
return v___x_2747_;
}
case 11:
{
lean_object* v_typeName_2748_; lean_object* v_idx_2749_; lean_object* v_struct_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___f_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; 
lean_dec(v___f_2721_);
v_typeName_2748_ = lean_ctor_get(v___y_2726_, 0);
lean_inc(v_typeName_2748_);
v_idx_2749_ = lean_ctor_get(v___y_2726_, 1);
lean_inc(v_idx_2749_);
v_struct_2750_ = lean_ctor_get(v___y_2726_, 2);
lean_inc_ref_n(v_struct_2750_, 2);
v___x_2751_ = lean_box(v_usedLetOnly_2715_);
v___x_2752_ = lean_box(v_skipConstInApp_2716_);
v___x_2753_ = lean_box(v_skipInstances_2717_);
lean_inc(v___y_2720_);
lean_inc(v_x_2719_);
lean_inc(v_post_2714_);
lean_inc(v_pre_2713_);
lean_inc_ref(v_inst_2712_);
lean_inc(v_inst_2711_);
lean_inc_ref(v_inst_2710_);
v___f_2754_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__10___boxed), 16, 15);
lean_closure_set(v___f_2754_, 0, v_struct_2750_);
lean_closure_set(v___f_2754_, 1, v_typeName_2748_);
lean_closure_set(v___f_2754_, 2, v_idx_2749_);
lean_closure_set(v___f_2754_, 3, v_inst_2710_);
lean_closure_set(v___f_2754_, 4, v_inst_2711_);
lean_closure_set(v___f_2754_, 5, v_inst_2712_);
lean_closure_set(v___f_2754_, 6, v_pre_2713_);
lean_closure_set(v___f_2754_, 7, v_post_2714_);
lean_closure_set(v___f_2754_, 8, v___x_2751_);
lean_closure_set(v___f_2754_, 9, v___x_2752_);
lean_closure_set(v___f_2754_, 10, v___x_2753_);
lean_closure_set(v___f_2754_, 11, v_x_2718_);
lean_closure_set(v___f_2754_, 12, v_x_2719_);
lean_closure_set(v___f_2754_, 13, v___y_2720_);
lean_closure_set(v___f_2754_, 14, v___y_2726_);
v___x_2755_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2710_, v_inst_2711_, v_inst_2712_, v_pre_2713_, v_post_2714_, v_usedLetOnly_2715_, v_skipConstInApp_2716_, v_skipInstances_2717_, v_x_2718_, v_x_2719_, v_struct_2750_, v___y_2720_);
v___x_2756_ = lean_apply_4(v_toBind_2722_, lean_box(0), lean_box(0), v___x_2755_, v___f_2754_);
return v___x_2756_;
}
default: 
{
lean_object* v___x_2757_; 
lean_dec(v_toBind_2722_);
lean_dec(v___f_2721_);
v___x_2757_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2710_, v_inst_2711_, v_inst_2712_, v_pre_2713_, v_post_2714_, v_usedLetOnly_2715_, v_skipConstInApp_2716_, v_skipInstances_2717_, v_x_2718_, v_x_2719_, v___y_2726_, v___y_2720_);
return v___x_2757_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___boxed(lean_object* v_toApplicative_2765_, lean_object* v_inst_2766_, lean_object* v_inst_2767_, lean_object* v_inst_2768_, lean_object* v_pre_2769_, lean_object* v_post_2770_, lean_object* v_usedLetOnly_2771_, lean_object* v_skipConstInApp_2772_, lean_object* v_skipInstances_2773_, lean_object* v_x_2774_, lean_object* v_x_2775_, lean_object* v___y_2776_, lean_object* v___f_2777_, lean_object* v_toBind_2778_, lean_object* v_e_2779_, lean_object* v_a_2780_){
_start:
{
uint8_t v_usedLetOnly_boxed_2781_; uint8_t v_skipConstInApp_boxed_2782_; uint8_t v_skipInstances_boxed_2783_; lean_object* v_res_2784_; 
v_usedLetOnly_boxed_2781_ = lean_unbox(v_usedLetOnly_2771_);
v_skipConstInApp_boxed_2782_ = lean_unbox(v_skipConstInApp_2772_);
v_skipInstances_boxed_2783_ = lean_unbox(v_skipInstances_2773_);
v_res_2784_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11(v_toApplicative_2765_, v_inst_2766_, v_inst_2767_, v_inst_2768_, v_pre_2769_, v_post_2770_, v_usedLetOnly_boxed_2781_, v_skipConstInApp_boxed_2782_, v_skipInstances_boxed_2783_, v_x_2774_, v_x_2775_, v___y_2776_, v___f_2777_, v_toBind_2778_, v_e_2779_, v_a_2780_);
lean_dec(v___y_2776_);
return v_res_2784_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12(lean_object* v_toApplicative_2785_, lean_object* v_inst_2786_, lean_object* v_inst_2787_, lean_object* v_inst_2788_, lean_object* v_pre_2789_, lean_object* v_post_2790_, uint8_t v_usedLetOnly_2791_, uint8_t v_skipConstInApp_2792_, uint8_t v_skipInstances_2793_, lean_object* v_x_2794_, lean_object* v_x_2795_, lean_object* v___f_2796_, lean_object* v_toBind_2797_, lean_object* v_e_2798_, lean_object* v_____r_2799_, lean_object* v___y_2800_){
_start:
{
lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___f_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; 
v___x_2801_ = lean_box(v_usedLetOnly_2791_);
v___x_2802_ = lean_box(v_skipConstInApp_2792_);
v___x_2803_ = lean_box(v_skipInstances_2793_);
lean_inc_ref(v_e_2798_);
lean_inc(v_toBind_2797_);
lean_inc(v___y_2800_);
lean_inc(v_pre_2789_);
v___f_2804_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___boxed), 16, 15);
lean_closure_set(v___f_2804_, 0, v_toApplicative_2785_);
lean_closure_set(v___f_2804_, 1, v_inst_2786_);
lean_closure_set(v___f_2804_, 2, v_inst_2787_);
lean_closure_set(v___f_2804_, 3, v_inst_2788_);
lean_closure_set(v___f_2804_, 4, v_pre_2789_);
lean_closure_set(v___f_2804_, 5, v_post_2790_);
lean_closure_set(v___f_2804_, 6, v___x_2801_);
lean_closure_set(v___f_2804_, 7, v___x_2802_);
lean_closure_set(v___f_2804_, 8, v___x_2803_);
lean_closure_set(v___f_2804_, 9, v_x_2794_);
lean_closure_set(v___f_2804_, 10, v_x_2795_);
lean_closure_set(v___f_2804_, 11, v___y_2800_);
lean_closure_set(v___f_2804_, 12, v___f_2796_);
lean_closure_set(v___f_2804_, 13, v_toBind_2797_);
lean_closure_set(v___f_2804_, 14, v_e_2798_);
v___x_2805_ = lean_apply_1(v_pre_2789_, v_e_2798_);
v___x_2806_ = lean_apply_4(v_toBind_2797_, lean_box(0), lean_box(0), v___x_2805_, v___f_2804_);
return v___x_2806_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12___boxed(lean_object* v_toApplicative_2807_, lean_object* v_inst_2808_, lean_object* v_inst_2809_, lean_object* v_inst_2810_, lean_object* v_pre_2811_, lean_object* v_post_2812_, lean_object* v_usedLetOnly_2813_, lean_object* v_skipConstInApp_2814_, lean_object* v_skipInstances_2815_, lean_object* v_x_2816_, lean_object* v_x_2817_, lean_object* v___f_2818_, lean_object* v_toBind_2819_, lean_object* v_e_2820_, lean_object* v_____r_2821_, lean_object* v___y_2822_){
_start:
{
uint8_t v_usedLetOnly_boxed_2823_; uint8_t v_skipConstInApp_boxed_2824_; uint8_t v_skipInstances_boxed_2825_; lean_object* v_res_2826_; 
v_usedLetOnly_boxed_2823_ = lean_unbox(v_usedLetOnly_2813_);
v_skipConstInApp_boxed_2824_ = lean_unbox(v_skipConstInApp_2814_);
v_skipInstances_boxed_2825_ = lean_unbox(v_skipInstances_2815_);
v_res_2826_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12(v_toApplicative_2807_, v_inst_2808_, v_inst_2809_, v_inst_2810_, v_pre_2811_, v_post_2812_, v_usedLetOnly_boxed_2823_, v_skipConstInApp_boxed_2824_, v_skipInstances_boxed_2825_, v_x_2816_, v_x_2817_, v___f_2818_, v_toBind_2819_, v_e_2820_, v_____r_2821_, v___y_2822_);
lean_dec(v___y_2822_);
return v_res_2826_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(lean_object* v_inst_2827_, lean_object* v_inst_2828_, lean_object* v_inst_2829_, lean_object* v_pre_2830_, lean_object* v_post_2831_, uint8_t v_usedLetOnly_2832_, uint8_t v_skipConstInApp_2833_, uint8_t v_skipInstances_2834_, lean_object* v_x_2835_, lean_object* v_x_2836_, lean_object* v_e_2837_, lean_object* v_a_2838_){
_start:
{
lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___f_2843_; lean_object* v___f_2844_; lean_object* v___x_2845_; lean_object* v_toApplicative_2846_; lean_object* v_toBind_2847_; lean_object* v___f_2848_; lean_object* v___f_2849_; lean_object* v___f_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___f_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___f_2858_; lean_object* v___f_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; 
v___x_2839_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0));
v___x_2840_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1));
lean_inc_ref_n(v_inst_2827_, 3);
v___x_2841_ = l_Lean_MonadCacheT_instMonad___redArg(v_x_2835_, v___x_2839_, v___x_2840_, v_inst_2827_);
v___x_2842_ = l_Lean_MonadCacheT_instMonadControl___redArg(v_x_2835_, v___x_2839_, v___x_2840_);
lean_inc_ref_n(v_inst_2829_, 3);
lean_inc_ref(v___x_2842_);
v___f_2843_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_2843_, 0, v___x_2842_);
lean_closure_set(v___f_2843_, 1, v_inst_2829_);
v___f_2844_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_2844_, 0, v___x_2842_);
lean_closure_set(v___f_2844_, 1, v_inst_2829_);
v___x_2845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2845_, 0, v___f_2843_);
lean_ctor_set(v___x_2845_, 1, v___f_2844_);
v_toApplicative_2846_ = lean_ctor_get(v_inst_2827_, 0);
lean_inc_ref_n(v_toApplicative_2846_, 6);
v_toBind_2847_ = lean_ctor_get(v_inst_2827_, 1);
lean_inc_n(v_toBind_2847_, 6);
v___f_2848_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2848_, 0, v_toApplicative_2846_);
lean_inc_n(v_x_2836_, 3);
lean_inc_n(v_a_2838_, 3);
lean_inc_ref_n(v_e_2837_, 2);
v___f_2849_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_2849_, 0, v_toApplicative_2846_);
lean_closure_set(v___f_2849_, 1, v___x_2839_);
lean_closure_set(v___f_2849_, 2, v___x_2840_);
lean_closure_set(v___f_2849_, 3, v_e_2837_);
lean_closure_set(v___f_2849_, 4, v_a_2838_);
lean_closure_set(v___f_2849_, 5, v_x_2836_);
lean_closure_set(v___f_2849_, 6, v_toBind_2847_);
v___f_2850_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__3___boxed), 5, 4);
lean_closure_set(v___f_2850_, 0, v_toApplicative_2846_);
lean_closure_set(v___f_2850_, 1, v___x_2839_);
lean_closure_set(v___f_2850_, 2, v___x_2840_);
lean_closure_set(v___f_2850_, 3, v_e_2837_);
v___x_2851_ = lean_box(v_skipInstances_2834_);
v___x_2852_ = lean_box(v_usedLetOnly_2832_);
v___x_2853_ = lean_box(v_skipConstInApp_2833_);
lean_inc_ref(v___x_2841_);
lean_inc(v_post_2831_);
lean_inc(v_pre_2830_);
lean_inc_n(v_inst_2828_, 2);
v___f_2854_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__9___boxed), 17, 14);
lean_closure_set(v___f_2854_, 0, v___x_2851_);
lean_closure_set(v___f_2854_, 1, v_inst_2827_);
lean_closure_set(v___f_2854_, 2, v_inst_2828_);
lean_closure_set(v___f_2854_, 3, v_inst_2829_);
lean_closure_set(v___f_2854_, 4, v_pre_2830_);
lean_closure_set(v___f_2854_, 5, v_post_2831_);
lean_closure_set(v___f_2854_, 6, v___x_2852_);
lean_closure_set(v___f_2854_, 7, v___x_2853_);
lean_closure_set(v___f_2854_, 8, v_x_2835_);
lean_closure_set(v___f_2854_, 9, v_x_2836_);
lean_closure_set(v___f_2854_, 10, v___x_2841_);
lean_closure_set(v___f_2854_, 11, v_toBind_2847_);
lean_closure_set(v___f_2854_, 12, v_toApplicative_2846_);
lean_closure_set(v___f_2854_, 13, v___f_2848_);
v___x_2855_ = lean_box(v_usedLetOnly_2832_);
v___x_2856_ = lean_box(v_skipConstInApp_2833_);
v___x_2857_ = lean_box(v_skipInstances_2834_);
v___f_2858_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12___boxed), 16, 14);
lean_closure_set(v___f_2858_, 0, v_toApplicative_2846_);
lean_closure_set(v___f_2858_, 1, v_inst_2827_);
lean_closure_set(v___f_2858_, 2, v_inst_2828_);
lean_closure_set(v___f_2858_, 3, v_inst_2829_);
lean_closure_set(v___f_2858_, 4, v_pre_2830_);
lean_closure_set(v___f_2858_, 5, v_post_2831_);
lean_closure_set(v___f_2858_, 6, v___x_2855_);
lean_closure_set(v___f_2858_, 7, v___x_2856_);
lean_closure_set(v___f_2858_, 8, v___x_2857_);
lean_closure_set(v___f_2858_, 9, v_x_2835_);
lean_closure_set(v___f_2858_, 10, v_x_2836_);
lean_closure_set(v___f_2858_, 11, v___f_2854_);
lean_closure_set(v___f_2858_, 12, v_toBind_2847_);
lean_closure_set(v___f_2858_, 13, v_e_2837_);
v___f_2859_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14___boxed), 13, 12);
lean_closure_set(v___f_2859_, 0, v_inst_2828_);
lean_closure_set(v___f_2859_, 1, v_x_2835_);
lean_closure_set(v___f_2859_, 2, v___x_2839_);
lean_closure_set(v___f_2859_, 3, v___x_2840_);
lean_closure_set(v___f_2859_, 4, v_inst_2827_);
lean_closure_set(v___f_2859_, 5, v___f_2858_);
lean_closure_set(v___f_2859_, 6, v___x_2845_);
lean_closure_set(v___f_2859_, 7, v___x_2841_);
lean_closure_set(v___f_2859_, 8, v_a_2838_);
lean_closure_set(v___f_2859_, 9, v_toBind_2847_);
lean_closure_set(v___f_2859_, 10, v___f_2849_);
lean_closure_set(v___f_2859_, 11, v_toApplicative_2846_);
v___x_2860_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2860_, 0, lean_box(0));
lean_closure_set(v___x_2860_, 1, lean_box(0));
lean_closure_set(v___x_2860_, 2, v_a_2838_);
v___x_2861_ = lean_apply_2(v_x_2836_, lean_box(0), v___x_2860_);
v___x_2862_ = lean_apply_4(v_toBind_2847_, lean_box(0), lean_box(0), v___x_2861_, v___f_2850_);
v___x_2863_ = lean_apply_4(v_toBind_2847_, lean_box(0), lean_box(0), v___x_2862_, v___f_2859_);
return v___x_2863_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___lam__0(lean_object* v_toApplicative_2864_, lean_object* v_inst_2865_, lean_object* v_inst_2866_, lean_object* v_inst_2867_, lean_object* v_pre_2868_, lean_object* v_post_2869_, uint8_t v_usedLetOnly_2870_, uint8_t v_skipConstInApp_2871_, uint8_t v_skipInstances_2872_, lean_object* v_x_2873_, lean_object* v_x_2874_, lean_object* v_a_2875_, lean_object* v_e_2876_, lean_object* v_a_2877_){
_start:
{
lean_object* v___y_2879_; 
switch(lean_obj_tag(v_a_2877_))
{
case 0:
{
lean_object* v_e_2882_; lean_object* v_toPure_2883_; lean_object* v___x_2884_; 
lean_dec_ref(v_e_2876_);
lean_dec(v_x_2874_);
lean_dec(v_post_2869_);
lean_dec(v_pre_2868_);
lean_dec_ref(v_inst_2867_);
lean_dec(v_inst_2866_);
lean_dec_ref(v_inst_2865_);
v_e_2882_ = lean_ctor_get(v_a_2877_, 0);
lean_inc_ref(v_e_2882_);
lean_dec_ref(v_a_2877_);
v_toPure_2883_ = lean_ctor_get(v_toApplicative_2864_, 1);
lean_inc(v_toPure_2883_);
lean_dec_ref(v_toApplicative_2864_);
v___x_2884_ = lean_apply_2(v_toPure_2883_, lean_box(0), v_e_2882_);
return v___x_2884_;
}
case 1:
{
lean_object* v_e_2885_; lean_object* v___x_2886_; 
lean_dec_ref(v_e_2876_);
lean_dec_ref(v_toApplicative_2864_);
v_e_2885_ = lean_ctor_get(v_a_2877_, 0);
lean_inc_ref(v_e_2885_);
lean_dec_ref(v_a_2877_);
v___x_2886_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2865_, v_inst_2866_, v_inst_2867_, v_pre_2868_, v_post_2869_, v_usedLetOnly_2870_, v_skipConstInApp_2871_, v_skipInstances_2872_, v_x_2873_, v_x_2874_, v_e_2885_, v_a_2875_);
return v___x_2886_;
}
default: 
{
lean_object* v_e_x3f_2887_; 
lean_dec(v_x_2874_);
lean_dec(v_post_2869_);
lean_dec(v_pre_2868_);
lean_dec_ref(v_inst_2867_);
lean_dec(v_inst_2866_);
lean_dec_ref(v_inst_2865_);
v_e_x3f_2887_ = lean_ctor_get(v_a_2877_, 0);
lean_inc(v_e_x3f_2887_);
lean_dec_ref(v_a_2877_);
if (lean_obj_tag(v_e_x3f_2887_) == 0)
{
v___y_2879_ = v_e_2876_;
goto v___jp_2878_;
}
else
{
lean_object* v_val_2888_; 
lean_dec_ref(v_e_2876_);
v_val_2888_ = lean_ctor_get(v_e_x3f_2887_, 0);
lean_inc(v_val_2888_);
lean_dec_ref(v_e_x3f_2887_);
v___y_2879_ = v_val_2888_;
goto v___jp_2878_;
}
}
}
v___jp_2878_:
{
lean_object* v_toPure_2880_; lean_object* v___x_2881_; 
v_toPure_2880_ = lean_ctor_get(v_toApplicative_2864_, 1);
lean_inc(v_toPure_2880_);
lean_dec_ref(v_toApplicative_2864_);
v___x_2881_ = lean_apply_2(v_toPure_2880_, lean_box(0), v___y_2879_);
return v___x_2881_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___lam__0___boxed(lean_object* v_toApplicative_2889_, lean_object* v_inst_2890_, lean_object* v_inst_2891_, lean_object* v_inst_2892_, lean_object* v_pre_2893_, lean_object* v_post_2894_, lean_object* v_usedLetOnly_2895_, lean_object* v_skipConstInApp_2896_, lean_object* v_skipInstances_2897_, lean_object* v_x_2898_, lean_object* v_x_2899_, lean_object* v_a_2900_, lean_object* v_e_2901_, lean_object* v_a_2902_){
_start:
{
uint8_t v_usedLetOnly_boxed_2903_; uint8_t v_skipConstInApp_boxed_2904_; uint8_t v_skipInstances_boxed_2905_; lean_object* v_res_2906_; 
v_usedLetOnly_boxed_2903_ = lean_unbox(v_usedLetOnly_2895_);
v_skipConstInApp_boxed_2904_ = lean_unbox(v_skipConstInApp_2896_);
v_skipInstances_boxed_2905_ = lean_unbox(v_skipInstances_2897_);
v_res_2906_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___lam__0(v_toApplicative_2889_, v_inst_2890_, v_inst_2891_, v_inst_2892_, v_pre_2893_, v_post_2894_, v_usedLetOnly_boxed_2903_, v_skipConstInApp_boxed_2904_, v_skipInstances_boxed_2905_, v_x_2898_, v_x_2899_, v_a_2900_, v_e_2901_, v_a_2902_);
lean_dec(v_a_2900_);
return v_res_2906_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(lean_object* v_inst_2907_, lean_object* v_inst_2908_, lean_object* v_inst_2909_, lean_object* v_pre_2910_, lean_object* v_post_2911_, uint8_t v_usedLetOnly_2912_, uint8_t v_skipConstInApp_2913_, uint8_t v_skipInstances_2914_, lean_object* v_x_2915_, lean_object* v_x_2916_, lean_object* v_e_2917_, lean_object* v_a_2918_){
_start:
{
lean_object* v_toApplicative_2919_; lean_object* v_toBind_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___f_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; 
v_toApplicative_2919_ = lean_ctor_get(v_inst_2907_, 0);
lean_inc_ref(v_toApplicative_2919_);
v_toBind_2920_ = lean_ctor_get(v_inst_2907_, 1);
lean_inc(v_toBind_2920_);
v___x_2921_ = lean_box(v_usedLetOnly_2912_);
v___x_2922_ = lean_box(v_skipConstInApp_2913_);
v___x_2923_ = lean_box(v_skipInstances_2914_);
lean_inc_ref(v_e_2917_);
lean_inc(v_a_2918_);
lean_inc(v_post_2911_);
v___f_2924_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___lam__0___boxed), 14, 13);
lean_closure_set(v___f_2924_, 0, v_toApplicative_2919_);
lean_closure_set(v___f_2924_, 1, v_inst_2907_);
lean_closure_set(v___f_2924_, 2, v_inst_2908_);
lean_closure_set(v___f_2924_, 3, v_inst_2909_);
lean_closure_set(v___f_2924_, 4, v_pre_2910_);
lean_closure_set(v___f_2924_, 5, v_post_2911_);
lean_closure_set(v___f_2924_, 6, v___x_2921_);
lean_closure_set(v___f_2924_, 7, v___x_2922_);
lean_closure_set(v___f_2924_, 8, v___x_2923_);
lean_closure_set(v___f_2924_, 9, v_x_2915_);
lean_closure_set(v___f_2924_, 10, v_x_2916_);
lean_closure_set(v___f_2924_, 11, v_a_2918_);
lean_closure_set(v___f_2924_, 12, v_e_2917_);
v___x_2925_ = lean_apply_1(v_post_2911_, v_e_2917_);
v___x_2926_ = lean_apply_4(v_toBind_2920_, lean_box(0), lean_box(0), v___x_2925_, v___f_2924_);
return v___x_2926_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3(lean_object* v_inst_2927_, lean_object* v_inst_2928_, lean_object* v_inst_2929_, lean_object* v_pre_2930_, lean_object* v_post_2931_, uint8_t v_usedLetOnly_2932_, uint8_t v_skipConstInApp_2933_, uint8_t v_skipInstances_2934_, lean_object* v_x_2935_, lean_object* v_x_2936_, lean_object* v_a_2937_, lean_object* v_a_2938_){
_start:
{
lean_object* v___x_2939_; 
v___x_2939_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2927_, v_inst_2928_, v_inst_2929_, v_pre_2930_, v_post_2931_, v_usedLetOnly_2932_, v_skipConstInApp_2933_, v_skipInstances_2934_, v_x_2935_, v_x_2936_, v_a_2938_, v_a_2937_);
return v___x_2939_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___boxed(lean_object* v_inst_2940_, lean_object* v_inst_2941_, lean_object* v_inst_2942_, lean_object* v_pre_2943_, lean_object* v_post_2944_, lean_object* v_usedLetOnly_2945_, lean_object* v_skipConstInApp_2946_, lean_object* v_skipInstances_2947_, lean_object* v_x_2948_, lean_object* v_x_2949_, lean_object* v_e_2950_, lean_object* v_a_2951_){
_start:
{
uint8_t v_usedLetOnly_boxed_2952_; uint8_t v_skipConstInApp_boxed_2953_; uint8_t v_skipInstances_boxed_2954_; lean_object* v_res_2955_; 
v_usedLetOnly_boxed_2952_ = lean_unbox(v_usedLetOnly_2945_);
v_skipConstInApp_boxed_2953_ = lean_unbox(v_skipConstInApp_2946_);
v_skipInstances_boxed_2954_ = lean_unbox(v_skipInstances_2947_);
v_res_2955_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2940_, v_inst_2941_, v_inst_2942_, v_pre_2943_, v_post_2944_, v_usedLetOnly_boxed_2952_, v_skipConstInApp_boxed_2953_, v_skipInstances_boxed_2954_, v_x_2948_, v_x_2949_, v_e_2950_, v_a_2951_);
lean_dec(v_a_2951_);
return v_res_2955_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___boxed(lean_object* v_inst_2956_, lean_object* v_inst_2957_, lean_object* v_inst_2958_, lean_object* v_pre_2959_, lean_object* v_post_2960_, lean_object* v_usedLetOnly_2961_, lean_object* v_skipConstInApp_2962_, lean_object* v_skipInstances_2963_, lean_object* v_x_2964_, lean_object* v_x_2965_, lean_object* v_fvars_2966_, lean_object* v_e_2967_, lean_object* v_a_2968_){
_start:
{
uint8_t v_usedLetOnly_boxed_2969_; uint8_t v_skipConstInApp_boxed_2970_; uint8_t v_skipInstances_boxed_2971_; lean_object* v_res_2972_; 
v_usedLetOnly_boxed_2969_ = lean_unbox(v_usedLetOnly_2961_);
v_skipConstInApp_boxed_2970_ = lean_unbox(v_skipConstInApp_2962_);
v_skipInstances_boxed_2971_ = lean_unbox(v_skipInstances_2963_);
v_res_2972_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(v_inst_2956_, v_inst_2957_, v_inst_2958_, v_pre_2959_, v_post_2960_, v_usedLetOnly_boxed_2969_, v_skipConstInApp_boxed_2970_, v_skipInstances_boxed_2971_, v_x_2964_, v_x_2965_, v_fvars_2966_, v_e_2967_, v_a_2968_);
lean_dec(v_a_2968_);
return v_res_2972_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___boxed(lean_object* v_inst_2973_, lean_object* v_inst_2974_, lean_object* v_inst_2975_, lean_object* v_pre_2976_, lean_object* v_post_2977_, lean_object* v_usedLetOnly_2978_, lean_object* v_skipConstInApp_2979_, lean_object* v_skipInstances_2980_, lean_object* v_x_2981_, lean_object* v_x_2982_, lean_object* v_fvars_2983_, lean_object* v_e_2984_, lean_object* v_a_2985_){
_start:
{
uint8_t v_usedLetOnly_boxed_2986_; uint8_t v_skipConstInApp_boxed_2987_; uint8_t v_skipInstances_boxed_2988_; lean_object* v_res_2989_; 
v_usedLetOnly_boxed_2986_ = lean_unbox(v_usedLetOnly_2978_);
v_skipConstInApp_boxed_2987_ = lean_unbox(v_skipConstInApp_2979_);
v_skipInstances_boxed_2988_ = lean_unbox(v_skipInstances_2980_);
v_res_2989_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(v_inst_2973_, v_inst_2974_, v_inst_2975_, v_pre_2976_, v_post_2977_, v_usedLetOnly_boxed_2986_, v_skipConstInApp_boxed_2987_, v_skipInstances_boxed_2988_, v_x_2981_, v_x_2982_, v_fvars_2983_, v_e_2984_, v_a_2985_);
lean_dec(v_a_2985_);
return v_res_2989_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___boxed(lean_object* v_inst_2990_, lean_object* v_inst_2991_, lean_object* v_inst_2992_, lean_object* v_pre_2993_, lean_object* v_post_2994_, lean_object* v_usedLetOnly_2995_, lean_object* v_skipConstInApp_2996_, lean_object* v_skipInstances_2997_, lean_object* v_x_2998_, lean_object* v_x_2999_, lean_object* v_fvars_3000_, lean_object* v_e_3001_, lean_object* v_a_3002_){
_start:
{
uint8_t v_usedLetOnly_boxed_3003_; uint8_t v_skipConstInApp_boxed_3004_; uint8_t v_skipInstances_boxed_3005_; lean_object* v_res_3006_; 
v_usedLetOnly_boxed_3003_ = lean_unbox(v_usedLetOnly_2995_);
v_skipConstInApp_boxed_3004_ = lean_unbox(v_skipConstInApp_2996_);
v_skipInstances_boxed_3005_ = lean_unbox(v_skipInstances_2997_);
v_res_3006_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(v_inst_2990_, v_inst_2991_, v_inst_2992_, v_pre_2993_, v_post_2994_, v_usedLetOnly_boxed_3003_, v_skipConstInApp_boxed_3004_, v_skipInstances_boxed_3005_, v_x_2998_, v_x_2999_, v_fvars_3000_, v_e_3001_, v_a_3002_);
lean_dec(v_a_3002_);
return v_res_3006_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit(lean_object* v_m_3007_, lean_object* v_inst_3008_, lean_object* v_inst_3009_, lean_object* v_inst_3010_, lean_object* v_pre_3011_, lean_object* v_post_3012_, uint8_t v_usedLetOnly_3013_, uint8_t v_skipConstInApp_3014_, uint8_t v_skipInstances_3015_, lean_object* v_x_3016_, lean_object* v_x_3017_, lean_object* v_e_3018_, lean_object* v_a_3019_){
_start:
{
lean_object* v___x_3020_; 
v___x_3020_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_3008_, v_inst_3009_, v_inst_3010_, v_pre_3011_, v_post_3012_, v_usedLetOnly_3013_, v_skipConstInApp_3014_, v_skipInstances_3015_, v_x_3016_, v_x_3017_, v_e_3018_, v_a_3019_);
return v___x_3020_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___boxed(lean_object* v_m_3021_, lean_object* v_inst_3022_, lean_object* v_inst_3023_, lean_object* v_inst_3024_, lean_object* v_pre_3025_, lean_object* v_post_3026_, lean_object* v_usedLetOnly_3027_, lean_object* v_skipConstInApp_3028_, lean_object* v_skipInstances_3029_, lean_object* v_x_3030_, lean_object* v_x_3031_, lean_object* v_e_3032_, lean_object* v_a_3033_){
_start:
{
uint8_t v_usedLetOnly_boxed_3034_; uint8_t v_skipConstInApp_boxed_3035_; uint8_t v_skipInstances_boxed_3036_; lean_object* v_res_3037_; 
v_usedLetOnly_boxed_3034_ = lean_unbox(v_usedLetOnly_3027_);
v_skipConstInApp_boxed_3035_ = lean_unbox(v_skipConstInApp_3028_);
v_skipInstances_boxed_3036_ = lean_unbox(v_skipInstances_3029_);
v_res_3037_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit(v_m_3021_, v_inst_3022_, v_inst_3023_, v_inst_3024_, v_pre_3025_, v_post_3026_, v_usedLetOnly_boxed_3034_, v_skipConstInApp_boxed_3035_, v_skipInstances_boxed_3036_, v_x_3030_, v_x_3031_, v_e_3032_, v_a_3033_);
lean_dec(v_a_3033_);
return v_res_3037_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet(lean_object* v_m_3038_, lean_object* v_inst_3039_, lean_object* v_inst_3040_, lean_object* v_inst_3041_, lean_object* v_pre_3042_, lean_object* v_post_3043_, uint8_t v_usedLetOnly_3044_, uint8_t v_skipConstInApp_3045_, uint8_t v_skipInstances_3046_, lean_object* v_x_3047_, lean_object* v_x_3048_, lean_object* v_fvars_3049_, lean_object* v_e_3050_, lean_object* v_a_3051_){
_start:
{
lean_object* v___x_3052_; 
v___x_3052_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(v_inst_3039_, v_inst_3040_, v_inst_3041_, v_pre_3042_, v_post_3043_, v_usedLetOnly_3044_, v_skipConstInApp_3045_, v_skipInstances_3046_, v_x_3047_, v_x_3048_, v_fvars_3049_, v_e_3050_, v_a_3051_);
return v___x_3052_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___boxed(lean_object* v_m_3053_, lean_object* v_inst_3054_, lean_object* v_inst_3055_, lean_object* v_inst_3056_, lean_object* v_pre_3057_, lean_object* v_post_3058_, lean_object* v_usedLetOnly_3059_, lean_object* v_skipConstInApp_3060_, lean_object* v_skipInstances_3061_, lean_object* v_x_3062_, lean_object* v_x_3063_, lean_object* v_fvars_3064_, lean_object* v_e_3065_, lean_object* v_a_3066_){
_start:
{
uint8_t v_usedLetOnly_boxed_3067_; uint8_t v_skipConstInApp_boxed_3068_; uint8_t v_skipInstances_boxed_3069_; lean_object* v_res_3070_; 
v_usedLetOnly_boxed_3067_ = lean_unbox(v_usedLetOnly_3059_);
v_skipConstInApp_boxed_3068_ = lean_unbox(v_skipConstInApp_3060_);
v_skipInstances_boxed_3069_ = lean_unbox(v_skipInstances_3061_);
v_res_3070_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet(v_m_3053_, v_inst_3054_, v_inst_3055_, v_inst_3056_, v_pre_3057_, v_post_3058_, v_usedLetOnly_boxed_3067_, v_skipConstInApp_boxed_3068_, v_skipInstances_boxed_3069_, v_x_3062_, v_x_3063_, v_fvars_3064_, v_e_3065_, v_a_3066_);
lean_dec(v_a_3066_);
return v_res_3070_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost(lean_object* v_m_3071_, lean_object* v_inst_3072_, lean_object* v_inst_3073_, lean_object* v_inst_3074_, lean_object* v_pre_3075_, lean_object* v_post_3076_, uint8_t v_usedLetOnly_3077_, uint8_t v_skipConstInApp_3078_, uint8_t v_skipInstances_3079_, lean_object* v_x_3080_, lean_object* v_x_3081_, lean_object* v_e_3082_, lean_object* v_a_3083_){
_start:
{
lean_object* v___x_3084_; 
v___x_3084_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_3072_, v_inst_3073_, v_inst_3074_, v_pre_3075_, v_post_3076_, v_usedLetOnly_3077_, v_skipConstInApp_3078_, v_skipInstances_3079_, v_x_3080_, v_x_3081_, v_e_3082_, v_a_3083_);
return v___x_3084_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___boxed(lean_object* v_m_3085_, lean_object* v_inst_3086_, lean_object* v_inst_3087_, lean_object* v_inst_3088_, lean_object* v_pre_3089_, lean_object* v_post_3090_, lean_object* v_usedLetOnly_3091_, lean_object* v_skipConstInApp_3092_, lean_object* v_skipInstances_3093_, lean_object* v_x_3094_, lean_object* v_x_3095_, lean_object* v_e_3096_, lean_object* v_a_3097_){
_start:
{
uint8_t v_usedLetOnly_boxed_3098_; uint8_t v_skipConstInApp_boxed_3099_; uint8_t v_skipInstances_boxed_3100_; lean_object* v_res_3101_; 
v_usedLetOnly_boxed_3098_ = lean_unbox(v_usedLetOnly_3091_);
v_skipConstInApp_boxed_3099_ = lean_unbox(v_skipConstInApp_3092_);
v_skipInstances_boxed_3100_ = lean_unbox(v_skipInstances_3093_);
v_res_3101_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost(v_m_3085_, v_inst_3086_, v_inst_3087_, v_inst_3088_, v_pre_3089_, v_post_3090_, v_usedLetOnly_boxed_3098_, v_skipConstInApp_boxed_3099_, v_skipInstances_boxed_3100_, v_x_3094_, v_x_3095_, v_e_3096_, v_a_3097_);
lean_dec(v_a_3097_);
return v_res_3101_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda(lean_object* v_m_3102_, lean_object* v_inst_3103_, lean_object* v_inst_3104_, lean_object* v_inst_3105_, lean_object* v_pre_3106_, lean_object* v_post_3107_, uint8_t v_usedLetOnly_3108_, uint8_t v_skipConstInApp_3109_, uint8_t v_skipInstances_3110_, lean_object* v_x_3111_, lean_object* v_x_3112_, lean_object* v_fvars_3113_, lean_object* v_e_3114_, lean_object* v_a_3115_){
_start:
{
lean_object* v___x_3116_; 
v___x_3116_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(v_inst_3103_, v_inst_3104_, v_inst_3105_, v_pre_3106_, v_post_3107_, v_usedLetOnly_3108_, v_skipConstInApp_3109_, v_skipInstances_3110_, v_x_3111_, v_x_3112_, v_fvars_3113_, v_e_3114_, v_a_3115_);
return v___x_3116_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___boxed(lean_object* v_m_3117_, lean_object* v_inst_3118_, lean_object* v_inst_3119_, lean_object* v_inst_3120_, lean_object* v_pre_3121_, lean_object* v_post_3122_, lean_object* v_usedLetOnly_3123_, lean_object* v_skipConstInApp_3124_, lean_object* v_skipInstances_3125_, lean_object* v_x_3126_, lean_object* v_x_3127_, lean_object* v_fvars_3128_, lean_object* v_e_3129_, lean_object* v_a_3130_){
_start:
{
uint8_t v_usedLetOnly_boxed_3131_; uint8_t v_skipConstInApp_boxed_3132_; uint8_t v_skipInstances_boxed_3133_; lean_object* v_res_3134_; 
v_usedLetOnly_boxed_3131_ = lean_unbox(v_usedLetOnly_3123_);
v_skipConstInApp_boxed_3132_ = lean_unbox(v_skipConstInApp_3124_);
v_skipInstances_boxed_3133_ = lean_unbox(v_skipInstances_3125_);
v_res_3134_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda(v_m_3117_, v_inst_3118_, v_inst_3119_, v_inst_3120_, v_pre_3121_, v_post_3122_, v_usedLetOnly_boxed_3131_, v_skipConstInApp_boxed_3132_, v_skipInstances_boxed_3133_, v_x_3126_, v_x_3127_, v_fvars_3128_, v_e_3129_, v_a_3130_);
lean_dec(v_a_3130_);
return v_res_3134_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall(lean_object* v_m_3135_, lean_object* v_inst_3136_, lean_object* v_inst_3137_, lean_object* v_inst_3138_, lean_object* v_pre_3139_, lean_object* v_post_3140_, uint8_t v_usedLetOnly_3141_, uint8_t v_skipConstInApp_3142_, uint8_t v_skipInstances_3143_, lean_object* v_x_3144_, lean_object* v_x_3145_, lean_object* v_fvars_3146_, lean_object* v_e_3147_, lean_object* v_a_3148_){
_start:
{
lean_object* v___x_3149_; 
v___x_3149_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(v_inst_3136_, v_inst_3137_, v_inst_3138_, v_pre_3139_, v_post_3140_, v_usedLetOnly_3141_, v_skipConstInApp_3142_, v_skipInstances_3143_, v_x_3144_, v_x_3145_, v_fvars_3146_, v_e_3147_, v_a_3148_);
return v___x_3149_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___boxed(lean_object* v_m_3150_, lean_object* v_inst_3151_, lean_object* v_inst_3152_, lean_object* v_inst_3153_, lean_object* v_pre_3154_, lean_object* v_post_3155_, lean_object* v_usedLetOnly_3156_, lean_object* v_skipConstInApp_3157_, lean_object* v_skipInstances_3158_, lean_object* v_x_3159_, lean_object* v_x_3160_, lean_object* v_fvars_3161_, lean_object* v_e_3162_, lean_object* v_a_3163_){
_start:
{
uint8_t v_usedLetOnly_boxed_3164_; uint8_t v_skipConstInApp_boxed_3165_; uint8_t v_skipInstances_boxed_3166_; lean_object* v_res_3167_; 
v_usedLetOnly_boxed_3164_ = lean_unbox(v_usedLetOnly_3156_);
v_skipConstInApp_boxed_3165_ = lean_unbox(v_skipConstInApp_3157_);
v_skipInstances_boxed_3166_ = lean_unbox(v_skipInstances_3158_);
v_res_3167_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall(v_m_3150_, v_inst_3151_, v_inst_3152_, v_inst_3153_, v_pre_3154_, v_post_3155_, v_usedLetOnly_boxed_3164_, v_skipConstInApp_boxed_3165_, v_skipInstances_boxed_3166_, v_x_3159_, v_x_3160_, v_fvars_3161_, v_e_3162_, v_a_3163_);
lean_dec(v_a_3163_);
return v_res_3167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__0(lean_object* v_x_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_){
_start:
{
lean_object* v___x_3174_; lean_object* v___x_3175_; 
v___x_3174_ = lean_apply_1(v_x_3168_, lean_box(0));
v___x_3175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3175_, 0, v___x_3174_);
return v___x_3175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__0___boxed(lean_object* v_x_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_){
_start:
{
lean_object* v_res_3182_; 
v_res_3182_ = l_Lean_Meta_transformWithCache___redArg___lam__0(v_x_3176_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_);
lean_dec(v___y_3180_);
lean_dec_ref(v___y_3179_);
lean_dec(v___y_3178_);
lean_dec_ref(v___y_3177_);
return v_res_3182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__1(lean_object* v_inst_3183_, lean_object* v_00_u03b1_3184_, lean_object* v_x_3185_){
_start:
{
lean_object* v___f_3186_; lean_object* v___x_3187_; 
v___f_3186_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_3186_, 0, v_x_3185_);
v___x_3187_ = lean_apply_2(v_inst_3183_, lean_box(0), v___f_3186_);
return v___x_3187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__4(lean_object* v_toPure_3188_, lean_object* v_x_3189_, lean_object* v_toBind_3190_, lean_object* v_inst_3191_, lean_object* v_inst_3192_, lean_object* v_inst_3193_, lean_object* v_pre_3194_, lean_object* v_post_3195_, uint8_t v_usedLetOnly_3196_, uint8_t v_skipConstInApp_3197_, uint8_t v_skipInstances_3198_, lean_object* v_x_3199_, lean_object* v_input_3200_, lean_object* v_ref_3201_){
_start:
{
lean_object* v___f_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; 
lean_inc(v_toBind_3190_);
lean_inc(v_x_3189_);
lean_inc(v_ref_3201_);
v___f_3202_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__4), 5, 4);
lean_closure_set(v___f_3202_, 0, v_toPure_3188_);
lean_closure_set(v___f_3202_, 1, v_ref_3201_);
lean_closure_set(v___f_3202_, 2, v_x_3189_);
lean_closure_set(v___f_3202_, 3, v_toBind_3190_);
v___x_3203_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_3191_, v_inst_3192_, v_inst_3193_, v_pre_3194_, v_post_3195_, v_usedLetOnly_3196_, v_skipConstInApp_3197_, v_skipInstances_3198_, v_x_3199_, v_x_3189_, v_input_3200_, v_ref_3201_);
lean_dec(v_ref_3201_);
v___x_3204_ = lean_apply_4(v_toBind_3190_, lean_box(0), lean_box(0), v___x_3203_, v___f_3202_);
return v___x_3204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__4___boxed(lean_object* v_toPure_3205_, lean_object* v_x_3206_, lean_object* v_toBind_3207_, lean_object* v_inst_3208_, lean_object* v_inst_3209_, lean_object* v_inst_3210_, lean_object* v_pre_3211_, lean_object* v_post_3212_, lean_object* v_usedLetOnly_3213_, lean_object* v_skipConstInApp_3214_, lean_object* v_skipInstances_3215_, lean_object* v_x_3216_, lean_object* v_input_3217_, lean_object* v_ref_3218_){
_start:
{
uint8_t v_usedLetOnly_boxed_3219_; uint8_t v_skipConstInApp_boxed_3220_; uint8_t v_skipInstances_boxed_3221_; lean_object* v_res_3222_; 
v_usedLetOnly_boxed_3219_ = lean_unbox(v_usedLetOnly_3213_);
v_skipConstInApp_boxed_3220_ = lean_unbox(v_skipConstInApp_3214_);
v_skipInstances_boxed_3221_ = lean_unbox(v_skipInstances_3215_);
v_res_3222_ = l_Lean_Meta_transformWithCache___redArg___lam__4(v_toPure_3205_, v_x_3206_, v_toBind_3207_, v_inst_3208_, v_inst_3209_, v_inst_3210_, v_pre_3211_, v_post_3212_, v_usedLetOnly_boxed_3219_, v_skipConstInApp_boxed_3220_, v_skipInstances_boxed_3221_, v_x_3216_, v_input_3217_, v_ref_3218_);
return v_res_3222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg(lean_object* v_inst_3223_, lean_object* v_inst_3224_, lean_object* v_inst_3225_, lean_object* v_input_3226_, lean_object* v_cache_3227_, lean_object* v_pre_3228_, lean_object* v_post_3229_, uint8_t v_usedLetOnly_3230_, uint8_t v_skipConstInApp_3231_, uint8_t v_skipInstances_3232_){
_start:
{
lean_object* v_x_3233_; lean_object* v_toApplicative_3234_; lean_object* v_toBind_3235_; lean_object* v_toPure_3236_; lean_object* v_x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___f_3243_; lean_object* v___x_3244_; 
v_x_3233_ = lean_box(0);
v_toApplicative_3234_ = lean_ctor_get(v_inst_3223_, 0);
v_toBind_3235_ = lean_ctor_get(v_inst_3223_, 1);
lean_inc_n(v_toBind_3235_, 2);
v_toPure_3236_ = lean_ctor_get(v_toApplicative_3234_, 1);
lean_inc(v_toPure_3236_);
lean_inc_n(v_inst_3224_, 2);
v_x_3237_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__1), 3, 1);
lean_closure_set(v_x_3237_, 0, v_inst_3224_);
v___x_3238_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_3238_, 0, lean_box(0));
lean_closure_set(v___x_3238_, 1, lean_box(0));
lean_closure_set(v___x_3238_, 2, v_cache_3227_);
v___x_3239_ = l_Lean_Meta_transformWithCache___redArg___lam__1(v_inst_3224_, lean_box(0), v___x_3238_);
v___x_3240_ = lean_box(v_usedLetOnly_3230_);
v___x_3241_ = lean_box(v_skipConstInApp_3231_);
v___x_3242_ = lean_box(v_skipInstances_3232_);
v___f_3243_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__4___boxed), 14, 13);
lean_closure_set(v___f_3243_, 0, v_toPure_3236_);
lean_closure_set(v___f_3243_, 1, v_x_3237_);
lean_closure_set(v___f_3243_, 2, v_toBind_3235_);
lean_closure_set(v___f_3243_, 3, v_inst_3223_);
lean_closure_set(v___f_3243_, 4, v_inst_3224_);
lean_closure_set(v___f_3243_, 5, v_inst_3225_);
lean_closure_set(v___f_3243_, 6, v_pre_3228_);
lean_closure_set(v___f_3243_, 7, v_post_3229_);
lean_closure_set(v___f_3243_, 8, v___x_3240_);
lean_closure_set(v___f_3243_, 9, v___x_3241_);
lean_closure_set(v___f_3243_, 10, v___x_3242_);
lean_closure_set(v___f_3243_, 11, v_x_3233_);
lean_closure_set(v___f_3243_, 12, v_input_3226_);
v___x_3244_ = lean_apply_4(v_toBind_3235_, lean_box(0), lean_box(0), v___x_3239_, v___f_3243_);
return v___x_3244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___boxed(lean_object* v_inst_3245_, lean_object* v_inst_3246_, lean_object* v_inst_3247_, lean_object* v_input_3248_, lean_object* v_cache_3249_, lean_object* v_pre_3250_, lean_object* v_post_3251_, lean_object* v_usedLetOnly_3252_, lean_object* v_skipConstInApp_3253_, lean_object* v_skipInstances_3254_){
_start:
{
uint8_t v_usedLetOnly_boxed_3255_; uint8_t v_skipConstInApp_boxed_3256_; uint8_t v_skipInstances_boxed_3257_; lean_object* v_res_3258_; 
v_usedLetOnly_boxed_3255_ = lean_unbox(v_usedLetOnly_3252_);
v_skipConstInApp_boxed_3256_ = lean_unbox(v_skipConstInApp_3253_);
v_skipInstances_boxed_3257_ = lean_unbox(v_skipInstances_3254_);
v_res_3258_ = l_Lean_Meta_transformWithCache___redArg(v_inst_3245_, v_inst_3246_, v_inst_3247_, v_input_3248_, v_cache_3249_, v_pre_3250_, v_post_3251_, v_usedLetOnly_boxed_3255_, v_skipConstInApp_boxed_3256_, v_skipInstances_boxed_3257_);
return v_res_3258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache(lean_object* v_m_3259_, lean_object* v_inst_3260_, lean_object* v_inst_3261_, lean_object* v_inst_3262_, lean_object* v_input_3263_, lean_object* v_cache_3264_, lean_object* v_pre_3265_, lean_object* v_post_3266_, uint8_t v_usedLetOnly_3267_, uint8_t v_skipConstInApp_3268_, uint8_t v_skipInstances_3269_){
_start:
{
lean_object* v_x_3270_; lean_object* v_toApplicative_3271_; lean_object* v_toBind_3272_; lean_object* v_toPure_3273_; lean_object* v_x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___f_3280_; lean_object* v___x_3281_; 
v_x_3270_ = lean_box(0);
v_toApplicative_3271_ = lean_ctor_get(v_inst_3260_, 0);
v_toBind_3272_ = lean_ctor_get(v_inst_3260_, 1);
lean_inc_n(v_toBind_3272_, 2);
v_toPure_3273_ = lean_ctor_get(v_toApplicative_3271_, 1);
lean_inc(v_toPure_3273_);
lean_inc_n(v_inst_3261_, 2);
v_x_3274_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__1), 3, 1);
lean_closure_set(v_x_3274_, 0, v_inst_3261_);
v___x_3275_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_3275_, 0, lean_box(0));
lean_closure_set(v___x_3275_, 1, lean_box(0));
lean_closure_set(v___x_3275_, 2, v_cache_3264_);
v___x_3276_ = l_Lean_Meta_transformWithCache___redArg___lam__1(v_inst_3261_, lean_box(0), v___x_3275_);
v___x_3277_ = lean_box(v_usedLetOnly_3267_);
v___x_3278_ = lean_box(v_skipConstInApp_3268_);
v___x_3279_ = lean_box(v_skipInstances_3269_);
v___f_3280_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__4___boxed), 14, 13);
lean_closure_set(v___f_3280_, 0, v_toPure_3273_);
lean_closure_set(v___f_3280_, 1, v_x_3274_);
lean_closure_set(v___f_3280_, 2, v_toBind_3272_);
lean_closure_set(v___f_3280_, 3, v_inst_3260_);
lean_closure_set(v___f_3280_, 4, v_inst_3261_);
lean_closure_set(v___f_3280_, 5, v_inst_3262_);
lean_closure_set(v___f_3280_, 6, v_pre_3265_);
lean_closure_set(v___f_3280_, 7, v_post_3266_);
lean_closure_set(v___f_3280_, 8, v___x_3277_);
lean_closure_set(v___f_3280_, 9, v___x_3278_);
lean_closure_set(v___f_3280_, 10, v___x_3279_);
lean_closure_set(v___f_3280_, 11, v_x_3270_);
lean_closure_set(v___f_3280_, 12, v_input_3263_);
v___x_3281_ = lean_apply_4(v_toBind_3272_, lean_box(0), lean_box(0), v___x_3276_, v___f_3280_);
return v___x_3281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___boxed(lean_object* v_m_3282_, lean_object* v_inst_3283_, lean_object* v_inst_3284_, lean_object* v_inst_3285_, lean_object* v_input_3286_, lean_object* v_cache_3287_, lean_object* v_pre_3288_, lean_object* v_post_3289_, lean_object* v_usedLetOnly_3290_, lean_object* v_skipConstInApp_3291_, lean_object* v_skipInstances_3292_){
_start:
{
uint8_t v_usedLetOnly_boxed_3293_; uint8_t v_skipConstInApp_boxed_3294_; uint8_t v_skipInstances_boxed_3295_; lean_object* v_res_3296_; 
v_usedLetOnly_boxed_3293_ = lean_unbox(v_usedLetOnly_3290_);
v_skipConstInApp_boxed_3294_ = lean_unbox(v_skipConstInApp_3291_);
v_skipInstances_boxed_3295_ = lean_unbox(v_skipInstances_3292_);
v_res_3296_ = l_Lean_Meta_transformWithCache(v_m_3282_, v_inst_3283_, v_inst_3284_, v_inst_3285_, v_input_3286_, v_cache_3287_, v_pre_3288_, v_post_3289_, v_usedLetOnly_boxed_3293_, v_skipConstInApp_boxed_3294_, v_skipInstances_boxed_3295_);
return v_res_3296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___redArg___lam__5(lean_object* v_toPure_3297_, lean_object* v_x_3298_, lean_object* v_toBind_3299_, lean_object* v_inst_3300_, lean_object* v_inst_3301_, lean_object* v_inst_3302_, lean_object* v_pre_3303_, lean_object* v_post_3304_, uint8_t v_usedLetOnly_3305_, uint8_t v_skipConstInApp_3306_, uint8_t v___x_3307_, lean_object* v_x_3308_, lean_object* v_input_3309_, lean_object* v_ref_3310_){
_start:
{
lean_object* v___f_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; 
lean_inc(v_toBind_3299_);
lean_inc(v_x_3298_);
lean_inc(v_ref_3310_);
v___f_3311_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__4), 5, 4);
lean_closure_set(v___f_3311_, 0, v_toPure_3297_);
lean_closure_set(v___f_3311_, 1, v_ref_3310_);
lean_closure_set(v___f_3311_, 2, v_x_3298_);
lean_closure_set(v___f_3311_, 3, v_toBind_3299_);
v___x_3312_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_3300_, v_inst_3301_, v_inst_3302_, v_pre_3303_, v_post_3304_, v_usedLetOnly_3305_, v_skipConstInApp_3306_, v___x_3307_, v_x_3308_, v_x_3298_, v_input_3309_, v_ref_3310_);
lean_dec(v_ref_3310_);
v___x_3313_ = lean_apply_4(v_toBind_3299_, lean_box(0), lean_box(0), v___x_3312_, v___f_3311_);
return v___x_3313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___redArg___lam__5___boxed(lean_object* v_toPure_3314_, lean_object* v_x_3315_, lean_object* v_toBind_3316_, lean_object* v_inst_3317_, lean_object* v_inst_3318_, lean_object* v_inst_3319_, lean_object* v_pre_3320_, lean_object* v_post_3321_, lean_object* v_usedLetOnly_3322_, lean_object* v_skipConstInApp_3323_, lean_object* v___x_3324_, lean_object* v_x_3325_, lean_object* v_input_3326_, lean_object* v_ref_3327_){
_start:
{
uint8_t v_usedLetOnly_boxed_3328_; uint8_t v_skipConstInApp_boxed_3329_; uint8_t v___x_114__boxed_3330_; lean_object* v_res_3331_; 
v_usedLetOnly_boxed_3328_ = lean_unbox(v_usedLetOnly_3322_);
v_skipConstInApp_boxed_3329_ = lean_unbox(v_skipConstInApp_3323_);
v___x_114__boxed_3330_ = lean_unbox(v___x_3324_);
v_res_3331_ = l_Lean_Meta_transform___redArg___lam__5(v_toPure_3314_, v_x_3315_, v_toBind_3316_, v_inst_3317_, v_inst_3318_, v_inst_3319_, v_pre_3320_, v_post_3321_, v_usedLetOnly_boxed_3328_, v_skipConstInApp_boxed_3329_, v___x_114__boxed_3330_, v_x_3325_, v_input_3326_, v_ref_3327_);
return v_res_3331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___redArg(lean_object* v_inst_3332_, lean_object* v_inst_3333_, lean_object* v_inst_3334_, lean_object* v_input_3335_, lean_object* v_pre_3336_, lean_object* v_post_3337_, uint8_t v_usedLetOnly_3338_, uint8_t v_skipConstInApp_3339_){
_start:
{
lean_object* v_toApplicative_3340_; lean_object* v_toBind_3341_; lean_object* v_x_3342_; lean_object* v_toPure_3343_; lean_object* v_x_3344_; uint8_t v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___f_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___f_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; 
v_toApplicative_3340_ = lean_ctor_get(v_inst_3332_, 0);
v_toBind_3341_ = lean_ctor_get(v_inst_3332_, 1);
lean_inc_n(v_toBind_3341_, 3);
v_x_3342_ = lean_box(0);
v_toPure_3343_ = lean_ctor_get(v_toApplicative_3340_, 1);
lean_inc_n(v_toPure_3343_, 2);
lean_inc_n(v_inst_3333_, 2);
v_x_3344_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__1), 3, 1);
lean_closure_set(v_x_3344_, 0, v_inst_3333_);
v___x_3345_ = 0;
v___x_3346_ = lean_obj_once(&l_Lean_Core_transform___redArg___closed__2, &l_Lean_Core_transform___redArg___closed__2_once, _init_l_Lean_Core_transform___redArg___closed__2);
v___x_3347_ = l_Lean_Meta_transformWithCache___redArg___lam__1(v_inst_3333_, lean_box(0), v___x_3346_);
v___f_3348_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__2), 2, 1);
lean_closure_set(v___f_3348_, 0, v_toPure_3343_);
v___x_3349_ = lean_box(v_usedLetOnly_3338_);
v___x_3350_ = lean_box(v_skipConstInApp_3339_);
v___x_3351_ = lean_box(v___x_3345_);
v___f_3352_ = lean_alloc_closure((void*)(l_Lean_Meta_transform___redArg___lam__5___boxed), 14, 13);
lean_closure_set(v___f_3352_, 0, v_toPure_3343_);
lean_closure_set(v___f_3352_, 1, v_x_3344_);
lean_closure_set(v___f_3352_, 2, v_toBind_3341_);
lean_closure_set(v___f_3352_, 3, v_inst_3332_);
lean_closure_set(v___f_3352_, 4, v_inst_3333_);
lean_closure_set(v___f_3352_, 5, v_inst_3334_);
lean_closure_set(v___f_3352_, 6, v_pre_3336_);
lean_closure_set(v___f_3352_, 7, v_post_3337_);
lean_closure_set(v___f_3352_, 8, v___x_3349_);
lean_closure_set(v___f_3352_, 9, v___x_3350_);
lean_closure_set(v___f_3352_, 10, v___x_3351_);
lean_closure_set(v___f_3352_, 11, v_x_3342_);
lean_closure_set(v___f_3352_, 12, v_input_3335_);
v___x_3353_ = lean_apply_4(v_toBind_3341_, lean_box(0), lean_box(0), v___x_3347_, v___f_3352_);
v___x_3354_ = lean_apply_4(v_toBind_3341_, lean_box(0), lean_box(0), v___x_3353_, v___f_3348_);
return v___x_3354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___redArg___boxed(lean_object* v_inst_3355_, lean_object* v_inst_3356_, lean_object* v_inst_3357_, lean_object* v_input_3358_, lean_object* v_pre_3359_, lean_object* v_post_3360_, lean_object* v_usedLetOnly_3361_, lean_object* v_skipConstInApp_3362_){
_start:
{
uint8_t v_usedLetOnly_boxed_3363_; uint8_t v_skipConstInApp_boxed_3364_; lean_object* v_res_3365_; 
v_usedLetOnly_boxed_3363_ = lean_unbox(v_usedLetOnly_3361_);
v_skipConstInApp_boxed_3364_ = lean_unbox(v_skipConstInApp_3362_);
v_res_3365_ = l_Lean_Meta_transform___redArg(v_inst_3355_, v_inst_3356_, v_inst_3357_, v_input_3358_, v_pre_3359_, v_post_3360_, v_usedLetOnly_boxed_3363_, v_skipConstInApp_boxed_3364_);
return v_res_3365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform(lean_object* v_m_3366_, lean_object* v_inst_3367_, lean_object* v_inst_3368_, lean_object* v_inst_3369_, lean_object* v_input_3370_, lean_object* v_pre_3371_, lean_object* v_post_3372_, uint8_t v_usedLetOnly_3373_, uint8_t v_skipConstInApp_3374_){
_start:
{
lean_object* v___x_3375_; 
v___x_3375_ = l_Lean_Meta_transform___redArg(v_inst_3367_, v_inst_3368_, v_inst_3369_, v_input_3370_, v_pre_3371_, v_post_3372_, v_usedLetOnly_3373_, v_skipConstInApp_3374_);
return v___x_3375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___boxed(lean_object* v_m_3376_, lean_object* v_inst_3377_, lean_object* v_inst_3378_, lean_object* v_inst_3379_, lean_object* v_input_3380_, lean_object* v_pre_3381_, lean_object* v_post_3382_, lean_object* v_usedLetOnly_3383_, lean_object* v_skipConstInApp_3384_){
_start:
{
uint8_t v_usedLetOnly_boxed_3385_; uint8_t v_skipConstInApp_boxed_3386_; lean_object* v_res_3387_; 
v_usedLetOnly_boxed_3385_ = lean_unbox(v_usedLetOnly_3383_);
v_skipConstInApp_boxed_3386_ = lean_unbox(v_skipConstInApp_3384_);
v_res_3387_ = l_Lean_Meta_transform(v_m_3376_, v_inst_3377_, v_inst_3378_, v_inst_3379_, v_input_3380_, v_pre_3381_, v_post_3382_, v_usedLetOnly_boxed_3385_, v_skipConstInApp_boxed_3386_);
return v_res_3387_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(lean_object* v_e_3388_, lean_object* v___y_3389_){
_start:
{
uint8_t v___x_3391_; 
v___x_3391_ = l_Lean_Expr_hasMVar(v_e_3388_);
if (v___x_3391_ == 0)
{
lean_object* v___x_3392_; 
v___x_3392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3392_, 0, v_e_3388_);
return v___x_3392_;
}
else
{
lean_object* v___x_3393_; lean_object* v_mctx_3394_; lean_object* v___x_3395_; lean_object* v_fst_3396_; lean_object* v_snd_3397_; lean_object* v___x_3398_; lean_object* v_cache_3399_; lean_object* v_zetaDeltaFVarIds_3400_; lean_object* v_postponed_3401_; lean_object* v_diag_3402_; lean_object* v___x_3404_; uint8_t v_isShared_3405_; uint8_t v_isSharedCheck_3411_; 
v___x_3393_ = lean_st_ref_get(v___y_3389_);
v_mctx_3394_ = lean_ctor_get(v___x_3393_, 0);
lean_inc_ref(v_mctx_3394_);
lean_dec(v___x_3393_);
v___x_3395_ = l_Lean_instantiateMVarsCore(v_mctx_3394_, v_e_3388_);
v_fst_3396_ = lean_ctor_get(v___x_3395_, 0);
lean_inc(v_fst_3396_);
v_snd_3397_ = lean_ctor_get(v___x_3395_, 1);
lean_inc(v_snd_3397_);
lean_dec_ref(v___x_3395_);
v___x_3398_ = lean_st_ref_take(v___y_3389_);
v_cache_3399_ = lean_ctor_get(v___x_3398_, 1);
v_zetaDeltaFVarIds_3400_ = lean_ctor_get(v___x_3398_, 2);
v_postponed_3401_ = lean_ctor_get(v___x_3398_, 3);
v_diag_3402_ = lean_ctor_get(v___x_3398_, 4);
v_isSharedCheck_3411_ = !lean_is_exclusive(v___x_3398_);
if (v_isSharedCheck_3411_ == 0)
{
lean_object* v_unused_3412_; 
v_unused_3412_ = lean_ctor_get(v___x_3398_, 0);
lean_dec(v_unused_3412_);
v___x_3404_ = v___x_3398_;
v_isShared_3405_ = v_isSharedCheck_3411_;
goto v_resetjp_3403_;
}
else
{
lean_inc(v_diag_3402_);
lean_inc(v_postponed_3401_);
lean_inc(v_zetaDeltaFVarIds_3400_);
lean_inc(v_cache_3399_);
lean_dec(v___x_3398_);
v___x_3404_ = lean_box(0);
v_isShared_3405_ = v_isSharedCheck_3411_;
goto v_resetjp_3403_;
}
v_resetjp_3403_:
{
lean_object* v___x_3407_; 
if (v_isShared_3405_ == 0)
{
lean_ctor_set(v___x_3404_, 0, v_snd_3397_);
v___x_3407_ = v___x_3404_;
goto v_reusejp_3406_;
}
else
{
lean_object* v_reuseFailAlloc_3410_; 
v_reuseFailAlloc_3410_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3410_, 0, v_snd_3397_);
lean_ctor_set(v_reuseFailAlloc_3410_, 1, v_cache_3399_);
lean_ctor_set(v_reuseFailAlloc_3410_, 2, v_zetaDeltaFVarIds_3400_);
lean_ctor_set(v_reuseFailAlloc_3410_, 3, v_postponed_3401_);
lean_ctor_set(v_reuseFailAlloc_3410_, 4, v_diag_3402_);
v___x_3407_ = v_reuseFailAlloc_3410_;
goto v_reusejp_3406_;
}
v_reusejp_3406_:
{
lean_object* v___x_3408_; lean_object* v___x_3409_; 
v___x_3408_ = lean_st_ref_set(v___y_3389_, v___x_3407_);
v___x_3409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3409_, 0, v_fst_3396_);
return v___x_3409_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg___boxed(lean_object* v_e_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_){
_start:
{
lean_object* v_res_3416_; 
v_res_3416_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(v_e_3413_, v___y_3414_);
lean_dec(v___y_3414_);
return v_res_3416_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0(lean_object* v_e_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_){
_start:
{
lean_object* v___x_3423_; 
v___x_3423_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(v_e_3417_, v___y_3419_);
return v___x_3423_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___boxed(lean_object* v_e_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_){
_start:
{
lean_object* v_res_3430_; 
v_res_3430_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0(v_e_3424_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_);
lean_dec(v___y_3428_);
lean_dec_ref(v___y_3427_);
lean_dec(v___y_3426_);
lean_dec_ref(v___y_3425_);
return v_res_3430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__0(uint8_t v_zetaHave_3431_, lean_object* v___x_3432_, uint8_t v_zetaDelta_3433_, lean_object* v_fvarId_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_){
_start:
{
lean_object* v___x_3440_; 
v___x_3440_ = l_Lean_FVarId_findDecl_x3f___redArg(v_fvarId_3434_, v___y_3435_);
if (lean_obj_tag(v___x_3440_) == 0)
{
lean_object* v_a_3441_; lean_object* v___x_3443_; uint8_t v_isShared_3444_; uint8_t v_isSharedCheck_3469_; 
v_a_3441_ = lean_ctor_get(v___x_3440_, 0);
v_isSharedCheck_3469_ = !lean_is_exclusive(v___x_3440_);
if (v_isSharedCheck_3469_ == 0)
{
v___x_3443_ = v___x_3440_;
v_isShared_3444_ = v_isSharedCheck_3469_;
goto v_resetjp_3442_;
}
else
{
lean_inc(v_a_3441_);
lean_dec(v___x_3440_);
v___x_3443_ = lean_box(0);
v_isShared_3444_ = v_isSharedCheck_3469_;
goto v_resetjp_3442_;
}
v_resetjp_3442_:
{
if (lean_obj_tag(v_a_3441_) == 1)
{
lean_object* v_val_3445_; lean_object* v___x_3447_; uint8_t v_isShared_3448_; uint8_t v_isSharedCheck_3464_; 
v_val_3445_ = lean_ctor_get(v_a_3441_, 0);
v_isSharedCheck_3464_ = !lean_is_exclusive(v_a_3441_);
if (v_isSharedCheck_3464_ == 0)
{
v___x_3447_ = v_a_3441_;
v_isShared_3448_ = v_isSharedCheck_3464_;
goto v_resetjp_3446_;
}
else
{
lean_inc(v_val_3445_);
lean_dec(v_a_3441_);
v___x_3447_ = lean_box(0);
v_isShared_3448_ = v_isSharedCheck_3464_;
goto v_resetjp_3446_;
}
v_resetjp_3446_:
{
uint8_t v___y_3450_; 
if (v_zetaDelta_3433_ == 0)
{
lean_object* v___x_3458_; uint8_t v___x_3459_; 
v___x_3458_ = l_Lean_LocalDecl_index(v_val_3445_);
v___x_3459_ = lean_nat_dec_lt(v___x_3458_, v___x_3432_);
lean_dec(v___x_3458_);
if (v___x_3459_ == 0)
{
lean_del_object(v___x_3447_);
goto v___jp_3455_;
}
else
{
lean_object* v___x_3460_; lean_object* v___x_3462_; 
lean_dec(v_val_3445_);
lean_del_object(v___x_3443_);
v___x_3460_ = lean_box(0);
if (v_isShared_3448_ == 0)
{
lean_ctor_set_tag(v___x_3447_, 0);
lean_ctor_set(v___x_3447_, 0, v___x_3460_);
v___x_3462_ = v___x_3447_;
goto v_reusejp_3461_;
}
else
{
lean_object* v_reuseFailAlloc_3463_; 
v_reuseFailAlloc_3463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3463_, 0, v___x_3460_);
v___x_3462_ = v_reuseFailAlloc_3463_;
goto v_reusejp_3461_;
}
v_reusejp_3461_:
{
return v___x_3462_;
}
}
}
else
{
lean_del_object(v___x_3447_);
goto v___jp_3455_;
}
v___jp_3449_:
{
lean_object* v___x_3451_; lean_object* v___x_3453_; 
v___x_3451_ = l_Lean_LocalDecl_value_x3f(v_val_3445_, v___y_3450_);
lean_dec(v_val_3445_);
if (v_isShared_3444_ == 0)
{
lean_ctor_set(v___x_3443_, 0, v___x_3451_);
v___x_3453_ = v___x_3443_;
goto v_reusejp_3452_;
}
else
{
lean_object* v_reuseFailAlloc_3454_; 
v_reuseFailAlloc_3454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3454_, 0, v___x_3451_);
v___x_3453_ = v_reuseFailAlloc_3454_;
goto v_reusejp_3452_;
}
v_reusejp_3452_:
{
return v___x_3453_;
}
}
v___jp_3455_:
{
if (v_zetaHave_3431_ == 0)
{
v___y_3450_ = v_zetaHave_3431_;
goto v___jp_3449_;
}
else
{
lean_object* v___x_3456_; uint8_t v___x_3457_; 
v___x_3456_ = l_Lean_LocalDecl_index(v_val_3445_);
v___x_3457_ = lean_nat_dec_le(v___x_3432_, v___x_3456_);
lean_dec(v___x_3456_);
v___y_3450_ = v___x_3457_;
goto v___jp_3449_;
}
}
}
}
else
{
lean_object* v___x_3465_; lean_object* v___x_3467_; 
lean_dec(v_a_3441_);
v___x_3465_ = lean_box(0);
if (v_isShared_3444_ == 0)
{
lean_ctor_set(v___x_3443_, 0, v___x_3465_);
v___x_3467_ = v___x_3443_;
goto v_reusejp_3466_;
}
else
{
lean_object* v_reuseFailAlloc_3468_; 
v_reuseFailAlloc_3468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3468_, 0, v___x_3465_);
v___x_3467_ = v_reuseFailAlloc_3468_;
goto v_reusejp_3466_;
}
v_reusejp_3466_:
{
return v___x_3467_;
}
}
}
}
else
{
lean_object* v_a_3470_; lean_object* v___x_3472_; uint8_t v_isShared_3473_; uint8_t v_isSharedCheck_3477_; 
v_a_3470_ = lean_ctor_get(v___x_3440_, 0);
v_isSharedCheck_3477_ = !lean_is_exclusive(v___x_3440_);
if (v_isSharedCheck_3477_ == 0)
{
v___x_3472_ = v___x_3440_;
v_isShared_3473_ = v_isSharedCheck_3477_;
goto v_resetjp_3471_;
}
else
{
lean_inc(v_a_3470_);
lean_dec(v___x_3440_);
v___x_3472_ = lean_box(0);
v_isShared_3473_ = v_isSharedCheck_3477_;
goto v_resetjp_3471_;
}
v_resetjp_3471_:
{
lean_object* v___x_3475_; 
if (v_isShared_3473_ == 0)
{
v___x_3475_ = v___x_3472_;
goto v_reusejp_3474_;
}
else
{
lean_object* v_reuseFailAlloc_3476_; 
v_reuseFailAlloc_3476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3476_, 0, v_a_3470_);
v___x_3475_ = v_reuseFailAlloc_3476_;
goto v_reusejp_3474_;
}
v_reusejp_3474_:
{
return v___x_3475_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__0___boxed(lean_object* v_zetaHave_3478_, lean_object* v___x_3479_, lean_object* v_zetaDelta_3480_, lean_object* v_fvarId_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_){
_start:
{
uint8_t v_zetaHave_boxed_3487_; uint8_t v_zetaDelta_boxed_3488_; lean_object* v_res_3489_; 
v_zetaHave_boxed_3487_ = lean_unbox(v_zetaHave_3478_);
v_zetaDelta_boxed_3488_ = lean_unbox(v_zetaDelta_3480_);
v_res_3489_ = l_Lean_Meta_zetaReduce___lam__0(v_zetaHave_boxed_3487_, v___x_3479_, v_zetaDelta_boxed_3488_, v_fvarId_3481_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_);
lean_dec(v___y_3485_);
lean_dec_ref(v___y_3484_);
lean_dec(v___y_3483_);
lean_dec_ref(v___y_3482_);
lean_dec(v___x_3479_);
return v_res_3489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__1(lean_object* v_e_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_){
_start:
{
lean_object* v___x_3496_; lean_object* v___x_3497_; 
v___x_3496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3496_, 0, v_e_3490_);
v___x_3497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3497_, 0, v___x_3496_);
return v___x_3497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__1___boxed(lean_object* v_e_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_){
_start:
{
lean_object* v_res_3504_; 
v_res_3504_ = l_Lean_Meta_zetaReduce___lam__1(v_e_3498_, v___y_3499_, v___y_3500_, v___y_3501_, v___y_3502_);
lean_dec(v___y_3502_);
lean_dec_ref(v___y_3501_);
lean_dec(v___y_3500_);
lean_dec_ref(v___y_3499_);
return v_res_3504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__2(lean_object* v___f_3505_, lean_object* v_e_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_){
_start:
{
if (lean_obj_tag(v_e_3506_) == 1)
{
lean_object* v_fvarId_3512_; lean_object* v___x_3513_; 
v_fvarId_3512_ = lean_ctor_get(v_e_3506_, 0);
lean_inc(v___y_3510_);
lean_inc_ref(v___y_3509_);
lean_inc(v___y_3508_);
lean_inc_ref(v___y_3507_);
lean_inc(v_fvarId_3512_);
v___x_3513_ = lean_apply_6(v___f_3505_, v_fvarId_3512_, v___y_3507_, v___y_3508_, v___y_3509_, v___y_3510_, lean_box(0));
if (lean_obj_tag(v___x_3513_) == 0)
{
lean_object* v_a_3514_; lean_object* v___x_3516_; uint8_t v_isShared_3517_; uint8_t v_isSharedCheck_3539_; 
v_a_3514_ = lean_ctor_get(v___x_3513_, 0);
v_isSharedCheck_3539_ = !lean_is_exclusive(v___x_3513_);
if (v_isSharedCheck_3539_ == 0)
{
v___x_3516_ = v___x_3513_;
v_isShared_3517_ = v_isSharedCheck_3539_;
goto v_resetjp_3515_;
}
else
{
lean_inc(v_a_3514_);
lean_dec(v___x_3513_);
v___x_3516_ = lean_box(0);
v_isShared_3517_ = v_isSharedCheck_3539_;
goto v_resetjp_3515_;
}
v_resetjp_3515_:
{
if (lean_obj_tag(v_a_3514_) == 1)
{
lean_object* v_val_3518_; lean_object* v___x_3520_; uint8_t v_isShared_3521_; uint8_t v_isSharedCheck_3534_; 
lean_del_object(v___x_3516_);
lean_dec_ref(v_e_3506_);
v_val_3518_ = lean_ctor_get(v_a_3514_, 0);
v_isSharedCheck_3534_ = !lean_is_exclusive(v_a_3514_);
if (v_isSharedCheck_3534_ == 0)
{
v___x_3520_ = v_a_3514_;
v_isShared_3521_ = v_isSharedCheck_3534_;
goto v_resetjp_3519_;
}
else
{
lean_inc(v_val_3518_);
lean_dec(v_a_3514_);
v___x_3520_ = lean_box(0);
v_isShared_3521_ = v_isSharedCheck_3534_;
goto v_resetjp_3519_;
}
v_resetjp_3519_:
{
lean_object* v___x_3522_; lean_object* v_a_3523_; lean_object* v___x_3525_; uint8_t v_isShared_3526_; uint8_t v_isSharedCheck_3533_; 
v___x_3522_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(v_val_3518_, v___y_3508_);
v_a_3523_ = lean_ctor_get(v___x_3522_, 0);
v_isSharedCheck_3533_ = !lean_is_exclusive(v___x_3522_);
if (v_isSharedCheck_3533_ == 0)
{
v___x_3525_ = v___x_3522_;
v_isShared_3526_ = v_isSharedCheck_3533_;
goto v_resetjp_3524_;
}
else
{
lean_inc(v_a_3523_);
lean_dec(v___x_3522_);
v___x_3525_ = lean_box(0);
v_isShared_3526_ = v_isSharedCheck_3533_;
goto v_resetjp_3524_;
}
v_resetjp_3524_:
{
lean_object* v___x_3528_; 
if (v_isShared_3521_ == 0)
{
lean_ctor_set(v___x_3520_, 0, v_a_3523_);
v___x_3528_ = v___x_3520_;
goto v_reusejp_3527_;
}
else
{
lean_object* v_reuseFailAlloc_3532_; 
v_reuseFailAlloc_3532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3532_, 0, v_a_3523_);
v___x_3528_ = v_reuseFailAlloc_3532_;
goto v_reusejp_3527_;
}
v_reusejp_3527_:
{
lean_object* v___x_3530_; 
if (v_isShared_3526_ == 0)
{
lean_ctor_set(v___x_3525_, 0, v___x_3528_);
v___x_3530_ = v___x_3525_;
goto v_reusejp_3529_;
}
else
{
lean_object* v_reuseFailAlloc_3531_; 
v_reuseFailAlloc_3531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3531_, 0, v___x_3528_);
v___x_3530_ = v_reuseFailAlloc_3531_;
goto v_reusejp_3529_;
}
v_reusejp_3529_:
{
return v___x_3530_;
}
}
}
}
}
else
{
lean_object* v___x_3535_; lean_object* v___x_3537_; 
lean_dec(v_a_3514_);
v___x_3535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3535_, 0, v_e_3506_);
if (v_isShared_3517_ == 0)
{
lean_ctor_set(v___x_3516_, 0, v___x_3535_);
v___x_3537_ = v___x_3516_;
goto v_reusejp_3536_;
}
else
{
lean_object* v_reuseFailAlloc_3538_; 
v_reuseFailAlloc_3538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3538_, 0, v___x_3535_);
v___x_3537_ = v_reuseFailAlloc_3538_;
goto v_reusejp_3536_;
}
v_reusejp_3536_:
{
return v___x_3537_;
}
}
}
}
else
{
lean_object* v_a_3540_; lean_object* v___x_3542_; uint8_t v_isShared_3543_; uint8_t v_isSharedCheck_3547_; 
lean_dec_ref(v_e_3506_);
v_a_3540_ = lean_ctor_get(v___x_3513_, 0);
v_isSharedCheck_3547_ = !lean_is_exclusive(v___x_3513_);
if (v_isSharedCheck_3547_ == 0)
{
v___x_3542_ = v___x_3513_;
v_isShared_3543_ = v_isSharedCheck_3547_;
goto v_resetjp_3541_;
}
else
{
lean_inc(v_a_3540_);
lean_dec(v___x_3513_);
v___x_3542_ = lean_box(0);
v_isShared_3543_ = v_isSharedCheck_3547_;
goto v_resetjp_3541_;
}
v_resetjp_3541_:
{
lean_object* v___x_3545_; 
if (v_isShared_3543_ == 0)
{
v___x_3545_ = v___x_3542_;
goto v_reusejp_3544_;
}
else
{
lean_object* v_reuseFailAlloc_3546_; 
v_reuseFailAlloc_3546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3546_, 0, v_a_3540_);
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
else
{
lean_object* v___x_3548_; lean_object* v___x_3549_; 
lean_dec_ref(v_e_3506_);
lean_dec_ref(v___f_3505_);
v___x_3548_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_3549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3549_, 0, v___x_3548_);
return v___x_3549_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__2___boxed(lean_object* v___f_3550_, lean_object* v_e_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_){
_start:
{
lean_object* v_res_3557_; 
v_res_3557_ = l_Lean_Meta_zetaReduce___lam__2(v___f_3550_, v_e_3551_, v___y_3552_, v___y_3553_, v___y_3554_, v___y_3555_);
lean_dec(v___y_3555_);
lean_dec_ref(v___y_3554_);
lean_dec(v___y_3553_);
lean_dec_ref(v___y_3552_);
return v_res_3557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__4(lean_object* v___f_3558_, lean_object* v_e_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_){
_start:
{
lean_object* v___x_3565_; 
v___x_3565_ = l_Lean_Expr_getAppFn(v_e_3559_);
if (lean_obj_tag(v___x_3565_) == 1)
{
lean_object* v_fvarId_3566_; lean_object* v___x_3567_; 
v_fvarId_3566_ = lean_ctor_get(v___x_3565_, 0);
lean_inc(v_fvarId_3566_);
lean_dec_ref(v___x_3565_);
lean_inc(v___y_3563_);
lean_inc_ref(v___y_3562_);
lean_inc(v___y_3561_);
lean_inc_ref(v___y_3560_);
v___x_3567_ = lean_apply_6(v___f_3558_, v_fvarId_3566_, v___y_3560_, v___y_3561_, v___y_3562_, v___y_3563_, lean_box(0));
if (lean_obj_tag(v___x_3567_) == 0)
{
lean_object* v_a_3568_; lean_object* v___x_3570_; uint8_t v_isShared_3571_; uint8_t v_isSharedCheck_3600_; 
v_a_3568_ = lean_ctor_get(v___x_3567_, 0);
v_isSharedCheck_3600_ = !lean_is_exclusive(v___x_3567_);
if (v_isSharedCheck_3600_ == 0)
{
v___x_3570_ = v___x_3567_;
v_isShared_3571_ = v_isSharedCheck_3600_;
goto v_resetjp_3569_;
}
else
{
lean_inc(v_a_3568_);
lean_dec(v___x_3567_);
v___x_3570_ = lean_box(0);
v_isShared_3571_ = v_isSharedCheck_3600_;
goto v_resetjp_3569_;
}
v_resetjp_3569_:
{
if (lean_obj_tag(v_a_3568_) == 1)
{
lean_object* v_val_3572_; lean_object* v___x_3574_; uint8_t v_isShared_3575_; uint8_t v_isSharedCheck_3595_; 
lean_del_object(v___x_3570_);
v_val_3572_ = lean_ctor_get(v_a_3568_, 0);
v_isSharedCheck_3595_ = !lean_is_exclusive(v_a_3568_);
if (v_isSharedCheck_3595_ == 0)
{
v___x_3574_ = v_a_3568_;
v_isShared_3575_ = v_isSharedCheck_3595_;
goto v_resetjp_3573_;
}
else
{
lean_inc(v_val_3572_);
lean_dec(v_a_3568_);
v___x_3574_ = lean_box(0);
v_isShared_3575_ = v_isSharedCheck_3595_;
goto v_resetjp_3573_;
}
v_resetjp_3573_:
{
lean_object* v___x_3576_; lean_object* v_a_3577_; lean_object* v___x_3579_; uint8_t v_isShared_3580_; uint8_t v_isSharedCheck_3594_; 
v___x_3576_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(v_val_3572_, v___y_3561_);
v_a_3577_ = lean_ctor_get(v___x_3576_, 0);
v_isSharedCheck_3594_ = !lean_is_exclusive(v___x_3576_);
if (v_isSharedCheck_3594_ == 0)
{
v___x_3579_ = v___x_3576_;
v_isShared_3580_ = v_isSharedCheck_3594_;
goto v_resetjp_3578_;
}
else
{
lean_inc(v_a_3577_);
lean_dec(v___x_3576_);
v___x_3579_ = lean_box(0);
v_isShared_3580_ = v_isSharedCheck_3594_;
goto v_resetjp_3578_;
}
v_resetjp_3578_:
{
lean_object* v_dummy_3581_; lean_object* v_nargs_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3589_; 
v_dummy_3581_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_3582_ = l_Lean_Expr_getAppNumArgs(v_e_3559_);
lean_inc(v_nargs_3582_);
v___x_3583_ = lean_mk_array(v_nargs_3582_, v_dummy_3581_);
v___x_3584_ = lean_unsigned_to_nat(1u);
v___x_3585_ = lean_nat_sub(v_nargs_3582_, v___x_3584_);
lean_dec(v_nargs_3582_);
v___x_3586_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3559_, v___x_3583_, v___x_3585_);
v___x_3587_ = l_Lean_Expr_beta(v_a_3577_, v___x_3586_);
if (v_isShared_3575_ == 0)
{
lean_ctor_set(v___x_3574_, 0, v___x_3587_);
v___x_3589_ = v___x_3574_;
goto v_reusejp_3588_;
}
else
{
lean_object* v_reuseFailAlloc_3593_; 
v_reuseFailAlloc_3593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3593_, 0, v___x_3587_);
v___x_3589_ = v_reuseFailAlloc_3593_;
goto v_reusejp_3588_;
}
v_reusejp_3588_:
{
lean_object* v___x_3591_; 
if (v_isShared_3580_ == 0)
{
lean_ctor_set(v___x_3579_, 0, v___x_3589_);
v___x_3591_ = v___x_3579_;
goto v_reusejp_3590_;
}
else
{
lean_object* v_reuseFailAlloc_3592_; 
v_reuseFailAlloc_3592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3592_, 0, v___x_3589_);
v___x_3591_ = v_reuseFailAlloc_3592_;
goto v_reusejp_3590_;
}
v_reusejp_3590_:
{
return v___x_3591_;
}
}
}
}
}
else
{
lean_object* v___x_3596_; lean_object* v___x_3598_; 
lean_dec(v_a_3568_);
lean_dec_ref(v_e_3559_);
v___x_3596_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
if (v_isShared_3571_ == 0)
{
lean_ctor_set(v___x_3570_, 0, v___x_3596_);
v___x_3598_ = v___x_3570_;
goto v_reusejp_3597_;
}
else
{
lean_object* v_reuseFailAlloc_3599_; 
v_reuseFailAlloc_3599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3599_, 0, v___x_3596_);
v___x_3598_ = v_reuseFailAlloc_3599_;
goto v_reusejp_3597_;
}
v_reusejp_3597_:
{
return v___x_3598_;
}
}
}
}
else
{
lean_object* v_a_3601_; lean_object* v___x_3603_; uint8_t v_isShared_3604_; uint8_t v_isSharedCheck_3608_; 
lean_dec_ref(v_e_3559_);
v_a_3601_ = lean_ctor_get(v___x_3567_, 0);
v_isSharedCheck_3608_ = !lean_is_exclusive(v___x_3567_);
if (v_isSharedCheck_3608_ == 0)
{
v___x_3603_ = v___x_3567_;
v_isShared_3604_ = v_isSharedCheck_3608_;
goto v_resetjp_3602_;
}
else
{
lean_inc(v_a_3601_);
lean_dec(v___x_3567_);
v___x_3603_ = lean_box(0);
v_isShared_3604_ = v_isSharedCheck_3608_;
goto v_resetjp_3602_;
}
v_resetjp_3602_:
{
lean_object* v___x_3606_; 
if (v_isShared_3604_ == 0)
{
v___x_3606_ = v___x_3603_;
goto v_reusejp_3605_;
}
else
{
lean_object* v_reuseFailAlloc_3607_; 
v_reuseFailAlloc_3607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3607_, 0, v_a_3601_);
v___x_3606_ = v_reuseFailAlloc_3607_;
goto v_reusejp_3605_;
}
v_reusejp_3605_:
{
return v___x_3606_;
}
}
}
}
else
{
lean_object* v___x_3609_; lean_object* v___x_3610_; 
lean_dec_ref(v___x_3565_);
lean_dec_ref(v_e_3559_);
lean_dec_ref(v___f_3558_);
v___x_3609_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_3610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3610_, 0, v___x_3609_);
return v___x_3610_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__4___boxed(lean_object* v___f_3611_, lean_object* v_e_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_){
_start:
{
lean_object* v_res_3618_; 
v_res_3618_ = l_Lean_Meta_zetaReduce___lam__4(v___f_3611_, v_e_3612_, v___y_3613_, v___y_3614_, v___y_3615_, v___y_3616_);
lean_dec(v___y_3616_);
lean_dec_ref(v___y_3615_);
lean_dec(v___y_3614_);
lean_dec_ref(v___y_3613_);
return v_res_3618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0(lean_object* v_00_u03b1_3619_, lean_object* v_x_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_){
_start:
{
lean_object* v___x_3626_; lean_object* v___x_3627_; 
v___x_3626_ = lean_apply_1(v_x_3620_, lean_box(0));
v___x_3627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3627_, 0, v___x_3626_);
return v___x_3627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0___boxed(lean_object* v_00_u03b1_3628_, lean_object* v_x_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_){
_start:
{
lean_object* v_res_3635_; 
v_res_3635_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0(v_00_u03b1_3628_, v_x_3629_, v___y_3630_, v___y_3631_, v___y_3632_, v___y_3633_);
lean_dec(v___y_3633_);
lean_dec_ref(v___y_3632_);
lean_dec(v___y_3631_);
lean_dec_ref(v___y_3630_);
return v_res_3635_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__2(lean_object* v___x_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_){
_start:
{
lean_object* v___x_3642_; 
v___x_3642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3642_, 0, v___x_3636_);
return v___x_3642_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__2___boxed(lean_object* v___x_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_){
_start:
{
lean_object* v_res_3649_; 
v_res_3649_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__2(v___x_3643_, v___y_3644_, v___y_3645_, v___y_3646_, v___y_3647_);
lean_dec(v___y_3647_);
lean_dec_ref(v___y_3646_);
lean_dec(v___y_3645_);
lean_dec_ref(v___y_3644_);
return v_res_3649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0(lean_object* v_k_3650_, lean_object* v___y_3651_, lean_object* v_b_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_){
_start:
{
lean_object* v___x_3658_; 
lean_inc(v___y_3656_);
lean_inc_ref(v___y_3655_);
lean_inc(v___y_3654_);
lean_inc_ref(v___y_3653_);
lean_inc(v___y_3651_);
v___x_3658_ = lean_apply_7(v_k_3650_, v_b_3652_, v___y_3651_, v___y_3653_, v___y_3654_, v___y_3655_, v___y_3656_, lean_box(0));
return v___x_3658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0___boxed(lean_object* v_k_3659_, lean_object* v___y_3660_, lean_object* v_b_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_){
_start:
{
lean_object* v_res_3667_; 
v_res_3667_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0(v_k_3659_, v___y_3660_, v_b_3661_, v___y_3662_, v___y_3663_, v___y_3664_, v___y_3665_);
lean_dec(v___y_3665_);
lean_dec_ref(v___y_3664_);
lean_dec(v___y_3663_);
lean_dec_ref(v___y_3662_);
lean_dec(v___y_3660_);
return v_res_3667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(lean_object* v_name_3668_, uint8_t v_bi_3669_, lean_object* v_type_3670_, lean_object* v_k_3671_, uint8_t v_kind_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_){
_start:
{
lean_object* v___f_3679_; lean_object* v___x_3680_; 
lean_inc(v___y_3673_);
v___f_3679_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3679_, 0, v_k_3671_);
lean_closure_set(v___f_3679_, 1, v___y_3673_);
v___x_3680_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3668_, v_bi_3669_, v_type_3670_, v___f_3679_, v_kind_3672_, v___y_3674_, v___y_3675_, v___y_3676_, v___y_3677_);
if (lean_obj_tag(v___x_3680_) == 0)
{
return v___x_3680_;
}
else
{
lean_object* v_a_3681_; lean_object* v___x_3683_; uint8_t v_isShared_3684_; uint8_t v_isSharedCheck_3688_; 
v_a_3681_ = lean_ctor_get(v___x_3680_, 0);
v_isSharedCheck_3688_ = !lean_is_exclusive(v___x_3680_);
if (v_isSharedCheck_3688_ == 0)
{
v___x_3683_ = v___x_3680_;
v_isShared_3684_ = v_isSharedCheck_3688_;
goto v_resetjp_3682_;
}
else
{
lean_inc(v_a_3681_);
lean_dec(v___x_3680_);
v___x_3683_ = lean_box(0);
v_isShared_3684_ = v_isSharedCheck_3688_;
goto v_resetjp_3682_;
}
v_resetjp_3682_:
{
lean_object* v___x_3686_; 
if (v_isShared_3684_ == 0)
{
v___x_3686_ = v___x_3683_;
goto v_reusejp_3685_;
}
else
{
lean_object* v_reuseFailAlloc_3687_; 
v_reuseFailAlloc_3687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3687_, 0, v_a_3681_);
v___x_3686_ = v_reuseFailAlloc_3687_;
goto v_reusejp_3685_;
}
v_reusejp_3685_:
{
return v___x_3686_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___boxed(lean_object* v_name_3689_, lean_object* v_bi_3690_, lean_object* v_type_3691_, lean_object* v_k_3692_, lean_object* v_kind_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_){
_start:
{
uint8_t v_bi_boxed_3700_; uint8_t v_kind_boxed_3701_; lean_object* v_res_3702_; 
v_bi_boxed_3700_ = lean_unbox(v_bi_3690_);
v_kind_boxed_3701_ = lean_unbox(v_kind_3693_);
v_res_3702_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_name_3689_, v_bi_boxed_3700_, v_type_3691_, v_k_3692_, v_kind_boxed_3701_, v___y_3694_, v___y_3695_, v___y_3696_, v___y_3697_, v___y_3698_);
lean_dec(v___y_3698_);
lean_dec_ref(v___y_3697_);
lean_dec(v___y_3696_);
lean_dec_ref(v___y_3695_);
lean_dec(v___y_3694_);
return v_res_3702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg(lean_object* v_name_3703_, lean_object* v_type_3704_, lean_object* v_val_3705_, lean_object* v_k_3706_, uint8_t v_nondep_3707_, uint8_t v_kind_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_){
_start:
{
lean_object* v___f_3715_; lean_object* v___x_3716_; 
lean_inc(v___y_3709_);
v___f_3715_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3715_, 0, v_k_3706_);
lean_closure_set(v___f_3715_, 1, v___y_3709_);
v___x_3716_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_3703_, v_type_3704_, v_val_3705_, v___f_3715_, v_nondep_3707_, v_kind_3708_, v___y_3710_, v___y_3711_, v___y_3712_, v___y_3713_);
if (lean_obj_tag(v___x_3716_) == 0)
{
return v___x_3716_;
}
else
{
lean_object* v_a_3717_; lean_object* v___x_3719_; uint8_t v_isShared_3720_; uint8_t v_isSharedCheck_3724_; 
v_a_3717_ = lean_ctor_get(v___x_3716_, 0);
v_isSharedCheck_3724_ = !lean_is_exclusive(v___x_3716_);
if (v_isSharedCheck_3724_ == 0)
{
v___x_3719_ = v___x_3716_;
v_isShared_3720_ = v_isSharedCheck_3724_;
goto v_resetjp_3718_;
}
else
{
lean_inc(v_a_3717_);
lean_dec(v___x_3716_);
v___x_3719_ = lean_box(0);
v_isShared_3720_ = v_isSharedCheck_3724_;
goto v_resetjp_3718_;
}
v_resetjp_3718_:
{
lean_object* v___x_3722_; 
if (v_isShared_3720_ == 0)
{
v___x_3722_ = v___x_3719_;
goto v_reusejp_3721_;
}
else
{
lean_object* v_reuseFailAlloc_3723_; 
v_reuseFailAlloc_3723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3723_, 0, v_a_3717_);
v___x_3722_ = v_reuseFailAlloc_3723_;
goto v_reusejp_3721_;
}
v_reusejp_3721_:
{
return v___x_3722_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg___boxed(lean_object* v_name_3725_, lean_object* v_type_3726_, lean_object* v_val_3727_, lean_object* v_k_3728_, lean_object* v_nondep_3729_, lean_object* v_kind_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_){
_start:
{
uint8_t v_nondep_boxed_3737_; uint8_t v_kind_boxed_3738_; lean_object* v_res_3739_; 
v_nondep_boxed_3737_ = lean_unbox(v_nondep_3729_);
v_kind_boxed_3738_ = lean_unbox(v_kind_3730_);
v_res_3739_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg(v_name_3725_, v_type_3726_, v_val_3727_, v_k_3728_, v_nondep_boxed_3737_, v_kind_boxed_3738_, v___y_3731_, v___y_3732_, v___y_3733_, v___y_3734_, v___y_3735_);
lean_dec(v___y_3735_);
lean_dec_ref(v___y_3734_);
lean_dec(v___y_3733_);
lean_dec_ref(v___y_3732_);
lean_dec(v___y_3731_);
return v_res_3739_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0(lean_object* v_00_u03b1_3740_, lean_object* v_x_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_){
_start:
{
lean_object* v___x_3747_; lean_object* v___x_3748_; 
v___x_3747_ = lean_apply_1(v_x_3741_, lean_box(0));
v___x_3748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3748_, 0, v___x_3747_);
return v___x_3748_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0___boxed(lean_object* v_00_u03b1_3749_, lean_object* v_x_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_){
_start:
{
lean_object* v_res_3756_; 
v_res_3756_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0(v_00_u03b1_3749_, v_x_3750_, v___y_3751_, v___y_3752_, v___y_3753_, v___y_3754_);
lean_dec(v___y_3754_);
lean_dec_ref(v___y_3753_);
lean_dec(v___y_3752_);
lean_dec_ref(v___y_3751_);
return v_res_3756_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg(lean_object* v_ref_3757_){
_start:
{
lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; 
v___x_3759_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5);
v___x_3760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3760_, 0, v_ref_3757_);
lean_ctor_set(v___x_3760_, 1, v___x_3759_);
v___x_3761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3761_, 0, v___x_3760_);
return v___x_3761_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg___boxed(lean_object* v_ref_3762_, lean_object* v___y_3763_){
_start:
{
lean_object* v_res_3764_; 
v_res_3764_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg(v_ref_3762_);
return v_res_3764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg(lean_object* v_x_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_){
_start:
{
lean_object* v___y_3773_; lean_object* v_fileName_3782_; lean_object* v_fileMap_3783_; lean_object* v_options_3784_; lean_object* v_currRecDepth_3785_; lean_object* v_maxRecDepth_3786_; lean_object* v_ref_3787_; lean_object* v_currNamespace_3788_; lean_object* v_openDecls_3789_; lean_object* v_initHeartbeats_3790_; lean_object* v_maxHeartbeats_3791_; lean_object* v_quotContext_3792_; lean_object* v_currMacroScope_3793_; uint8_t v_diag_3794_; lean_object* v_cancelTk_x3f_3795_; uint8_t v_suppressElabErrors_3796_; lean_object* v_inheritedTraceOptions_3797_; lean_object* v___x_3803_; uint8_t v___x_3804_; 
v_fileName_3782_ = lean_ctor_get(v___y_3769_, 0);
v_fileMap_3783_ = lean_ctor_get(v___y_3769_, 1);
v_options_3784_ = lean_ctor_get(v___y_3769_, 2);
v_currRecDepth_3785_ = lean_ctor_get(v___y_3769_, 3);
v_maxRecDepth_3786_ = lean_ctor_get(v___y_3769_, 4);
v_ref_3787_ = lean_ctor_get(v___y_3769_, 5);
v_currNamespace_3788_ = lean_ctor_get(v___y_3769_, 6);
v_openDecls_3789_ = lean_ctor_get(v___y_3769_, 7);
v_initHeartbeats_3790_ = lean_ctor_get(v___y_3769_, 8);
v_maxHeartbeats_3791_ = lean_ctor_get(v___y_3769_, 9);
v_quotContext_3792_ = lean_ctor_get(v___y_3769_, 10);
v_currMacroScope_3793_ = lean_ctor_get(v___y_3769_, 11);
v_diag_3794_ = lean_ctor_get_uint8(v___y_3769_, sizeof(void*)*14);
v_cancelTk_x3f_3795_ = lean_ctor_get(v___y_3769_, 12);
v_suppressElabErrors_3796_ = lean_ctor_get_uint8(v___y_3769_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3797_ = lean_ctor_get(v___y_3769_, 13);
v___x_3803_ = lean_unsigned_to_nat(0u);
v___x_3804_ = lean_nat_dec_eq(v_maxRecDepth_3786_, v___x_3803_);
if (v___x_3804_ == 0)
{
uint8_t v___x_3805_; 
v___x_3805_ = lean_nat_dec_eq(v_currRecDepth_3785_, v_maxRecDepth_3786_);
if (v___x_3805_ == 0)
{
goto v___jp_3798_;
}
else
{
lean_object* v___x_3806_; 
lean_dec_ref(v_x_3765_);
lean_inc(v_ref_3787_);
v___x_3806_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg(v_ref_3787_);
v___y_3773_ = v___x_3806_;
goto v___jp_3772_;
}
}
else
{
goto v___jp_3798_;
}
v___jp_3772_:
{
if (lean_obj_tag(v___y_3773_) == 0)
{
return v___y_3773_;
}
else
{
lean_object* v_a_3774_; lean_object* v___x_3776_; uint8_t v_isShared_3777_; uint8_t v_isSharedCheck_3781_; 
v_a_3774_ = lean_ctor_get(v___y_3773_, 0);
v_isSharedCheck_3781_ = !lean_is_exclusive(v___y_3773_);
if (v_isSharedCheck_3781_ == 0)
{
v___x_3776_ = v___y_3773_;
v_isShared_3777_ = v_isSharedCheck_3781_;
goto v_resetjp_3775_;
}
else
{
lean_inc(v_a_3774_);
lean_dec(v___y_3773_);
v___x_3776_ = lean_box(0);
v_isShared_3777_ = v_isSharedCheck_3781_;
goto v_resetjp_3775_;
}
v_resetjp_3775_:
{
lean_object* v___x_3779_; 
if (v_isShared_3777_ == 0)
{
v___x_3779_ = v___x_3776_;
goto v_reusejp_3778_;
}
else
{
lean_object* v_reuseFailAlloc_3780_; 
v_reuseFailAlloc_3780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3780_, 0, v_a_3774_);
v___x_3779_ = v_reuseFailAlloc_3780_;
goto v_reusejp_3778_;
}
v_reusejp_3778_:
{
return v___x_3779_;
}
}
}
}
v___jp_3798_:
{
lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; 
v___x_3799_ = lean_unsigned_to_nat(1u);
v___x_3800_ = lean_nat_add(v_currRecDepth_3785_, v___x_3799_);
lean_inc_ref(v_inheritedTraceOptions_3797_);
lean_inc(v_cancelTk_x3f_3795_);
lean_inc(v_currMacroScope_3793_);
lean_inc(v_quotContext_3792_);
lean_inc(v_maxHeartbeats_3791_);
lean_inc(v_initHeartbeats_3790_);
lean_inc(v_openDecls_3789_);
lean_inc(v_currNamespace_3788_);
lean_inc(v_ref_3787_);
lean_inc(v_maxRecDepth_3786_);
lean_inc_ref(v_options_3784_);
lean_inc_ref(v_fileMap_3783_);
lean_inc_ref(v_fileName_3782_);
v___x_3801_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3801_, 0, v_fileName_3782_);
lean_ctor_set(v___x_3801_, 1, v_fileMap_3783_);
lean_ctor_set(v___x_3801_, 2, v_options_3784_);
lean_ctor_set(v___x_3801_, 3, v___x_3800_);
lean_ctor_set(v___x_3801_, 4, v_maxRecDepth_3786_);
lean_ctor_set(v___x_3801_, 5, v_ref_3787_);
lean_ctor_set(v___x_3801_, 6, v_currNamespace_3788_);
lean_ctor_set(v___x_3801_, 7, v_openDecls_3789_);
lean_ctor_set(v___x_3801_, 8, v_initHeartbeats_3790_);
lean_ctor_set(v___x_3801_, 9, v_maxHeartbeats_3791_);
lean_ctor_set(v___x_3801_, 10, v_quotContext_3792_);
lean_ctor_set(v___x_3801_, 11, v_currMacroScope_3793_);
lean_ctor_set(v___x_3801_, 12, v_cancelTk_x3f_3795_);
lean_ctor_set(v___x_3801_, 13, v_inheritedTraceOptions_3797_);
lean_ctor_set_uint8(v___x_3801_, sizeof(void*)*14, v_diag_3794_);
lean_ctor_set_uint8(v___x_3801_, sizeof(void*)*14 + 1, v_suppressElabErrors_3796_);
lean_inc(v___y_3770_);
lean_inc(v___y_3768_);
lean_inc_ref(v___y_3767_);
lean_inc(v___y_3766_);
v___x_3802_ = lean_apply_6(v_x_3765_, v___y_3766_, v___y_3767_, v___y_3768_, v___x_3801_, v___y_3770_, lean_box(0));
v___y_3773_ = v___x_3802_;
goto v___jp_3772_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg___boxed(lean_object* v_x_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_){
_start:
{
lean_object* v_res_3814_; 
v_res_3814_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg(v_x_3807_, v___y_3808_, v___y_3809_, v___y_3810_, v___y_3811_, v___y_3812_);
lean_dec(v___y_3812_);
lean_dec_ref(v___y_3811_);
lean_dec(v___y_3810_);
lean_dec_ref(v___y_3809_);
lean_dec(v___y_3808_);
return v_res_3814_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___lam__0(lean_object* v_fvars_3815_, lean_object* v_pre_3816_, lean_object* v_post_3817_, uint8_t v_usedLetOnly_3818_, uint8_t v_skipConstInApp_3819_, uint8_t v_skipInstances_3820_, lean_object* v_body_3821_, lean_object* v_x_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_){
_start:
{
lean_object* v___x_3829_; lean_object* v___x_3830_; 
v___x_3829_ = lean_array_push(v_fvars_3815_, v_x_3822_);
v___x_3830_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6(v_pre_3816_, v_post_3817_, v_usedLetOnly_3818_, v_skipConstInApp_3819_, v_skipInstances_3820_, v___x_3829_, v_body_3821_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_);
return v___x_3830_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___lam__0___boxed(lean_object* v_fvars_3831_, lean_object* v_pre_3832_, lean_object* v_post_3833_, lean_object* v_usedLetOnly_3834_, lean_object* v_skipConstInApp_3835_, lean_object* v_skipInstances_3836_, lean_object* v_body_3837_, lean_object* v_x_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_){
_start:
{
uint8_t v_usedLetOnly_boxed_3845_; uint8_t v_skipConstInApp_boxed_3846_; uint8_t v_skipInstances_boxed_3847_; lean_object* v_res_3848_; 
v_usedLetOnly_boxed_3845_ = lean_unbox(v_usedLetOnly_3834_);
v_skipConstInApp_boxed_3846_ = lean_unbox(v_skipConstInApp_3835_);
v_skipInstances_boxed_3847_ = lean_unbox(v_skipInstances_3836_);
v_res_3848_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___lam__0(v_fvars_3831_, v_pre_3832_, v_post_3833_, v_usedLetOnly_boxed_3845_, v_skipConstInApp_boxed_3846_, v_skipInstances_boxed_3847_, v_body_3837_, v_x_3838_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_);
lean_dec(v___y_3843_);
lean_dec_ref(v___y_3842_);
lean_dec(v___y_3841_);
lean_dec_ref(v___y_3840_);
lean_dec(v___y_3839_);
return v_res_3848_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(lean_object* v_pre_3849_, lean_object* v_post_3850_, uint8_t v_usedLetOnly_3851_, uint8_t v_skipConstInApp_3852_, uint8_t v_skipInstances_3853_, lean_object* v_e_3854_, lean_object* v_a_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_){
_start:
{
lean_object* v___x_3861_; 
lean_inc_ref(v_post_3850_);
lean_inc(v___y_3859_);
lean_inc_ref(v___y_3858_);
lean_inc(v___y_3857_);
lean_inc_ref(v___y_3856_);
lean_inc_ref(v_e_3854_);
v___x_3861_ = lean_apply_6(v_post_3850_, v_e_3854_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_, lean_box(0));
if (lean_obj_tag(v___x_3861_) == 0)
{
lean_object* v_a_3862_; lean_object* v___x_3864_; uint8_t v_isShared_3865_; uint8_t v_isSharedCheck_3880_; 
v_a_3862_ = lean_ctor_get(v___x_3861_, 0);
v_isSharedCheck_3880_ = !lean_is_exclusive(v___x_3861_);
if (v_isSharedCheck_3880_ == 0)
{
v___x_3864_ = v___x_3861_;
v_isShared_3865_ = v_isSharedCheck_3880_;
goto v_resetjp_3863_;
}
else
{
lean_inc(v_a_3862_);
lean_dec(v___x_3861_);
v___x_3864_ = lean_box(0);
v_isShared_3865_ = v_isSharedCheck_3880_;
goto v_resetjp_3863_;
}
v_resetjp_3863_:
{
switch(lean_obj_tag(v_a_3862_))
{
case 0:
{
lean_object* v_e_3866_; lean_object* v___x_3868_; 
lean_dec_ref(v_e_3854_);
lean_dec_ref(v_post_3850_);
lean_dec_ref(v_pre_3849_);
v_e_3866_ = lean_ctor_get(v_a_3862_, 0);
lean_inc_ref(v_e_3866_);
lean_dec_ref(v_a_3862_);
if (v_isShared_3865_ == 0)
{
lean_ctor_set(v___x_3864_, 0, v_e_3866_);
v___x_3868_ = v___x_3864_;
goto v_reusejp_3867_;
}
else
{
lean_object* v_reuseFailAlloc_3869_; 
v_reuseFailAlloc_3869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3869_, 0, v_e_3866_);
v___x_3868_ = v_reuseFailAlloc_3869_;
goto v_reusejp_3867_;
}
v_reusejp_3867_:
{
return v___x_3868_;
}
}
case 1:
{
lean_object* v_e_3870_; lean_object* v___x_3871_; 
lean_del_object(v___x_3864_);
lean_dec_ref(v_e_3854_);
v_e_3870_ = lean_ctor_get(v_a_3862_, 0);
lean_inc_ref(v_e_3870_);
lean_dec_ref(v_a_3862_);
v___x_3871_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3849_, v_post_3850_, v_usedLetOnly_3851_, v_skipConstInApp_3852_, v_skipInstances_3853_, v_e_3870_, v_a_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_);
return v___x_3871_;
}
default: 
{
lean_object* v_e_x3f_3872_; 
lean_dec_ref(v_post_3850_);
lean_dec_ref(v_pre_3849_);
v_e_x3f_3872_ = lean_ctor_get(v_a_3862_, 0);
lean_inc(v_e_x3f_3872_);
lean_dec_ref(v_a_3862_);
if (lean_obj_tag(v_e_x3f_3872_) == 0)
{
lean_object* v___x_3874_; 
if (v_isShared_3865_ == 0)
{
lean_ctor_set(v___x_3864_, 0, v_e_3854_);
v___x_3874_ = v___x_3864_;
goto v_reusejp_3873_;
}
else
{
lean_object* v_reuseFailAlloc_3875_; 
v_reuseFailAlloc_3875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3875_, 0, v_e_3854_);
v___x_3874_ = v_reuseFailAlloc_3875_;
goto v_reusejp_3873_;
}
v_reusejp_3873_:
{
return v___x_3874_;
}
}
else
{
lean_object* v_val_3876_; lean_object* v___x_3878_; 
lean_dec_ref(v_e_3854_);
v_val_3876_ = lean_ctor_get(v_e_x3f_3872_, 0);
lean_inc(v_val_3876_);
lean_dec_ref(v_e_x3f_3872_);
if (v_isShared_3865_ == 0)
{
lean_ctor_set(v___x_3864_, 0, v_val_3876_);
v___x_3878_ = v___x_3864_;
goto v_reusejp_3877_;
}
else
{
lean_object* v_reuseFailAlloc_3879_; 
v_reuseFailAlloc_3879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3879_, 0, v_val_3876_);
v___x_3878_ = v_reuseFailAlloc_3879_;
goto v_reusejp_3877_;
}
v_reusejp_3877_:
{
return v___x_3878_;
}
}
}
}
}
}
else
{
lean_object* v_a_3881_; lean_object* v___x_3883_; uint8_t v_isShared_3884_; uint8_t v_isSharedCheck_3888_; 
lean_dec_ref(v_e_3854_);
lean_dec_ref(v_post_3850_);
lean_dec_ref(v_pre_3849_);
v_a_3881_ = lean_ctor_get(v___x_3861_, 0);
v_isSharedCheck_3888_ = !lean_is_exclusive(v___x_3861_);
if (v_isSharedCheck_3888_ == 0)
{
v___x_3883_ = v___x_3861_;
v_isShared_3884_ = v_isSharedCheck_3888_;
goto v_resetjp_3882_;
}
else
{
lean_inc(v_a_3881_);
lean_dec(v___x_3861_);
v___x_3883_ = lean_box(0);
v_isShared_3884_ = v_isSharedCheck_3888_;
goto v_resetjp_3882_;
}
v_resetjp_3882_:
{
lean_object* v___x_3886_; 
if (v_isShared_3884_ == 0)
{
v___x_3886_ = v___x_3883_;
goto v_reusejp_3885_;
}
else
{
lean_object* v_reuseFailAlloc_3887_; 
v_reuseFailAlloc_3887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3887_, 0, v_a_3881_);
v___x_3886_ = v_reuseFailAlloc_3887_;
goto v_reusejp_3885_;
}
v_reusejp_3885_:
{
return v___x_3886_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6(lean_object* v_pre_3889_, lean_object* v_post_3890_, uint8_t v_usedLetOnly_3891_, uint8_t v_skipConstInApp_3892_, uint8_t v_skipInstances_3893_, lean_object* v_fvars_3894_, lean_object* v_e_3895_, lean_object* v_a_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_){
_start:
{
if (lean_obj_tag(v_e_3895_) == 6)
{
lean_object* v_binderName_3902_; lean_object* v_binderType_3903_; lean_object* v_body_3904_; uint8_t v_binderInfo_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; 
v_binderName_3902_ = lean_ctor_get(v_e_3895_, 0);
lean_inc(v_binderName_3902_);
v_binderType_3903_ = lean_ctor_get(v_e_3895_, 1);
lean_inc_ref(v_binderType_3903_);
v_body_3904_ = lean_ctor_get(v_e_3895_, 2);
lean_inc_ref(v_body_3904_);
v_binderInfo_3905_ = lean_ctor_get_uint8(v_e_3895_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_3895_);
v___x_3906_ = lean_expr_instantiate_rev(v_binderType_3903_, v_fvars_3894_);
lean_dec_ref(v_binderType_3903_);
lean_inc_ref(v_post_3890_);
lean_inc_ref(v_pre_3889_);
v___x_3907_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3889_, v_post_3890_, v_usedLetOnly_3891_, v_skipConstInApp_3892_, v_skipInstances_3893_, v___x_3906_, v_a_3896_, v___y_3897_, v___y_3898_, v___y_3899_, v___y_3900_);
if (lean_obj_tag(v___x_3907_) == 0)
{
lean_object* v_a_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___f_3912_; uint8_t v___x_3913_; lean_object* v___x_3914_; 
v_a_3908_ = lean_ctor_get(v___x_3907_, 0);
lean_inc(v_a_3908_);
lean_dec_ref(v___x_3907_);
v___x_3909_ = lean_box(v_usedLetOnly_3891_);
v___x_3910_ = lean_box(v_skipConstInApp_3892_);
v___x_3911_ = lean_box(v_skipInstances_3893_);
v___f_3912_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___lam__0___boxed), 14, 7);
lean_closure_set(v___f_3912_, 0, v_fvars_3894_);
lean_closure_set(v___f_3912_, 1, v_pre_3889_);
lean_closure_set(v___f_3912_, 2, v_post_3890_);
lean_closure_set(v___f_3912_, 3, v___x_3909_);
lean_closure_set(v___f_3912_, 4, v___x_3910_);
lean_closure_set(v___f_3912_, 5, v___x_3911_);
lean_closure_set(v___f_3912_, 6, v_body_3904_);
v___x_3913_ = 0;
v___x_3914_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_binderName_3902_, v_binderInfo_3905_, v_a_3908_, v___f_3912_, v___x_3913_, v_a_3896_, v___y_3897_, v___y_3898_, v___y_3899_, v___y_3900_);
return v___x_3914_;
}
else
{
lean_dec_ref(v_body_3904_);
lean_dec(v_binderName_3902_);
lean_dec_ref(v_fvars_3894_);
lean_dec_ref(v_post_3890_);
lean_dec_ref(v_pre_3889_);
return v___x_3907_;
}
}
else
{
lean_object* v___x_3915_; lean_object* v___x_3916_; 
v___x_3915_ = lean_expr_instantiate_rev(v_e_3895_, v_fvars_3894_);
lean_dec_ref(v_e_3895_);
lean_inc_ref(v_post_3890_);
lean_inc_ref(v_pre_3889_);
v___x_3916_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3889_, v_post_3890_, v_usedLetOnly_3891_, v_skipConstInApp_3892_, v_skipInstances_3893_, v___x_3915_, v_a_3896_, v___y_3897_, v___y_3898_, v___y_3899_, v___y_3900_);
if (lean_obj_tag(v___x_3916_) == 0)
{
lean_object* v_a_3917_; uint8_t v___x_3918_; uint8_t v___x_3919_; uint8_t v___x_3920_; lean_object* v___x_3921_; 
v_a_3917_ = lean_ctor_get(v___x_3916_, 0);
lean_inc(v_a_3917_);
lean_dec_ref(v___x_3916_);
v___x_3918_ = 0;
v___x_3919_ = 1;
v___x_3920_ = 1;
v___x_3921_ = l_Lean_Meta_mkLambdaFVars(v_fvars_3894_, v_a_3917_, v___x_3918_, v_usedLetOnly_3891_, v___x_3918_, v___x_3919_, v___x_3920_, v___y_3897_, v___y_3898_, v___y_3899_, v___y_3900_);
lean_dec_ref(v_fvars_3894_);
if (lean_obj_tag(v___x_3921_) == 0)
{
lean_object* v_a_3922_; lean_object* v___x_3923_; 
v_a_3922_ = lean_ctor_get(v___x_3921_, 0);
lean_inc(v_a_3922_);
lean_dec_ref(v___x_3921_);
v___x_3923_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_3889_, v_post_3890_, v_usedLetOnly_3891_, v_skipConstInApp_3892_, v_skipInstances_3893_, v_a_3922_, v_a_3896_, v___y_3897_, v___y_3898_, v___y_3899_, v___y_3900_);
return v___x_3923_;
}
else
{
lean_dec_ref(v_post_3890_);
lean_dec_ref(v_pre_3889_);
return v___x_3921_;
}
}
else
{
lean_dec_ref(v_fvars_3894_);
lean_dec_ref(v_post_3890_);
lean_dec_ref(v_pre_3889_);
return v___x_3916_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___lam__0(lean_object* v_fvars_3924_, lean_object* v_pre_3925_, lean_object* v_post_3926_, uint8_t v_usedLetOnly_3927_, uint8_t v_skipConstInApp_3928_, uint8_t v_skipInstances_3929_, lean_object* v_body_3930_, lean_object* v_x_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_){
_start:
{
lean_object* v___x_3938_; lean_object* v___x_3939_; 
v___x_3938_ = lean_array_push(v_fvars_3924_, v_x_3931_);
v___x_3939_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7(v_pre_3925_, v_post_3926_, v_usedLetOnly_3927_, v_skipConstInApp_3928_, v_skipInstances_3929_, v___x_3938_, v_body_3930_, v___y_3932_, v___y_3933_, v___y_3934_, v___y_3935_, v___y_3936_);
return v___x_3939_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___lam__0___boxed(lean_object* v_fvars_3940_, lean_object* v_pre_3941_, lean_object* v_post_3942_, lean_object* v_usedLetOnly_3943_, lean_object* v_skipConstInApp_3944_, lean_object* v_skipInstances_3945_, lean_object* v_body_3946_, lean_object* v_x_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_){
_start:
{
uint8_t v_usedLetOnly_boxed_3954_; uint8_t v_skipConstInApp_boxed_3955_; uint8_t v_skipInstances_boxed_3956_; lean_object* v_res_3957_; 
v_usedLetOnly_boxed_3954_ = lean_unbox(v_usedLetOnly_3943_);
v_skipConstInApp_boxed_3955_ = lean_unbox(v_skipConstInApp_3944_);
v_skipInstances_boxed_3956_ = lean_unbox(v_skipInstances_3945_);
v_res_3957_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___lam__0(v_fvars_3940_, v_pre_3941_, v_post_3942_, v_usedLetOnly_boxed_3954_, v_skipConstInApp_boxed_3955_, v_skipInstances_boxed_3956_, v_body_3946_, v_x_3947_, v___y_3948_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_);
lean_dec(v___y_3952_);
lean_dec_ref(v___y_3951_);
lean_dec(v___y_3950_);
lean_dec_ref(v___y_3949_);
lean_dec(v___y_3948_);
return v_res_3957_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7(lean_object* v_pre_3958_, lean_object* v_post_3959_, uint8_t v_usedLetOnly_3960_, uint8_t v_skipConstInApp_3961_, uint8_t v_skipInstances_3962_, lean_object* v_fvars_3963_, lean_object* v_e_3964_, lean_object* v_a_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_){
_start:
{
if (lean_obj_tag(v_e_3964_) == 8)
{
lean_object* v_declName_3971_; lean_object* v_type_3972_; lean_object* v_value_3973_; lean_object* v_body_3974_; uint8_t v_nondep_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; 
v_declName_3971_ = lean_ctor_get(v_e_3964_, 0);
lean_inc(v_declName_3971_);
v_type_3972_ = lean_ctor_get(v_e_3964_, 1);
lean_inc_ref(v_type_3972_);
v_value_3973_ = lean_ctor_get(v_e_3964_, 2);
lean_inc_ref(v_value_3973_);
v_body_3974_ = lean_ctor_get(v_e_3964_, 3);
lean_inc_ref(v_body_3974_);
v_nondep_3975_ = lean_ctor_get_uint8(v_e_3964_, sizeof(void*)*4 + 8);
lean_dec_ref(v_e_3964_);
v___x_3976_ = lean_expr_instantiate_rev(v_type_3972_, v_fvars_3963_);
lean_dec_ref(v_type_3972_);
lean_inc_ref(v_post_3959_);
lean_inc_ref(v_pre_3958_);
v___x_3977_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3958_, v_post_3959_, v_usedLetOnly_3960_, v_skipConstInApp_3961_, v_skipInstances_3962_, v___x_3976_, v_a_3965_, v___y_3966_, v___y_3967_, v___y_3968_, v___y_3969_);
if (lean_obj_tag(v___x_3977_) == 0)
{
lean_object* v_a_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; 
v_a_3978_ = lean_ctor_get(v___x_3977_, 0);
lean_inc(v_a_3978_);
lean_dec_ref(v___x_3977_);
v___x_3979_ = lean_expr_instantiate_rev(v_value_3973_, v_fvars_3963_);
lean_dec_ref(v_value_3973_);
lean_inc_ref(v_post_3959_);
lean_inc_ref(v_pre_3958_);
v___x_3980_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3958_, v_post_3959_, v_usedLetOnly_3960_, v_skipConstInApp_3961_, v_skipInstances_3962_, v___x_3979_, v_a_3965_, v___y_3966_, v___y_3967_, v___y_3968_, v___y_3969_);
if (lean_obj_tag(v___x_3980_) == 0)
{
lean_object* v_a_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___f_3985_; uint8_t v___x_3986_; lean_object* v___x_3987_; 
v_a_3981_ = lean_ctor_get(v___x_3980_, 0);
lean_inc(v_a_3981_);
lean_dec_ref(v___x_3980_);
v___x_3982_ = lean_box(v_usedLetOnly_3960_);
v___x_3983_ = lean_box(v_skipConstInApp_3961_);
v___x_3984_ = lean_box(v_skipInstances_3962_);
v___f_3985_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___lam__0___boxed), 14, 7);
lean_closure_set(v___f_3985_, 0, v_fvars_3963_);
lean_closure_set(v___f_3985_, 1, v_pre_3958_);
lean_closure_set(v___f_3985_, 2, v_post_3959_);
lean_closure_set(v___f_3985_, 3, v___x_3982_);
lean_closure_set(v___f_3985_, 4, v___x_3983_);
lean_closure_set(v___f_3985_, 5, v___x_3984_);
lean_closure_set(v___f_3985_, 6, v_body_3974_);
v___x_3986_ = 0;
v___x_3987_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg(v_declName_3971_, v_a_3978_, v_a_3981_, v___f_3985_, v_nondep_3975_, v___x_3986_, v_a_3965_, v___y_3966_, v___y_3967_, v___y_3968_, v___y_3969_);
return v___x_3987_;
}
else
{
lean_dec(v_a_3978_);
lean_dec_ref(v_body_3974_);
lean_dec(v_declName_3971_);
lean_dec_ref(v_fvars_3963_);
lean_dec_ref(v_post_3959_);
lean_dec_ref(v_pre_3958_);
return v___x_3980_;
}
}
else
{
lean_dec_ref(v_body_3974_);
lean_dec_ref(v_value_3973_);
lean_dec(v_declName_3971_);
lean_dec_ref(v_fvars_3963_);
lean_dec_ref(v_post_3959_);
lean_dec_ref(v_pre_3958_);
return v___x_3977_;
}
}
else
{
lean_object* v___x_3988_; lean_object* v___x_3989_; 
v___x_3988_ = lean_expr_instantiate_rev(v_e_3964_, v_fvars_3963_);
lean_dec_ref(v_e_3964_);
lean_inc_ref(v_post_3959_);
lean_inc_ref(v_pre_3958_);
v___x_3989_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3958_, v_post_3959_, v_usedLetOnly_3960_, v_skipConstInApp_3961_, v_skipInstances_3962_, v___x_3988_, v_a_3965_, v___y_3966_, v___y_3967_, v___y_3968_, v___y_3969_);
if (lean_obj_tag(v___x_3989_) == 0)
{
lean_object* v_a_3990_; uint8_t v___x_3991_; uint8_t v___x_3992_; lean_object* v___x_3993_; 
v_a_3990_ = lean_ctor_get(v___x_3989_, 0);
lean_inc(v_a_3990_);
lean_dec_ref(v___x_3989_);
v___x_3991_ = 0;
v___x_3992_ = 1;
v___x_3993_ = l_Lean_Meta_mkLetFVars(v_fvars_3963_, v_a_3990_, v_usedLetOnly_3960_, v___x_3991_, v___x_3992_, v___y_3966_, v___y_3967_, v___y_3968_, v___y_3969_);
lean_dec_ref(v_fvars_3963_);
if (lean_obj_tag(v___x_3993_) == 0)
{
lean_object* v_a_3994_; lean_object* v___x_3995_; 
v_a_3994_ = lean_ctor_get(v___x_3993_, 0);
lean_inc(v_a_3994_);
lean_dec_ref(v___x_3993_);
v___x_3995_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_3958_, v_post_3959_, v_usedLetOnly_3960_, v_skipConstInApp_3961_, v_skipInstances_3962_, v_a_3994_, v_a_3965_, v___y_3966_, v___y_3967_, v___y_3968_, v___y_3969_);
return v___x_3995_;
}
else
{
lean_dec_ref(v_post_3959_);
lean_dec_ref(v_pre_3958_);
return v___x_3993_;
}
}
else
{
lean_dec_ref(v_fvars_3963_);
lean_dec_ref(v_post_3959_);
lean_dec_ref(v_pre_3958_);
return v___x_3989_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__2(lean_object* v_pre_3996_, lean_object* v_post_3997_, uint8_t v_usedLetOnly_3998_, uint8_t v_skipConstInApp_3999_, uint8_t v_skipInstances_4000_, size_t v_sz_4001_, size_t v_i_4002_, lean_object* v_bs_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_){
_start:
{
uint8_t v___x_4010_; 
v___x_4010_ = lean_usize_dec_lt(v_i_4002_, v_sz_4001_);
if (v___x_4010_ == 0)
{
lean_object* v___x_4011_; 
lean_dec_ref(v_post_3997_);
lean_dec_ref(v_pre_3996_);
v___x_4011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4011_, 0, v_bs_4003_);
return v___x_4011_;
}
else
{
lean_object* v_v_4012_; lean_object* v___x_4013_; 
v_v_4012_ = lean_array_uget_borrowed(v_bs_4003_, v_i_4002_);
lean_inc(v_v_4012_);
lean_inc_ref(v_post_3997_);
lean_inc_ref(v_pre_3996_);
v___x_4013_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3996_, v_post_3997_, v_usedLetOnly_3998_, v_skipConstInApp_3999_, v_skipInstances_4000_, v_v_4012_, v___y_4004_, v___y_4005_, v___y_4006_, v___y_4007_, v___y_4008_);
if (lean_obj_tag(v___x_4013_) == 0)
{
lean_object* v_a_4014_; lean_object* v___x_4015_; lean_object* v_bs_x27_4016_; size_t v___x_4017_; size_t v___x_4018_; lean_object* v___x_4019_; 
v_a_4014_ = lean_ctor_get(v___x_4013_, 0);
lean_inc(v_a_4014_);
lean_dec_ref(v___x_4013_);
v___x_4015_ = lean_unsigned_to_nat(0u);
v_bs_x27_4016_ = lean_array_uset(v_bs_4003_, v_i_4002_, v___x_4015_);
v___x_4017_ = ((size_t)1ULL);
v___x_4018_ = lean_usize_add(v_i_4002_, v___x_4017_);
v___x_4019_ = lean_array_uset(v_bs_x27_4016_, v_i_4002_, v_a_4014_);
v_i_4002_ = v___x_4018_;
v_bs_4003_ = v___x_4019_;
goto _start;
}
else
{
lean_object* v_a_4021_; lean_object* v___x_4023_; uint8_t v_isShared_4024_; uint8_t v_isSharedCheck_4028_; 
lean_dec_ref(v_bs_4003_);
lean_dec_ref(v_post_3997_);
lean_dec_ref(v_pre_3996_);
v_a_4021_ = lean_ctor_get(v___x_4013_, 0);
v_isSharedCheck_4028_ = !lean_is_exclusive(v___x_4013_);
if (v_isSharedCheck_4028_ == 0)
{
v___x_4023_ = v___x_4013_;
v_isShared_4024_ = v_isSharedCheck_4028_;
goto v_resetjp_4022_;
}
else
{
lean_inc(v_a_4021_);
lean_dec(v___x_4013_);
v___x_4023_ = lean_box(0);
v_isShared_4024_ = v_isSharedCheck_4028_;
goto v_resetjp_4022_;
}
v_resetjp_4022_:
{
lean_object* v___x_4026_; 
if (v_isShared_4024_ == 0)
{
v___x_4026_ = v___x_4023_;
goto v_reusejp_4025_;
}
else
{
lean_object* v_reuseFailAlloc_4027_; 
v_reuseFailAlloc_4027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4027_, 0, v_a_4021_);
v___x_4026_ = v_reuseFailAlloc_4027_;
goto v_reusejp_4025_;
}
v_reusejp_4025_:
{
return v___x_4026_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0(lean_object* v_pre_4029_, lean_object* v_post_4030_, uint8_t v_usedLetOnly_4031_, uint8_t v_skipConstInApp_4032_, uint8_t v_skipInstances_4033_, lean_object* v___x_4034_, lean_object* v___y_4035_, lean_object* v_b_4036_, lean_object* v_a_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_){
_start:
{
lean_object* v___x_4043_; 
v___x_4043_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4029_, v_post_4030_, v_usedLetOnly_4031_, v_skipConstInApp_4032_, v_skipInstances_4033_, v___x_4034_, v___y_4035_, v___y_4038_, v___y_4039_, v___y_4040_, v___y_4041_);
if (lean_obj_tag(v___x_4043_) == 0)
{
lean_object* v_a_4044_; lean_object* v___x_4046_; uint8_t v_isShared_4047_; uint8_t v_isSharedCheck_4053_; 
v_a_4044_ = lean_ctor_get(v___x_4043_, 0);
v_isSharedCheck_4053_ = !lean_is_exclusive(v___x_4043_);
if (v_isSharedCheck_4053_ == 0)
{
v___x_4046_ = v___x_4043_;
v_isShared_4047_ = v_isSharedCheck_4053_;
goto v_resetjp_4045_;
}
else
{
lean_inc(v_a_4044_);
lean_dec(v___x_4043_);
v___x_4046_ = lean_box(0);
v_isShared_4047_ = v_isSharedCheck_4053_;
goto v_resetjp_4045_;
}
v_resetjp_4045_:
{
lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4051_; 
v___x_4048_ = lean_array_fset(v_b_4036_, v_a_4037_, v_a_4044_);
v___x_4049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4049_, 0, v___x_4048_);
if (v_isShared_4047_ == 0)
{
lean_ctor_set(v___x_4046_, 0, v___x_4049_);
v___x_4051_ = v___x_4046_;
goto v_reusejp_4050_;
}
else
{
lean_object* v_reuseFailAlloc_4052_; 
v_reuseFailAlloc_4052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4052_, 0, v___x_4049_);
v___x_4051_ = v_reuseFailAlloc_4052_;
goto v_reusejp_4050_;
}
v_reusejp_4050_:
{
return v___x_4051_;
}
}
}
else
{
lean_object* v_a_4054_; lean_object* v___x_4056_; uint8_t v_isShared_4057_; uint8_t v_isSharedCheck_4061_; 
lean_dec_ref(v_b_4036_);
v_a_4054_ = lean_ctor_get(v___x_4043_, 0);
v_isSharedCheck_4061_ = !lean_is_exclusive(v___x_4043_);
if (v_isSharedCheck_4061_ == 0)
{
v___x_4056_ = v___x_4043_;
v_isShared_4057_ = v_isSharedCheck_4061_;
goto v_resetjp_4055_;
}
else
{
lean_inc(v_a_4054_);
lean_dec(v___x_4043_);
v___x_4056_ = lean_box(0);
v_isShared_4057_ = v_isSharedCheck_4061_;
goto v_resetjp_4055_;
}
v_resetjp_4055_:
{
lean_object* v___x_4059_; 
if (v_isShared_4057_ == 0)
{
v___x_4059_ = v___x_4056_;
goto v_reusejp_4058_;
}
else
{
lean_object* v_reuseFailAlloc_4060_; 
v_reuseFailAlloc_4060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4060_, 0, v_a_4054_);
v___x_4059_ = v_reuseFailAlloc_4060_;
goto v_reusejp_4058_;
}
v_reusejp_4058_:
{
return v___x_4059_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed(lean_object* v_pre_4062_, lean_object* v_post_4063_, lean_object* v_usedLetOnly_4064_, lean_object* v_skipConstInApp_4065_, lean_object* v_skipInstances_4066_, lean_object* v___x_4067_, lean_object* v___y_4068_, lean_object* v_b_4069_, lean_object* v_a_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_){
_start:
{
uint8_t v_usedLetOnly_boxed_4076_; uint8_t v_skipConstInApp_boxed_4077_; uint8_t v_skipInstances_boxed_4078_; lean_object* v_res_4079_; 
v_usedLetOnly_boxed_4076_ = lean_unbox(v_usedLetOnly_4064_);
v_skipConstInApp_boxed_4077_ = lean_unbox(v_skipConstInApp_4065_);
v_skipInstances_boxed_4078_ = lean_unbox(v_skipInstances_4066_);
v_res_4079_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0(v_pre_4062_, v_post_4063_, v_usedLetOnly_boxed_4076_, v_skipConstInApp_boxed_4077_, v_skipInstances_boxed_4078_, v___x_4067_, v___y_4068_, v_b_4069_, v_a_4070_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_);
lean_dec(v___y_4074_);
lean_dec_ref(v___y_4073_);
lean_dec(v___y_4072_);
lean_dec_ref(v___y_4071_);
lean_dec(v_a_4070_);
lean_dec(v___y_4068_);
return v_res_4079_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg(lean_object* v_upperBound_4080_, lean_object* v___x_4081_, lean_object* v_pre_4082_, lean_object* v_post_4083_, uint8_t v_usedLetOnly_4084_, uint8_t v_skipConstInApp_4085_, uint8_t v_skipInstances_4086_, lean_object* v_a_4087_, lean_object* v_b_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_){
_start:
{
lean_object* v___y_4096_; uint8_t v___x_4119_; 
v___x_4119_ = lean_nat_dec_lt(v_a_4087_, v_upperBound_4080_);
if (v___x_4119_ == 0)
{
lean_object* v___x_4120_; 
lean_dec(v_a_4087_);
lean_dec_ref(v_post_4083_);
lean_dec_ref(v_pre_4082_);
v___x_4120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4120_, 0, v_b_4088_);
return v___x_4120_;
}
else
{
lean_object* v___x_4121_; lean_object* v___x_4122_; uint8_t v___x_4123_; 
v___x_4121_ = lean_array_fget_borrowed(v_b_4088_, v_a_4087_);
v___x_4122_ = lean_array_get_size(v___x_4081_);
v___x_4123_ = lean_nat_dec_lt(v_a_4087_, v___x_4122_);
if (v___x_4123_ == 0)
{
lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___f_4127_; 
lean_inc(v___x_4121_);
v___x_4124_ = lean_box(v_usedLetOnly_4084_);
v___x_4125_ = lean_box(v_skipConstInApp_4085_);
v___x_4126_ = lean_box(v_skipInstances_4086_);
lean_inc(v_a_4087_);
lean_inc(v___y_4089_);
lean_inc_ref(v_post_4083_);
lean_inc_ref(v_pre_4082_);
v___f_4127_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_4127_, 0, v_pre_4082_);
lean_closure_set(v___f_4127_, 1, v_post_4083_);
lean_closure_set(v___f_4127_, 2, v___x_4124_);
lean_closure_set(v___f_4127_, 3, v___x_4125_);
lean_closure_set(v___f_4127_, 4, v___x_4126_);
lean_closure_set(v___f_4127_, 5, v___x_4121_);
lean_closure_set(v___f_4127_, 6, v___y_4089_);
lean_closure_set(v___f_4127_, 7, v_b_4088_);
lean_closure_set(v___f_4127_, 8, v_a_4087_);
v___y_4096_ = v___f_4127_;
goto v___jp_4095_;
}
else
{
lean_object* v___x_4128_; uint8_t v_isInstance_4129_; 
v___x_4128_ = lean_array_fget_borrowed(v___x_4081_, v_a_4087_);
v_isInstance_4129_ = lean_ctor_get_uint8(v___x_4128_, sizeof(void*)*1 + 4);
if (v_isInstance_4129_ == 0)
{
lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; lean_object* v___f_4133_; 
lean_inc(v___x_4121_);
v___x_4130_ = lean_box(v_usedLetOnly_4084_);
v___x_4131_ = lean_box(v_skipConstInApp_4085_);
v___x_4132_ = lean_box(v_skipInstances_4086_);
lean_inc(v_a_4087_);
lean_inc(v___y_4089_);
lean_inc_ref(v_post_4083_);
lean_inc_ref(v_pre_4082_);
v___f_4133_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_4133_, 0, v_pre_4082_);
lean_closure_set(v___f_4133_, 1, v_post_4083_);
lean_closure_set(v___f_4133_, 2, v___x_4130_);
lean_closure_set(v___f_4133_, 3, v___x_4131_);
lean_closure_set(v___f_4133_, 4, v___x_4132_);
lean_closure_set(v___f_4133_, 5, v___x_4121_);
lean_closure_set(v___f_4133_, 6, v___y_4089_);
lean_closure_set(v___f_4133_, 7, v_b_4088_);
lean_closure_set(v___f_4133_, 8, v_a_4087_);
v___y_4096_ = v___f_4133_;
goto v___jp_4095_;
}
else
{
lean_object* v___x_4134_; lean_object* v___f_4135_; 
v___x_4134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4134_, 0, v_b_4088_);
v___f_4135_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_4135_, 0, v___x_4134_);
v___y_4096_ = v___f_4135_;
goto v___jp_4095_;
}
}
}
v___jp_4095_:
{
lean_object* v___x_4097_; 
lean_inc(v___y_4093_);
lean_inc_ref(v___y_4092_);
lean_inc(v___y_4091_);
lean_inc_ref(v___y_4090_);
v___x_4097_ = lean_apply_5(v___y_4096_, v___y_4090_, v___y_4091_, v___y_4092_, v___y_4093_, lean_box(0));
if (lean_obj_tag(v___x_4097_) == 0)
{
lean_object* v_a_4098_; lean_object* v___x_4100_; uint8_t v_isShared_4101_; uint8_t v_isSharedCheck_4110_; 
v_a_4098_ = lean_ctor_get(v___x_4097_, 0);
v_isSharedCheck_4110_ = !lean_is_exclusive(v___x_4097_);
if (v_isSharedCheck_4110_ == 0)
{
v___x_4100_ = v___x_4097_;
v_isShared_4101_ = v_isSharedCheck_4110_;
goto v_resetjp_4099_;
}
else
{
lean_inc(v_a_4098_);
lean_dec(v___x_4097_);
v___x_4100_ = lean_box(0);
v_isShared_4101_ = v_isSharedCheck_4110_;
goto v_resetjp_4099_;
}
v_resetjp_4099_:
{
if (lean_obj_tag(v_a_4098_) == 0)
{
lean_object* v_a_4102_; lean_object* v___x_4104_; 
lean_dec(v_a_4087_);
lean_dec_ref(v_post_4083_);
lean_dec_ref(v_pre_4082_);
v_a_4102_ = lean_ctor_get(v_a_4098_, 0);
lean_inc(v_a_4102_);
lean_dec_ref(v_a_4098_);
if (v_isShared_4101_ == 0)
{
lean_ctor_set(v___x_4100_, 0, v_a_4102_);
v___x_4104_ = v___x_4100_;
goto v_reusejp_4103_;
}
else
{
lean_object* v_reuseFailAlloc_4105_; 
v_reuseFailAlloc_4105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4105_, 0, v_a_4102_);
v___x_4104_ = v_reuseFailAlloc_4105_;
goto v_reusejp_4103_;
}
v_reusejp_4103_:
{
return v___x_4104_;
}
}
else
{
lean_object* v_a_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; 
lean_del_object(v___x_4100_);
v_a_4106_ = lean_ctor_get(v_a_4098_, 0);
lean_inc(v_a_4106_);
lean_dec_ref(v_a_4098_);
v___x_4107_ = lean_unsigned_to_nat(1u);
v___x_4108_ = lean_nat_add(v_a_4087_, v___x_4107_);
lean_dec(v_a_4087_);
v_a_4087_ = v___x_4108_;
v_b_4088_ = v_a_4106_;
goto _start;
}
}
}
else
{
lean_object* v_a_4111_; lean_object* v___x_4113_; uint8_t v_isShared_4114_; uint8_t v_isSharedCheck_4118_; 
lean_dec(v_a_4087_);
lean_dec_ref(v_post_4083_);
lean_dec_ref(v_pre_4082_);
v_a_4111_ = lean_ctor_get(v___x_4097_, 0);
v_isSharedCheck_4118_ = !lean_is_exclusive(v___x_4097_);
if (v_isSharedCheck_4118_ == 0)
{
v___x_4113_ = v___x_4097_;
v_isShared_4114_ = v_isSharedCheck_4118_;
goto v_resetjp_4112_;
}
else
{
lean_inc(v_a_4111_);
lean_dec(v___x_4097_);
v___x_4113_ = lean_box(0);
v_isShared_4114_ = v_isSharedCheck_4118_;
goto v_resetjp_4112_;
}
v_resetjp_4112_:
{
lean_object* v___x_4116_; 
if (v_isShared_4114_ == 0)
{
v___x_4116_ = v___x_4113_;
goto v_reusejp_4115_;
}
else
{
lean_object* v_reuseFailAlloc_4117_; 
v_reuseFailAlloc_4117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4117_, 0, v_a_4111_);
v___x_4116_ = v_reuseFailAlloc_4117_;
goto v_reusejp_4115_;
}
v_reusejp_4115_:
{
return v___x_4116_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__8(uint8_t v_skipInstances_4136_, lean_object* v_pre_4137_, lean_object* v_post_4138_, uint8_t v_usedLetOnly_4139_, uint8_t v_skipConstInApp_4140_, lean_object* v_x_4141_, lean_object* v_x_4142_, lean_object* v_x_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_){
_start:
{
lean_object* v_f_4151_; lean_object* v___y_4152_; lean_object* v___y_4153_; lean_object* v___y_4154_; lean_object* v___y_4155_; lean_object* v___y_4156_; 
if (lean_obj_tag(v_x_4141_) == 5)
{
lean_object* v_fn_4199_; lean_object* v_arg_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; 
v_fn_4199_ = lean_ctor_get(v_x_4141_, 0);
lean_inc_ref(v_fn_4199_);
v_arg_4200_ = lean_ctor_get(v_x_4141_, 1);
lean_inc_ref(v_arg_4200_);
lean_dec_ref(v_x_4141_);
v___x_4201_ = lean_array_set(v_x_4142_, v_x_4143_, v_arg_4200_);
v___x_4202_ = lean_unsigned_to_nat(1u);
v___x_4203_ = lean_nat_sub(v_x_4143_, v___x_4202_);
lean_dec(v_x_4143_);
v_x_4141_ = v_fn_4199_;
v_x_4142_ = v___x_4201_;
v_x_4143_ = v___x_4203_;
goto _start;
}
else
{
lean_dec(v_x_4143_);
if (v_skipConstInApp_4140_ == 0)
{
goto v___jp_4196_;
}
else
{
uint8_t v___x_4205_; 
v___x_4205_ = l_Lean_Expr_isConst(v_x_4141_);
if (v___x_4205_ == 0)
{
goto v___jp_4196_;
}
else
{
v_f_4151_ = v_x_4141_;
v___y_4152_ = v___y_4144_;
v___y_4153_ = v___y_4145_;
v___y_4154_ = v___y_4146_;
v___y_4155_ = v___y_4147_;
v___y_4156_ = v___y_4148_;
goto v___jp_4150_;
}
}
}
v___jp_4150_:
{
if (v_skipInstances_4136_ == 0)
{
size_t v_sz_4157_; size_t v___x_4158_; lean_object* v___x_4159_; 
v_sz_4157_ = lean_array_size(v_x_4142_);
v___x_4158_ = ((size_t)0ULL);
lean_inc_ref(v_post_4138_);
lean_inc_ref(v_pre_4137_);
v___x_4159_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__2(v_pre_4137_, v_post_4138_, v_usedLetOnly_4139_, v_skipConstInApp_4140_, v_skipInstances_4136_, v_sz_4157_, v___x_4158_, v_x_4142_, v___y_4152_, v___y_4153_, v___y_4154_, v___y_4155_, v___y_4156_);
if (lean_obj_tag(v___x_4159_) == 0)
{
lean_object* v_a_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; 
v_a_4160_ = lean_ctor_get(v___x_4159_, 0);
lean_inc(v_a_4160_);
lean_dec_ref(v___x_4159_);
v___x_4161_ = l_Lean_mkAppN(v_f_4151_, v_a_4160_);
lean_dec(v_a_4160_);
v___x_4162_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4137_, v_post_4138_, v_usedLetOnly_4139_, v_skipConstInApp_4140_, v_skipInstances_4136_, v___x_4161_, v___y_4152_, v___y_4153_, v___y_4154_, v___y_4155_, v___y_4156_);
return v___x_4162_;
}
else
{
lean_object* v_a_4163_; lean_object* v___x_4165_; uint8_t v_isShared_4166_; uint8_t v_isSharedCheck_4170_; 
lean_dec_ref(v_f_4151_);
lean_dec_ref(v_post_4138_);
lean_dec_ref(v_pre_4137_);
v_a_4163_ = lean_ctor_get(v___x_4159_, 0);
v_isSharedCheck_4170_ = !lean_is_exclusive(v___x_4159_);
if (v_isSharedCheck_4170_ == 0)
{
v___x_4165_ = v___x_4159_;
v_isShared_4166_ = v_isSharedCheck_4170_;
goto v_resetjp_4164_;
}
else
{
lean_inc(v_a_4163_);
lean_dec(v___x_4159_);
v___x_4165_ = lean_box(0);
v_isShared_4166_ = v_isSharedCheck_4170_;
goto v_resetjp_4164_;
}
v_resetjp_4164_:
{
lean_object* v___x_4168_; 
if (v_isShared_4166_ == 0)
{
v___x_4168_ = v___x_4165_;
goto v_reusejp_4167_;
}
else
{
lean_object* v_reuseFailAlloc_4169_; 
v_reuseFailAlloc_4169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4169_, 0, v_a_4163_);
v___x_4168_ = v_reuseFailAlloc_4169_;
goto v_reusejp_4167_;
}
v_reusejp_4167_:
{
return v___x_4168_;
}
}
}
}
else
{
lean_object* v___x_4171_; lean_object* v___x_4172_; 
v___x_4171_ = lean_array_get_size(v_x_4142_);
lean_inc_ref(v_f_4151_);
v___x_4172_ = l_Lean_Meta_getFunInfoNArgs(v_f_4151_, v___x_4171_, v___y_4153_, v___y_4154_, v___y_4155_, v___y_4156_);
if (lean_obj_tag(v___x_4172_) == 0)
{
lean_object* v_a_4173_; lean_object* v_paramInfo_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; 
v_a_4173_ = lean_ctor_get(v___x_4172_, 0);
lean_inc(v_a_4173_);
lean_dec_ref(v___x_4172_);
v_paramInfo_4174_ = lean_ctor_get(v_a_4173_, 0);
lean_inc_ref(v_paramInfo_4174_);
lean_dec(v_a_4173_);
v___x_4175_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_4138_);
lean_inc_ref(v_pre_4137_);
v___x_4176_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg(v___x_4171_, v_paramInfo_4174_, v_pre_4137_, v_post_4138_, v_usedLetOnly_4139_, v_skipConstInApp_4140_, v_skipInstances_4136_, v___x_4175_, v_x_4142_, v___y_4152_, v___y_4153_, v___y_4154_, v___y_4155_, v___y_4156_);
lean_dec_ref(v_paramInfo_4174_);
if (lean_obj_tag(v___x_4176_) == 0)
{
lean_object* v_a_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; 
v_a_4177_ = lean_ctor_get(v___x_4176_, 0);
lean_inc(v_a_4177_);
lean_dec_ref(v___x_4176_);
v___x_4178_ = l_Lean_mkAppN(v_f_4151_, v_a_4177_);
lean_dec(v_a_4177_);
v___x_4179_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4137_, v_post_4138_, v_usedLetOnly_4139_, v_skipConstInApp_4140_, v_skipInstances_4136_, v___x_4178_, v___y_4152_, v___y_4153_, v___y_4154_, v___y_4155_, v___y_4156_);
return v___x_4179_;
}
else
{
lean_object* v_a_4180_; lean_object* v___x_4182_; uint8_t v_isShared_4183_; uint8_t v_isSharedCheck_4187_; 
lean_dec_ref(v_f_4151_);
lean_dec_ref(v_post_4138_);
lean_dec_ref(v_pre_4137_);
v_a_4180_ = lean_ctor_get(v___x_4176_, 0);
v_isSharedCheck_4187_ = !lean_is_exclusive(v___x_4176_);
if (v_isSharedCheck_4187_ == 0)
{
v___x_4182_ = v___x_4176_;
v_isShared_4183_ = v_isSharedCheck_4187_;
goto v_resetjp_4181_;
}
else
{
lean_inc(v_a_4180_);
lean_dec(v___x_4176_);
v___x_4182_ = lean_box(0);
v_isShared_4183_ = v_isSharedCheck_4187_;
goto v_resetjp_4181_;
}
v_resetjp_4181_:
{
lean_object* v___x_4185_; 
if (v_isShared_4183_ == 0)
{
v___x_4185_ = v___x_4182_;
goto v_reusejp_4184_;
}
else
{
lean_object* v_reuseFailAlloc_4186_; 
v_reuseFailAlloc_4186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4186_, 0, v_a_4180_);
v___x_4185_ = v_reuseFailAlloc_4186_;
goto v_reusejp_4184_;
}
v_reusejp_4184_:
{
return v___x_4185_;
}
}
}
}
else
{
lean_object* v_a_4188_; lean_object* v___x_4190_; uint8_t v_isShared_4191_; uint8_t v_isSharedCheck_4195_; 
lean_dec_ref(v_f_4151_);
lean_dec_ref(v_x_4142_);
lean_dec_ref(v_post_4138_);
lean_dec_ref(v_pre_4137_);
v_a_4188_ = lean_ctor_get(v___x_4172_, 0);
v_isSharedCheck_4195_ = !lean_is_exclusive(v___x_4172_);
if (v_isSharedCheck_4195_ == 0)
{
v___x_4190_ = v___x_4172_;
v_isShared_4191_ = v_isSharedCheck_4195_;
goto v_resetjp_4189_;
}
else
{
lean_inc(v_a_4188_);
lean_dec(v___x_4172_);
v___x_4190_ = lean_box(0);
v_isShared_4191_ = v_isSharedCheck_4195_;
goto v_resetjp_4189_;
}
v_resetjp_4189_:
{
lean_object* v___x_4193_; 
if (v_isShared_4191_ == 0)
{
v___x_4193_ = v___x_4190_;
goto v_reusejp_4192_;
}
else
{
lean_object* v_reuseFailAlloc_4194_; 
v_reuseFailAlloc_4194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4194_, 0, v_a_4188_);
v___x_4193_ = v_reuseFailAlloc_4194_;
goto v_reusejp_4192_;
}
v_reusejp_4192_:
{
return v___x_4193_;
}
}
}
}
}
v___jp_4196_:
{
lean_object* v___x_4197_; 
lean_inc_ref(v_post_4138_);
lean_inc_ref(v_pre_4137_);
v___x_4197_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4137_, v_post_4138_, v_usedLetOnly_4139_, v_skipConstInApp_4140_, v_skipInstances_4136_, v_x_4141_, v___y_4144_, v___y_4145_, v___y_4146_, v___y_4147_, v___y_4148_);
if (lean_obj_tag(v___x_4197_) == 0)
{
lean_object* v_a_4198_; 
v_a_4198_ = lean_ctor_get(v___x_4197_, 0);
lean_inc(v_a_4198_);
lean_dec_ref(v___x_4197_);
v_f_4151_ = v_a_4198_;
v___y_4152_ = v___y_4144_;
v___y_4153_ = v___y_4145_;
v___y_4154_ = v___y_4146_;
v___y_4155_ = v___y_4147_;
v___y_4156_ = v___y_4148_;
goto v___jp_4150_;
}
else
{
lean_dec_ref(v_x_4142_);
lean_dec_ref(v_post_4138_);
lean_dec_ref(v_pre_4137_);
return v___x_4197_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1(lean_object* v___x_4206_, lean_object* v_pre_4207_, lean_object* v_e_4208_, lean_object* v_post_4209_, uint8_t v_usedLetOnly_4210_, uint8_t v_skipConstInApp_4211_, uint8_t v_skipInstances_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_){
_start:
{
lean_object* v___x_4219_; 
v___x_4219_ = l_Lean_Core_checkSystem(v___x_4206_, v___y_4216_, v___y_4217_);
if (lean_obj_tag(v___x_4219_) == 0)
{
lean_object* v___x_4220_; 
lean_dec_ref(v___x_4219_);
lean_inc_ref(v_pre_4207_);
lean_inc(v___y_4217_);
lean_inc_ref(v___y_4216_);
lean_inc(v___y_4215_);
lean_inc_ref(v___y_4214_);
lean_inc_ref(v_e_4208_);
v___x_4220_ = lean_apply_6(v_pre_4207_, v_e_4208_, v___y_4214_, v___y_4215_, v___y_4216_, v___y_4217_, lean_box(0));
if (lean_obj_tag(v___x_4220_) == 0)
{
lean_object* v_a_4221_; lean_object* v___x_4223_; uint8_t v_isShared_4224_; uint8_t v_isSharedCheck_4269_; 
v_a_4221_ = lean_ctor_get(v___x_4220_, 0);
v_isSharedCheck_4269_ = !lean_is_exclusive(v___x_4220_);
if (v_isSharedCheck_4269_ == 0)
{
v___x_4223_ = v___x_4220_;
v_isShared_4224_ = v_isSharedCheck_4269_;
goto v_resetjp_4222_;
}
else
{
lean_inc(v_a_4221_);
lean_dec(v___x_4220_);
v___x_4223_ = lean_box(0);
v_isShared_4224_ = v_isSharedCheck_4269_;
goto v_resetjp_4222_;
}
v_resetjp_4222_:
{
lean_object* v___y_4226_; 
switch(lean_obj_tag(v_a_4221_))
{
case 0:
{
lean_object* v_e_4261_; lean_object* v___x_4263_; 
lean_dec_ref(v_post_4209_);
lean_dec_ref(v_e_4208_);
lean_dec_ref(v_pre_4207_);
v_e_4261_ = lean_ctor_get(v_a_4221_, 0);
lean_inc_ref(v_e_4261_);
lean_dec_ref(v_a_4221_);
if (v_isShared_4224_ == 0)
{
lean_ctor_set(v___x_4223_, 0, v_e_4261_);
v___x_4263_ = v___x_4223_;
goto v_reusejp_4262_;
}
else
{
lean_object* v_reuseFailAlloc_4264_; 
v_reuseFailAlloc_4264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4264_, 0, v_e_4261_);
v___x_4263_ = v_reuseFailAlloc_4264_;
goto v_reusejp_4262_;
}
v_reusejp_4262_:
{
return v___x_4263_;
}
}
case 1:
{
lean_object* v_e_4265_; lean_object* v___x_4266_; 
lean_del_object(v___x_4223_);
lean_dec_ref(v_e_4208_);
v_e_4265_ = lean_ctor_get(v_a_4221_, 0);
lean_inc_ref(v_e_4265_);
lean_dec_ref(v_a_4221_);
v___x_4266_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4207_, v_post_4209_, v_usedLetOnly_4210_, v_skipConstInApp_4211_, v_skipInstances_4212_, v_e_4265_, v___y_4213_, v___y_4214_, v___y_4215_, v___y_4216_, v___y_4217_);
return v___x_4266_;
}
default: 
{
lean_object* v_e_x3f_4267_; 
lean_del_object(v___x_4223_);
v_e_x3f_4267_ = lean_ctor_get(v_a_4221_, 0);
lean_inc(v_e_x3f_4267_);
lean_dec_ref(v_a_4221_);
if (lean_obj_tag(v_e_x3f_4267_) == 0)
{
v___y_4226_ = v_e_4208_;
goto v___jp_4225_;
}
else
{
lean_object* v_val_4268_; 
lean_dec_ref(v_e_4208_);
v_val_4268_ = lean_ctor_get(v_e_x3f_4267_, 0);
lean_inc(v_val_4268_);
lean_dec_ref(v_e_x3f_4267_);
v___y_4226_ = v_val_4268_;
goto v___jp_4225_;
}
}
}
v___jp_4225_:
{
switch(lean_obj_tag(v___y_4226_))
{
case 7:
{
lean_object* v___x_4227_; lean_object* v___x_4228_; 
v___x_4227_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_4228_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5(v_pre_4207_, v_post_4209_, v_usedLetOnly_4210_, v_skipConstInApp_4211_, v_skipInstances_4212_, v___x_4227_, v___y_4226_, v___y_4213_, v___y_4214_, v___y_4215_, v___y_4216_, v___y_4217_);
return v___x_4228_;
}
case 6:
{
lean_object* v___x_4229_; lean_object* v___x_4230_; 
v___x_4229_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_4230_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6(v_pre_4207_, v_post_4209_, v_usedLetOnly_4210_, v_skipConstInApp_4211_, v_skipInstances_4212_, v___x_4229_, v___y_4226_, v___y_4213_, v___y_4214_, v___y_4215_, v___y_4216_, v___y_4217_);
return v___x_4230_;
}
case 8:
{
lean_object* v___x_4231_; lean_object* v___x_4232_; 
v___x_4231_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_4232_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7(v_pre_4207_, v_post_4209_, v_usedLetOnly_4210_, v_skipConstInApp_4211_, v_skipInstances_4212_, v___x_4231_, v___y_4226_, v___y_4213_, v___y_4214_, v___y_4215_, v___y_4216_, v___y_4217_);
return v___x_4232_;
}
case 5:
{
lean_object* v_dummy_4233_; lean_object* v_nargs_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; 
v_dummy_4233_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_4234_ = l_Lean_Expr_getAppNumArgs(v___y_4226_);
lean_inc(v_nargs_4234_);
v___x_4235_ = lean_mk_array(v_nargs_4234_, v_dummy_4233_);
v___x_4236_ = lean_unsigned_to_nat(1u);
v___x_4237_ = lean_nat_sub(v_nargs_4234_, v___x_4236_);
lean_dec(v_nargs_4234_);
v___x_4238_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__8(v_skipInstances_4212_, v_pre_4207_, v_post_4209_, v_usedLetOnly_4210_, v_skipConstInApp_4211_, v___y_4226_, v___x_4235_, v___x_4237_, v___y_4213_, v___y_4214_, v___y_4215_, v___y_4216_, v___y_4217_);
return v___x_4238_;
}
case 10:
{
lean_object* v_data_4239_; lean_object* v_expr_4240_; lean_object* v___x_4241_; 
v_data_4239_ = lean_ctor_get(v___y_4226_, 0);
v_expr_4240_ = lean_ctor_get(v___y_4226_, 1);
lean_inc_ref(v_expr_4240_);
lean_inc_ref(v_post_4209_);
lean_inc_ref(v_pre_4207_);
v___x_4241_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4207_, v_post_4209_, v_usedLetOnly_4210_, v_skipConstInApp_4211_, v_skipInstances_4212_, v_expr_4240_, v___y_4213_, v___y_4214_, v___y_4215_, v___y_4216_, v___y_4217_);
if (lean_obj_tag(v___x_4241_) == 0)
{
lean_object* v_a_4242_; size_t v___x_4243_; size_t v___x_4244_; uint8_t v___x_4245_; 
v_a_4242_ = lean_ctor_get(v___x_4241_, 0);
lean_inc(v_a_4242_);
lean_dec_ref(v___x_4241_);
v___x_4243_ = lean_ptr_addr(v_expr_4240_);
v___x_4244_ = lean_ptr_addr(v_a_4242_);
v___x_4245_ = lean_usize_dec_eq(v___x_4243_, v___x_4244_);
if (v___x_4245_ == 0)
{
lean_object* v___x_4246_; lean_object* v___x_4247_; 
lean_inc(v_data_4239_);
lean_dec_ref(v___y_4226_);
v___x_4246_ = l_Lean_Expr_mdata___override(v_data_4239_, v_a_4242_);
v___x_4247_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4207_, v_post_4209_, v_usedLetOnly_4210_, v_skipConstInApp_4211_, v_skipInstances_4212_, v___x_4246_, v___y_4213_, v___y_4214_, v___y_4215_, v___y_4216_, v___y_4217_);
return v___x_4247_;
}
else
{
lean_object* v___x_4248_; 
lean_dec(v_a_4242_);
v___x_4248_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4207_, v_post_4209_, v_usedLetOnly_4210_, v_skipConstInApp_4211_, v_skipInstances_4212_, v___y_4226_, v___y_4213_, v___y_4214_, v___y_4215_, v___y_4216_, v___y_4217_);
return v___x_4248_;
}
}
else
{
lean_dec_ref(v___y_4226_);
lean_dec_ref(v_post_4209_);
lean_dec_ref(v_pre_4207_);
return v___x_4241_;
}
}
case 11:
{
lean_object* v_typeName_4249_; lean_object* v_idx_4250_; lean_object* v_struct_4251_; lean_object* v___x_4252_; 
v_typeName_4249_ = lean_ctor_get(v___y_4226_, 0);
v_idx_4250_ = lean_ctor_get(v___y_4226_, 1);
v_struct_4251_ = lean_ctor_get(v___y_4226_, 2);
lean_inc_ref(v_struct_4251_);
lean_inc_ref(v_post_4209_);
lean_inc_ref(v_pre_4207_);
v___x_4252_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4207_, v_post_4209_, v_usedLetOnly_4210_, v_skipConstInApp_4211_, v_skipInstances_4212_, v_struct_4251_, v___y_4213_, v___y_4214_, v___y_4215_, v___y_4216_, v___y_4217_);
if (lean_obj_tag(v___x_4252_) == 0)
{
lean_object* v_a_4253_; size_t v___x_4254_; size_t v___x_4255_; uint8_t v___x_4256_; 
v_a_4253_ = lean_ctor_get(v___x_4252_, 0);
lean_inc(v_a_4253_);
lean_dec_ref(v___x_4252_);
v___x_4254_ = lean_ptr_addr(v_struct_4251_);
v___x_4255_ = lean_ptr_addr(v_a_4253_);
v___x_4256_ = lean_usize_dec_eq(v___x_4254_, v___x_4255_);
if (v___x_4256_ == 0)
{
lean_object* v___x_4257_; lean_object* v___x_4258_; 
lean_inc(v_idx_4250_);
lean_inc(v_typeName_4249_);
lean_dec_ref(v___y_4226_);
v___x_4257_ = l_Lean_Expr_proj___override(v_typeName_4249_, v_idx_4250_, v_a_4253_);
v___x_4258_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4207_, v_post_4209_, v_usedLetOnly_4210_, v_skipConstInApp_4211_, v_skipInstances_4212_, v___x_4257_, v___y_4213_, v___y_4214_, v___y_4215_, v___y_4216_, v___y_4217_);
return v___x_4258_;
}
else
{
lean_object* v___x_4259_; 
lean_dec(v_a_4253_);
v___x_4259_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4207_, v_post_4209_, v_usedLetOnly_4210_, v_skipConstInApp_4211_, v_skipInstances_4212_, v___y_4226_, v___y_4213_, v___y_4214_, v___y_4215_, v___y_4216_, v___y_4217_);
return v___x_4259_;
}
}
else
{
lean_dec_ref(v___y_4226_);
lean_dec_ref(v_post_4209_);
lean_dec_ref(v_pre_4207_);
return v___x_4252_;
}
}
default: 
{
lean_object* v___x_4260_; 
v___x_4260_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4207_, v_post_4209_, v_usedLetOnly_4210_, v_skipConstInApp_4211_, v_skipInstances_4212_, v___y_4226_, v___y_4213_, v___y_4214_, v___y_4215_, v___y_4216_, v___y_4217_);
return v___x_4260_;
}
}
}
}
}
else
{
lean_object* v_a_4270_; lean_object* v___x_4272_; uint8_t v_isShared_4273_; uint8_t v_isSharedCheck_4277_; 
lean_dec_ref(v_post_4209_);
lean_dec_ref(v_e_4208_);
lean_dec_ref(v_pre_4207_);
v_a_4270_ = lean_ctor_get(v___x_4220_, 0);
v_isSharedCheck_4277_ = !lean_is_exclusive(v___x_4220_);
if (v_isSharedCheck_4277_ == 0)
{
v___x_4272_ = v___x_4220_;
v_isShared_4273_ = v_isSharedCheck_4277_;
goto v_resetjp_4271_;
}
else
{
lean_inc(v_a_4270_);
lean_dec(v___x_4220_);
v___x_4272_ = lean_box(0);
v_isShared_4273_ = v_isSharedCheck_4277_;
goto v_resetjp_4271_;
}
v_resetjp_4271_:
{
lean_object* v___x_4275_; 
if (v_isShared_4273_ == 0)
{
v___x_4275_ = v___x_4272_;
goto v_reusejp_4274_;
}
else
{
lean_object* v_reuseFailAlloc_4276_; 
v_reuseFailAlloc_4276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4276_, 0, v_a_4270_);
v___x_4275_ = v_reuseFailAlloc_4276_;
goto v_reusejp_4274_;
}
v_reusejp_4274_:
{
return v___x_4275_;
}
}
}
}
else
{
lean_object* v_a_4278_; lean_object* v___x_4280_; uint8_t v_isShared_4281_; uint8_t v_isSharedCheck_4285_; 
lean_dec_ref(v_post_4209_);
lean_dec_ref(v_e_4208_);
lean_dec_ref(v_pre_4207_);
v_a_4278_ = lean_ctor_get(v___x_4219_, 0);
v_isSharedCheck_4285_ = !lean_is_exclusive(v___x_4219_);
if (v_isSharedCheck_4285_ == 0)
{
v___x_4280_ = v___x_4219_;
v_isShared_4281_ = v_isSharedCheck_4285_;
goto v_resetjp_4279_;
}
else
{
lean_inc(v_a_4278_);
lean_dec(v___x_4219_);
v___x_4280_ = lean_box(0);
v_isShared_4281_ = v_isSharedCheck_4285_;
goto v_resetjp_4279_;
}
v_resetjp_4279_:
{
lean_object* v___x_4283_; 
if (v_isShared_4281_ == 0)
{
v___x_4283_ = v___x_4280_;
goto v_reusejp_4282_;
}
else
{
lean_object* v_reuseFailAlloc_4284_; 
v_reuseFailAlloc_4284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4284_, 0, v_a_4278_);
v___x_4283_ = v_reuseFailAlloc_4284_;
goto v_reusejp_4282_;
}
v_reusejp_4282_:
{
return v___x_4283_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1___boxed(lean_object* v___x_4286_, lean_object* v_pre_4287_, lean_object* v_e_4288_, lean_object* v_post_4289_, lean_object* v_usedLetOnly_4290_, lean_object* v_skipConstInApp_4291_, lean_object* v_skipInstances_4292_, lean_object* v___y_4293_, lean_object* v___y_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_, lean_object* v___y_4298_){
_start:
{
uint8_t v_usedLetOnly_boxed_4299_; uint8_t v_skipConstInApp_boxed_4300_; uint8_t v_skipInstances_boxed_4301_; lean_object* v_res_4302_; 
v_usedLetOnly_boxed_4299_ = lean_unbox(v_usedLetOnly_4290_);
v_skipConstInApp_boxed_4300_ = lean_unbox(v_skipConstInApp_4291_);
v_skipInstances_boxed_4301_ = lean_unbox(v_skipInstances_4292_);
v_res_4302_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1(v___x_4286_, v_pre_4287_, v_e_4288_, v_post_4289_, v_usedLetOnly_boxed_4299_, v_skipConstInApp_boxed_4300_, v_skipInstances_boxed_4301_, v___y_4293_, v___y_4294_, v___y_4295_, v___y_4296_, v___y_4297_);
lean_dec(v___y_4297_);
lean_dec_ref(v___y_4296_);
lean_dec(v___y_4295_);
lean_dec_ref(v___y_4294_);
lean_dec(v___y_4293_);
return v_res_4302_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(lean_object* v_pre_4303_, lean_object* v_post_4304_, uint8_t v_usedLetOnly_4305_, uint8_t v_skipConstInApp_4306_, uint8_t v_skipInstances_4307_, lean_object* v_e_4308_, lean_object* v_a_4309_, lean_object* v___y_4310_, lean_object* v___y_4311_, lean_object* v___y_4312_, lean_object* v___y_4313_){
_start:
{
lean_object* v___x_4315_; lean_object* v___x_4316_; 
lean_inc(v_a_4309_);
v___x_4315_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_4315_, 0, lean_box(0));
lean_closure_set(v___x_4315_, 1, lean_box(0));
lean_closure_set(v___x_4315_, 2, v_a_4309_);
v___x_4316_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0(lean_box(0), v___x_4315_, v___y_4310_, v___y_4311_, v___y_4312_, v___y_4313_);
if (lean_obj_tag(v___x_4316_) == 0)
{
lean_object* v_a_4317_; lean_object* v___x_4319_; uint8_t v_isShared_4320_; uint8_t v_isSharedCheck_4351_; 
v_a_4317_ = lean_ctor_get(v___x_4316_, 0);
v_isSharedCheck_4351_ = !lean_is_exclusive(v___x_4316_);
if (v_isSharedCheck_4351_ == 0)
{
v___x_4319_ = v___x_4316_;
v_isShared_4320_ = v_isSharedCheck_4351_;
goto v_resetjp_4318_;
}
else
{
lean_inc(v_a_4317_);
lean_dec(v___x_4316_);
v___x_4319_ = lean_box(0);
v_isShared_4320_ = v_isSharedCheck_4351_;
goto v_resetjp_4318_;
}
v_resetjp_4318_:
{
lean_object* v___x_4321_; 
v___x_4321_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg(v_a_4317_, v_e_4308_);
lean_dec(v_a_4317_);
if (lean_obj_tag(v___x_4321_) == 0)
{
lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; lean_object* v___x_4325_; lean_object* v___f_4326_; lean_object* v___x_4327_; 
lean_del_object(v___x_4319_);
v___x_4322_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__19___closed__0));
v___x_4323_ = lean_box(v_usedLetOnly_4305_);
v___x_4324_ = lean_box(v_skipConstInApp_4306_);
v___x_4325_ = lean_box(v_skipInstances_4307_);
lean_inc_ref(v_e_4308_);
v___f_4326_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1___boxed), 13, 7);
lean_closure_set(v___f_4326_, 0, v___x_4322_);
lean_closure_set(v___f_4326_, 1, v_pre_4303_);
lean_closure_set(v___f_4326_, 2, v_e_4308_);
lean_closure_set(v___f_4326_, 3, v_post_4304_);
lean_closure_set(v___f_4326_, 4, v___x_4323_);
lean_closure_set(v___f_4326_, 5, v___x_4324_);
lean_closure_set(v___f_4326_, 6, v___x_4325_);
v___x_4327_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg(v___f_4326_, v_a_4309_, v___y_4310_, v___y_4311_, v___y_4312_, v___y_4313_);
if (lean_obj_tag(v___x_4327_) == 0)
{
lean_object* v_a_4328_; lean_object* v___f_4329_; lean_object* v___x_4330_; 
v_a_4328_ = lean_ctor_get(v___x_4327_, 0);
lean_inc_n(v_a_4328_, 2);
lean_dec_ref(v___x_4327_);
lean_inc(v_a_4309_);
v___f_4329_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_4329_, 0, v_a_4309_);
lean_closure_set(v___f_4329_, 1, v_e_4308_);
lean_closure_set(v___f_4329_, 2, v_a_4328_);
v___x_4330_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0(lean_box(0), v___f_4329_, v___y_4310_, v___y_4311_, v___y_4312_, v___y_4313_);
if (lean_obj_tag(v___x_4330_) == 0)
{
lean_object* v___x_4332_; uint8_t v_isShared_4333_; uint8_t v_isSharedCheck_4337_; 
v_isSharedCheck_4337_ = !lean_is_exclusive(v___x_4330_);
if (v_isSharedCheck_4337_ == 0)
{
lean_object* v_unused_4338_; 
v_unused_4338_ = lean_ctor_get(v___x_4330_, 0);
lean_dec(v_unused_4338_);
v___x_4332_ = v___x_4330_;
v_isShared_4333_ = v_isSharedCheck_4337_;
goto v_resetjp_4331_;
}
else
{
lean_dec(v___x_4330_);
v___x_4332_ = lean_box(0);
v_isShared_4333_ = v_isSharedCheck_4337_;
goto v_resetjp_4331_;
}
v_resetjp_4331_:
{
lean_object* v___x_4335_; 
if (v_isShared_4333_ == 0)
{
lean_ctor_set(v___x_4332_, 0, v_a_4328_);
v___x_4335_ = v___x_4332_;
goto v_reusejp_4334_;
}
else
{
lean_object* v_reuseFailAlloc_4336_; 
v_reuseFailAlloc_4336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4336_, 0, v_a_4328_);
v___x_4335_ = v_reuseFailAlloc_4336_;
goto v_reusejp_4334_;
}
v_reusejp_4334_:
{
return v___x_4335_;
}
}
}
else
{
lean_object* v_a_4339_; lean_object* v___x_4341_; uint8_t v_isShared_4342_; uint8_t v_isSharedCheck_4346_; 
lean_dec(v_a_4328_);
v_a_4339_ = lean_ctor_get(v___x_4330_, 0);
v_isSharedCheck_4346_ = !lean_is_exclusive(v___x_4330_);
if (v_isSharedCheck_4346_ == 0)
{
v___x_4341_ = v___x_4330_;
v_isShared_4342_ = v_isSharedCheck_4346_;
goto v_resetjp_4340_;
}
else
{
lean_inc(v_a_4339_);
lean_dec(v___x_4330_);
v___x_4341_ = lean_box(0);
v_isShared_4342_ = v_isSharedCheck_4346_;
goto v_resetjp_4340_;
}
v_resetjp_4340_:
{
lean_object* v___x_4344_; 
if (v_isShared_4342_ == 0)
{
v___x_4344_ = v___x_4341_;
goto v_reusejp_4343_;
}
else
{
lean_object* v_reuseFailAlloc_4345_; 
v_reuseFailAlloc_4345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4345_, 0, v_a_4339_);
v___x_4344_ = v_reuseFailAlloc_4345_;
goto v_reusejp_4343_;
}
v_reusejp_4343_:
{
return v___x_4344_;
}
}
}
}
else
{
lean_dec_ref(v_e_4308_);
return v___x_4327_;
}
}
else
{
lean_object* v_val_4347_; lean_object* v___x_4349_; 
lean_dec_ref(v_e_4308_);
lean_dec_ref(v_post_4304_);
lean_dec_ref(v_pre_4303_);
v_val_4347_ = lean_ctor_get(v___x_4321_, 0);
lean_inc(v_val_4347_);
lean_dec_ref(v___x_4321_);
if (v_isShared_4320_ == 0)
{
lean_ctor_set(v___x_4319_, 0, v_val_4347_);
v___x_4349_ = v___x_4319_;
goto v_reusejp_4348_;
}
else
{
lean_object* v_reuseFailAlloc_4350_; 
v_reuseFailAlloc_4350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4350_, 0, v_val_4347_);
v___x_4349_ = v_reuseFailAlloc_4350_;
goto v_reusejp_4348_;
}
v_reusejp_4348_:
{
return v___x_4349_;
}
}
}
}
else
{
lean_object* v_a_4352_; lean_object* v___x_4354_; uint8_t v_isShared_4355_; uint8_t v_isSharedCheck_4359_; 
lean_dec_ref(v_e_4308_);
lean_dec_ref(v_post_4304_);
lean_dec_ref(v_pre_4303_);
v_a_4352_ = lean_ctor_get(v___x_4316_, 0);
v_isSharedCheck_4359_ = !lean_is_exclusive(v___x_4316_);
if (v_isSharedCheck_4359_ == 0)
{
v___x_4354_ = v___x_4316_;
v_isShared_4355_ = v_isSharedCheck_4359_;
goto v_resetjp_4353_;
}
else
{
lean_inc(v_a_4352_);
lean_dec(v___x_4316_);
v___x_4354_ = lean_box(0);
v_isShared_4355_ = v_isSharedCheck_4359_;
goto v_resetjp_4353_;
}
v_resetjp_4353_:
{
lean_object* v___x_4357_; 
if (v_isShared_4355_ == 0)
{
v___x_4357_ = v___x_4354_;
goto v_reusejp_4356_;
}
else
{
lean_object* v_reuseFailAlloc_4358_; 
v_reuseFailAlloc_4358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4358_, 0, v_a_4352_);
v___x_4357_ = v_reuseFailAlloc_4358_;
goto v_reusejp_4356_;
}
v_reusejp_4356_:
{
return v___x_4357_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___lam__0___boxed(lean_object* v_fvars_4360_, lean_object* v_pre_4361_, lean_object* v_post_4362_, lean_object* v_usedLetOnly_4363_, lean_object* v_skipConstInApp_4364_, lean_object* v_skipInstances_4365_, lean_object* v_body_4366_, lean_object* v_x_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_, lean_object* v___y_4371_, lean_object* v___y_4372_, lean_object* v___y_4373_){
_start:
{
uint8_t v_usedLetOnly_boxed_4374_; uint8_t v_skipConstInApp_boxed_4375_; uint8_t v_skipInstances_boxed_4376_; lean_object* v_res_4377_; 
v_usedLetOnly_boxed_4374_ = lean_unbox(v_usedLetOnly_4363_);
v_skipConstInApp_boxed_4375_ = lean_unbox(v_skipConstInApp_4364_);
v_skipInstances_boxed_4376_ = lean_unbox(v_skipInstances_4365_);
v_res_4377_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___lam__0(v_fvars_4360_, v_pre_4361_, v_post_4362_, v_usedLetOnly_boxed_4374_, v_skipConstInApp_boxed_4375_, v_skipInstances_boxed_4376_, v_body_4366_, v_x_4367_, v___y_4368_, v___y_4369_, v___y_4370_, v___y_4371_, v___y_4372_);
lean_dec(v___y_4372_);
lean_dec_ref(v___y_4371_);
lean_dec(v___y_4370_);
lean_dec_ref(v___y_4369_);
lean_dec(v___y_4368_);
return v_res_4377_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5(lean_object* v_pre_4378_, lean_object* v_post_4379_, uint8_t v_usedLetOnly_4380_, uint8_t v_skipConstInApp_4381_, uint8_t v_skipInstances_4382_, lean_object* v_fvars_4383_, lean_object* v_e_4384_, lean_object* v_a_4385_, lean_object* v___y_4386_, lean_object* v___y_4387_, lean_object* v___y_4388_, lean_object* v___y_4389_){
_start:
{
if (lean_obj_tag(v_e_4384_) == 7)
{
lean_object* v_binderName_4391_; lean_object* v_binderType_4392_; lean_object* v_body_4393_; uint8_t v_binderInfo_4394_; lean_object* v___x_4395_; lean_object* v___x_4396_; 
v_binderName_4391_ = lean_ctor_get(v_e_4384_, 0);
lean_inc(v_binderName_4391_);
v_binderType_4392_ = lean_ctor_get(v_e_4384_, 1);
lean_inc_ref(v_binderType_4392_);
v_body_4393_ = lean_ctor_get(v_e_4384_, 2);
lean_inc_ref(v_body_4393_);
v_binderInfo_4394_ = lean_ctor_get_uint8(v_e_4384_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_4384_);
v___x_4395_ = lean_expr_instantiate_rev(v_binderType_4392_, v_fvars_4383_);
lean_dec_ref(v_binderType_4392_);
lean_inc_ref(v_post_4379_);
lean_inc_ref(v_pre_4378_);
v___x_4396_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4378_, v_post_4379_, v_usedLetOnly_4380_, v_skipConstInApp_4381_, v_skipInstances_4382_, v___x_4395_, v_a_4385_, v___y_4386_, v___y_4387_, v___y_4388_, v___y_4389_);
if (lean_obj_tag(v___x_4396_) == 0)
{
lean_object* v_a_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; lean_object* v___f_4401_; uint8_t v___x_4402_; lean_object* v___x_4403_; 
v_a_4397_ = lean_ctor_get(v___x_4396_, 0);
lean_inc(v_a_4397_);
lean_dec_ref(v___x_4396_);
v___x_4398_ = lean_box(v_usedLetOnly_4380_);
v___x_4399_ = lean_box(v_skipConstInApp_4381_);
v___x_4400_ = lean_box(v_skipInstances_4382_);
v___f_4401_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___lam__0___boxed), 14, 7);
lean_closure_set(v___f_4401_, 0, v_fvars_4383_);
lean_closure_set(v___f_4401_, 1, v_pre_4378_);
lean_closure_set(v___f_4401_, 2, v_post_4379_);
lean_closure_set(v___f_4401_, 3, v___x_4398_);
lean_closure_set(v___f_4401_, 4, v___x_4399_);
lean_closure_set(v___f_4401_, 5, v___x_4400_);
lean_closure_set(v___f_4401_, 6, v_body_4393_);
v___x_4402_ = 0;
v___x_4403_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_binderName_4391_, v_binderInfo_4394_, v_a_4397_, v___f_4401_, v___x_4402_, v_a_4385_, v___y_4386_, v___y_4387_, v___y_4388_, v___y_4389_);
return v___x_4403_;
}
else
{
lean_dec_ref(v_body_4393_);
lean_dec(v_binderName_4391_);
lean_dec_ref(v_fvars_4383_);
lean_dec_ref(v_post_4379_);
lean_dec_ref(v_pre_4378_);
return v___x_4396_;
}
}
else
{
lean_object* v___x_4404_; lean_object* v___x_4405_; 
v___x_4404_ = lean_expr_instantiate_rev(v_e_4384_, v_fvars_4383_);
lean_dec_ref(v_e_4384_);
lean_inc_ref(v_post_4379_);
lean_inc_ref(v_pre_4378_);
v___x_4405_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4378_, v_post_4379_, v_usedLetOnly_4380_, v_skipConstInApp_4381_, v_skipInstances_4382_, v___x_4404_, v_a_4385_, v___y_4386_, v___y_4387_, v___y_4388_, v___y_4389_);
if (lean_obj_tag(v___x_4405_) == 0)
{
lean_object* v_a_4406_; uint8_t v___x_4407_; uint8_t v___x_4408_; uint8_t v___x_4409_; lean_object* v___x_4410_; 
v_a_4406_ = lean_ctor_get(v___x_4405_, 0);
lean_inc(v_a_4406_);
lean_dec_ref(v___x_4405_);
v___x_4407_ = 0;
v___x_4408_ = 1;
v___x_4409_ = 1;
v___x_4410_ = l_Lean_Meta_mkForallFVars(v_fvars_4383_, v_a_4406_, v___x_4407_, v_usedLetOnly_4380_, v___x_4408_, v___x_4409_, v___y_4386_, v___y_4387_, v___y_4388_, v___y_4389_);
lean_dec_ref(v_fvars_4383_);
if (lean_obj_tag(v___x_4410_) == 0)
{
lean_object* v_a_4411_; lean_object* v___x_4412_; 
v_a_4411_ = lean_ctor_get(v___x_4410_, 0);
lean_inc(v_a_4411_);
lean_dec_ref(v___x_4410_);
v___x_4412_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4378_, v_post_4379_, v_usedLetOnly_4380_, v_skipConstInApp_4381_, v_skipInstances_4382_, v_a_4411_, v_a_4385_, v___y_4386_, v___y_4387_, v___y_4388_, v___y_4389_);
return v___x_4412_;
}
else
{
lean_dec_ref(v_post_4379_);
lean_dec_ref(v_pre_4378_);
return v___x_4410_;
}
}
else
{
lean_dec_ref(v_fvars_4383_);
lean_dec_ref(v_post_4379_);
lean_dec_ref(v_pre_4378_);
return v___x_4405_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___lam__0(lean_object* v_fvars_4413_, lean_object* v_pre_4414_, lean_object* v_post_4415_, uint8_t v_usedLetOnly_4416_, uint8_t v_skipConstInApp_4417_, uint8_t v_skipInstances_4418_, lean_object* v_body_4419_, lean_object* v_x_4420_, lean_object* v___y_4421_, lean_object* v___y_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_, lean_object* v___y_4425_){
_start:
{
lean_object* v___x_4427_; lean_object* v___x_4428_; 
v___x_4427_ = lean_array_push(v_fvars_4413_, v_x_4420_);
v___x_4428_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5(v_pre_4414_, v_post_4415_, v_usedLetOnly_4416_, v_skipConstInApp_4417_, v_skipInstances_4418_, v___x_4427_, v_body_4419_, v___y_4421_, v___y_4422_, v___y_4423_, v___y_4424_, v___y_4425_);
return v___x_4428_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3___boxed(lean_object* v_pre_4429_, lean_object* v_post_4430_, lean_object* v_usedLetOnly_4431_, lean_object* v_skipConstInApp_4432_, lean_object* v_skipInstances_4433_, lean_object* v_e_4434_, lean_object* v_a_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_){
_start:
{
uint8_t v_usedLetOnly_boxed_4441_; uint8_t v_skipConstInApp_boxed_4442_; uint8_t v_skipInstances_boxed_4443_; lean_object* v_res_4444_; 
v_usedLetOnly_boxed_4441_ = lean_unbox(v_usedLetOnly_4431_);
v_skipConstInApp_boxed_4442_ = lean_unbox(v_skipConstInApp_4432_);
v_skipInstances_boxed_4443_ = lean_unbox(v_skipInstances_4433_);
v_res_4444_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4429_, v_post_4430_, v_usedLetOnly_boxed_4441_, v_skipConstInApp_boxed_4442_, v_skipInstances_boxed_4443_, v_e_4434_, v_a_4435_, v___y_4436_, v___y_4437_, v___y_4438_, v___y_4439_);
lean_dec(v___y_4439_);
lean_dec_ref(v___y_4438_);
lean_dec(v___y_4437_);
lean_dec_ref(v___y_4436_);
lean_dec(v_a_4435_);
return v_res_4444_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__2___boxed(lean_object* v_pre_4445_, lean_object* v_post_4446_, lean_object* v_usedLetOnly_4447_, lean_object* v_skipConstInApp_4448_, lean_object* v_skipInstances_4449_, lean_object* v_sz_4450_, lean_object* v_i_4451_, lean_object* v_bs_4452_, lean_object* v___y_4453_, lean_object* v___y_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_){
_start:
{
uint8_t v_usedLetOnly_boxed_4459_; uint8_t v_skipConstInApp_boxed_4460_; uint8_t v_skipInstances_boxed_4461_; size_t v_sz_boxed_4462_; size_t v_i_boxed_4463_; lean_object* v_res_4464_; 
v_usedLetOnly_boxed_4459_ = lean_unbox(v_usedLetOnly_4447_);
v_skipConstInApp_boxed_4460_ = lean_unbox(v_skipConstInApp_4448_);
v_skipInstances_boxed_4461_ = lean_unbox(v_skipInstances_4449_);
v_sz_boxed_4462_ = lean_unbox_usize(v_sz_4450_);
lean_dec(v_sz_4450_);
v_i_boxed_4463_ = lean_unbox_usize(v_i_4451_);
lean_dec(v_i_4451_);
v_res_4464_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__2(v_pre_4445_, v_post_4446_, v_usedLetOnly_boxed_4459_, v_skipConstInApp_boxed_4460_, v_skipInstances_boxed_4461_, v_sz_boxed_4462_, v_i_boxed_4463_, v_bs_4452_, v___y_4453_, v___y_4454_, v___y_4455_, v___y_4456_, v___y_4457_);
lean_dec(v___y_4457_);
lean_dec_ref(v___y_4456_);
lean_dec(v___y_4455_);
lean_dec_ref(v___y_4454_);
lean_dec(v___y_4453_);
return v_res_4464_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___boxed(lean_object* v_pre_4465_, lean_object* v_post_4466_, lean_object* v_usedLetOnly_4467_, lean_object* v_skipConstInApp_4468_, lean_object* v_skipInstances_4469_, lean_object* v_e_4470_, lean_object* v_a_4471_, lean_object* v___y_4472_, lean_object* v___y_4473_, lean_object* v___y_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_){
_start:
{
uint8_t v_usedLetOnly_boxed_4477_; uint8_t v_skipConstInApp_boxed_4478_; uint8_t v_skipInstances_boxed_4479_; lean_object* v_res_4480_; 
v_usedLetOnly_boxed_4477_ = lean_unbox(v_usedLetOnly_4467_);
v_skipConstInApp_boxed_4478_ = lean_unbox(v_skipConstInApp_4468_);
v_skipInstances_boxed_4479_ = lean_unbox(v_skipInstances_4469_);
v_res_4480_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4465_, v_post_4466_, v_usedLetOnly_boxed_4477_, v_skipConstInApp_boxed_4478_, v_skipInstances_boxed_4479_, v_e_4470_, v_a_4471_, v___y_4472_, v___y_4473_, v___y_4474_, v___y_4475_);
lean_dec(v___y_4475_);
lean_dec_ref(v___y_4474_);
lean_dec(v___y_4473_);
lean_dec_ref(v___y_4472_);
lean_dec(v_a_4471_);
return v_res_4480_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___boxed(lean_object* v_pre_4481_, lean_object* v_post_4482_, lean_object* v_usedLetOnly_4483_, lean_object* v_skipConstInApp_4484_, lean_object* v_skipInstances_4485_, lean_object* v_fvars_4486_, lean_object* v_e_4487_, lean_object* v_a_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_, lean_object* v___y_4493_){
_start:
{
uint8_t v_usedLetOnly_boxed_4494_; uint8_t v_skipConstInApp_boxed_4495_; uint8_t v_skipInstances_boxed_4496_; lean_object* v_res_4497_; 
v_usedLetOnly_boxed_4494_ = lean_unbox(v_usedLetOnly_4483_);
v_skipConstInApp_boxed_4495_ = lean_unbox(v_skipConstInApp_4484_);
v_skipInstances_boxed_4496_ = lean_unbox(v_skipInstances_4485_);
v_res_4497_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5(v_pre_4481_, v_post_4482_, v_usedLetOnly_boxed_4494_, v_skipConstInApp_boxed_4495_, v_skipInstances_boxed_4496_, v_fvars_4486_, v_e_4487_, v_a_4488_, v___y_4489_, v___y_4490_, v___y_4491_, v___y_4492_);
lean_dec(v___y_4492_);
lean_dec_ref(v___y_4491_);
lean_dec(v___y_4490_);
lean_dec_ref(v___y_4489_);
lean_dec(v_a_4488_);
return v_res_4497_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___boxed(lean_object* v_pre_4498_, lean_object* v_post_4499_, lean_object* v_usedLetOnly_4500_, lean_object* v_skipConstInApp_4501_, lean_object* v_skipInstances_4502_, lean_object* v_fvars_4503_, lean_object* v_e_4504_, lean_object* v_a_4505_, lean_object* v___y_4506_, lean_object* v___y_4507_, lean_object* v___y_4508_, lean_object* v___y_4509_, lean_object* v___y_4510_){
_start:
{
uint8_t v_usedLetOnly_boxed_4511_; uint8_t v_skipConstInApp_boxed_4512_; uint8_t v_skipInstances_boxed_4513_; lean_object* v_res_4514_; 
v_usedLetOnly_boxed_4511_ = lean_unbox(v_usedLetOnly_4500_);
v_skipConstInApp_boxed_4512_ = lean_unbox(v_skipConstInApp_4501_);
v_skipInstances_boxed_4513_ = lean_unbox(v_skipInstances_4502_);
v_res_4514_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6(v_pre_4498_, v_post_4499_, v_usedLetOnly_boxed_4511_, v_skipConstInApp_boxed_4512_, v_skipInstances_boxed_4513_, v_fvars_4503_, v_e_4504_, v_a_4505_, v___y_4506_, v___y_4507_, v___y_4508_, v___y_4509_);
lean_dec(v___y_4509_);
lean_dec_ref(v___y_4508_);
lean_dec(v___y_4507_);
lean_dec_ref(v___y_4506_);
lean_dec(v_a_4505_);
return v_res_4514_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___boxed(lean_object* v_pre_4515_, lean_object* v_post_4516_, lean_object* v_usedLetOnly_4517_, lean_object* v_skipConstInApp_4518_, lean_object* v_skipInstances_4519_, lean_object* v_fvars_4520_, lean_object* v_e_4521_, lean_object* v_a_4522_, lean_object* v___y_4523_, lean_object* v___y_4524_, lean_object* v___y_4525_, lean_object* v___y_4526_, lean_object* v___y_4527_){
_start:
{
uint8_t v_usedLetOnly_boxed_4528_; uint8_t v_skipConstInApp_boxed_4529_; uint8_t v_skipInstances_boxed_4530_; lean_object* v_res_4531_; 
v_usedLetOnly_boxed_4528_ = lean_unbox(v_usedLetOnly_4517_);
v_skipConstInApp_boxed_4529_ = lean_unbox(v_skipConstInApp_4518_);
v_skipInstances_boxed_4530_ = lean_unbox(v_skipInstances_4519_);
v_res_4531_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7(v_pre_4515_, v_post_4516_, v_usedLetOnly_boxed_4528_, v_skipConstInApp_boxed_4529_, v_skipInstances_boxed_4530_, v_fvars_4520_, v_e_4521_, v_a_4522_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_);
lean_dec(v___y_4526_);
lean_dec_ref(v___y_4525_);
lean_dec(v___y_4524_);
lean_dec_ref(v___y_4523_);
lean_dec(v_a_4522_);
return v_res_4531_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_upperBound_4532_, lean_object* v___x_4533_, lean_object* v_pre_4534_, lean_object* v_post_4535_, lean_object* v_usedLetOnly_4536_, lean_object* v_skipConstInApp_4537_, lean_object* v_skipInstances_4538_, lean_object* v_a_4539_, lean_object* v_b_4540_, lean_object* v___y_4541_, lean_object* v___y_4542_, lean_object* v___y_4543_, lean_object* v___y_4544_, lean_object* v___y_4545_, lean_object* v___y_4546_){
_start:
{
uint8_t v_usedLetOnly_boxed_4547_; uint8_t v_skipConstInApp_boxed_4548_; uint8_t v_skipInstances_boxed_4549_; lean_object* v_res_4550_; 
v_usedLetOnly_boxed_4547_ = lean_unbox(v_usedLetOnly_4536_);
v_skipConstInApp_boxed_4548_ = lean_unbox(v_skipConstInApp_4537_);
v_skipInstances_boxed_4549_ = lean_unbox(v_skipInstances_4538_);
v_res_4550_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg(v_upperBound_4532_, v___x_4533_, v_pre_4534_, v_post_4535_, v_usedLetOnly_boxed_4547_, v_skipConstInApp_boxed_4548_, v_skipInstances_boxed_4549_, v_a_4539_, v_b_4540_, v___y_4541_, v___y_4542_, v___y_4543_, v___y_4544_, v___y_4545_);
lean_dec(v___y_4545_);
lean_dec_ref(v___y_4544_);
lean_dec(v___y_4543_);
lean_dec_ref(v___y_4542_);
lean_dec(v___y_4541_);
lean_dec_ref(v___x_4533_);
lean_dec(v_upperBound_4532_);
return v_res_4550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__8___boxed(lean_object* v_skipInstances_4551_, lean_object* v_pre_4552_, lean_object* v_post_4553_, lean_object* v_usedLetOnly_4554_, lean_object* v_skipConstInApp_4555_, lean_object* v_x_4556_, lean_object* v_x_4557_, lean_object* v_x_4558_, lean_object* v___y_4559_, lean_object* v___y_4560_, lean_object* v___y_4561_, lean_object* v___y_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_){
_start:
{
uint8_t v_skipInstances_boxed_4565_; uint8_t v_usedLetOnly_boxed_4566_; uint8_t v_skipConstInApp_boxed_4567_; lean_object* v_res_4568_; 
v_skipInstances_boxed_4565_ = lean_unbox(v_skipInstances_4551_);
v_usedLetOnly_boxed_4566_ = lean_unbox(v_usedLetOnly_4554_);
v_skipConstInApp_boxed_4567_ = lean_unbox(v_skipConstInApp_4555_);
v_res_4568_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__8(v_skipInstances_boxed_4565_, v_pre_4552_, v_post_4553_, v_usedLetOnly_boxed_4566_, v_skipConstInApp_boxed_4567_, v_x_4556_, v_x_4557_, v_x_4558_, v___y_4559_, v___y_4560_, v___y_4561_, v___y_4562_, v___y_4563_);
lean_dec(v___y_4563_);
lean_dec_ref(v___y_4562_);
lean_dec(v___y_4561_);
lean_dec_ref(v___y_4560_);
lean_dec(v___y_4559_);
return v_res_4568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(lean_object* v_input_4569_, lean_object* v_pre_4570_, lean_object* v_post_4571_, uint8_t v_usedLetOnly_4572_, uint8_t v_skipConstInApp_4573_, lean_object* v___y_4574_, lean_object* v___y_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_){
_start:
{
lean_object* v___x_4579_; lean_object* v___x_4580_; lean_object* v_a_4581_; uint8_t v___x_4582_; lean_object* v___x_4583_; 
v___x_4579_ = lean_obj_once(&l_Lean_Core_transform___redArg___closed__2, &l_Lean_Core_transform___redArg___closed__2_once, _init_l_Lean_Core_transform___redArg___closed__2);
v___x_4580_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0(lean_box(0), v___x_4579_, v___y_4574_, v___y_4575_, v___y_4576_, v___y_4577_);
v_a_4581_ = lean_ctor_get(v___x_4580_, 0);
lean_inc(v_a_4581_);
lean_dec_ref(v___x_4580_);
v___x_4582_ = 0;
v___x_4583_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4570_, v_post_4571_, v_usedLetOnly_4572_, v_skipConstInApp_4573_, v___x_4582_, v_input_4569_, v_a_4581_, v___y_4574_, v___y_4575_, v___y_4576_, v___y_4577_);
if (lean_obj_tag(v___x_4583_) == 0)
{
lean_object* v_a_4584_; lean_object* v___x_4585_; lean_object* v___x_4586_; lean_object* v___x_4588_; uint8_t v_isShared_4589_; uint8_t v_isSharedCheck_4593_; 
v_a_4584_ = lean_ctor_get(v___x_4583_, 0);
lean_inc(v_a_4584_);
lean_dec_ref(v___x_4583_);
v___x_4585_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_4585_, 0, lean_box(0));
lean_closure_set(v___x_4585_, 1, lean_box(0));
lean_closure_set(v___x_4585_, 2, v_a_4581_);
v___x_4586_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0(lean_box(0), v___x_4585_, v___y_4574_, v___y_4575_, v___y_4576_, v___y_4577_);
v_isSharedCheck_4593_ = !lean_is_exclusive(v___x_4586_);
if (v_isSharedCheck_4593_ == 0)
{
lean_object* v_unused_4594_; 
v_unused_4594_ = lean_ctor_get(v___x_4586_, 0);
lean_dec(v_unused_4594_);
v___x_4588_ = v___x_4586_;
v_isShared_4589_ = v_isSharedCheck_4593_;
goto v_resetjp_4587_;
}
else
{
lean_dec(v___x_4586_);
v___x_4588_ = lean_box(0);
v_isShared_4589_ = v_isSharedCheck_4593_;
goto v_resetjp_4587_;
}
v_resetjp_4587_:
{
lean_object* v___x_4591_; 
if (v_isShared_4589_ == 0)
{
lean_ctor_set(v___x_4588_, 0, v_a_4584_);
v___x_4591_ = v___x_4588_;
goto v_reusejp_4590_;
}
else
{
lean_object* v_reuseFailAlloc_4592_; 
v_reuseFailAlloc_4592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4592_, 0, v_a_4584_);
v___x_4591_ = v_reuseFailAlloc_4592_;
goto v_reusejp_4590_;
}
v_reusejp_4590_:
{
return v___x_4591_;
}
}
}
else
{
lean_dec(v_a_4581_);
return v___x_4583_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___boxed(lean_object* v_input_4595_, lean_object* v_pre_4596_, lean_object* v_post_4597_, lean_object* v_usedLetOnly_4598_, lean_object* v_skipConstInApp_4599_, lean_object* v___y_4600_, lean_object* v___y_4601_, lean_object* v___y_4602_, lean_object* v___y_4603_, lean_object* v___y_4604_){
_start:
{
uint8_t v_usedLetOnly_boxed_4605_; uint8_t v_skipConstInApp_boxed_4606_; lean_object* v_res_4607_; 
v_usedLetOnly_boxed_4605_ = lean_unbox(v_usedLetOnly_4598_);
v_skipConstInApp_boxed_4606_ = lean_unbox(v_skipConstInApp_4599_);
v_res_4607_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(v_input_4595_, v_pre_4596_, v_post_4597_, v_usedLetOnly_boxed_4605_, v_skipConstInApp_boxed_4606_, v___y_4600_, v___y_4601_, v___y_4602_, v___y_4603_);
lean_dec(v___y_4603_);
lean_dec_ref(v___y_4602_);
lean_dec(v___y_4601_);
lean_dec_ref(v___y_4600_);
return v_res_4607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce(lean_object* v_e_4609_, uint8_t v_zetaDelta_4610_, uint8_t v_zetaHave_4611_, uint8_t v_beta_4612_, lean_object* v_a_4613_, lean_object* v_a_4614_, lean_object* v_a_4615_, lean_object* v_a_4616_){
_start:
{
lean_object* v_lctx_4618_; lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; lean_object* v___f_4622_; uint8_t v___x_4623_; 
v_lctx_4618_ = lean_ctor_get(v_a_4613_, 2);
lean_inc_ref(v_lctx_4618_);
v___x_4619_ = lean_local_ctx_num_indices(v_lctx_4618_);
v___x_4620_ = lean_box(v_zetaHave_4611_);
v___x_4621_ = lean_box(v_zetaDelta_4610_);
v___f_4622_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaReduce___lam__0___boxed), 9, 3);
lean_closure_set(v___f_4622_, 0, v___x_4620_);
lean_closure_set(v___f_4622_, 1, v___x_4619_);
lean_closure_set(v___f_4622_, 2, v___x_4621_);
v___x_4623_ = 1;
if (v_beta_4612_ == 0)
{
lean_object* v___f_4624_; lean_object* v___f_4625_; lean_object* v___x_4626_; 
v___f_4624_ = ((lean_object*)(l_Lean_Meta_zetaReduce___closed__0));
v___f_4625_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaReduce___lam__2___boxed), 7, 1);
lean_closure_set(v___f_4625_, 0, v___f_4622_);
v___x_4626_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(v_e_4609_, v___f_4625_, v___f_4624_, v___x_4623_, v_beta_4612_, v_a_4613_, v_a_4614_, v_a_4615_, v_a_4616_);
return v___x_4626_;
}
else
{
lean_object* v___f_4627_; lean_object* v___f_4628_; uint8_t v___x_4629_; lean_object* v___x_4630_; 
v___f_4627_ = ((lean_object*)(l_Lean_Meta_zetaReduce___closed__0));
v___f_4628_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaReduce___lam__4___boxed), 7, 1);
lean_closure_set(v___f_4628_, 0, v___f_4622_);
v___x_4629_ = 0;
v___x_4630_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(v_e_4609_, v___f_4628_, v___f_4627_, v___x_4623_, v___x_4629_, v_a_4613_, v_a_4614_, v_a_4615_, v_a_4616_);
return v___x_4630_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___boxed(lean_object* v_e_4631_, lean_object* v_zetaDelta_4632_, lean_object* v_zetaHave_4633_, lean_object* v_beta_4634_, lean_object* v_a_4635_, lean_object* v_a_4636_, lean_object* v_a_4637_, lean_object* v_a_4638_, lean_object* v_a_4639_){
_start:
{
uint8_t v_zetaDelta_boxed_4640_; uint8_t v_zetaHave_boxed_4641_; uint8_t v_beta_boxed_4642_; lean_object* v_res_4643_; 
v_zetaDelta_boxed_4640_ = lean_unbox(v_zetaDelta_4632_);
v_zetaHave_boxed_4641_ = lean_unbox(v_zetaHave_4633_);
v_beta_boxed_4642_ = lean_unbox(v_beta_4634_);
v_res_4643_ = l_Lean_Meta_zetaReduce(v_e_4631_, v_zetaDelta_boxed_4640_, v_zetaHave_boxed_4641_, v_beta_boxed_4642_, v_a_4635_, v_a_4636_, v_a_4637_, v_a_4638_);
lean_dec(v_a_4638_);
lean_dec_ref(v_a_4637_);
lean_dec(v_a_4636_);
lean_dec_ref(v_a_4635_);
return v_res_4643_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4(lean_object* v_upperBound_4644_, lean_object* v___x_4645_, lean_object* v_pre_4646_, lean_object* v_post_4647_, uint8_t v_usedLetOnly_4648_, uint8_t v_skipConstInApp_4649_, uint8_t v_skipInstances_4650_, lean_object* v___x_4651_, lean_object* v_inst_4652_, lean_object* v_R_4653_, lean_object* v_a_4654_, lean_object* v_b_4655_, lean_object* v_c_4656_, lean_object* v___y_4657_, lean_object* v___y_4658_, lean_object* v___y_4659_, lean_object* v___y_4660_, lean_object* v___y_4661_){
_start:
{
lean_object* v___x_4663_; 
v___x_4663_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg(v_upperBound_4644_, v___x_4645_, v_pre_4646_, v_post_4647_, v_usedLetOnly_4648_, v_skipConstInApp_4649_, v_skipInstances_4650_, v_a_4654_, v_b_4655_, v___y_4657_, v___y_4658_, v___y_4659_, v___y_4660_, v___y_4661_);
return v___x_4663_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___boxed(lean_object** _args){
lean_object* v_upperBound_4664_ = _args[0];
lean_object* v___x_4665_ = _args[1];
lean_object* v_pre_4666_ = _args[2];
lean_object* v_post_4667_ = _args[3];
lean_object* v_usedLetOnly_4668_ = _args[4];
lean_object* v_skipConstInApp_4669_ = _args[5];
lean_object* v_skipInstances_4670_ = _args[6];
lean_object* v___x_4671_ = _args[7];
lean_object* v_inst_4672_ = _args[8];
lean_object* v_R_4673_ = _args[9];
lean_object* v_a_4674_ = _args[10];
lean_object* v_b_4675_ = _args[11];
lean_object* v_c_4676_ = _args[12];
lean_object* v___y_4677_ = _args[13];
lean_object* v___y_4678_ = _args[14];
lean_object* v___y_4679_ = _args[15];
lean_object* v___y_4680_ = _args[16];
lean_object* v___y_4681_ = _args[17];
lean_object* v___y_4682_ = _args[18];
_start:
{
uint8_t v_usedLetOnly_boxed_4683_; uint8_t v_skipConstInApp_boxed_4684_; uint8_t v_skipInstances_boxed_4685_; lean_object* v_res_4686_; 
v_usedLetOnly_boxed_4683_ = lean_unbox(v_usedLetOnly_4668_);
v_skipConstInApp_boxed_4684_ = lean_unbox(v_skipConstInApp_4669_);
v_skipInstances_boxed_4685_ = lean_unbox(v_skipInstances_4670_);
v_res_4686_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4(v_upperBound_4664_, v___x_4665_, v_pre_4666_, v_post_4667_, v_usedLetOnly_boxed_4683_, v_skipConstInApp_boxed_4684_, v_skipInstances_boxed_4685_, v___x_4671_, v_inst_4672_, v_R_4673_, v_a_4674_, v_b_4675_, v_c_4676_, v___y_4677_, v___y_4678_, v___y_4679_, v___y_4680_, v___y_4681_);
lean_dec(v___y_4681_);
lean_dec_ref(v___y_4680_);
lean_dec(v___y_4679_);
lean_dec_ref(v___y_4678_);
lean_dec(v___y_4677_);
lean_dec(v___x_4671_);
lean_dec_ref(v___x_4665_);
lean_dec(v_upperBound_4664_);
return v_res_4686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6(lean_object* v_00_u03b1_4687_, lean_object* v_name_4688_, uint8_t v_bi_4689_, lean_object* v_type_4690_, lean_object* v_k_4691_, uint8_t v_kind_4692_, lean_object* v___y_4693_, lean_object* v___y_4694_, lean_object* v___y_4695_, lean_object* v___y_4696_, lean_object* v___y_4697_){
_start:
{
lean_object* v___x_4699_; 
v___x_4699_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_name_4688_, v_bi_4689_, v_type_4690_, v_k_4691_, v_kind_4692_, v___y_4693_, v___y_4694_, v___y_4695_, v___y_4696_, v___y_4697_);
return v___x_4699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___boxed(lean_object* v_00_u03b1_4700_, lean_object* v_name_4701_, lean_object* v_bi_4702_, lean_object* v_type_4703_, lean_object* v_k_4704_, lean_object* v_kind_4705_, lean_object* v___y_4706_, lean_object* v___y_4707_, lean_object* v___y_4708_, lean_object* v___y_4709_, lean_object* v___y_4710_, lean_object* v___y_4711_){
_start:
{
uint8_t v_bi_boxed_4712_; uint8_t v_kind_boxed_4713_; lean_object* v_res_4714_; 
v_bi_boxed_4712_ = lean_unbox(v_bi_4702_);
v_kind_boxed_4713_ = lean_unbox(v_kind_4705_);
v_res_4714_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6(v_00_u03b1_4700_, v_name_4701_, v_bi_boxed_4712_, v_type_4703_, v_k_4704_, v_kind_boxed_4713_, v___y_4706_, v___y_4707_, v___y_4708_, v___y_4709_, v___y_4710_);
lean_dec(v___y_4710_);
lean_dec_ref(v___y_4709_);
lean_dec(v___y_4708_);
lean_dec_ref(v___y_4707_);
lean_dec(v___y_4706_);
return v_res_4714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9(lean_object* v_00_u03b1_4715_, lean_object* v_name_4716_, lean_object* v_type_4717_, lean_object* v_val_4718_, lean_object* v_k_4719_, uint8_t v_nondep_4720_, uint8_t v_kind_4721_, lean_object* v___y_4722_, lean_object* v___y_4723_, lean_object* v___y_4724_, lean_object* v___y_4725_, lean_object* v___y_4726_){
_start:
{
lean_object* v___x_4728_; 
v___x_4728_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg(v_name_4716_, v_type_4717_, v_val_4718_, v_k_4719_, v_nondep_4720_, v_kind_4721_, v___y_4722_, v___y_4723_, v___y_4724_, v___y_4725_, v___y_4726_);
return v___x_4728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___boxed(lean_object* v_00_u03b1_4729_, lean_object* v_name_4730_, lean_object* v_type_4731_, lean_object* v_val_4732_, lean_object* v_k_4733_, lean_object* v_nondep_4734_, lean_object* v_kind_4735_, lean_object* v___y_4736_, lean_object* v___y_4737_, lean_object* v___y_4738_, lean_object* v___y_4739_, lean_object* v___y_4740_, lean_object* v___y_4741_){
_start:
{
uint8_t v_nondep_boxed_4742_; uint8_t v_kind_boxed_4743_; lean_object* v_res_4744_; 
v_nondep_boxed_4742_ = lean_unbox(v_nondep_4734_);
v_kind_boxed_4743_ = lean_unbox(v_kind_4735_);
v_res_4744_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9(v_00_u03b1_4729_, v_name_4730_, v_type_4731_, v_val_4732_, v_k_4733_, v_nondep_boxed_4742_, v_kind_boxed_4743_, v___y_4736_, v___y_4737_, v___y_4738_, v___y_4739_, v___y_4740_);
lean_dec(v___y_4740_);
lean_dec_ref(v___y_4739_);
lean_dec(v___y_4738_);
lean_dec_ref(v___y_4737_);
lean_dec(v___y_4736_);
return v_res_4744_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12(lean_object* v_00_u03b1_4745_, lean_object* v_ref_4746_, lean_object* v___y_4747_, lean_object* v___y_4748_, lean_object* v___y_4749_, lean_object* v___y_4750_){
_start:
{
lean_object* v___x_4752_; 
v___x_4752_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg(v_ref_4746_);
return v___x_4752_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___boxed(lean_object* v_00_u03b1_4753_, lean_object* v_ref_4754_, lean_object* v___y_4755_, lean_object* v___y_4756_, lean_object* v___y_4757_, lean_object* v___y_4758_, lean_object* v___y_4759_){
_start:
{
lean_object* v_res_4760_; 
v_res_4760_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12(v_00_u03b1_4753_, v_ref_4754_, v___y_4755_, v___y_4756_, v___y_4757_, v___y_4758_);
lean_dec(v___y_4758_);
lean_dec_ref(v___y_4757_);
lean_dec(v___y_4756_);
lean_dec_ref(v___y_4755_);
return v_res_4760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9(lean_object* v_00_u03b1_4761_, lean_object* v_x_4762_, lean_object* v___y_4763_, lean_object* v___y_4764_, lean_object* v___y_4765_, lean_object* v___y_4766_, lean_object* v___y_4767_){
_start:
{
lean_object* v___x_4769_; 
v___x_4769_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg(v_x_4762_, v___y_4763_, v___y_4764_, v___y_4765_, v___y_4766_, v___y_4767_);
return v___x_4769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___boxed(lean_object* v_00_u03b1_4770_, lean_object* v_x_4771_, lean_object* v___y_4772_, lean_object* v___y_4773_, lean_object* v___y_4774_, lean_object* v___y_4775_, lean_object* v___y_4776_, lean_object* v___y_4777_){
_start:
{
lean_object* v_res_4778_; 
v_res_4778_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9(v_00_u03b1_4770_, v_x_4771_, v___y_4772_, v___y_4773_, v___y_4774_, v___y_4775_, v___y_4776_);
lean_dec(v___y_4776_);
lean_dec_ref(v___y_4775_);
lean_dec(v___y_4774_);
lean_dec_ref(v___y_4773_);
lean_dec(v___y_4772_);
return v_res_4778_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0_spec__0(lean_object* v_a_4779_, lean_object* v_as_4780_, size_t v_i_4781_, size_t v_stop_4782_){
_start:
{
uint8_t v___x_4783_; 
v___x_4783_ = lean_usize_dec_eq(v_i_4781_, v_stop_4782_);
if (v___x_4783_ == 0)
{
lean_object* v___x_4784_; uint8_t v___x_4785_; 
v___x_4784_ = lean_array_uget_borrowed(v_as_4780_, v_i_4781_);
v___x_4785_ = l_Lean_instBEqFVarId_beq(v_a_4779_, v___x_4784_);
if (v___x_4785_ == 0)
{
size_t v___x_4786_; size_t v___x_4787_; 
v___x_4786_ = ((size_t)1ULL);
v___x_4787_ = lean_usize_add(v_i_4781_, v___x_4786_);
v_i_4781_ = v___x_4787_;
goto _start;
}
else
{
return v___x_4785_;
}
}
else
{
uint8_t v___x_4789_; 
v___x_4789_ = 0;
return v___x_4789_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0_spec__0___boxed(lean_object* v_a_4790_, lean_object* v_as_4791_, lean_object* v_i_4792_, lean_object* v_stop_4793_){
_start:
{
size_t v_i_boxed_4794_; size_t v_stop_boxed_4795_; uint8_t v_res_4796_; lean_object* v_r_4797_; 
v_i_boxed_4794_ = lean_unbox_usize(v_i_4792_);
lean_dec(v_i_4792_);
v_stop_boxed_4795_ = lean_unbox_usize(v_stop_4793_);
lean_dec(v_stop_4793_);
v_res_4796_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0_spec__0(v_a_4790_, v_as_4791_, v_i_boxed_4794_, v_stop_boxed_4795_);
lean_dec_ref(v_as_4791_);
lean_dec(v_a_4790_);
v_r_4797_ = lean_box(v_res_4796_);
return v_r_4797_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0(lean_object* v_as_4798_, lean_object* v_a_4799_){
_start:
{
lean_object* v___x_4800_; lean_object* v___x_4801_; uint8_t v___x_4802_; 
v___x_4800_ = lean_unsigned_to_nat(0u);
v___x_4801_ = lean_array_get_size(v_as_4798_);
v___x_4802_ = lean_nat_dec_lt(v___x_4800_, v___x_4801_);
if (v___x_4802_ == 0)
{
return v___x_4802_;
}
else
{
if (v___x_4802_ == 0)
{
return v___x_4802_;
}
else
{
size_t v___x_4803_; size_t v___x_4804_; uint8_t v___x_4805_; 
v___x_4803_ = ((size_t)0ULL);
v___x_4804_ = lean_usize_of_nat(v___x_4801_);
v___x_4805_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0_spec__0(v_a_4799_, v_as_4798_, v___x_4803_, v___x_4804_);
return v___x_4805_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0___boxed(lean_object* v_as_4806_, lean_object* v_a_4807_){
_start:
{
uint8_t v_res_4808_; lean_object* v_r_4809_; 
v_res_4808_ = l_Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0(v_as_4806_, v_a_4807_);
lean_dec(v_a_4807_);
lean_dec_ref(v_as_4806_);
v_r_4809_ = lean_box(v_res_4808_);
return v_r_4809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaFVars___lam__1(lean_object* v_fvars_4810_, lean_object* v_e_4811_, lean_object* v___y_4812_, lean_object* v___y_4813_, lean_object* v___y_4814_, lean_object* v___y_4815_){
_start:
{
lean_object* v___x_4820_; 
v___x_4820_ = l_Lean_Expr_getAppFn(v_e_4811_);
if (lean_obj_tag(v___x_4820_) == 1)
{
lean_object* v_fvarId_4821_; uint8_t v___x_4822_; 
v_fvarId_4821_ = lean_ctor_get(v___x_4820_, 0);
lean_inc(v_fvarId_4821_);
lean_dec_ref(v___x_4820_);
v___x_4822_ = l_Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0(v_fvars_4810_, v_fvarId_4821_);
if (v___x_4822_ == 0)
{
lean_dec(v_fvarId_4821_);
lean_dec_ref(v_e_4811_);
goto v___jp_4817_;
}
else
{
uint8_t v___x_4823_; lean_object* v___x_4824_; 
v___x_4823_ = 0;
v___x_4824_ = l_Lean_FVarId_getValue_x3f___redArg(v_fvarId_4821_, v___x_4823_, v___y_4812_, v___y_4814_, v___y_4815_);
if (lean_obj_tag(v___x_4824_) == 0)
{
lean_object* v_a_4825_; 
v_a_4825_ = lean_ctor_get(v___x_4824_, 0);
lean_inc(v_a_4825_);
lean_dec_ref(v___x_4824_);
if (lean_obj_tag(v_a_4825_) == 1)
{
lean_object* v_val_4826_; lean_object* v___x_4828_; uint8_t v_isShared_4829_; uint8_t v_isSharedCheck_4849_; 
v_val_4826_ = lean_ctor_get(v_a_4825_, 0);
v_isSharedCheck_4849_ = !lean_is_exclusive(v_a_4825_);
if (v_isSharedCheck_4849_ == 0)
{
v___x_4828_ = v_a_4825_;
v_isShared_4829_ = v_isSharedCheck_4849_;
goto v_resetjp_4827_;
}
else
{
lean_inc(v_val_4826_);
lean_dec(v_a_4825_);
v___x_4828_ = lean_box(0);
v_isShared_4829_ = v_isSharedCheck_4849_;
goto v_resetjp_4827_;
}
v_resetjp_4827_:
{
lean_object* v___x_4830_; lean_object* v_a_4831_; lean_object* v___x_4833_; uint8_t v_isShared_4834_; uint8_t v_isSharedCheck_4848_; 
v___x_4830_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(v_val_4826_, v___y_4813_);
v_a_4831_ = lean_ctor_get(v___x_4830_, 0);
v_isSharedCheck_4848_ = !lean_is_exclusive(v___x_4830_);
if (v_isSharedCheck_4848_ == 0)
{
v___x_4833_ = v___x_4830_;
v_isShared_4834_ = v_isSharedCheck_4848_;
goto v_resetjp_4832_;
}
else
{
lean_inc(v_a_4831_);
lean_dec(v___x_4830_);
v___x_4833_ = lean_box(0);
v_isShared_4834_ = v_isSharedCheck_4848_;
goto v_resetjp_4832_;
}
v_resetjp_4832_:
{
lean_object* v_dummy_4835_; lean_object* v_nargs_4836_; lean_object* v___x_4837_; lean_object* v___x_4838_; lean_object* v___x_4839_; lean_object* v___x_4840_; lean_object* v___x_4841_; lean_object* v___x_4843_; 
v_dummy_4835_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_4836_ = l_Lean_Expr_getAppNumArgs(v_e_4811_);
lean_inc(v_nargs_4836_);
v___x_4837_ = lean_mk_array(v_nargs_4836_, v_dummy_4835_);
v___x_4838_ = lean_unsigned_to_nat(1u);
v___x_4839_ = lean_nat_sub(v_nargs_4836_, v___x_4838_);
lean_dec(v_nargs_4836_);
v___x_4840_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_4811_, v___x_4837_, v___x_4839_);
v___x_4841_ = l_Lean_Expr_beta(v_a_4831_, v___x_4840_);
if (v_isShared_4829_ == 0)
{
lean_ctor_set(v___x_4828_, 0, v___x_4841_);
v___x_4843_ = v___x_4828_;
goto v_reusejp_4842_;
}
else
{
lean_object* v_reuseFailAlloc_4847_; 
v_reuseFailAlloc_4847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4847_, 0, v___x_4841_);
v___x_4843_ = v_reuseFailAlloc_4847_;
goto v_reusejp_4842_;
}
v_reusejp_4842_:
{
lean_object* v___x_4845_; 
if (v_isShared_4834_ == 0)
{
lean_ctor_set(v___x_4833_, 0, v___x_4843_);
v___x_4845_ = v___x_4833_;
goto v_reusejp_4844_;
}
else
{
lean_object* v_reuseFailAlloc_4846_; 
v_reuseFailAlloc_4846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4846_, 0, v___x_4843_);
v___x_4845_ = v_reuseFailAlloc_4846_;
goto v_reusejp_4844_;
}
v_reusejp_4844_:
{
return v___x_4845_;
}
}
}
}
}
else
{
lean_dec(v_a_4825_);
lean_dec_ref(v_e_4811_);
goto v___jp_4817_;
}
}
else
{
lean_object* v_a_4850_; lean_object* v___x_4852_; uint8_t v_isShared_4853_; uint8_t v_isSharedCheck_4857_; 
lean_dec_ref(v_e_4811_);
v_a_4850_ = lean_ctor_get(v___x_4824_, 0);
v_isSharedCheck_4857_ = !lean_is_exclusive(v___x_4824_);
if (v_isSharedCheck_4857_ == 0)
{
v___x_4852_ = v___x_4824_;
v_isShared_4853_ = v_isSharedCheck_4857_;
goto v_resetjp_4851_;
}
else
{
lean_inc(v_a_4850_);
lean_dec(v___x_4824_);
v___x_4852_ = lean_box(0);
v_isShared_4853_ = v_isSharedCheck_4857_;
goto v_resetjp_4851_;
}
v_resetjp_4851_:
{
lean_object* v___x_4855_; 
if (v_isShared_4853_ == 0)
{
v___x_4855_ = v___x_4852_;
goto v_reusejp_4854_;
}
else
{
lean_object* v_reuseFailAlloc_4856_; 
v_reuseFailAlloc_4856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4856_, 0, v_a_4850_);
v___x_4855_ = v_reuseFailAlloc_4856_;
goto v_reusejp_4854_;
}
v_reusejp_4854_:
{
return v___x_4855_;
}
}
}
}
}
else
{
lean_object* v___x_4858_; lean_object* v___x_4859_; 
lean_dec_ref(v___x_4820_);
lean_dec_ref(v_e_4811_);
v___x_4858_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_4859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4859_, 0, v___x_4858_);
return v___x_4859_;
}
v___jp_4817_:
{
lean_object* v___x_4818_; lean_object* v___x_4819_; 
v___x_4818_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_4819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4819_, 0, v___x_4818_);
return v___x_4819_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaFVars___lam__1___boxed(lean_object* v_fvars_4860_, lean_object* v_e_4861_, lean_object* v___y_4862_, lean_object* v___y_4863_, lean_object* v___y_4864_, lean_object* v___y_4865_, lean_object* v___y_4866_){
_start:
{
lean_object* v_res_4867_; 
v_res_4867_ = l_Lean_Meta_zetaDeltaFVars___lam__1(v_fvars_4860_, v_e_4861_, v___y_4862_, v___y_4863_, v___y_4864_, v___y_4865_);
lean_dec(v___y_4865_);
lean_dec_ref(v___y_4864_);
lean_dec(v___y_4863_);
lean_dec_ref(v___y_4862_);
lean_dec_ref(v_fvars_4860_);
return v_res_4867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaFVars(lean_object* v_e_4868_, lean_object* v_fvars_4869_, lean_object* v_a_4870_, lean_object* v_a_4871_, lean_object* v_a_4872_, lean_object* v_a_4873_){
_start:
{
lean_object* v___f_4875_; lean_object* v_pre_4876_; uint8_t v___x_4877_; lean_object* v___x_4878_; 
v___f_4875_ = ((lean_object*)(l_Lean_Meta_zetaReduce___closed__0));
v_pre_4876_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaDeltaFVars___lam__1___boxed), 7, 1);
lean_closure_set(v_pre_4876_, 0, v_fvars_4869_);
v___x_4877_ = 0;
v___x_4878_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(v_e_4868_, v_pre_4876_, v___f_4875_, v___x_4877_, v___x_4877_, v_a_4870_, v_a_4871_, v_a_4872_, v_a_4873_);
return v___x_4878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaFVars___boxed(lean_object* v_e_4879_, lean_object* v_fvars_4880_, lean_object* v_a_4881_, lean_object* v_a_4882_, lean_object* v_a_4883_, lean_object* v_a_4884_, lean_object* v_a_4885_){
_start:
{
lean_object* v_res_4886_; 
v_res_4886_ = l_Lean_Meta_zetaDeltaFVars(v_e_4879_, v_fvars_4880_, v_a_4881_, v_a_4882_, v_a_4883_, v_a_4884_);
lean_dec(v_a_4884_);
lean_dec_ref(v_a_4883_);
lean_dec(v_a_4882_);
lean_dec_ref(v_a_4881_);
return v_res_4886_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_4887_; 
v___x_4887_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4887_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_4888_; lean_object* v___x_4889_; 
v___x_4888_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__0, &l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__0);
v___x_4889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4889_, 0, v___x_4888_);
return v___x_4889_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_4890_; lean_object* v___x_4891_; 
v___x_4890_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__1, &l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__1);
v___x_4891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4891_, 0, v___x_4890_);
lean_ctor_set(v___x_4891_, 1, v___x_4890_);
return v___x_4891_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(lean_object* v_env_4892_, lean_object* v___y_4893_){
_start:
{
lean_object* v___x_4895_; lean_object* v_nextMacroScope_4896_; lean_object* v_ngen_4897_; lean_object* v_auxDeclNGen_4898_; lean_object* v_traceState_4899_; lean_object* v_messages_4900_; lean_object* v_infoState_4901_; lean_object* v_snapshotTasks_4902_; lean_object* v___x_4904_; uint8_t v_isShared_4905_; uint8_t v_isSharedCheck_4913_; 
v___x_4895_ = lean_st_ref_take(v___y_4893_);
v_nextMacroScope_4896_ = lean_ctor_get(v___x_4895_, 1);
v_ngen_4897_ = lean_ctor_get(v___x_4895_, 2);
v_auxDeclNGen_4898_ = lean_ctor_get(v___x_4895_, 3);
v_traceState_4899_ = lean_ctor_get(v___x_4895_, 4);
v_messages_4900_ = lean_ctor_get(v___x_4895_, 6);
v_infoState_4901_ = lean_ctor_get(v___x_4895_, 7);
v_snapshotTasks_4902_ = lean_ctor_get(v___x_4895_, 8);
v_isSharedCheck_4913_ = !lean_is_exclusive(v___x_4895_);
if (v_isSharedCheck_4913_ == 0)
{
lean_object* v_unused_4914_; lean_object* v_unused_4915_; 
v_unused_4914_ = lean_ctor_get(v___x_4895_, 5);
lean_dec(v_unused_4914_);
v_unused_4915_ = lean_ctor_get(v___x_4895_, 0);
lean_dec(v_unused_4915_);
v___x_4904_ = v___x_4895_;
v_isShared_4905_ = v_isSharedCheck_4913_;
goto v_resetjp_4903_;
}
else
{
lean_inc(v_snapshotTasks_4902_);
lean_inc(v_infoState_4901_);
lean_inc(v_messages_4900_);
lean_inc(v_traceState_4899_);
lean_inc(v_auxDeclNGen_4898_);
lean_inc(v_ngen_4897_);
lean_inc(v_nextMacroScope_4896_);
lean_dec(v___x_4895_);
v___x_4904_ = lean_box(0);
v_isShared_4905_ = v_isSharedCheck_4913_;
goto v_resetjp_4903_;
}
v_resetjp_4903_:
{
lean_object* v___x_4906_; lean_object* v___x_4908_; 
v___x_4906_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2, &l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2);
if (v_isShared_4905_ == 0)
{
lean_ctor_set(v___x_4904_, 5, v___x_4906_);
lean_ctor_set(v___x_4904_, 0, v_env_4892_);
v___x_4908_ = v___x_4904_;
goto v_reusejp_4907_;
}
else
{
lean_object* v_reuseFailAlloc_4912_; 
v_reuseFailAlloc_4912_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4912_, 0, v_env_4892_);
lean_ctor_set(v_reuseFailAlloc_4912_, 1, v_nextMacroScope_4896_);
lean_ctor_set(v_reuseFailAlloc_4912_, 2, v_ngen_4897_);
lean_ctor_set(v_reuseFailAlloc_4912_, 3, v_auxDeclNGen_4898_);
lean_ctor_set(v_reuseFailAlloc_4912_, 4, v_traceState_4899_);
lean_ctor_set(v_reuseFailAlloc_4912_, 5, v___x_4906_);
lean_ctor_set(v_reuseFailAlloc_4912_, 6, v_messages_4900_);
lean_ctor_set(v_reuseFailAlloc_4912_, 7, v_infoState_4901_);
lean_ctor_set(v_reuseFailAlloc_4912_, 8, v_snapshotTasks_4902_);
v___x_4908_ = v_reuseFailAlloc_4912_;
goto v_reusejp_4907_;
}
v_reusejp_4907_:
{
lean_object* v___x_4909_; lean_object* v___x_4910_; lean_object* v___x_4911_; 
v___x_4909_ = lean_st_ref_set(v___y_4893_, v___x_4908_);
v___x_4910_ = lean_box(0);
v___x_4911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4911_, 0, v___x_4910_);
return v___x_4911_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___boxed(lean_object* v_env_4916_, lean_object* v___y_4917_, lean_object* v___y_4918_){
_start:
{
lean_object* v_res_4919_; 
v_res_4919_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_4916_, v___y_4917_);
lean_dec(v___y_4917_);
return v_res_4919_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0(lean_object* v_env_4920_, lean_object* v___y_4921_, lean_object* v___y_4922_){
_start:
{
lean_object* v___x_4924_; 
v___x_4924_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_4920_, v___y_4922_);
return v___x_4924_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___boxed(lean_object* v_env_4925_, lean_object* v___y_4926_, lean_object* v___y_4927_, lean_object* v___y_4928_){
_start:
{
lean_object* v_res_4929_; 
v_res_4929_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0(v_env_4925_, v___y_4926_, v___y_4927_);
lean_dec(v___y_4927_);
lean_dec_ref(v___y_4926_);
return v_res_4929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___lam__1(lean_object* v_env_4930_, lean_object* v___x_4931_, uint8_t v___x_4932_, lean_object* v_e_4933_, lean_object* v___y_4934_, lean_object* v___y_4935_){
_start:
{
if (lean_obj_tag(v_e_4933_) == 4)
{
lean_object* v_declName_4937_; lean_object* v_us_4938_; uint8_t v___x_4939_; uint8_t v___x_4940_; 
v_declName_4937_ = lean_ctor_get(v_e_4933_, 0);
v_us_4938_ = lean_ctor_get(v_e_4933_, 1);
v___x_4939_ = 1;
lean_inc(v_declName_4937_);
v___x_4940_ = l_Lean_Environment_contains(v_env_4930_, v_declName_4937_, v___x_4939_);
if (v___x_4940_ == 0)
{
lean_object* v___x_4941_; 
lean_inc(v_declName_4937_);
v___x_4941_ = l_Lean_Environment_find_x3f(v___x_4931_, v_declName_4937_, v___x_4932_);
if (lean_obj_tag(v___x_4941_) == 1)
{
lean_object* v_val_4942_; lean_object* v___x_4944_; uint8_t v_isShared_4945_; uint8_t v_isSharedCheck_4971_; 
v_val_4942_ = lean_ctor_get(v___x_4941_, 0);
v_isSharedCheck_4971_ = !lean_is_exclusive(v___x_4941_);
if (v_isSharedCheck_4971_ == 0)
{
v___x_4944_ = v___x_4941_;
v_isShared_4945_ = v_isSharedCheck_4971_;
goto v_resetjp_4943_;
}
else
{
lean_inc(v_val_4942_);
lean_dec(v___x_4941_);
v___x_4944_ = lean_box(0);
v_isShared_4945_ = v_isSharedCheck_4971_;
goto v_resetjp_4943_;
}
v_resetjp_4943_:
{
uint8_t v___x_4946_; 
v___x_4946_ = l_Lean_ConstantInfo_hasValue(v_val_4942_, v___x_4939_);
if (v___x_4946_ == 0)
{
lean_object* v___x_4948_; 
lean_dec(v_val_4942_);
if (v_isShared_4945_ == 0)
{
lean_ctor_set_tag(v___x_4944_, 0);
lean_ctor_set(v___x_4944_, 0, v_e_4933_);
v___x_4948_ = v___x_4944_;
goto v_reusejp_4947_;
}
else
{
lean_object* v_reuseFailAlloc_4950_; 
v_reuseFailAlloc_4950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4950_, 0, v_e_4933_);
v___x_4948_ = v_reuseFailAlloc_4950_;
goto v_reusejp_4947_;
}
v_reusejp_4947_:
{
lean_object* v___x_4949_; 
v___x_4949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4949_, 0, v___x_4948_);
return v___x_4949_;
}
}
else
{
lean_object* v___x_4951_; 
lean_inc(v_us_4938_);
lean_dec_ref(v_e_4933_);
v___x_4951_ = l_Lean_Core_instantiateValueLevelParams(v_val_4942_, v_us_4938_, v___x_4939_, v___y_4934_, v___y_4935_);
lean_dec(v_val_4942_);
if (lean_obj_tag(v___x_4951_) == 0)
{
lean_object* v_a_4952_; lean_object* v___x_4954_; uint8_t v_isShared_4955_; uint8_t v_isSharedCheck_4962_; 
v_a_4952_ = lean_ctor_get(v___x_4951_, 0);
v_isSharedCheck_4962_ = !lean_is_exclusive(v___x_4951_);
if (v_isSharedCheck_4962_ == 0)
{
v___x_4954_ = v___x_4951_;
v_isShared_4955_ = v_isSharedCheck_4962_;
goto v_resetjp_4953_;
}
else
{
lean_inc(v_a_4952_);
lean_dec(v___x_4951_);
v___x_4954_ = lean_box(0);
v_isShared_4955_ = v_isSharedCheck_4962_;
goto v_resetjp_4953_;
}
v_resetjp_4953_:
{
lean_object* v___x_4957_; 
if (v_isShared_4945_ == 0)
{
lean_ctor_set(v___x_4944_, 0, v_a_4952_);
v___x_4957_ = v___x_4944_;
goto v_reusejp_4956_;
}
else
{
lean_object* v_reuseFailAlloc_4961_; 
v_reuseFailAlloc_4961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4961_, 0, v_a_4952_);
v___x_4957_ = v_reuseFailAlloc_4961_;
goto v_reusejp_4956_;
}
v_reusejp_4956_:
{
lean_object* v___x_4959_; 
if (v_isShared_4955_ == 0)
{
lean_ctor_set(v___x_4954_, 0, v___x_4957_);
v___x_4959_ = v___x_4954_;
goto v_reusejp_4958_;
}
else
{
lean_object* v_reuseFailAlloc_4960_; 
v_reuseFailAlloc_4960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4960_, 0, v___x_4957_);
v___x_4959_ = v_reuseFailAlloc_4960_;
goto v_reusejp_4958_;
}
v_reusejp_4958_:
{
return v___x_4959_;
}
}
}
}
else
{
lean_object* v_a_4963_; lean_object* v___x_4965_; uint8_t v_isShared_4966_; uint8_t v_isSharedCheck_4970_; 
lean_del_object(v___x_4944_);
v_a_4963_ = lean_ctor_get(v___x_4951_, 0);
v_isSharedCheck_4970_ = !lean_is_exclusive(v___x_4951_);
if (v_isSharedCheck_4970_ == 0)
{
v___x_4965_ = v___x_4951_;
v_isShared_4966_ = v_isSharedCheck_4970_;
goto v_resetjp_4964_;
}
else
{
lean_inc(v_a_4963_);
lean_dec(v___x_4951_);
v___x_4965_ = lean_box(0);
v_isShared_4966_ = v_isSharedCheck_4970_;
goto v_resetjp_4964_;
}
v_resetjp_4964_:
{
lean_object* v___x_4968_; 
if (v_isShared_4966_ == 0)
{
v___x_4968_ = v___x_4965_;
goto v_reusejp_4967_;
}
else
{
lean_object* v_reuseFailAlloc_4969_; 
v_reuseFailAlloc_4969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4969_, 0, v_a_4963_);
v___x_4968_ = v_reuseFailAlloc_4969_;
goto v_reusejp_4967_;
}
v_reusejp_4967_:
{
return v___x_4968_;
}
}
}
}
}
}
else
{
lean_object* v___x_4972_; lean_object* v___x_4973_; 
lean_dec(v___x_4941_);
v___x_4972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4972_, 0, v_e_4933_);
v___x_4973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4973_, 0, v___x_4972_);
return v___x_4973_;
}
}
else
{
lean_object* v___x_4974_; lean_object* v___x_4975_; 
lean_dec_ref(v___x_4931_);
v___x_4974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4974_, 0, v_e_4933_);
v___x_4975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4975_, 0, v___x_4974_);
return v___x_4975_;
}
}
else
{
lean_object* v___x_4976_; lean_object* v___x_4977_; 
lean_dec_ref(v_e_4933_);
lean_dec_ref(v___x_4931_);
lean_dec_ref(v_env_4930_);
v___x_4976_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_4977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4977_, 0, v___x_4976_);
return v___x_4977_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___lam__1___boxed(lean_object* v_env_4978_, lean_object* v___x_4979_, lean_object* v___x_4980_, lean_object* v_e_4981_, lean_object* v___y_4982_, lean_object* v___y_4983_, lean_object* v___y_4984_){
_start:
{
uint8_t v___x_2152__boxed_4985_; lean_object* v_res_4986_; 
v___x_2152__boxed_4985_ = lean_unbox(v___x_4980_);
v_res_4986_ = l_Lean_Meta_unfoldDeclsFrom___lam__1(v_env_4978_, v___x_4979_, v___x_2152__boxed_4985_, v_e_4981_, v___y_4982_, v___y_4983_);
lean_dec(v___y_4983_);
lean_dec_ref(v___y_4982_);
return v_res_4986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___lam__0(lean_object* v_biggerEnv_4987_, lean_object* v_e_4988_, lean_object* v___f_4989_, lean_object* v___y_4990_, lean_object* v___y_4991_){
_start:
{
lean_object* v___x_4993_; uint8_t v___x_4994_; lean_object* v___x_4995_; lean_object* v___x_4996_; lean_object* v_env_4997_; lean_object* v___x_4998_; lean_object* v___f_4999_; lean_object* v___x_5000_; 
v___x_4993_ = lean_st_ref_get(v___y_4991_);
v___x_4994_ = 0;
v___x_4995_ = l_Lean_Environment_setExporting(v_biggerEnv_4987_, v___x_4994_);
lean_inc_ref(v___x_4995_);
v___x_4996_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v___x_4995_, v___y_4991_);
lean_dec_ref(v___x_4996_);
v_env_4997_ = lean_ctor_get(v___x_4993_, 0);
lean_inc_ref(v_env_4997_);
lean_dec(v___x_4993_);
v___x_4998_ = lean_box(v___x_4994_);
v___f_4999_ = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDeclsFrom___lam__1___boxed), 7, 3);
lean_closure_set(v___f_4999_, 0, v_env_4997_);
lean_closure_set(v___f_4999_, 1, v___x_4995_);
lean_closure_set(v___f_4999_, 2, v___x_4998_);
v___x_5000_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_4988_, v___f_4999_, v___f_4989_, v___y_4990_, v___y_4991_);
return v___x_5000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___lam__0___boxed(lean_object* v_biggerEnv_5001_, lean_object* v_e_5002_, lean_object* v___f_5003_, lean_object* v___y_5004_, lean_object* v___y_5005_, lean_object* v___y_5006_){
_start:
{
lean_object* v_res_5007_; 
v_res_5007_ = l_Lean_Meta_unfoldDeclsFrom___lam__0(v_biggerEnv_5001_, v_e_5002_, v___f_5003_, v___y_5004_, v___y_5005_);
lean_dec(v___y_5005_);
lean_dec_ref(v___y_5004_);
return v_res_5007_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg(lean_object* v_env_5008_, lean_object* v_x_5009_, lean_object* v___y_5010_, lean_object* v___y_5011_){
_start:
{
lean_object* v___x_5013_; lean_object* v_env_5014_; lean_object* v_a_5016_; lean_object* v___x_5026_; lean_object* v___x_5027_; 
v___x_5013_ = lean_st_ref_get(v___y_5011_);
v_env_5014_ = lean_ctor_get(v___x_5013_, 0);
lean_inc_ref(v_env_5014_);
lean_dec(v___x_5013_);
v___x_5026_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_5008_, v___y_5011_);
lean_dec_ref(v___x_5026_);
lean_inc(v___y_5011_);
lean_inc_ref(v___y_5010_);
v___x_5027_ = lean_apply_3(v_x_5009_, v___y_5010_, v___y_5011_, lean_box(0));
if (lean_obj_tag(v___x_5027_) == 0)
{
lean_object* v_a_5028_; lean_object* v___x_5029_; lean_object* v___x_5031_; uint8_t v_isShared_5032_; uint8_t v_isSharedCheck_5036_; 
v_a_5028_ = lean_ctor_get(v___x_5027_, 0);
lean_inc(v_a_5028_);
lean_dec_ref(v___x_5027_);
v___x_5029_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_5014_, v___y_5011_);
v_isSharedCheck_5036_ = !lean_is_exclusive(v___x_5029_);
if (v_isSharedCheck_5036_ == 0)
{
lean_object* v_unused_5037_; 
v_unused_5037_ = lean_ctor_get(v___x_5029_, 0);
lean_dec(v_unused_5037_);
v___x_5031_ = v___x_5029_;
v_isShared_5032_ = v_isSharedCheck_5036_;
goto v_resetjp_5030_;
}
else
{
lean_dec(v___x_5029_);
v___x_5031_ = lean_box(0);
v_isShared_5032_ = v_isSharedCheck_5036_;
goto v_resetjp_5030_;
}
v_resetjp_5030_:
{
lean_object* v___x_5034_; 
if (v_isShared_5032_ == 0)
{
lean_ctor_set(v___x_5031_, 0, v_a_5028_);
v___x_5034_ = v___x_5031_;
goto v_reusejp_5033_;
}
else
{
lean_object* v_reuseFailAlloc_5035_; 
v_reuseFailAlloc_5035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5035_, 0, v_a_5028_);
v___x_5034_ = v_reuseFailAlloc_5035_;
goto v_reusejp_5033_;
}
v_reusejp_5033_:
{
return v___x_5034_;
}
}
}
else
{
lean_object* v_a_5038_; 
v_a_5038_ = lean_ctor_get(v___x_5027_, 0);
lean_inc(v_a_5038_);
lean_dec_ref(v___x_5027_);
v_a_5016_ = v_a_5038_;
goto v___jp_5015_;
}
v___jp_5015_:
{
lean_object* v___x_5017_; lean_object* v___x_5019_; uint8_t v_isShared_5020_; uint8_t v_isSharedCheck_5024_; 
v___x_5017_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_5014_, v___y_5011_);
v_isSharedCheck_5024_ = !lean_is_exclusive(v___x_5017_);
if (v_isSharedCheck_5024_ == 0)
{
lean_object* v_unused_5025_; 
v_unused_5025_ = lean_ctor_get(v___x_5017_, 0);
lean_dec(v_unused_5025_);
v___x_5019_ = v___x_5017_;
v_isShared_5020_ = v_isSharedCheck_5024_;
goto v_resetjp_5018_;
}
else
{
lean_dec(v___x_5017_);
v___x_5019_ = lean_box(0);
v_isShared_5020_ = v_isSharedCheck_5024_;
goto v_resetjp_5018_;
}
v_resetjp_5018_:
{
lean_object* v___x_5022_; 
if (v_isShared_5020_ == 0)
{
lean_ctor_set_tag(v___x_5019_, 1);
lean_ctor_set(v___x_5019_, 0, v_a_5016_);
v___x_5022_ = v___x_5019_;
goto v_reusejp_5021_;
}
else
{
lean_object* v_reuseFailAlloc_5023_; 
v_reuseFailAlloc_5023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5023_, 0, v_a_5016_);
v___x_5022_ = v_reuseFailAlloc_5023_;
goto v_reusejp_5021_;
}
v_reusejp_5021_:
{
return v___x_5022_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg___boxed(lean_object* v_env_5039_, lean_object* v_x_5040_, lean_object* v___y_5041_, lean_object* v___y_5042_, lean_object* v___y_5043_){
_start:
{
lean_object* v_res_5044_; 
v_res_5044_ = l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg(v_env_5039_, v_x_5040_, v___y_5041_, v___y_5042_);
lean_dec(v___y_5042_);
lean_dec_ref(v___y_5041_);
return v_res_5044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom(lean_object* v_biggerEnv_5045_, lean_object* v_e_5046_, lean_object* v_a_5047_, lean_object* v_a_5048_){
_start:
{
lean_object* v___x_5050_; lean_object* v_env_5051_; lean_object* v___f_5052_; lean_object* v___f_5053_; lean_object* v___x_5054_; lean_object* v___x_5055_; 
v___x_5050_ = lean_st_ref_get(v_a_5048_);
v_env_5051_ = lean_ctor_get(v___x_5050_, 0);
lean_inc_ref(v_env_5051_);
lean_dec(v___x_5050_);
v___f_5052_ = ((lean_object*)(l_Lean_Core_betaReduce___closed__1));
v___f_5053_ = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDeclsFrom___lam__0___boxed), 6, 3);
lean_closure_set(v___f_5053_, 0, v_biggerEnv_5045_);
lean_closure_set(v___f_5053_, 1, v_e_5046_);
lean_closure_set(v___f_5053_, 2, v___f_5052_);
v___x_5054_ = l_Lean_Environment_unlockAsync(v_env_5051_);
v___x_5055_ = l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg(v___x_5054_, v___f_5053_, v_a_5047_, v_a_5048_);
return v___x_5055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___boxed(lean_object* v_biggerEnv_5056_, lean_object* v_e_5057_, lean_object* v_a_5058_, lean_object* v_a_5059_, lean_object* v_a_5060_){
_start:
{
lean_object* v_res_5061_; 
v_res_5061_ = l_Lean_Meta_unfoldDeclsFrom(v_biggerEnv_5056_, v_e_5057_, v_a_5058_, v_a_5059_);
lean_dec(v_a_5059_);
lean_dec_ref(v_a_5058_);
return v_res_5061_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1(lean_object* v_00_u03b1_5062_, lean_object* v_env_5063_, lean_object* v_x_5064_, lean_object* v___y_5065_, lean_object* v___y_5066_){
_start:
{
lean_object* v___x_5068_; 
v___x_5068_ = l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg(v_env_5063_, v_x_5064_, v___y_5065_, v___y_5066_);
return v___x_5068_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___boxed(lean_object* v_00_u03b1_5069_, lean_object* v_env_5070_, lean_object* v_x_5071_, lean_object* v___y_5072_, lean_object* v___y_5073_, lean_object* v___y_5074_){
_start:
{
lean_object* v_res_5075_; 
v_res_5075_ = l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1(v_00_u03b1_5069_, v_env_5070_, v_x_5071_, v___y_5072_, v___y_5073_);
lean_dec(v___y_5073_);
lean_dec_ref(v___y_5072_);
return v_res_5075_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0(lean_object* v_af_5076_, lean_object* v_axs_5077_, lean_object* v_numSectionVars_5078_, lean_object* v_as_5079_, size_t v_i_5080_, size_t v_stop_5081_){
_start:
{
uint8_t v___x_5082_; 
v___x_5082_ = lean_usize_dec_eq(v_i_5080_, v_stop_5081_);
if (v___x_5082_ == 0)
{
uint8_t v___x_5083_; uint8_t v___y_5085_; lean_object* v___x_5089_; lean_object* v___x_5090_; uint8_t v___x_5091_; 
v___x_5083_ = 1;
v___x_5089_ = lean_array_uget_borrowed(v_as_5079_, v_i_5080_);
v___x_5090_ = l_Lean_Expr_constName_x21(v_af_5076_);
v___x_5091_ = lean_name_eq(v___x_5090_, v___x_5089_);
lean_dec(v___x_5090_);
if (v___x_5091_ == 0)
{
v___y_5085_ = v___x_5091_;
goto v___jp_5084_;
}
else
{
lean_object* v___x_5092_; uint8_t v___x_5093_; 
v___x_5092_ = lean_array_get_size(v_axs_5077_);
v___x_5093_ = lean_nat_dec_le(v___x_5092_, v_numSectionVars_5078_);
v___y_5085_ = v___x_5093_;
goto v___jp_5084_;
}
v___jp_5084_:
{
if (v___y_5085_ == 0)
{
size_t v___x_5086_; size_t v___x_5087_; 
v___x_5086_ = ((size_t)1ULL);
v___x_5087_ = lean_usize_add(v_i_5080_, v___x_5086_);
v_i_5080_ = v___x_5087_;
goto _start;
}
else
{
return v___x_5083_;
}
}
}
else
{
uint8_t v___x_5094_; 
v___x_5094_ = 0;
return v___x_5094_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0___boxed(lean_object* v_af_5095_, lean_object* v_axs_5096_, lean_object* v_numSectionVars_5097_, lean_object* v_as_5098_, lean_object* v_i_5099_, lean_object* v_stop_5100_){
_start:
{
size_t v_i_boxed_5101_; size_t v_stop_boxed_5102_; uint8_t v_res_5103_; lean_object* v_r_5104_; 
v_i_boxed_5101_ = lean_unbox_usize(v_i_5099_);
lean_dec(v_i_5099_);
v_stop_boxed_5102_ = lean_unbox_usize(v_stop_5100_);
lean_dec(v_stop_5100_);
v_res_5103_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0(v_af_5095_, v_axs_5096_, v_numSectionVars_5097_, v_as_5098_, v_i_boxed_5101_, v_stop_boxed_5102_);
lean_dec_ref(v_as_5098_);
lean_dec(v_numSectionVars_5097_);
lean_dec_ref(v_axs_5096_);
lean_dec_ref(v_af_5095_);
v_r_5104_ = lean_box(v_res_5103_);
return v_r_5104_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1_spec__1(lean_object* v_fnNames_5105_, lean_object* v_numSectionVars_5106_, lean_object* v_x_5107_, lean_object* v_x_5108_, lean_object* v_x_5109_){
_start:
{
if (lean_obj_tag(v_x_5107_) == 5)
{
lean_object* v_fn_5110_; lean_object* v_arg_5111_; lean_object* v___x_5112_; lean_object* v___x_5113_; lean_object* v___x_5114_; 
v_fn_5110_ = lean_ctor_get(v_x_5107_, 0);
lean_inc_ref(v_fn_5110_);
v_arg_5111_ = lean_ctor_get(v_x_5107_, 1);
lean_inc_ref(v_arg_5111_);
lean_dec_ref(v_x_5107_);
v___x_5112_ = lean_array_set(v_x_5108_, v_x_5109_, v_arg_5111_);
v___x_5113_ = lean_unsigned_to_nat(1u);
v___x_5114_ = lean_nat_sub(v_x_5109_, v___x_5113_);
lean_dec(v_x_5109_);
v_x_5107_ = v_fn_5110_;
v_x_5108_ = v___x_5112_;
v_x_5109_ = v___x_5114_;
goto _start;
}
else
{
uint8_t v___x_5116_; 
lean_dec(v_x_5109_);
v___x_5116_ = l_Lean_Expr_isConst(v_x_5107_);
if (v___x_5116_ == 0)
{
lean_dec_ref(v_x_5108_);
lean_dec_ref(v_x_5107_);
return v___x_5116_;
}
else
{
lean_object* v___x_5117_; lean_object* v___x_5118_; uint8_t v___x_5119_; 
v___x_5117_ = lean_unsigned_to_nat(0u);
v___x_5118_ = lean_array_get_size(v_fnNames_5105_);
v___x_5119_ = lean_nat_dec_lt(v___x_5117_, v___x_5118_);
if (v___x_5119_ == 0)
{
lean_dec_ref(v_x_5108_);
lean_dec_ref(v_x_5107_);
return v___x_5119_;
}
else
{
if (v___x_5119_ == 0)
{
lean_dec_ref(v_x_5108_);
lean_dec_ref(v_x_5107_);
return v___x_5119_;
}
else
{
size_t v___x_5120_; size_t v___x_5121_; uint8_t v___x_5122_; 
v___x_5120_ = ((size_t)0ULL);
v___x_5121_ = lean_usize_of_nat(v___x_5118_);
v___x_5122_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0(v_x_5107_, v_x_5108_, v_numSectionVars_5106_, v_fnNames_5105_, v___x_5120_, v___x_5121_);
lean_dec_ref(v_x_5108_);
lean_dec_ref(v_x_5107_);
return v___x_5122_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1_spec__1___boxed(lean_object* v_fnNames_5123_, lean_object* v_numSectionVars_5124_, lean_object* v_x_5125_, lean_object* v_x_5126_, lean_object* v_x_5127_){
_start:
{
uint8_t v_res_5128_; lean_object* v_r_5129_; 
v_res_5128_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1_spec__1(v_fnNames_5123_, v_numSectionVars_5124_, v_x_5125_, v_x_5126_, v_x_5127_);
lean_dec(v_numSectionVars_5124_);
lean_dec_ref(v_fnNames_5123_);
v_r_5129_ = lean_box(v_res_5128_);
return v_r_5129_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1(lean_object* v_numSectionVars_5130_, lean_object* v_fnNames_5131_, lean_object* v_x_5132_, lean_object* v_x_5133_, lean_object* v_x_5134_){
_start:
{
if (lean_obj_tag(v_x_5132_) == 5)
{
lean_object* v_fn_5135_; lean_object* v_arg_5136_; lean_object* v___x_5137_; lean_object* v___x_5138_; lean_object* v___x_5139_; uint8_t v___x_5140_; 
v_fn_5135_ = lean_ctor_get(v_x_5132_, 0);
lean_inc_ref(v_fn_5135_);
v_arg_5136_ = lean_ctor_get(v_x_5132_, 1);
lean_inc_ref(v_arg_5136_);
lean_dec_ref(v_x_5132_);
v___x_5137_ = lean_array_set(v_x_5133_, v_x_5134_, v_arg_5136_);
v___x_5138_ = lean_unsigned_to_nat(1u);
v___x_5139_ = lean_nat_sub(v_x_5134_, v___x_5138_);
v___x_5140_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1_spec__1(v_fnNames_5131_, v_numSectionVars_5130_, v_fn_5135_, v___x_5137_, v___x_5139_);
return v___x_5140_;
}
else
{
uint8_t v___x_5141_; 
v___x_5141_ = l_Lean_Expr_isConst(v_x_5132_);
if (v___x_5141_ == 0)
{
lean_dec_ref(v_x_5133_);
lean_dec_ref(v_x_5132_);
return v___x_5141_;
}
else
{
lean_object* v___x_5142_; lean_object* v___x_5143_; uint8_t v___x_5144_; 
v___x_5142_ = lean_unsigned_to_nat(0u);
v___x_5143_ = lean_array_get_size(v_fnNames_5131_);
v___x_5144_ = lean_nat_dec_lt(v___x_5142_, v___x_5143_);
if (v___x_5144_ == 0)
{
lean_dec_ref(v_x_5133_);
lean_dec_ref(v_x_5132_);
return v___x_5144_;
}
else
{
if (v___x_5144_ == 0)
{
lean_dec_ref(v_x_5133_);
lean_dec_ref(v_x_5132_);
return v___x_5144_;
}
else
{
size_t v___x_5145_; size_t v___x_5146_; uint8_t v___x_5147_; 
v___x_5145_ = ((size_t)0ULL);
v___x_5146_ = lean_usize_of_nat(v___x_5143_);
v___x_5147_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0(v_x_5132_, v_x_5133_, v_numSectionVars_5130_, v_fnNames_5131_, v___x_5145_, v___x_5146_);
lean_dec_ref(v_x_5133_);
lean_dec_ref(v_x_5132_);
return v___x_5147_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1___boxed(lean_object* v_numSectionVars_5148_, lean_object* v_fnNames_5149_, lean_object* v_x_5150_, lean_object* v_x_5151_, lean_object* v_x_5152_){
_start:
{
uint8_t v_res_5153_; lean_object* v_r_5154_; 
v_res_5153_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1(v_numSectionVars_5148_, v_fnNames_5149_, v_x_5150_, v_x_5151_, v_x_5152_);
lean_dec(v_x_5152_);
lean_dec_ref(v_fnNames_5149_);
lean_dec(v_numSectionVars_5148_);
v_r_5154_ = lean_box(v_res_5153_);
return v_r_5154_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg(lean_object* v_fnNames_5155_, lean_object* v_numSectionVars_5156_, lean_object* v_a_5157_){
_start:
{
lean_object* v_dummy_5158_; lean_object* v_nargs_5159_; lean_object* v___x_5160_; lean_object* v___x_5161_; lean_object* v___x_5162_; uint8_t v___x_5163_; 
v_dummy_5158_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_5159_ = l_Lean_Expr_getAppNumArgs(v_a_5157_);
lean_inc(v_nargs_5159_);
v___x_5160_ = lean_mk_array(v_nargs_5159_, v_dummy_5158_);
v___x_5161_ = lean_unsigned_to_nat(1u);
v___x_5162_ = lean_nat_sub(v_nargs_5159_, v___x_5161_);
lean_dec(v_nargs_5159_);
v___x_5163_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1(v_numSectionVars_5156_, v_fnNames_5155_, v_a_5157_, v___x_5160_, v___x_5162_);
lean_dec(v___x_5162_);
return v___x_5163_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg___boxed(lean_object* v_fnNames_5164_, lean_object* v_numSectionVars_5165_, lean_object* v_a_5166_){
_start:
{
uint8_t v_res_5167_; lean_object* v_r_5168_; 
v_res_5167_ = l___private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg(v_fnNames_5164_, v_numSectionVars_5165_, v_a_5166_);
lean_dec(v_numSectionVars_5165_);
lean_dec_ref(v_fnNames_5164_);
v_r_5168_ = lean_box(v_res_5167_);
return v_r_5168_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__0(lean_object* v_fnNames_5169_, lean_object* v_numSectionVars_5170_, lean_object* v_as_5171_, size_t v_i_5172_, size_t v_stop_5173_){
_start:
{
uint8_t v___x_5174_; 
v___x_5174_ = lean_usize_dec_eq(v_i_5172_, v_stop_5173_);
if (v___x_5174_ == 0)
{
lean_object* v___x_5175_; uint8_t v___x_5176_; 
v___x_5175_ = lean_array_uget_borrowed(v_as_5171_, v_i_5172_);
lean_inc(v___x_5175_);
v___x_5176_ = l___private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg(v_fnNames_5169_, v_numSectionVars_5170_, v___x_5175_);
if (v___x_5176_ == 0)
{
size_t v___x_5177_; size_t v___x_5178_; 
v___x_5177_ = ((size_t)1ULL);
v___x_5178_ = lean_usize_add(v_i_5172_, v___x_5177_);
v_i_5172_ = v___x_5178_;
goto _start;
}
else
{
return v___x_5176_;
}
}
else
{
uint8_t v___x_5180_; 
v___x_5180_ = 0;
return v___x_5180_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__0___boxed(lean_object* v_fnNames_5181_, lean_object* v_numSectionVars_5182_, lean_object* v_as_5183_, lean_object* v_i_5184_, lean_object* v_stop_5185_){
_start:
{
size_t v_i_boxed_5186_; size_t v_stop_boxed_5187_; uint8_t v_res_5188_; lean_object* v_r_5189_; 
v_i_boxed_5186_ = lean_unbox_usize(v_i_5184_);
lean_dec(v_i_5184_);
v_stop_boxed_5187_ = lean_unbox_usize(v_stop_5185_);
lean_dec(v_stop_5185_);
v_res_5188_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__0(v_fnNames_5181_, v_numSectionVars_5182_, v_as_5183_, v_i_boxed_5186_, v_stop_boxed_5187_);
lean_dec_ref(v_as_5183_);
lean_dec(v_numSectionVars_5182_);
lean_dec_ref(v_fnNames_5181_);
v_r_5189_ = lean_box(v_res_5188_);
return v_r_5189_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__1(lean_object* v_fnNames_5190_, lean_object* v_numSectionVars_5191_, lean_object* v___x_5192_, lean_object* v_x_5193_, lean_object* v_x_5194_, lean_object* v___y_5195_, lean_object* v___y_5196_){
_start:
{
if (lean_obj_tag(v_x_5193_) == 5)
{
lean_object* v_fn_5201_; lean_object* v_arg_5202_; lean_object* v___x_5203_; 
v_fn_5201_ = lean_ctor_get(v_x_5193_, 0);
lean_inc_ref(v_fn_5201_);
v_arg_5202_ = lean_ctor_get(v_x_5193_, 1);
lean_inc_ref(v_arg_5202_);
lean_dec_ref(v_x_5193_);
v___x_5203_ = lean_array_push(v_x_5194_, v_arg_5202_);
v_x_5193_ = v_fn_5201_;
v_x_5194_ = v___x_5203_;
goto _start;
}
else
{
uint8_t v___x_5205_; 
v___x_5205_ = l_Lean_Expr_isConst(v_x_5193_);
if (v___x_5205_ == 0)
{
lean_dec_ref(v_x_5194_);
lean_dec_ref(v_x_5193_);
lean_dec_ref(v___x_5192_);
goto v___jp_5198_;
}
else
{
lean_object* v___x_5206_; lean_object* v___x_5207_; uint8_t v___x_5208_; 
v___x_5206_ = lean_unsigned_to_nat(0u);
v___x_5207_ = lean_array_get_size(v_x_5194_);
v___x_5208_ = lean_nat_dec_lt(v___x_5206_, v___x_5207_);
if (v___x_5208_ == 0)
{
lean_dec_ref(v_x_5194_);
lean_dec_ref(v_x_5193_);
lean_dec_ref(v___x_5192_);
goto v___jp_5198_;
}
else
{
if (v___x_5208_ == 0)
{
lean_dec_ref(v_x_5194_);
lean_dec_ref(v_x_5193_);
lean_dec_ref(v___x_5192_);
goto v___jp_5198_;
}
else
{
size_t v___x_5209_; size_t v___x_5210_; uint8_t v___x_5211_; 
v___x_5209_ = ((size_t)0ULL);
v___x_5210_ = lean_usize_of_nat(v___x_5207_);
v___x_5211_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__0(v_fnNames_5190_, v_numSectionVars_5191_, v_x_5194_, v___x_5209_, v___x_5210_);
if (v___x_5211_ == 0)
{
lean_dec_ref(v_x_5194_);
lean_dec_ref(v_x_5193_);
lean_dec_ref(v___x_5192_);
goto v___jp_5198_;
}
else
{
lean_object* v___x_5212_; uint8_t v___x_5213_; lean_object* v___x_5214_; 
v___x_5212_ = l_Lean_Expr_constName_x21(v_x_5193_);
v___x_5213_ = 0;
v___x_5214_ = l_Lean_Environment_find_x3f(v___x_5192_, v___x_5212_, v___x_5213_);
if (lean_obj_tag(v___x_5214_) == 1)
{
lean_object* v_val_5215_; 
v_val_5215_ = lean_ctor_get(v___x_5214_, 0);
lean_inc(v_val_5215_);
lean_dec_ref(v___x_5214_);
if (lean_obj_tag(v_val_5215_) == 2)
{
lean_object* v___x_5216_; lean_object* v___x_5217_; lean_object* v___x_5219_; uint8_t v_isShared_5220_; uint8_t v_isSharedCheck_5241_; 
v___x_5216_ = l_Lean_Expr_constLevels_x21(v_x_5193_);
lean_dec_ref(v_x_5193_);
v___x_5217_ = l_Lean_Core_instantiateValueLevelParams(v_val_5215_, v___x_5216_, v___x_5205_, v___y_5195_, v___y_5196_);
v_isSharedCheck_5241_ = !lean_is_exclusive(v_val_5215_);
if (v_isSharedCheck_5241_ == 0)
{
lean_object* v_unused_5242_; 
v_unused_5242_ = lean_ctor_get(v_val_5215_, 0);
lean_dec(v_unused_5242_);
v___x_5219_ = v_val_5215_;
v_isShared_5220_ = v_isSharedCheck_5241_;
goto v_resetjp_5218_;
}
else
{
lean_dec(v_val_5215_);
v___x_5219_ = lean_box(0);
v_isShared_5220_ = v_isSharedCheck_5241_;
goto v_resetjp_5218_;
}
v_resetjp_5218_:
{
if (lean_obj_tag(v___x_5217_) == 0)
{
lean_object* v_a_5221_; lean_object* v___x_5223_; uint8_t v_isShared_5224_; uint8_t v_isSharedCheck_5232_; 
v_a_5221_ = lean_ctor_get(v___x_5217_, 0);
v_isSharedCheck_5232_ = !lean_is_exclusive(v___x_5217_);
if (v_isSharedCheck_5232_ == 0)
{
v___x_5223_ = v___x_5217_;
v_isShared_5224_ = v_isSharedCheck_5232_;
goto v_resetjp_5222_;
}
else
{
lean_inc(v_a_5221_);
lean_dec(v___x_5217_);
v___x_5223_ = lean_box(0);
v_isShared_5224_ = v_isSharedCheck_5232_;
goto v_resetjp_5222_;
}
v_resetjp_5222_:
{
lean_object* v___x_5225_; lean_object* v___x_5227_; 
v___x_5225_ = l_Lean_Expr_betaRev(v_a_5221_, v_x_5194_, v___x_5213_, v___x_5213_);
lean_dec_ref(v_x_5194_);
if (v_isShared_5220_ == 0)
{
lean_ctor_set_tag(v___x_5219_, 1);
lean_ctor_set(v___x_5219_, 0, v___x_5225_);
v___x_5227_ = v___x_5219_;
goto v_reusejp_5226_;
}
else
{
lean_object* v_reuseFailAlloc_5231_; 
v_reuseFailAlloc_5231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5231_, 0, v___x_5225_);
v___x_5227_ = v_reuseFailAlloc_5231_;
goto v_reusejp_5226_;
}
v_reusejp_5226_:
{
lean_object* v___x_5229_; 
if (v_isShared_5224_ == 0)
{
lean_ctor_set(v___x_5223_, 0, v___x_5227_);
v___x_5229_ = v___x_5223_;
goto v_reusejp_5228_;
}
else
{
lean_object* v_reuseFailAlloc_5230_; 
v_reuseFailAlloc_5230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5230_, 0, v___x_5227_);
v___x_5229_ = v_reuseFailAlloc_5230_;
goto v_reusejp_5228_;
}
v_reusejp_5228_:
{
return v___x_5229_;
}
}
}
}
else
{
lean_object* v_a_5233_; lean_object* v___x_5235_; uint8_t v_isShared_5236_; uint8_t v_isSharedCheck_5240_; 
lean_del_object(v___x_5219_);
lean_dec_ref(v_x_5194_);
v_a_5233_ = lean_ctor_get(v___x_5217_, 0);
v_isSharedCheck_5240_ = !lean_is_exclusive(v___x_5217_);
if (v_isSharedCheck_5240_ == 0)
{
v___x_5235_ = v___x_5217_;
v_isShared_5236_ = v_isSharedCheck_5240_;
goto v_resetjp_5234_;
}
else
{
lean_inc(v_a_5233_);
lean_dec(v___x_5217_);
v___x_5235_ = lean_box(0);
v_isShared_5236_ = v_isSharedCheck_5240_;
goto v_resetjp_5234_;
}
v_resetjp_5234_:
{
lean_object* v___x_5238_; 
if (v_isShared_5236_ == 0)
{
v___x_5238_ = v___x_5235_;
goto v_reusejp_5237_;
}
else
{
lean_object* v_reuseFailAlloc_5239_; 
v_reuseFailAlloc_5239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5239_, 0, v_a_5233_);
v___x_5238_ = v_reuseFailAlloc_5239_;
goto v_reusejp_5237_;
}
v_reusejp_5237_:
{
return v___x_5238_;
}
}
}
}
}
else
{
lean_dec(v_val_5215_);
lean_dec_ref(v_x_5194_);
lean_dec_ref(v_x_5193_);
goto v___jp_5198_;
}
}
else
{
lean_dec(v___x_5214_);
lean_dec_ref(v_x_5194_);
lean_dec_ref(v_x_5193_);
goto v___jp_5198_;
}
}
}
}
}
}
v___jp_5198_:
{
lean_object* v___x_5199_; lean_object* v___x_5200_; 
v___x_5199_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_5200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5200_, 0, v___x_5199_);
return v___x_5200_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__1___boxed(lean_object* v_fnNames_5243_, lean_object* v_numSectionVars_5244_, lean_object* v___x_5245_, lean_object* v_x_5246_, lean_object* v_x_5247_, lean_object* v___y_5248_, lean_object* v___y_5249_, lean_object* v___y_5250_){
_start:
{
lean_object* v_res_5251_; 
v_res_5251_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__1(v_fnNames_5243_, v_numSectionVars_5244_, v___x_5245_, v_x_5246_, v_x_5247_, v___y_5248_, v___y_5249_);
lean_dec(v___y_5249_);
lean_dec_ref(v___y_5248_);
lean_dec(v_numSectionVars_5244_);
lean_dec_ref(v_fnNames_5243_);
return v_res_5251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___lam__1(lean_object* v_fnNames_5252_, lean_object* v_numSectionVars_5253_, lean_object* v_env_5254_, lean_object* v_e_5255_, lean_object* v___y_5256_, lean_object* v___y_5257_){
_start:
{
lean_object* v___x_5259_; lean_object* v___x_5260_; lean_object* v___x_5261_; 
v___x_5259_ = l_Lean_Expr_getAppNumArgs(v_e_5255_);
v___x_5260_ = lean_mk_empty_array_with_capacity(v___x_5259_);
lean_dec(v___x_5259_);
v___x_5261_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__1(v_fnNames_5252_, v_numSectionVars_5253_, v_env_5254_, v_e_5255_, v___x_5260_, v___y_5256_, v___y_5257_);
return v___x_5261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___lam__1___boxed(lean_object* v_fnNames_5262_, lean_object* v_numSectionVars_5263_, lean_object* v_env_5264_, lean_object* v_e_5265_, lean_object* v___y_5266_, lean_object* v___y_5267_, lean_object* v___y_5268_){
_start:
{
lean_object* v_res_5269_; 
v_res_5269_ = l_Lean_Meta_unfoldIfArgIsAppOf___lam__1(v_fnNames_5262_, v_numSectionVars_5263_, v_env_5264_, v_e_5265_, v___y_5266_, v___y_5267_);
lean_dec(v___y_5267_);
lean_dec_ref(v___y_5266_);
lean_dec(v_numSectionVars_5263_);
lean_dec_ref(v_fnNames_5262_);
return v_res_5269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___lam__0(lean_object* v_fnNames_5270_, lean_object* v_numSectionVars_5271_, lean_object* v_e_5272_, lean_object* v___f_5273_, lean_object* v___y_5274_, lean_object* v___y_5275_){
_start:
{
lean_object* v___x_5277_; lean_object* v_env_5278_; lean_object* v___f_5279_; lean_object* v___x_5280_; 
v___x_5277_ = lean_st_ref_get(v___y_5275_);
v_env_5278_ = lean_ctor_get(v___x_5277_, 0);
lean_inc_ref(v_env_5278_);
lean_dec(v___x_5277_);
v___f_5279_ = lean_alloc_closure((void*)(l_Lean_Meta_unfoldIfArgIsAppOf___lam__1___boxed), 7, 3);
lean_closure_set(v___f_5279_, 0, v_fnNames_5270_);
lean_closure_set(v___f_5279_, 1, v_numSectionVars_5271_);
lean_closure_set(v___f_5279_, 2, v_env_5278_);
v___x_5280_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_5272_, v___f_5279_, v___f_5273_, v___y_5274_, v___y_5275_);
return v___x_5280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___lam__0___boxed(lean_object* v_fnNames_5281_, lean_object* v_numSectionVars_5282_, lean_object* v_e_5283_, lean_object* v___f_5284_, lean_object* v___y_5285_, lean_object* v___y_5286_, lean_object* v___y_5287_){
_start:
{
lean_object* v_res_5288_; 
v_res_5288_ = l_Lean_Meta_unfoldIfArgIsAppOf___lam__0(v_fnNames_5281_, v_numSectionVars_5282_, v_e_5283_, v___f_5284_, v___y_5285_, v___y_5286_);
lean_dec(v___y_5286_);
lean_dec_ref(v___y_5285_);
return v_res_5288_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0(lean_object* v___y_5289_, uint8_t v_isExporting_5290_, lean_object* v___x_5291_, lean_object* v_a_x3f_5292_){
_start:
{
lean_object* v___x_5294_; lean_object* v_env_5295_; lean_object* v_nextMacroScope_5296_; lean_object* v_ngen_5297_; lean_object* v_auxDeclNGen_5298_; lean_object* v_traceState_5299_; lean_object* v_messages_5300_; lean_object* v_infoState_5301_; lean_object* v_snapshotTasks_5302_; lean_object* v___x_5304_; uint8_t v_isShared_5305_; uint8_t v_isSharedCheck_5313_; 
v___x_5294_ = lean_st_ref_take(v___y_5289_);
v_env_5295_ = lean_ctor_get(v___x_5294_, 0);
v_nextMacroScope_5296_ = lean_ctor_get(v___x_5294_, 1);
v_ngen_5297_ = lean_ctor_get(v___x_5294_, 2);
v_auxDeclNGen_5298_ = lean_ctor_get(v___x_5294_, 3);
v_traceState_5299_ = lean_ctor_get(v___x_5294_, 4);
v_messages_5300_ = lean_ctor_get(v___x_5294_, 6);
v_infoState_5301_ = lean_ctor_get(v___x_5294_, 7);
v_snapshotTasks_5302_ = lean_ctor_get(v___x_5294_, 8);
v_isSharedCheck_5313_ = !lean_is_exclusive(v___x_5294_);
if (v_isSharedCheck_5313_ == 0)
{
lean_object* v_unused_5314_; 
v_unused_5314_ = lean_ctor_get(v___x_5294_, 5);
lean_dec(v_unused_5314_);
v___x_5304_ = v___x_5294_;
v_isShared_5305_ = v_isSharedCheck_5313_;
goto v_resetjp_5303_;
}
else
{
lean_inc(v_snapshotTasks_5302_);
lean_inc(v_infoState_5301_);
lean_inc(v_messages_5300_);
lean_inc(v_traceState_5299_);
lean_inc(v_auxDeclNGen_5298_);
lean_inc(v_ngen_5297_);
lean_inc(v_nextMacroScope_5296_);
lean_inc(v_env_5295_);
lean_dec(v___x_5294_);
v___x_5304_ = lean_box(0);
v_isShared_5305_ = v_isSharedCheck_5313_;
goto v_resetjp_5303_;
}
v_resetjp_5303_:
{
lean_object* v___x_5306_; lean_object* v___x_5308_; 
v___x_5306_ = l_Lean_Environment_setExporting(v_env_5295_, v_isExporting_5290_);
if (v_isShared_5305_ == 0)
{
lean_ctor_set(v___x_5304_, 5, v___x_5291_);
lean_ctor_set(v___x_5304_, 0, v___x_5306_);
v___x_5308_ = v___x_5304_;
goto v_reusejp_5307_;
}
else
{
lean_object* v_reuseFailAlloc_5312_; 
v_reuseFailAlloc_5312_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5312_, 0, v___x_5306_);
lean_ctor_set(v_reuseFailAlloc_5312_, 1, v_nextMacroScope_5296_);
lean_ctor_set(v_reuseFailAlloc_5312_, 2, v_ngen_5297_);
lean_ctor_set(v_reuseFailAlloc_5312_, 3, v_auxDeclNGen_5298_);
lean_ctor_set(v_reuseFailAlloc_5312_, 4, v_traceState_5299_);
lean_ctor_set(v_reuseFailAlloc_5312_, 5, v___x_5291_);
lean_ctor_set(v_reuseFailAlloc_5312_, 6, v_messages_5300_);
lean_ctor_set(v_reuseFailAlloc_5312_, 7, v_infoState_5301_);
lean_ctor_set(v_reuseFailAlloc_5312_, 8, v_snapshotTasks_5302_);
v___x_5308_ = v_reuseFailAlloc_5312_;
goto v_reusejp_5307_;
}
v_reusejp_5307_:
{
lean_object* v___x_5309_; lean_object* v___x_5310_; lean_object* v___x_5311_; 
v___x_5309_ = lean_st_ref_set(v___y_5289_, v___x_5308_);
v___x_5310_ = lean_box(0);
v___x_5311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5311_, 0, v___x_5310_);
return v___x_5311_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0___boxed(lean_object* v___y_5315_, lean_object* v_isExporting_5316_, lean_object* v___x_5317_, lean_object* v_a_x3f_5318_, lean_object* v___y_5319_){
_start:
{
uint8_t v_isExporting_boxed_5320_; lean_object* v_res_5321_; 
v_isExporting_boxed_5320_ = lean_unbox(v_isExporting_5316_);
v_res_5321_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0(v___y_5315_, v_isExporting_boxed_5320_, v___x_5317_, v_a_x3f_5318_);
lean_dec(v_a_x3f_5318_);
lean_dec(v___y_5315_);
return v_res_5321_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg(lean_object* v_x_5322_, uint8_t v_isExporting_5323_, lean_object* v___y_5324_, lean_object* v___y_5325_){
_start:
{
lean_object* v___x_5327_; lean_object* v_env_5328_; uint8_t v_isExporting_5329_; lean_object* v___x_5330_; lean_object* v_env_5331_; lean_object* v_nextMacroScope_5332_; lean_object* v_ngen_5333_; lean_object* v_auxDeclNGen_5334_; lean_object* v_traceState_5335_; lean_object* v_messages_5336_; lean_object* v_infoState_5337_; lean_object* v_snapshotTasks_5338_; lean_object* v___x_5340_; uint8_t v_isShared_5341_; uint8_t v_isSharedCheck_5377_; 
v___x_5327_ = lean_st_ref_get(v___y_5325_);
v_env_5328_ = lean_ctor_get(v___x_5327_, 0);
lean_inc_ref(v_env_5328_);
lean_dec(v___x_5327_);
v_isExporting_5329_ = lean_ctor_get_uint8(v_env_5328_, sizeof(void*)*8);
lean_dec_ref(v_env_5328_);
v___x_5330_ = lean_st_ref_take(v___y_5325_);
v_env_5331_ = lean_ctor_get(v___x_5330_, 0);
v_nextMacroScope_5332_ = lean_ctor_get(v___x_5330_, 1);
v_ngen_5333_ = lean_ctor_get(v___x_5330_, 2);
v_auxDeclNGen_5334_ = lean_ctor_get(v___x_5330_, 3);
v_traceState_5335_ = lean_ctor_get(v___x_5330_, 4);
v_messages_5336_ = lean_ctor_get(v___x_5330_, 6);
v_infoState_5337_ = lean_ctor_get(v___x_5330_, 7);
v_snapshotTasks_5338_ = lean_ctor_get(v___x_5330_, 8);
v_isSharedCheck_5377_ = !lean_is_exclusive(v___x_5330_);
if (v_isSharedCheck_5377_ == 0)
{
lean_object* v_unused_5378_; 
v_unused_5378_ = lean_ctor_get(v___x_5330_, 5);
lean_dec(v_unused_5378_);
v___x_5340_ = v___x_5330_;
v_isShared_5341_ = v_isSharedCheck_5377_;
goto v_resetjp_5339_;
}
else
{
lean_inc(v_snapshotTasks_5338_);
lean_inc(v_infoState_5337_);
lean_inc(v_messages_5336_);
lean_inc(v_traceState_5335_);
lean_inc(v_auxDeclNGen_5334_);
lean_inc(v_ngen_5333_);
lean_inc(v_nextMacroScope_5332_);
lean_inc(v_env_5331_);
lean_dec(v___x_5330_);
v___x_5340_ = lean_box(0);
v_isShared_5341_ = v_isSharedCheck_5377_;
goto v_resetjp_5339_;
}
v_resetjp_5339_:
{
lean_object* v___x_5342_; lean_object* v___x_5343_; lean_object* v___x_5345_; 
v___x_5342_ = l_Lean_Environment_setExporting(v_env_5331_, v_isExporting_5323_);
v___x_5343_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2, &l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2);
if (v_isShared_5341_ == 0)
{
lean_ctor_set(v___x_5340_, 5, v___x_5343_);
lean_ctor_set(v___x_5340_, 0, v___x_5342_);
v___x_5345_ = v___x_5340_;
goto v_reusejp_5344_;
}
else
{
lean_object* v_reuseFailAlloc_5376_; 
v_reuseFailAlloc_5376_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5376_, 0, v___x_5342_);
lean_ctor_set(v_reuseFailAlloc_5376_, 1, v_nextMacroScope_5332_);
lean_ctor_set(v_reuseFailAlloc_5376_, 2, v_ngen_5333_);
lean_ctor_set(v_reuseFailAlloc_5376_, 3, v_auxDeclNGen_5334_);
lean_ctor_set(v_reuseFailAlloc_5376_, 4, v_traceState_5335_);
lean_ctor_set(v_reuseFailAlloc_5376_, 5, v___x_5343_);
lean_ctor_set(v_reuseFailAlloc_5376_, 6, v_messages_5336_);
lean_ctor_set(v_reuseFailAlloc_5376_, 7, v_infoState_5337_);
lean_ctor_set(v_reuseFailAlloc_5376_, 8, v_snapshotTasks_5338_);
v___x_5345_ = v_reuseFailAlloc_5376_;
goto v_reusejp_5344_;
}
v_reusejp_5344_:
{
lean_object* v___x_5346_; lean_object* v_r_5347_; 
v___x_5346_ = lean_st_ref_set(v___y_5325_, v___x_5345_);
lean_inc(v___y_5325_);
lean_inc_ref(v___y_5324_);
v_r_5347_ = lean_apply_3(v_x_5322_, v___y_5324_, v___y_5325_, lean_box(0));
if (lean_obj_tag(v_r_5347_) == 0)
{
lean_object* v_a_5348_; lean_object* v___x_5350_; uint8_t v_isShared_5351_; uint8_t v_isSharedCheck_5364_; 
v_a_5348_ = lean_ctor_get(v_r_5347_, 0);
v_isSharedCheck_5364_ = !lean_is_exclusive(v_r_5347_);
if (v_isSharedCheck_5364_ == 0)
{
v___x_5350_ = v_r_5347_;
v_isShared_5351_ = v_isSharedCheck_5364_;
goto v_resetjp_5349_;
}
else
{
lean_inc(v_a_5348_);
lean_dec(v_r_5347_);
v___x_5350_ = lean_box(0);
v_isShared_5351_ = v_isSharedCheck_5364_;
goto v_resetjp_5349_;
}
v_resetjp_5349_:
{
lean_object* v___x_5353_; 
lean_inc(v_a_5348_);
if (v_isShared_5351_ == 0)
{
lean_ctor_set_tag(v___x_5350_, 1);
v___x_5353_ = v___x_5350_;
goto v_reusejp_5352_;
}
else
{
lean_object* v_reuseFailAlloc_5363_; 
v_reuseFailAlloc_5363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5363_, 0, v_a_5348_);
v___x_5353_ = v_reuseFailAlloc_5363_;
goto v_reusejp_5352_;
}
v_reusejp_5352_:
{
lean_object* v___x_5354_; lean_object* v___x_5356_; uint8_t v_isShared_5357_; uint8_t v_isSharedCheck_5361_; 
v___x_5354_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0(v___y_5325_, v_isExporting_5329_, v___x_5343_, v___x_5353_);
lean_dec_ref(v___x_5353_);
v_isSharedCheck_5361_ = !lean_is_exclusive(v___x_5354_);
if (v_isSharedCheck_5361_ == 0)
{
lean_object* v_unused_5362_; 
v_unused_5362_ = lean_ctor_get(v___x_5354_, 0);
lean_dec(v_unused_5362_);
v___x_5356_ = v___x_5354_;
v_isShared_5357_ = v_isSharedCheck_5361_;
goto v_resetjp_5355_;
}
else
{
lean_dec(v___x_5354_);
v___x_5356_ = lean_box(0);
v_isShared_5357_ = v_isSharedCheck_5361_;
goto v_resetjp_5355_;
}
v_resetjp_5355_:
{
lean_object* v___x_5359_; 
if (v_isShared_5357_ == 0)
{
lean_ctor_set(v___x_5356_, 0, v_a_5348_);
v___x_5359_ = v___x_5356_;
goto v_reusejp_5358_;
}
else
{
lean_object* v_reuseFailAlloc_5360_; 
v_reuseFailAlloc_5360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5360_, 0, v_a_5348_);
v___x_5359_ = v_reuseFailAlloc_5360_;
goto v_reusejp_5358_;
}
v_reusejp_5358_:
{
return v___x_5359_;
}
}
}
}
}
else
{
lean_object* v_a_5365_; lean_object* v___x_5366_; lean_object* v___x_5367_; lean_object* v___x_5369_; uint8_t v_isShared_5370_; uint8_t v_isSharedCheck_5374_; 
v_a_5365_ = lean_ctor_get(v_r_5347_, 0);
lean_inc(v_a_5365_);
lean_dec_ref(v_r_5347_);
v___x_5366_ = lean_box(0);
v___x_5367_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0(v___y_5325_, v_isExporting_5329_, v___x_5343_, v___x_5366_);
v_isSharedCheck_5374_ = !lean_is_exclusive(v___x_5367_);
if (v_isSharedCheck_5374_ == 0)
{
lean_object* v_unused_5375_; 
v_unused_5375_ = lean_ctor_get(v___x_5367_, 0);
lean_dec(v_unused_5375_);
v___x_5369_ = v___x_5367_;
v_isShared_5370_ = v_isSharedCheck_5374_;
goto v_resetjp_5368_;
}
else
{
lean_dec(v___x_5367_);
v___x_5369_ = lean_box(0);
v_isShared_5370_ = v_isSharedCheck_5374_;
goto v_resetjp_5368_;
}
v_resetjp_5368_:
{
lean_object* v___x_5372_; 
if (v_isShared_5370_ == 0)
{
lean_ctor_set_tag(v___x_5369_, 1);
lean_ctor_set(v___x_5369_, 0, v_a_5365_);
v___x_5372_ = v___x_5369_;
goto v_reusejp_5371_;
}
else
{
lean_object* v_reuseFailAlloc_5373_; 
v_reuseFailAlloc_5373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5373_, 0, v_a_5365_);
v___x_5372_ = v_reuseFailAlloc_5373_;
goto v_reusejp_5371_;
}
v_reusejp_5371_:
{
return v___x_5372_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___boxed(lean_object* v_x_5379_, lean_object* v_isExporting_5380_, lean_object* v___y_5381_, lean_object* v___y_5382_, lean_object* v___y_5383_){
_start:
{
uint8_t v_isExporting_boxed_5384_; lean_object* v_res_5385_; 
v_isExporting_boxed_5384_ = lean_unbox(v_isExporting_5380_);
v_res_5385_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg(v_x_5379_, v_isExporting_boxed_5384_, v___y_5381_, v___y_5382_);
lean_dec(v___y_5382_);
lean_dec_ref(v___y_5381_);
return v_res_5385_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg(lean_object* v_x_5386_, uint8_t v_when_5387_, lean_object* v___y_5388_, lean_object* v___y_5389_){
_start:
{
if (v_when_5387_ == 0)
{
lean_object* v___x_5391_; 
lean_inc(v___y_5389_);
lean_inc_ref(v___y_5388_);
v___x_5391_ = lean_apply_3(v_x_5386_, v___y_5388_, v___y_5389_, lean_box(0));
return v___x_5391_;
}
else
{
uint8_t v___x_5392_; lean_object* v___x_5393_; 
v___x_5392_ = 0;
v___x_5393_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg(v_x_5386_, v___x_5392_, v___y_5388_, v___y_5389_);
return v___x_5393_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg___boxed(lean_object* v_x_5394_, lean_object* v_when_5395_, lean_object* v___y_5396_, lean_object* v___y_5397_, lean_object* v___y_5398_){
_start:
{
uint8_t v_when_boxed_5399_; lean_object* v_res_5400_; 
v_when_boxed_5399_ = lean_unbox(v_when_5395_);
v_res_5400_ = l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg(v_x_5394_, v_when_boxed_5399_, v___y_5396_, v___y_5397_);
lean_dec(v___y_5397_);
lean_dec_ref(v___y_5396_);
return v_res_5400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf(lean_object* v_fnNames_5401_, lean_object* v_numSectionVars_5402_, lean_object* v_e_5403_, lean_object* v_a_5404_, lean_object* v_a_5405_){
_start:
{
lean_object* v___f_5407_; lean_object* v___f_5408_; uint8_t v___x_5409_; lean_object* v___x_5410_; 
v___f_5407_ = ((lean_object*)(l_Lean_Core_betaReduce___closed__1));
v___f_5408_ = lean_alloc_closure((void*)(l_Lean_Meta_unfoldIfArgIsAppOf___lam__0___boxed), 7, 4);
lean_closure_set(v___f_5408_, 0, v_fnNames_5401_);
lean_closure_set(v___f_5408_, 1, v_numSectionVars_5402_);
lean_closure_set(v___f_5408_, 2, v_e_5403_);
lean_closure_set(v___f_5408_, 3, v___f_5407_);
v___x_5409_ = 1;
v___x_5410_ = l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg(v___f_5408_, v___x_5409_, v_a_5404_, v_a_5405_);
return v___x_5410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___boxed(lean_object* v_fnNames_5411_, lean_object* v_numSectionVars_5412_, lean_object* v_e_5413_, lean_object* v_a_5414_, lean_object* v_a_5415_, lean_object* v_a_5416_){
_start:
{
lean_object* v_res_5417_; 
v_res_5417_ = l_Lean_Meta_unfoldIfArgIsAppOf(v_fnNames_5411_, v_numSectionVars_5412_, v_e_5413_, v_a_5414_, v_a_5415_);
lean_dec(v_a_5415_);
lean_dec_ref(v_a_5414_);
return v_res_5417_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2(lean_object* v_00_u03b1_5418_, lean_object* v_x_5419_, uint8_t v_isExporting_5420_, lean_object* v___y_5421_, lean_object* v___y_5422_){
_start:
{
lean_object* v___x_5424_; 
v___x_5424_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg(v_x_5419_, v_isExporting_5420_, v___y_5421_, v___y_5422_);
return v___x_5424_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___boxed(lean_object* v_00_u03b1_5425_, lean_object* v_x_5426_, lean_object* v_isExporting_5427_, lean_object* v___y_5428_, lean_object* v___y_5429_, lean_object* v___y_5430_){
_start:
{
uint8_t v_isExporting_boxed_5431_; lean_object* v_res_5432_; 
v_isExporting_boxed_5431_ = lean_unbox(v_isExporting_5427_);
v_res_5432_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2(v_00_u03b1_5425_, v_x_5426_, v_isExporting_boxed_5431_, v___y_5428_, v___y_5429_);
lean_dec(v___y_5429_);
lean_dec_ref(v___y_5428_);
return v_res_5432_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2(lean_object* v_00_u03b1_5433_, lean_object* v_x_5434_, uint8_t v_when_5435_, lean_object* v___y_5436_, lean_object* v___y_5437_){
_start:
{
lean_object* v___x_5439_; 
v___x_5439_ = l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg(v_x_5434_, v_when_5435_, v___y_5436_, v___y_5437_);
return v___x_5439_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___boxed(lean_object* v_00_u03b1_5440_, lean_object* v_x_5441_, lean_object* v_when_5442_, lean_object* v___y_5443_, lean_object* v___y_5444_, lean_object* v___y_5445_){
_start:
{
uint8_t v_when_boxed_5446_; lean_object* v_res_5447_; 
v_when_boxed_5446_ = lean_unbox(v_when_5442_);
v_res_5447_ = l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2(v_00_u03b1_5440_, v_x_5441_, v_when_boxed_5446_, v___y_5443_, v___y_5444_);
lean_dec(v___y_5444_);
lean_dec_ref(v___y_5443_);
return v_res_5447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___lam__0(lean_object* v_x_5448_, lean_object* v___y_5449_, lean_object* v___y_5450_){
_start:
{
lean_object* v___x_5452_; lean_object* v___x_5453_; 
v___x_5452_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_5453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5453_, 0, v___x_5452_);
return v___x_5453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___lam__0___boxed(lean_object* v_x_5454_, lean_object* v___y_5455_, lean_object* v___y_5456_, lean_object* v___y_5457_){
_start:
{
lean_object* v_res_5458_; 
v_res_5458_ = l_Lean_Meta_eraseInaccessibleAnnotations___lam__0(v_x_5454_, v___y_5455_, v___y_5456_);
lean_dec(v___y_5456_);
lean_dec_ref(v___y_5455_);
lean_dec_ref(v_x_5454_);
return v_res_5458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___lam__1(lean_object* v_e_5459_, lean_object* v___y_5460_, lean_object* v___y_5461_){
_start:
{
lean_object* v___y_5464_; lean_object* v___x_5467_; 
v___x_5467_ = l_Lean_inaccessible_x3f(v_e_5459_);
if (lean_obj_tag(v___x_5467_) == 1)
{
lean_object* v_val_5468_; 
lean_dec_ref(v_e_5459_);
v_val_5468_ = lean_ctor_get(v___x_5467_, 0);
lean_inc(v_val_5468_);
lean_dec_ref(v___x_5467_);
v___y_5464_ = v_val_5468_;
goto v___jp_5463_;
}
else
{
lean_dec(v___x_5467_);
v___y_5464_ = v_e_5459_;
goto v___jp_5463_;
}
v___jp_5463_:
{
lean_object* v___x_5465_; lean_object* v___x_5466_; 
v___x_5465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5465_, 0, v___y_5464_);
v___x_5466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5466_, 0, v___x_5465_);
return v___x_5466_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___lam__1___boxed(lean_object* v_e_5469_, lean_object* v___y_5470_, lean_object* v___y_5471_, lean_object* v___y_5472_){
_start:
{
lean_object* v_res_5473_; 
v_res_5473_ = l_Lean_Meta_eraseInaccessibleAnnotations___lam__1(v_e_5469_, v___y_5470_, v___y_5471_);
lean_dec(v___y_5471_);
lean_dec_ref(v___y_5470_);
return v_res_5473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations(lean_object* v_e_5476_, lean_object* v_a_5477_, lean_object* v_a_5478_){
_start:
{
lean_object* v___f_5480_; lean_object* v___f_5481_; lean_object* v___x_5482_; 
v___f_5480_ = ((lean_object*)(l_Lean_Meta_eraseInaccessibleAnnotations___closed__0));
v___f_5481_ = ((lean_object*)(l_Lean_Meta_eraseInaccessibleAnnotations___closed__1));
v___x_5482_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_5476_, v___f_5480_, v___f_5481_, v_a_5477_, v_a_5478_);
return v___x_5482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___boxed(lean_object* v_e_5483_, lean_object* v_a_5484_, lean_object* v_a_5485_, lean_object* v_a_5486_){
_start:
{
lean_object* v_res_5487_; 
v_res_5487_ = l_Lean_Meta_eraseInaccessibleAnnotations(v_e_5483_, v_a_5484_, v_a_5485_);
lean_dec(v_a_5485_);
lean_dec_ref(v_a_5484_);
return v_res_5487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_erasePatternRefAnnotations___lam__1(lean_object* v_e_5488_, lean_object* v___y_5489_, lean_object* v___y_5490_){
_start:
{
lean_object* v___y_5493_; lean_object* v___x_5496_; 
v___x_5496_ = l_Lean_patternWithRef_x3f(v_e_5488_);
if (lean_obj_tag(v___x_5496_) == 1)
{
lean_object* v_val_5497_; lean_object* v_snd_5498_; 
lean_dec_ref(v_e_5488_);
v_val_5497_ = lean_ctor_get(v___x_5496_, 0);
lean_inc(v_val_5497_);
lean_dec_ref(v___x_5496_);
v_snd_5498_ = lean_ctor_get(v_val_5497_, 1);
lean_inc(v_snd_5498_);
lean_dec(v_val_5497_);
v___y_5493_ = v_snd_5498_;
goto v___jp_5492_;
}
else
{
lean_dec(v___x_5496_);
v___y_5493_ = v_e_5488_;
goto v___jp_5492_;
}
v___jp_5492_:
{
lean_object* v___x_5494_; lean_object* v___x_5495_; 
v___x_5494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5494_, 0, v___y_5493_);
v___x_5495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5495_, 0, v___x_5494_);
return v___x_5495_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_erasePatternRefAnnotations___lam__1___boxed(lean_object* v_e_5499_, lean_object* v___y_5500_, lean_object* v___y_5501_, lean_object* v___y_5502_){
_start:
{
lean_object* v_res_5503_; 
v_res_5503_ = l_Lean_Meta_erasePatternRefAnnotations___lam__1(v_e_5499_, v___y_5500_, v___y_5501_);
lean_dec(v___y_5501_);
lean_dec_ref(v___y_5500_);
return v_res_5503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_erasePatternRefAnnotations(lean_object* v_e_5505_, lean_object* v_a_5506_, lean_object* v_a_5507_){
_start:
{
lean_object* v___f_5509_; lean_object* v___f_5510_; lean_object* v___x_5511_; 
v___f_5509_ = ((lean_object*)(l_Lean_Meta_eraseInaccessibleAnnotations___closed__0));
v___f_5510_ = ((lean_object*)(l_Lean_Meta_erasePatternRefAnnotations___closed__0));
v___x_5511_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_5505_, v___f_5509_, v___f_5510_, v_a_5506_, v_a_5507_);
return v___x_5511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_erasePatternRefAnnotations___boxed(lean_object* v_e_5512_, lean_object* v_a_5513_, lean_object* v_a_5514_, lean_object* v_a_5515_){
_start:
{
lean_object* v_res_5516_; 
v_res_5516_ = l_Lean_Meta_erasePatternRefAnnotations(v_e_5512_, v_a_5513_, v_a_5514_);
lean_dec(v_a_5514_);
lean_dec_ref(v_a_5513_);
return v_res_5516_;
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
