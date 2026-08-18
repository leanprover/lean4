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
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
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
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_ExprStructEq_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_ExprStructEq_hash___boxed(lean_object*);
lean_object* l_Lean_MonadCacheT_instMonad___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadCacheT_instMonadControl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadControlTOfMonadControl___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadControlTOfMonadControl___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Environment_header(lean_object*);
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
static lean_once_cell_t l_Lean_Core_transform___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Core_transform___redArg___closed__3;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__7_spec__12_spec__13___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__7_spec__12_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__7_spec__12___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__7_spec__12___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__7___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__7___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__7___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__7_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__7_spec__12___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__7_spec__12_spec__13(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__7_spec__12_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*);
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
lean_dec_ref_known(v_t_7_, 1);
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
lean_dec_ref_known(v_x_65_, 1);
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
lean_dec_ref_known(v_x_99_, 1);
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
lean_dec_ref_known(v_x_99_, 1);
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
lean_dec_ref_known(v_x_99_, 1);
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
lean_object* v___x_161_; lean_object* v___y_163_; lean_object* v_i_164_; lean_object* v___y_171_; lean_object* v___y_183_; lean_object* v_i_184_; lean_object* v___x_202_; 
v___x_161_ = lean_box(0);
lean_inc_ref(v_e_158_);
lean_inc_ref(v___x_157_);
lean_inc_ref(v___x_156_);
v___x_202_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___x_156_, v___x_157_, v_s_160_, v_e_158_);
switch(lean_obj_tag(v___x_202_))
{
case 0:
{
lean_object* v_index_203_; lean_object* v_size_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
lean_dec_ref(v___x_157_);
lean_dec_ref(v___x_156_);
v_index_203_ = lean_ctor_get(v___x_202_, 0);
lean_inc(v_index_203_);
lean_dec_ref_known(v___x_202_, 3);
v_size_204_ = lean_ctor_get(v_s_160_, 0);
lean_inc(v_size_204_);
v___x_205_ = l_Std_DHashMap_Raw_setEntry___redArg(v_s_160_, v_size_204_, v_index_203_, v_e_158_, v_a_159_);
lean_dec(v_index_203_);
v___x_206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_206_, 0, v___x_161_);
lean_ctor_set(v___x_206_, 1, v___x_205_);
return v___x_206_;
}
case 1:
{
lean_object* v_index_207_; lean_object* v_size_208_; lean_object* v_keyArray_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; uint8_t v___x_213_; 
v_index_207_ = lean_ctor_get(v___x_202_, 0);
lean_inc(v_index_207_);
lean_dec_ref_known(v___x_202_, 1);
v_size_208_ = lean_ctor_get(v_s_160_, 0);
v_keyArray_209_ = lean_ctor_get(v_s_160_, 1);
v___x_210_ = lean_unsigned_to_nat(1u);
v___x_211_ = lean_nat_add(v_size_208_, v___x_210_);
v___x_212_ = lean_array_get_size(v_keyArray_209_);
v___x_213_ = lean_nat_dec_lt(v___x_211_, v___x_212_);
if (v___x_213_ == 0)
{
lean_dec(v___x_211_);
lean_dec(v_index_207_);
goto v___jp_190_;
}
else
{
lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; uint8_t v___x_218_; 
v___x_214_ = lean_unsigned_to_nat(4u);
v___x_215_ = lean_nat_mul(v___x_211_, v___x_214_);
v___x_216_ = lean_unsigned_to_nat(3u);
v___x_217_ = lean_nat_mul(v___x_212_, v___x_216_);
v___x_218_ = lean_nat_dec_le(v___x_215_, v___x_217_);
lean_dec(v___x_217_);
lean_dec(v___x_215_);
if (v___x_218_ == 0)
{
lean_dec(v___x_211_);
lean_dec(v_index_207_);
goto v___jp_190_;
}
else
{
lean_object* v___x_219_; lean_object* v___x_220_; 
lean_dec_ref(v___x_157_);
lean_dec_ref(v___x_156_);
v___x_219_ = l_Std_DHashMap_Raw_setEntry___redArg(v_s_160_, v___x_211_, v_index_207_, v_e_158_, v_a_159_);
lean_dec(v_index_207_);
v___x_220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_220_, 0, v___x_161_);
lean_ctor_set(v___x_220_, 1, v___x_219_);
return v___x_220_;
}
}
}
default: 
{
lean_object* v_size_221_; lean_object* v_keyArray_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; uint8_t v___x_226_; 
v_size_221_ = lean_ctor_get(v_s_160_, 0);
v_keyArray_222_ = lean_ctor_get(v_s_160_, 1);
v___x_223_ = lean_unsigned_to_nat(1u);
v___x_224_ = lean_nat_add(v_size_221_, v___x_223_);
v___x_225_ = lean_array_get_size(v_keyArray_222_);
v___x_226_ = lean_nat_dec_lt(v___x_224_, v___x_225_);
if (v___x_226_ == 0)
{
lean_object* v___x_227_; 
lean_dec(v___x_224_);
lean_inc_ref(v___x_157_);
lean_inc_ref(v___x_156_);
v___x_227_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___x_156_, v___x_157_, v_s_160_);
v___y_171_ = v___x_227_;
goto v___jp_170_;
}
else
{
lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; uint8_t v___x_232_; 
v___x_228_ = lean_unsigned_to_nat(4u);
v___x_229_ = lean_nat_mul(v___x_224_, v___x_228_);
lean_dec(v___x_224_);
v___x_230_ = lean_unsigned_to_nat(3u);
v___x_231_ = lean_nat_mul(v___x_225_, v___x_230_);
v___x_232_ = lean_nat_dec_le(v___x_229_, v___x_231_);
lean_dec(v___x_231_);
lean_dec(v___x_229_);
if (v___x_232_ == 0)
{
lean_object* v___x_233_; 
lean_inc_ref(v___x_157_);
lean_inc_ref(v___x_156_);
v___x_233_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___x_156_, v___x_157_, v_s_160_);
v___y_171_ = v___x_233_;
goto v___jp_170_;
}
else
{
v___y_171_ = v_s_160_;
goto v___jp_170_;
}
}
}
}
v___jp_162_:
{
lean_object* v_size_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v_size_165_ = lean_ctor_get(v___y_163_, 0);
v___x_166_ = lean_unsigned_to_nat(1u);
v___x_167_ = lean_nat_add(v_size_165_, v___x_166_);
v___x_168_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_163_, v___x_167_, v_i_164_, v_e_158_, v_a_159_);
lean_dec(v_i_164_);
v___x_169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_169_, 0, v___x_161_);
lean_ctor_set(v___x_169_, 1, v___x_168_);
return v___x_169_;
}
v___jp_170_:
{
lean_object* v___x_172_; 
lean_inc_ref(v_e_158_);
v___x_172_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___x_156_, v___x_157_, v___y_171_, v_e_158_);
switch(lean_obj_tag(v___x_172_))
{
case 0:
{
lean_object* v_index_173_; lean_object* v_size_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v_index_173_ = lean_ctor_get(v___x_172_, 0);
lean_inc(v_index_173_);
lean_dec_ref_known(v___x_172_, 3);
v_size_174_ = lean_ctor_get(v___y_171_, 0);
lean_inc(v_size_174_);
v___x_175_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_171_, v_size_174_, v_index_173_, v_e_158_, v_a_159_);
lean_dec(v_index_173_);
v___x_176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_176_, 0, v___x_161_);
lean_ctor_set(v___x_176_, 1, v___x_175_);
return v___x_176_;
}
case 1:
{
lean_object* v_index_177_; 
v_index_177_ = lean_ctor_get(v___x_172_, 0);
lean_inc(v_index_177_);
lean_dec_ref_known(v___x_172_, 1);
v___y_163_ = v___y_171_;
v_i_164_ = v_index_177_;
goto v___jp_162_;
}
default: 
{
lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_178_ = lean_unsigned_to_nat(0u);
v___x_179_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_171_, v___x_178_);
if (lean_obj_tag(v___x_179_) == 0)
{
lean_object* v_index_180_; 
v_index_180_ = lean_ctor_get(v___x_179_, 0);
lean_inc(v_index_180_);
lean_dec_ref_known(v___x_179_, 1);
v___y_163_ = v___y_171_;
v_i_164_ = v_index_180_;
goto v___jp_162_;
}
else
{
lean_object* v___x_181_; 
lean_dec_ref(v_a_159_);
lean_dec_ref(v_e_158_);
v___x_181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_181_, 0, v___x_161_);
lean_ctor_set(v___x_181_, 1, v___y_171_);
return v___x_181_;
}
}
}
}
v___jp_182_:
{
lean_object* v_size_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
v_size_185_ = lean_ctor_get(v___y_183_, 0);
v___x_186_ = lean_unsigned_to_nat(1u);
v___x_187_ = lean_nat_add(v_size_185_, v___x_186_);
v___x_188_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_183_, v___x_187_, v_i_184_, v_e_158_, v_a_159_);
lean_dec(v_i_184_);
v___x_189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_189_, 0, v___x_161_);
lean_ctor_set(v___x_189_, 1, v___x_188_);
return v___x_189_;
}
v___jp_190_:
{
lean_object* v___x_191_; lean_object* v___x_192_; 
lean_inc_ref(v___x_157_);
lean_inc_ref(v___x_156_);
v___x_191_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___x_156_, v___x_157_, v_s_160_);
lean_inc_ref(v_e_158_);
v___x_192_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___x_156_, v___x_157_, v___x_191_, v_e_158_);
switch(lean_obj_tag(v___x_192_))
{
case 0:
{
lean_object* v_index_193_; lean_object* v_size_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v_index_193_ = lean_ctor_get(v___x_192_, 0);
lean_inc(v_index_193_);
lean_dec_ref_known(v___x_192_, 3);
v_size_194_ = lean_ctor_get(v___x_191_, 0);
lean_inc(v_size_194_);
v___x_195_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_191_, v_size_194_, v_index_193_, v_e_158_, v_a_159_);
lean_dec(v_index_193_);
v___x_196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_196_, 0, v___x_161_);
lean_ctor_set(v___x_196_, 1, v___x_195_);
return v___x_196_;
}
case 1:
{
lean_object* v_index_197_; 
v_index_197_ = lean_ctor_get(v___x_192_, 0);
lean_inc(v_index_197_);
lean_dec_ref_known(v___x_192_, 1);
v___y_183_ = v___x_191_;
v_i_184_ = v_index_197_;
goto v___jp_182_;
}
default: 
{
lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_198_ = lean_unsigned_to_nat(0u);
v___x_199_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_191_, v___x_198_);
if (lean_obj_tag(v___x_199_) == 0)
{
lean_object* v_index_200_; 
v_index_200_ = lean_ctor_get(v___x_199_, 0);
lean_inc(v_index_200_);
lean_dec_ref_known(v___x_199_, 1);
v___y_183_ = v___x_191_;
v_i_184_ = v_index_200_;
goto v___jp_182_;
}
else
{
lean_object* v___x_201_; 
lean_dec_ref(v_a_159_);
lean_dec_ref(v_e_158_);
v___x_201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_201_, 0, v___x_161_);
lean_ctor_set(v___x_201_, 1, v___x_191_);
return v___x_201_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__2(lean_object* v_toApplicative_234_, lean_object* v___x_235_, lean_object* v___x_236_, lean_object* v_e_237_, lean_object* v_a_238_, lean_object* v_x_239_, lean_object* v_toBind_240_, lean_object* v_a_241_){
_start:
{
lean_object* v___f_242_; lean_object* v___f_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
lean_inc_ref(v_a_241_);
v___f_242_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__0), 3, 2);
lean_closure_set(v___f_242_, 0, v_toApplicative_234_);
lean_closure_set(v___f_242_, 1, v_a_241_);
v___f_243_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__1), 5, 4);
lean_closure_set(v___f_243_, 0, v___x_235_);
lean_closure_set(v___f_243_, 1, v___x_236_);
lean_closure_set(v___f_243_, 2, v_e_237_);
lean_closure_set(v___f_243_, 3, v_a_241_);
lean_inc(v_a_238_);
v___x_244_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_244_, 0, lean_box(0));
lean_closure_set(v___x_244_, 1, lean_box(0));
lean_closure_set(v___x_244_, 2, lean_box(0));
lean_closure_set(v___x_244_, 3, v_a_238_);
lean_closure_set(v___x_244_, 4, v___f_243_);
v___x_245_ = lean_apply_2(v_x_239_, lean_box(0), v___x_244_);
v___x_246_ = lean_apply_4(v_toBind_240_, lean_box(0), lean_box(0), v___x_245_, v___f_242_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__2___boxed(lean_object* v_toApplicative_247_, lean_object* v___x_248_, lean_object* v___x_249_, lean_object* v_e_250_, lean_object* v_a_251_, lean_object* v_x_252_, lean_object* v_toBind_253_, lean_object* v_a_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__2(v_toApplicative_247_, v___x_248_, v___x_249_, v_e_250_, v_a_251_, v_x_252_, v_toBind_253_, v_a_254_);
lean_dec(v_a_251_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__3(lean_object* v_toApplicative_256_, lean_object* v___x_257_, lean_object* v___x_258_, lean_object* v_e_259_, lean_object* v_a_260_){
_start:
{
lean_object* v_toPure_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v_toPure_261_ = lean_ctor_get(v_toApplicative_256_, 1);
lean_inc(v_toPure_261_);
lean_dec_ref(v_toApplicative_256_);
v___x_262_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___x_257_, v___x_258_, v_a_260_, v_e_259_);
v___x_263_ = lean_apply_2(v_toPure_261_, lean_box(0), v___x_262_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__3___boxed(lean_object* v_toApplicative_264_, lean_object* v___x_265_, lean_object* v___x_266_, lean_object* v_e_267_, lean_object* v_a_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__3(v_toApplicative_264_, v___x_265_, v___x_266_, v_e_267_, v_a_268_);
lean_dec_ref(v_a_268_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__19(lean_object* v_inst_273_, lean_object* v_x_274_, lean_object* v___x_275_, lean_object* v___x_276_, lean_object* v_inst_277_, lean_object* v___f_278_, lean_object* v___x_279_, lean_object* v___x_280_, lean_object* v_a_281_, lean_object* v_toBind_282_, lean_object* v___f_283_, lean_object* v_toApplicative_284_, lean_object* v_a_285_){
_start:
{
if (lean_obj_tag(v_a_285_) == 0)
{
lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_3095__overap_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
lean_dec_ref(v_toApplicative_284_);
v___x_286_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__19___closed__1));
v___x_287_ = lean_apply_2(v_inst_273_, lean_box(0), v___x_286_);
lean_inc_ref(v___x_276_);
lean_inc_ref(v___x_275_);
v___x_288_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonadLift___aux__1___boxed), 10, 9);
lean_closure_set(v___x_288_, 0, lean_box(0));
lean_closure_set(v___x_288_, 1, lean_box(0));
lean_closure_set(v___x_288_, 2, lean_box(0));
lean_closure_set(v___x_288_, 3, lean_box(0));
lean_closure_set(v___x_288_, 4, v_x_274_);
lean_closure_set(v___x_288_, 5, v___x_275_);
lean_closure_set(v___x_288_, 6, v___x_276_);
lean_closure_set(v___x_288_, 7, lean_box(0));
lean_closure_set(v___x_288_, 8, v___x_287_);
v___x_289_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonad___aux__13___boxed), 13, 12);
lean_closure_set(v___x_289_, 0, lean_box(0));
lean_closure_set(v___x_289_, 1, lean_box(0));
lean_closure_set(v___x_289_, 2, lean_box(0));
lean_closure_set(v___x_289_, 3, lean_box(0));
lean_closure_set(v___x_289_, 4, v_x_274_);
lean_closure_set(v___x_289_, 5, v___x_275_);
lean_closure_set(v___x_289_, 6, v___x_276_);
lean_closure_set(v___x_289_, 7, v_inst_277_);
lean_closure_set(v___x_289_, 8, lean_box(0));
lean_closure_set(v___x_289_, 9, lean_box(0));
lean_closure_set(v___x_289_, 10, v___x_288_);
lean_closure_set(v___x_289_, 11, v___f_278_);
v___x_3095__overap_290_ = l_Lean_Core_withIncRecDepth___redArg(v___x_279_, v___x_280_, v___x_289_);
lean_inc(v_a_281_);
v___x_291_ = lean_apply_1(v___x_3095__overap_290_, v_a_281_);
v___x_292_ = lean_apply_4(v_toBind_282_, lean_box(0), lean_box(0), v___x_291_, v___f_283_);
return v___x_292_;
}
else
{
lean_object* v_val_293_; lean_object* v_toPure_294_; lean_object* v___x_295_; 
lean_dec(v___f_283_);
lean_dec(v_toBind_282_);
lean_dec_ref(v___x_280_);
lean_dec_ref(v___x_279_);
lean_dec(v___f_278_);
lean_dec_ref(v_inst_277_);
lean_dec_ref(v___x_276_);
lean_dec_ref(v___x_275_);
lean_dec(v_inst_273_);
v_val_293_ = lean_ctor_get(v_a_285_, 0);
lean_inc(v_val_293_);
lean_dec_ref_known(v_a_285_, 1);
v_toPure_294_ = lean_ctor_get(v_toApplicative_284_, 1);
lean_inc(v_toPure_294_);
lean_dec_ref(v_toApplicative_284_);
v___x_295_ = lean_apply_2(v_toPure_294_, lean_box(0), v_val_293_);
return v___x_295_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__19___boxed(lean_object* v_inst_296_, lean_object* v_x_297_, lean_object* v___x_298_, lean_object* v___x_299_, lean_object* v_inst_300_, lean_object* v___f_301_, lean_object* v___x_302_, lean_object* v___x_303_, lean_object* v_a_304_, lean_object* v_toBind_305_, lean_object* v___f_306_, lean_object* v_toApplicative_307_, lean_object* v_a_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__19(v_inst_296_, v_x_297_, v___x_298_, v___x_299_, v_inst_300_, v___f_301_, v___x_302_, v___x_303_, v_a_304_, v_toBind_305_, v___f_306_, v_toApplicative_307_, v_a_308_);
lean_dec(v_a_304_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__4(lean_object* v_a_312_, lean_object* v_inst_313_, lean_object* v_inst_314_, lean_object* v_inst_315_, lean_object* v_pre_316_, lean_object* v_post_317_, lean_object* v_x_318_, lean_object* v_x_319_, lean_object* v___y_320_, lean_object* v_a_321_){
_start:
{
lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_322_ = l_Lean_mkAppN(v_a_312_, v_a_321_);
v___x_323_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_313_, v_inst_314_, v_inst_315_, v_pre_316_, v_post_317_, v_x_318_, v_x_319_, v___x_322_, v___y_320_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__4___boxed(lean_object* v_a_324_, lean_object* v_inst_325_, lean_object* v_inst_326_, lean_object* v_inst_327_, lean_object* v_pre_328_, lean_object* v_post_329_, lean_object* v_x_330_, lean_object* v_x_331_, lean_object* v___y_332_, lean_object* v_a_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__4(v_a_324_, v_inst_325_, v_inst_326_, v_inst_327_, v_pre_328_, v_post_329_, v_x_330_, v_x_331_, v___y_332_, v_a_333_);
lean_dec_ref(v_a_333_);
lean_dec(v___y_332_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___boxed(lean_object* v_inst_335_, lean_object* v_inst_336_, lean_object* v_inst_337_, lean_object* v_pre_338_, lean_object* v_post_339_, lean_object* v_x_340_, lean_object* v_x_341_, lean_object* v_e_342_, lean_object* v_a_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_335_, v_inst_336_, v_inst_337_, v_pre_338_, v_post_339_, v_x_340_, v_x_341_, v_e_342_, v_a_343_);
lean_dec(v_a_343_);
return v_res_344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__5(lean_object* v_inst_345_, lean_object* v_inst_346_, lean_object* v_inst_347_, lean_object* v_pre_348_, lean_object* v_post_349_, lean_object* v_x_350_, lean_object* v_x_351_, lean_object* v___y_352_, lean_object* v_args_353_, lean_object* v___x_354_, lean_object* v_toBind_355_, lean_object* v_a_356_){
_start:
{
lean_object* v___f_357_; lean_object* v___x_358_; size_t v_sz_359_; size_t v___x_360_; lean_object* v___x_2825__overap_361_; lean_object* v___x_362_; lean_object* v___x_363_; 
lean_inc_n(v___y_352_, 2);
lean_inc(v_x_351_);
lean_inc(v_post_349_);
lean_inc(v_pre_348_);
lean_inc_ref(v_inst_347_);
lean_inc(v_inst_346_);
lean_inc_ref(v_inst_345_);
v___f_357_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__4___boxed), 10, 9);
lean_closure_set(v___f_357_, 0, v_a_356_);
lean_closure_set(v___f_357_, 1, v_inst_345_);
lean_closure_set(v___f_357_, 2, v_inst_346_);
lean_closure_set(v___f_357_, 3, v_inst_347_);
lean_closure_set(v___f_357_, 4, v_pre_348_);
lean_closure_set(v___f_357_, 5, v_post_349_);
lean_closure_set(v___f_357_, 6, v_x_350_);
lean_closure_set(v___f_357_, 7, v_x_351_);
lean_closure_set(v___f_357_, 8, v___y_352_);
v___x_358_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___boxed), 9, 7);
lean_closure_set(v___x_358_, 0, v_inst_345_);
lean_closure_set(v___x_358_, 1, v_inst_346_);
lean_closure_set(v___x_358_, 2, v_inst_347_);
lean_closure_set(v___x_358_, 3, v_pre_348_);
lean_closure_set(v___x_358_, 4, v_post_349_);
lean_closure_set(v___x_358_, 5, v_x_350_);
lean_closure_set(v___x_358_, 6, v_x_351_);
v_sz_359_ = lean_array_size(v_args_353_);
v___x_360_ = ((size_t)0ULL);
v___x_2825__overap_361_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_354_, v___x_358_, v_sz_359_, v___x_360_, v_args_353_);
v___x_362_ = lean_apply_1(v___x_2825__overap_361_, v___y_352_);
v___x_363_ = lean_apply_4(v_toBind_355_, lean_box(0), lean_box(0), v___x_362_, v___f_357_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__5___boxed(lean_object* v_inst_364_, lean_object* v_inst_365_, lean_object* v_inst_366_, lean_object* v_pre_367_, lean_object* v_post_368_, lean_object* v_x_369_, lean_object* v_x_370_, lean_object* v___y_371_, lean_object* v_args_372_, lean_object* v___x_373_, lean_object* v_toBind_374_, lean_object* v_a_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__5(v_inst_364_, v_inst_365_, v_inst_366_, v_pre_367_, v_post_368_, v_x_369_, v_x_370_, v___y_371_, v_args_372_, v___x_373_, v_toBind_374_, v_a_375_);
lean_dec(v___y_371_);
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__6(lean_object* v_inst_377_, lean_object* v_inst_378_, lean_object* v_inst_379_, lean_object* v_pre_380_, lean_object* v_post_381_, lean_object* v_x_382_, lean_object* v_x_383_, lean_object* v___x_384_, lean_object* v_toBind_385_, lean_object* v_f_386_, lean_object* v_args_387_, lean_object* v___y_388_){
_start:
{
lean_object* v___f_389_; lean_object* v___x_390_; lean_object* v___x_391_; 
lean_inc(v_toBind_385_);
lean_inc(v___y_388_);
lean_inc(v_x_383_);
lean_inc(v_post_381_);
lean_inc(v_pre_380_);
lean_inc_ref(v_inst_379_);
lean_inc(v_inst_378_);
lean_inc_ref(v_inst_377_);
v___f_389_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__5___boxed), 12, 11);
lean_closure_set(v___f_389_, 0, v_inst_377_);
lean_closure_set(v___f_389_, 1, v_inst_378_);
lean_closure_set(v___f_389_, 2, v_inst_379_);
lean_closure_set(v___f_389_, 3, v_pre_380_);
lean_closure_set(v___f_389_, 4, v_post_381_);
lean_closure_set(v___f_389_, 5, v_x_382_);
lean_closure_set(v___f_389_, 6, v_x_383_);
lean_closure_set(v___f_389_, 7, v___y_388_);
lean_closure_set(v___f_389_, 8, v_args_387_);
lean_closure_set(v___f_389_, 9, v___x_384_);
lean_closure_set(v___f_389_, 10, v_toBind_385_);
v___x_390_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_377_, v_inst_378_, v_inst_379_, v_pre_380_, v_post_381_, v_x_382_, v_x_383_, v_f_386_, v___y_388_);
v___x_391_ = lean_apply_4(v_toBind_385_, lean_box(0), lean_box(0), v___x_390_, v___f_389_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__6___boxed(lean_object* v_inst_392_, lean_object* v_inst_393_, lean_object* v_inst_394_, lean_object* v_pre_395_, lean_object* v_post_396_, lean_object* v_x_397_, lean_object* v_x_398_, lean_object* v___x_399_, lean_object* v_toBind_400_, lean_object* v_f_401_, lean_object* v_args_402_, lean_object* v___y_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__6(v_inst_392_, v_inst_393_, v_inst_394_, v_pre_395_, v_post_396_, v_x_397_, v_x_398_, v___x_399_, v_toBind_400_, v_f_401_, v_args_402_, v___y_403_);
lean_dec(v___y_403_);
return v_res_404_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__7___boxed(lean_object* v_inst_405_, lean_object* v_inst_406_, lean_object* v_inst_407_, lean_object* v_pre_408_, lean_object* v_post_409_, lean_object* v_x_410_, lean_object* v_x_411_, lean_object* v___y_412_, lean_object* v_a_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__7(v_inst_405_, v_inst_406_, v_inst_407_, v_pre_408_, v_post_409_, v_x_410_, v_x_411_, v___y_412_, v_a_413_);
lean_dec(v___y_412_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__8(lean_object* v_binderName_415_, lean_object* v_a_416_, uint8_t v_binderInfo_417_, lean_object* v_inst_418_, lean_object* v_inst_419_, lean_object* v_inst_420_, lean_object* v_pre_421_, lean_object* v_post_422_, lean_object* v_x_423_, lean_object* v_x_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v_binderType_427_, lean_object* v_body_428_, lean_object* v_a_429_){
_start:
{
uint8_t v___y_431_; size_t v___x_438_; size_t v___x_439_; uint8_t v___x_440_; 
v___x_438_ = lean_ptr_addr(v_binderType_427_);
v___x_439_ = lean_ptr_addr(v_a_416_);
v___x_440_ = lean_usize_dec_eq(v___x_438_, v___x_439_);
if (v___x_440_ == 0)
{
v___y_431_ = v___x_440_;
goto v___jp_430_;
}
else
{
size_t v___x_441_; size_t v___x_442_; uint8_t v___x_443_; 
v___x_441_ = lean_ptr_addr(v_body_428_);
v___x_442_ = lean_ptr_addr(v_a_429_);
v___x_443_ = lean_usize_dec_eq(v___x_441_, v___x_442_);
v___y_431_ = v___x_443_;
goto v___jp_430_;
}
v___jp_430_:
{
if (v___y_431_ == 0)
{
lean_object* v___x_432_; lean_object* v___x_433_; 
lean_dec_ref(v___y_426_);
v___x_432_ = l_Lean_Expr_forallE___override(v_binderName_415_, v_a_416_, v_a_429_, v_binderInfo_417_);
v___x_433_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_418_, v_inst_419_, v_inst_420_, v_pre_421_, v_post_422_, v_x_423_, v_x_424_, v___x_432_, v___y_425_);
return v___x_433_;
}
else
{
uint8_t v___x_434_; 
v___x_434_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_417_, v_binderInfo_417_);
if (v___x_434_ == 0)
{
lean_object* v___x_435_; lean_object* v___x_436_; 
lean_dec_ref(v___y_426_);
v___x_435_ = l_Lean_Expr_forallE___override(v_binderName_415_, v_a_416_, v_a_429_, v_binderInfo_417_);
v___x_436_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_418_, v_inst_419_, v_inst_420_, v_pre_421_, v_post_422_, v_x_423_, v_x_424_, v___x_435_, v___y_425_);
return v___x_436_;
}
else
{
lean_object* v___x_437_; 
lean_dec_ref(v_a_429_);
lean_dec_ref(v_a_416_);
lean_dec(v_binderName_415_);
v___x_437_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_418_, v_inst_419_, v_inst_420_, v_pre_421_, v_post_422_, v_x_423_, v_x_424_, v___y_426_, v___y_425_);
return v___x_437_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__8___boxed(lean_object* v_binderName_444_, lean_object* v_a_445_, lean_object* v_binderInfo_446_, lean_object* v_inst_447_, lean_object* v_inst_448_, lean_object* v_inst_449_, lean_object* v_pre_450_, lean_object* v_post_451_, lean_object* v_x_452_, lean_object* v_x_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v_binderType_456_, lean_object* v_body_457_, lean_object* v_a_458_){
_start:
{
uint8_t v_binderInfo_3536__boxed_459_; lean_object* v_res_460_; 
v_binderInfo_3536__boxed_459_ = lean_unbox(v_binderInfo_446_);
v_res_460_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__8(v_binderName_444_, v_a_445_, v_binderInfo_3536__boxed_459_, v_inst_447_, v_inst_448_, v_inst_449_, v_pre_450_, v_post_451_, v_x_452_, v_x_453_, v___y_454_, v___y_455_, v_binderType_456_, v_body_457_, v_a_458_);
lean_dec_ref(v_body_457_);
lean_dec_ref(v_binderType_456_);
lean_dec(v___y_454_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__9(lean_object* v_binderName_461_, uint8_t v_binderInfo_462_, lean_object* v_inst_463_, lean_object* v_inst_464_, lean_object* v_inst_465_, lean_object* v_pre_466_, lean_object* v_post_467_, lean_object* v_x_468_, lean_object* v_x_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v_binderType_472_, lean_object* v_body_473_, lean_object* v_toBind_474_, lean_object* v_a_475_){
_start:
{
lean_object* v___x_476_; lean_object* v___f_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_476_ = lean_box(v_binderInfo_462_);
lean_inc_ref(v_body_473_);
lean_inc(v___y_470_);
lean_inc(v_x_469_);
lean_inc(v_post_467_);
lean_inc(v_pre_466_);
lean_inc_ref(v_inst_465_);
lean_inc(v_inst_464_);
lean_inc_ref(v_inst_463_);
v___f_477_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__8___boxed), 15, 14);
lean_closure_set(v___f_477_, 0, v_binderName_461_);
lean_closure_set(v___f_477_, 1, v_a_475_);
lean_closure_set(v___f_477_, 2, v___x_476_);
lean_closure_set(v___f_477_, 3, v_inst_463_);
lean_closure_set(v___f_477_, 4, v_inst_464_);
lean_closure_set(v___f_477_, 5, v_inst_465_);
lean_closure_set(v___f_477_, 6, v_pre_466_);
lean_closure_set(v___f_477_, 7, v_post_467_);
lean_closure_set(v___f_477_, 8, v_x_468_);
lean_closure_set(v___f_477_, 9, v_x_469_);
lean_closure_set(v___f_477_, 10, v___y_470_);
lean_closure_set(v___f_477_, 11, v___y_471_);
lean_closure_set(v___f_477_, 12, v_binderType_472_);
lean_closure_set(v___f_477_, 13, v_body_473_);
v___x_478_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_463_, v_inst_464_, v_inst_465_, v_pre_466_, v_post_467_, v_x_468_, v_x_469_, v_body_473_, v___y_470_);
v___x_479_ = lean_apply_4(v_toBind_474_, lean_box(0), lean_box(0), v___x_478_, v___f_477_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__9___boxed(lean_object* v_binderName_480_, lean_object* v_binderInfo_481_, lean_object* v_inst_482_, lean_object* v_inst_483_, lean_object* v_inst_484_, lean_object* v_pre_485_, lean_object* v_post_486_, lean_object* v_x_487_, lean_object* v_x_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v_binderType_491_, lean_object* v_body_492_, lean_object* v_toBind_493_, lean_object* v_a_494_){
_start:
{
uint8_t v_binderInfo_3397__boxed_495_; lean_object* v_res_496_; 
v_binderInfo_3397__boxed_495_ = lean_unbox(v_binderInfo_481_);
v_res_496_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__9(v_binderName_480_, v_binderInfo_3397__boxed_495_, v_inst_482_, v_inst_483_, v_inst_484_, v_pre_485_, v_post_486_, v_x_487_, v_x_488_, v___y_489_, v___y_490_, v_binderType_491_, v_body_492_, v_toBind_493_, v_a_494_);
lean_dec(v___y_489_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__10(lean_object* v_binderName_497_, lean_object* v_a_498_, uint8_t v_binderInfo_499_, lean_object* v_inst_500_, lean_object* v_inst_501_, lean_object* v_inst_502_, lean_object* v_pre_503_, lean_object* v_post_504_, lean_object* v_x_505_, lean_object* v_x_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v_binderType_509_, lean_object* v_body_510_, lean_object* v_a_511_){
_start:
{
uint8_t v___y_513_; size_t v___x_520_; size_t v___x_521_; uint8_t v___x_522_; 
v___x_520_ = lean_ptr_addr(v_binderType_509_);
v___x_521_ = lean_ptr_addr(v_a_498_);
v___x_522_ = lean_usize_dec_eq(v___x_520_, v___x_521_);
if (v___x_522_ == 0)
{
v___y_513_ = v___x_522_;
goto v___jp_512_;
}
else
{
size_t v___x_523_; size_t v___x_524_; uint8_t v___x_525_; 
v___x_523_ = lean_ptr_addr(v_body_510_);
v___x_524_ = lean_ptr_addr(v_a_511_);
v___x_525_ = lean_usize_dec_eq(v___x_523_, v___x_524_);
v___y_513_ = v___x_525_;
goto v___jp_512_;
}
v___jp_512_:
{
if (v___y_513_ == 0)
{
lean_object* v___x_514_; lean_object* v___x_515_; 
lean_dec_ref(v___y_508_);
v___x_514_ = l_Lean_Expr_lam___override(v_binderName_497_, v_a_498_, v_a_511_, v_binderInfo_499_);
v___x_515_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_500_, v_inst_501_, v_inst_502_, v_pre_503_, v_post_504_, v_x_505_, v_x_506_, v___x_514_, v___y_507_);
return v___x_515_;
}
else
{
uint8_t v___x_516_; 
v___x_516_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_499_, v_binderInfo_499_);
if (v___x_516_ == 0)
{
lean_object* v___x_517_; lean_object* v___x_518_; 
lean_dec_ref(v___y_508_);
v___x_517_ = l_Lean_Expr_lam___override(v_binderName_497_, v_a_498_, v_a_511_, v_binderInfo_499_);
v___x_518_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_500_, v_inst_501_, v_inst_502_, v_pre_503_, v_post_504_, v_x_505_, v_x_506_, v___x_517_, v___y_507_);
return v___x_518_;
}
else
{
lean_object* v___x_519_; 
lean_dec_ref(v_a_511_);
lean_dec_ref(v_a_498_);
lean_dec(v_binderName_497_);
v___x_519_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_500_, v_inst_501_, v_inst_502_, v_pre_503_, v_post_504_, v_x_505_, v_x_506_, v___y_508_, v___y_507_);
return v___x_519_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__10___boxed(lean_object* v_binderName_526_, lean_object* v_a_527_, lean_object* v_binderInfo_528_, lean_object* v_inst_529_, lean_object* v_inst_530_, lean_object* v_inst_531_, lean_object* v_pre_532_, lean_object* v_post_533_, lean_object* v_x_534_, lean_object* v_x_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v_binderType_538_, lean_object* v_body_539_, lean_object* v_a_540_){
_start:
{
uint8_t v_binderInfo_3511__boxed_541_; lean_object* v_res_542_; 
v_binderInfo_3511__boxed_541_ = lean_unbox(v_binderInfo_528_);
v_res_542_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__10(v_binderName_526_, v_a_527_, v_binderInfo_3511__boxed_541_, v_inst_529_, v_inst_530_, v_inst_531_, v_pre_532_, v_post_533_, v_x_534_, v_x_535_, v___y_536_, v___y_537_, v_binderType_538_, v_body_539_, v_a_540_);
lean_dec_ref(v_body_539_);
lean_dec_ref(v_binderType_538_);
lean_dec(v___y_536_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__11(lean_object* v_binderName_543_, uint8_t v_binderInfo_544_, lean_object* v_inst_545_, lean_object* v_inst_546_, lean_object* v_inst_547_, lean_object* v_pre_548_, lean_object* v_post_549_, lean_object* v_x_550_, lean_object* v_x_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v_binderType_554_, lean_object* v_body_555_, lean_object* v_toBind_556_, lean_object* v_a_557_){
_start:
{
lean_object* v___x_558_; lean_object* v___f_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_558_ = lean_box(v_binderInfo_544_);
lean_inc_ref(v_body_555_);
lean_inc(v___y_552_);
lean_inc(v_x_551_);
lean_inc(v_post_549_);
lean_inc(v_pre_548_);
lean_inc_ref(v_inst_547_);
lean_inc(v_inst_546_);
lean_inc_ref(v_inst_545_);
v___f_559_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__10___boxed), 15, 14);
lean_closure_set(v___f_559_, 0, v_binderName_543_);
lean_closure_set(v___f_559_, 1, v_a_557_);
lean_closure_set(v___f_559_, 2, v___x_558_);
lean_closure_set(v___f_559_, 3, v_inst_545_);
lean_closure_set(v___f_559_, 4, v_inst_546_);
lean_closure_set(v___f_559_, 5, v_inst_547_);
lean_closure_set(v___f_559_, 6, v_pre_548_);
lean_closure_set(v___f_559_, 7, v_post_549_);
lean_closure_set(v___f_559_, 8, v_x_550_);
lean_closure_set(v___f_559_, 9, v_x_551_);
lean_closure_set(v___f_559_, 10, v___y_552_);
lean_closure_set(v___f_559_, 11, v___y_553_);
lean_closure_set(v___f_559_, 12, v_binderType_554_);
lean_closure_set(v___f_559_, 13, v_body_555_);
v___x_560_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_545_, v_inst_546_, v_inst_547_, v_pre_548_, v_post_549_, v_x_550_, v_x_551_, v_body_555_, v___y_552_);
v___x_561_ = lean_apply_4(v_toBind_556_, lean_box(0), lean_box(0), v___x_560_, v___f_559_);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__11___boxed(lean_object* v_binderName_562_, lean_object* v_binderInfo_563_, lean_object* v_inst_564_, lean_object* v_inst_565_, lean_object* v_inst_566_, lean_object* v_pre_567_, lean_object* v_post_568_, lean_object* v_x_569_, lean_object* v_x_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v_binderType_573_, lean_object* v_body_574_, lean_object* v_toBind_575_, lean_object* v_a_576_){
_start:
{
uint8_t v_binderInfo_3343__boxed_577_; lean_object* v_res_578_; 
v_binderInfo_3343__boxed_577_ = lean_unbox(v_binderInfo_563_);
v_res_578_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__11(v_binderName_562_, v_binderInfo_3343__boxed_577_, v_inst_564_, v_inst_565_, v_inst_566_, v_pre_567_, v_post_568_, v_x_569_, v_x_570_, v___y_571_, v___y_572_, v_binderType_573_, v_body_574_, v_toBind_575_, v_a_576_);
lean_dec(v___y_571_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__12(lean_object* v_declName_579_, lean_object* v_a_580_, lean_object* v_a_581_, uint8_t v_nondep_582_, lean_object* v_inst_583_, lean_object* v_inst_584_, lean_object* v_inst_585_, lean_object* v_pre_586_, lean_object* v_post_587_, lean_object* v_x_588_, lean_object* v_x_589_, lean_object* v___y_590_, lean_object* v_body_591_, lean_object* v___y_592_, lean_object* v_type_593_, lean_object* v_value_594_, lean_object* v_a_595_){
_start:
{
uint8_t v___y_597_; size_t v___x_606_; size_t v___x_607_; uint8_t v___x_608_; 
v___x_606_ = lean_ptr_addr(v_type_593_);
v___x_607_ = lean_ptr_addr(v_a_580_);
v___x_608_ = lean_usize_dec_eq(v___x_606_, v___x_607_);
if (v___x_608_ == 0)
{
v___y_597_ = v___x_608_;
goto v___jp_596_;
}
else
{
size_t v___x_609_; size_t v___x_610_; uint8_t v___x_611_; 
v___x_609_ = lean_ptr_addr(v_value_594_);
v___x_610_ = lean_ptr_addr(v_a_581_);
v___x_611_ = lean_usize_dec_eq(v___x_609_, v___x_610_);
v___y_597_ = v___x_611_;
goto v___jp_596_;
}
v___jp_596_:
{
if (v___y_597_ == 0)
{
lean_object* v___x_598_; lean_object* v___x_599_; 
lean_dec_ref(v___y_592_);
v___x_598_ = l_Lean_Expr_letE___override(v_declName_579_, v_a_580_, v_a_581_, v_a_595_, v_nondep_582_);
v___x_599_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_583_, v_inst_584_, v_inst_585_, v_pre_586_, v_post_587_, v_x_588_, v_x_589_, v___x_598_, v___y_590_);
return v___x_599_;
}
else
{
size_t v___x_600_; size_t v___x_601_; uint8_t v___x_602_; 
v___x_600_ = lean_ptr_addr(v_body_591_);
v___x_601_ = lean_ptr_addr(v_a_595_);
v___x_602_ = lean_usize_dec_eq(v___x_600_, v___x_601_);
if (v___x_602_ == 0)
{
lean_object* v___x_603_; lean_object* v___x_604_; 
lean_dec_ref(v___y_592_);
v___x_603_ = l_Lean_Expr_letE___override(v_declName_579_, v_a_580_, v_a_581_, v_a_595_, v_nondep_582_);
v___x_604_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_583_, v_inst_584_, v_inst_585_, v_pre_586_, v_post_587_, v_x_588_, v_x_589_, v___x_603_, v___y_590_);
return v___x_604_;
}
else
{
lean_object* v___x_605_; 
lean_dec_ref(v_a_595_);
lean_dec_ref(v_a_581_);
lean_dec_ref(v_a_580_);
lean_dec(v_declName_579_);
v___x_605_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_583_, v_inst_584_, v_inst_585_, v_pre_586_, v_post_587_, v_x_588_, v_x_589_, v___y_592_, v___y_590_);
return v___x_605_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__12___boxed(lean_object** _args){
lean_object* v_declName_612_ = _args[0];
lean_object* v_a_613_ = _args[1];
lean_object* v_a_614_ = _args[2];
lean_object* v_nondep_615_ = _args[3];
lean_object* v_inst_616_ = _args[4];
lean_object* v_inst_617_ = _args[5];
lean_object* v_inst_618_ = _args[6];
lean_object* v_pre_619_ = _args[7];
lean_object* v_post_620_ = _args[8];
lean_object* v_x_621_ = _args[9];
lean_object* v_x_622_ = _args[10];
lean_object* v___y_623_ = _args[11];
lean_object* v_body_624_ = _args[12];
lean_object* v___y_625_ = _args[13];
lean_object* v_type_626_ = _args[14];
lean_object* v_value_627_ = _args[15];
lean_object* v_a_628_ = _args[16];
_start:
{
uint8_t v_nondep_3561__boxed_629_; lean_object* v_res_630_; 
v_nondep_3561__boxed_629_ = lean_unbox(v_nondep_615_);
v_res_630_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__12(v_declName_612_, v_a_613_, v_a_614_, v_nondep_3561__boxed_629_, v_inst_616_, v_inst_617_, v_inst_618_, v_pre_619_, v_post_620_, v_x_621_, v_x_622_, v___y_623_, v_body_624_, v___y_625_, v_type_626_, v_value_627_, v_a_628_);
lean_dec_ref(v_value_627_);
lean_dec_ref(v_type_626_);
lean_dec_ref(v_body_624_);
lean_dec(v___y_623_);
return v_res_630_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__13(lean_object* v_declName_631_, lean_object* v_a_632_, uint8_t v_nondep_633_, lean_object* v_inst_634_, lean_object* v_inst_635_, lean_object* v_inst_636_, lean_object* v_pre_637_, lean_object* v_post_638_, lean_object* v_x_639_, lean_object* v_x_640_, lean_object* v___y_641_, lean_object* v_body_642_, lean_object* v___y_643_, lean_object* v_type_644_, lean_object* v_value_645_, lean_object* v_toBind_646_, lean_object* v_a_647_){
_start:
{
lean_object* v___x_648_; lean_object* v___f_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_648_ = lean_box(v_nondep_633_);
lean_inc_ref(v_body_642_);
lean_inc(v___y_641_);
lean_inc(v_x_640_);
lean_inc(v_post_638_);
lean_inc(v_pre_637_);
lean_inc_ref(v_inst_636_);
lean_inc(v_inst_635_);
lean_inc_ref(v_inst_634_);
v___f_649_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__12___boxed), 17, 16);
lean_closure_set(v___f_649_, 0, v_declName_631_);
lean_closure_set(v___f_649_, 1, v_a_632_);
lean_closure_set(v___f_649_, 2, v_a_647_);
lean_closure_set(v___f_649_, 3, v___x_648_);
lean_closure_set(v___f_649_, 4, v_inst_634_);
lean_closure_set(v___f_649_, 5, v_inst_635_);
lean_closure_set(v___f_649_, 6, v_inst_636_);
lean_closure_set(v___f_649_, 7, v_pre_637_);
lean_closure_set(v___f_649_, 8, v_post_638_);
lean_closure_set(v___f_649_, 9, v_x_639_);
lean_closure_set(v___f_649_, 10, v_x_640_);
lean_closure_set(v___f_649_, 11, v___y_641_);
lean_closure_set(v___f_649_, 12, v_body_642_);
lean_closure_set(v___f_649_, 13, v___y_643_);
lean_closure_set(v___f_649_, 14, v_type_644_);
lean_closure_set(v___f_649_, 15, v_value_645_);
v___x_650_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_634_, v_inst_635_, v_inst_636_, v_pre_637_, v_post_638_, v_x_639_, v_x_640_, v_body_642_, v___y_641_);
v___x_651_ = lean_apply_4(v_toBind_646_, lean_box(0), lean_box(0), v___x_650_, v___f_649_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__13___boxed(lean_object** _args){
lean_object* v_declName_652_ = _args[0];
lean_object* v_a_653_ = _args[1];
lean_object* v_nondep_654_ = _args[2];
lean_object* v_inst_655_ = _args[3];
lean_object* v_inst_656_ = _args[4];
lean_object* v_inst_657_ = _args[5];
lean_object* v_pre_658_ = _args[6];
lean_object* v_post_659_ = _args[7];
lean_object* v_x_660_ = _args[8];
lean_object* v_x_661_ = _args[9];
lean_object* v___y_662_ = _args[10];
lean_object* v_body_663_ = _args[11];
lean_object* v___y_664_ = _args[12];
lean_object* v_type_665_ = _args[13];
lean_object* v_value_666_ = _args[14];
lean_object* v_toBind_667_ = _args[15];
lean_object* v_a_668_ = _args[16];
_start:
{
uint8_t v_nondep_3357__boxed_669_; lean_object* v_res_670_; 
v_nondep_3357__boxed_669_ = lean_unbox(v_nondep_654_);
v_res_670_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__13(v_declName_652_, v_a_653_, v_nondep_3357__boxed_669_, v_inst_655_, v_inst_656_, v_inst_657_, v_pre_658_, v_post_659_, v_x_660_, v_x_661_, v___y_662_, v_body_663_, v___y_664_, v_type_665_, v_value_666_, v_toBind_667_, v_a_668_);
lean_dec(v___y_662_);
return v_res_670_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__14(lean_object* v_declName_671_, uint8_t v_nondep_672_, lean_object* v_inst_673_, lean_object* v_inst_674_, lean_object* v_inst_675_, lean_object* v_pre_676_, lean_object* v_post_677_, lean_object* v_x_678_, lean_object* v_x_679_, lean_object* v___y_680_, lean_object* v_body_681_, lean_object* v___y_682_, lean_object* v_type_683_, lean_object* v_value_684_, lean_object* v_toBind_685_, lean_object* v_a_686_){
_start:
{
lean_object* v___x_687_; lean_object* v___f_688_; lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_687_ = lean_box(v_nondep_672_);
lean_inc(v_toBind_685_);
lean_inc_ref(v_value_684_);
lean_inc(v___y_680_);
lean_inc(v_x_679_);
lean_inc(v_post_677_);
lean_inc(v_pre_676_);
lean_inc_ref(v_inst_675_);
lean_inc(v_inst_674_);
lean_inc_ref(v_inst_673_);
v___f_688_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__13___boxed), 17, 16);
lean_closure_set(v___f_688_, 0, v_declName_671_);
lean_closure_set(v___f_688_, 1, v_a_686_);
lean_closure_set(v___f_688_, 2, v___x_687_);
lean_closure_set(v___f_688_, 3, v_inst_673_);
lean_closure_set(v___f_688_, 4, v_inst_674_);
lean_closure_set(v___f_688_, 5, v_inst_675_);
lean_closure_set(v___f_688_, 6, v_pre_676_);
lean_closure_set(v___f_688_, 7, v_post_677_);
lean_closure_set(v___f_688_, 8, v_x_678_);
lean_closure_set(v___f_688_, 9, v_x_679_);
lean_closure_set(v___f_688_, 10, v___y_680_);
lean_closure_set(v___f_688_, 11, v_body_681_);
lean_closure_set(v___f_688_, 12, v___y_682_);
lean_closure_set(v___f_688_, 13, v_type_683_);
lean_closure_set(v___f_688_, 14, v_value_684_);
lean_closure_set(v___f_688_, 15, v_toBind_685_);
v___x_689_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_673_, v_inst_674_, v_inst_675_, v_pre_676_, v_post_677_, v_x_678_, v_x_679_, v_value_684_, v___y_680_);
v___x_690_ = lean_apply_4(v_toBind_685_, lean_box(0), lean_box(0), v___x_689_, v___f_688_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__14___boxed(lean_object* v_declName_691_, lean_object* v_nondep_692_, lean_object* v_inst_693_, lean_object* v_inst_694_, lean_object* v_inst_695_, lean_object* v_pre_696_, lean_object* v_post_697_, lean_object* v_x_698_, lean_object* v_x_699_, lean_object* v___y_700_, lean_object* v_body_701_, lean_object* v___y_702_, lean_object* v_type_703_, lean_object* v_value_704_, lean_object* v_toBind_705_, lean_object* v_a_706_){
_start:
{
uint8_t v_nondep_3372__boxed_707_; lean_object* v_res_708_; 
v_nondep_3372__boxed_707_ = lean_unbox(v_nondep_692_);
v_res_708_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__14(v_declName_691_, v_nondep_3372__boxed_707_, v_inst_693_, v_inst_694_, v_inst_695_, v_pre_696_, v_post_697_, v_x_698_, v_x_699_, v___y_700_, v_body_701_, v___y_702_, v_type_703_, v_value_704_, v_toBind_705_, v_a_706_);
lean_dec(v___y_700_);
return v_res_708_;
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0(void){
_start:
{
lean_object* v___x_709_; lean_object* v_dummy_710_; 
v___x_709_ = lean_box(0);
v_dummy_710_ = l_Lean_Expr_sort___override(v___x_709_);
return v_dummy_710_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__15(lean_object* v_expr_711_, lean_object* v_data_712_, lean_object* v_inst_713_, lean_object* v_inst_714_, lean_object* v_inst_715_, lean_object* v_pre_716_, lean_object* v_post_717_, lean_object* v_x_718_, lean_object* v_x_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v_a_722_){
_start:
{
size_t v___x_723_; size_t v___x_724_; uint8_t v___x_725_; 
v___x_723_ = lean_ptr_addr(v_expr_711_);
v___x_724_ = lean_ptr_addr(v_a_722_);
v___x_725_ = lean_usize_dec_eq(v___x_723_, v___x_724_);
if (v___x_725_ == 0)
{
lean_object* v___x_726_; lean_object* v___x_727_; 
lean_dec_ref(v___y_721_);
v___x_726_ = l_Lean_Expr_mdata___override(v_data_712_, v_a_722_);
v___x_727_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_713_, v_inst_714_, v_inst_715_, v_pre_716_, v_post_717_, v_x_718_, v_x_719_, v___x_726_, v___y_720_);
return v___x_727_;
}
else
{
lean_object* v___x_728_; 
lean_dec_ref(v_a_722_);
lean_dec(v_data_712_);
v___x_728_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_713_, v_inst_714_, v_inst_715_, v_pre_716_, v_post_717_, v_x_718_, v_x_719_, v___y_721_, v___y_720_);
return v___x_728_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__15___boxed(lean_object* v_expr_729_, lean_object* v_data_730_, lean_object* v_inst_731_, lean_object* v_inst_732_, lean_object* v_inst_733_, lean_object* v_pre_734_, lean_object* v_post_735_, lean_object* v_x_736_, lean_object* v_x_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v_a_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__15(v_expr_729_, v_data_730_, v_inst_731_, v_inst_732_, v_inst_733_, v_pre_734_, v_post_735_, v_x_736_, v_x_737_, v___y_738_, v___y_739_, v_a_740_);
lean_dec(v___y_738_);
lean_dec_ref(v_expr_729_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__16(lean_object* v_struct_742_, lean_object* v_typeName_743_, lean_object* v_idx_744_, lean_object* v_inst_745_, lean_object* v_inst_746_, lean_object* v_inst_747_, lean_object* v_pre_748_, lean_object* v_post_749_, lean_object* v_x_750_, lean_object* v_x_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v_a_754_){
_start:
{
size_t v___x_755_; size_t v___x_756_; uint8_t v___x_757_; 
v___x_755_ = lean_ptr_addr(v_struct_742_);
v___x_756_ = lean_ptr_addr(v_a_754_);
v___x_757_ = lean_usize_dec_eq(v___x_755_, v___x_756_);
if (v___x_757_ == 0)
{
lean_object* v___x_758_; lean_object* v___x_759_; 
lean_dec_ref(v___y_753_);
v___x_758_ = l_Lean_Expr_proj___override(v_typeName_743_, v_idx_744_, v_a_754_);
v___x_759_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_745_, v_inst_746_, v_inst_747_, v_pre_748_, v_post_749_, v_x_750_, v_x_751_, v___x_758_, v___y_752_);
return v___x_759_;
}
else
{
lean_object* v___x_760_; 
lean_dec_ref(v_a_754_);
lean_dec(v_idx_744_);
lean_dec(v_typeName_743_);
v___x_760_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_745_, v_inst_746_, v_inst_747_, v_pre_748_, v_post_749_, v_x_750_, v_x_751_, v___y_753_, v___y_752_);
return v___x_760_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__16___boxed(lean_object* v_struct_761_, lean_object* v_typeName_762_, lean_object* v_idx_763_, lean_object* v_inst_764_, lean_object* v_inst_765_, lean_object* v_inst_766_, lean_object* v_pre_767_, lean_object* v_post_768_, lean_object* v_x_769_, lean_object* v_x_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v_a_773_){
_start:
{
lean_object* v_res_774_; 
v_res_774_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__16(v_struct_761_, v_typeName_762_, v_idx_763_, v_inst_764_, v_inst_765_, v_inst_766_, v_pre_767_, v_post_768_, v_x_769_, v_x_770_, v___y_771_, v___y_772_, v_a_773_);
lean_dec(v___y_771_);
lean_dec_ref(v_struct_761_);
return v_res_774_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17(lean_object* v_toApplicative_775_, lean_object* v_inst_776_, lean_object* v_inst_777_, lean_object* v_inst_778_, lean_object* v_pre_779_, lean_object* v_post_780_, lean_object* v_x_781_, lean_object* v_x_782_, lean_object* v___y_783_, lean_object* v_toBind_784_, lean_object* v___f_785_, lean_object* v___f_786_, lean_object* v_e_787_, lean_object* v_a_788_){
_start:
{
lean_object* v___y_790_; 
switch(lean_obj_tag(v_a_788_))
{
case 0:
{
lean_object* v_e_835_; lean_object* v_toPure_836_; lean_object* v___x_837_; 
lean_dec_ref(v_e_787_);
lean_dec(v___f_786_);
lean_dec(v___f_785_);
lean_dec(v_toBind_784_);
lean_dec(v_x_782_);
lean_dec(v_post_780_);
lean_dec(v_pre_779_);
lean_dec_ref(v_inst_778_);
lean_dec(v_inst_777_);
lean_dec_ref(v_inst_776_);
v_e_835_ = lean_ctor_get(v_a_788_, 0);
lean_inc_ref(v_e_835_);
lean_dec_ref_known(v_a_788_, 1);
v_toPure_836_ = lean_ctor_get(v_toApplicative_775_, 1);
lean_inc(v_toPure_836_);
lean_dec_ref(v_toApplicative_775_);
v___x_837_ = lean_apply_2(v_toPure_836_, lean_box(0), v_e_835_);
return v___x_837_;
}
case 1:
{
lean_object* v_e_838_; lean_object* v___x_839_; lean_object* v___x_840_; 
lean_dec_ref(v_e_787_);
lean_dec(v___f_786_);
lean_dec_ref(v_toApplicative_775_);
v_e_838_ = lean_ctor_get(v_a_788_, 0);
lean_inc_ref(v_e_838_);
lean_dec_ref_known(v_a_788_, 1);
v___x_839_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_776_, v_inst_777_, v_inst_778_, v_pre_779_, v_post_780_, v_x_781_, v_x_782_, v_e_838_, v___y_783_);
v___x_840_ = lean_apply_4(v_toBind_784_, lean_box(0), lean_box(0), v___x_839_, v___f_785_);
return v___x_840_;
}
default: 
{
lean_object* v_e_x3f_841_; 
lean_dec(v___f_785_);
lean_dec_ref(v_toApplicative_775_);
v_e_x3f_841_ = lean_ctor_get(v_a_788_, 0);
lean_inc(v_e_x3f_841_);
lean_dec_ref_known(v_a_788_, 1);
if (lean_obj_tag(v_e_x3f_841_) == 0)
{
v___y_790_ = v_e_787_;
goto v___jp_789_;
}
else
{
lean_object* v_val_842_; 
lean_dec_ref(v_e_787_);
v_val_842_ = lean_ctor_get(v_e_x3f_841_, 0);
lean_inc(v_val_842_);
lean_dec_ref_known(v_e_x3f_841_, 1);
v___y_790_ = v_val_842_;
goto v___jp_789_;
}
}
}
v___jp_789_:
{
switch(lean_obj_tag(v___y_790_))
{
case 7:
{
lean_object* v_binderName_791_; lean_object* v_binderType_792_; lean_object* v_body_793_; uint8_t v_binderInfo_794_; lean_object* v___x_795_; lean_object* v___f_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
lean_dec(v___f_786_);
v_binderName_791_ = lean_ctor_get(v___y_790_, 0);
lean_inc(v_binderName_791_);
v_binderType_792_ = lean_ctor_get(v___y_790_, 1);
lean_inc_ref_n(v_binderType_792_, 2);
v_body_793_ = lean_ctor_get(v___y_790_, 2);
lean_inc_ref(v_body_793_);
v_binderInfo_794_ = lean_ctor_get_uint8(v___y_790_, sizeof(void*)*3 + 8);
v___x_795_ = lean_box(v_binderInfo_794_);
lean_inc(v_toBind_784_);
lean_inc(v___y_783_);
lean_inc(v_x_782_);
lean_inc(v_post_780_);
lean_inc(v_pre_779_);
lean_inc_ref(v_inst_778_);
lean_inc(v_inst_777_);
lean_inc_ref(v_inst_776_);
v___f_796_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__9___boxed), 15, 14);
lean_closure_set(v___f_796_, 0, v_binderName_791_);
lean_closure_set(v___f_796_, 1, v___x_795_);
lean_closure_set(v___f_796_, 2, v_inst_776_);
lean_closure_set(v___f_796_, 3, v_inst_777_);
lean_closure_set(v___f_796_, 4, v_inst_778_);
lean_closure_set(v___f_796_, 5, v_pre_779_);
lean_closure_set(v___f_796_, 6, v_post_780_);
lean_closure_set(v___f_796_, 7, v_x_781_);
lean_closure_set(v___f_796_, 8, v_x_782_);
lean_closure_set(v___f_796_, 9, v___y_783_);
lean_closure_set(v___f_796_, 10, v___y_790_);
lean_closure_set(v___f_796_, 11, v_binderType_792_);
lean_closure_set(v___f_796_, 12, v_body_793_);
lean_closure_set(v___f_796_, 13, v_toBind_784_);
v___x_797_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_776_, v_inst_777_, v_inst_778_, v_pre_779_, v_post_780_, v_x_781_, v_x_782_, v_binderType_792_, v___y_783_);
v___x_798_ = lean_apply_4(v_toBind_784_, lean_box(0), lean_box(0), v___x_797_, v___f_796_);
return v___x_798_;
}
case 6:
{
lean_object* v_binderName_799_; lean_object* v_binderType_800_; lean_object* v_body_801_; uint8_t v_binderInfo_802_; lean_object* v___x_803_; lean_object* v___f_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
lean_dec(v___f_786_);
v_binderName_799_ = lean_ctor_get(v___y_790_, 0);
lean_inc(v_binderName_799_);
v_binderType_800_ = lean_ctor_get(v___y_790_, 1);
lean_inc_ref_n(v_binderType_800_, 2);
v_body_801_ = lean_ctor_get(v___y_790_, 2);
lean_inc_ref(v_body_801_);
v_binderInfo_802_ = lean_ctor_get_uint8(v___y_790_, sizeof(void*)*3 + 8);
v___x_803_ = lean_box(v_binderInfo_802_);
lean_inc(v_toBind_784_);
lean_inc(v___y_783_);
lean_inc(v_x_782_);
lean_inc(v_post_780_);
lean_inc(v_pre_779_);
lean_inc_ref(v_inst_778_);
lean_inc(v_inst_777_);
lean_inc_ref(v_inst_776_);
v___f_804_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__11___boxed), 15, 14);
lean_closure_set(v___f_804_, 0, v_binderName_799_);
lean_closure_set(v___f_804_, 1, v___x_803_);
lean_closure_set(v___f_804_, 2, v_inst_776_);
lean_closure_set(v___f_804_, 3, v_inst_777_);
lean_closure_set(v___f_804_, 4, v_inst_778_);
lean_closure_set(v___f_804_, 5, v_pre_779_);
lean_closure_set(v___f_804_, 6, v_post_780_);
lean_closure_set(v___f_804_, 7, v_x_781_);
lean_closure_set(v___f_804_, 8, v_x_782_);
lean_closure_set(v___f_804_, 9, v___y_783_);
lean_closure_set(v___f_804_, 10, v___y_790_);
lean_closure_set(v___f_804_, 11, v_binderType_800_);
lean_closure_set(v___f_804_, 12, v_body_801_);
lean_closure_set(v___f_804_, 13, v_toBind_784_);
v___x_805_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_776_, v_inst_777_, v_inst_778_, v_pre_779_, v_post_780_, v_x_781_, v_x_782_, v_binderType_800_, v___y_783_);
v___x_806_ = lean_apply_4(v_toBind_784_, lean_box(0), lean_box(0), v___x_805_, v___f_804_);
return v___x_806_;
}
case 8:
{
lean_object* v_declName_807_; lean_object* v_type_808_; lean_object* v_value_809_; lean_object* v_body_810_; uint8_t v_nondep_811_; lean_object* v___x_812_; lean_object* v___f_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
lean_dec(v___f_786_);
v_declName_807_ = lean_ctor_get(v___y_790_, 0);
lean_inc(v_declName_807_);
v_type_808_ = lean_ctor_get(v___y_790_, 1);
lean_inc_ref_n(v_type_808_, 2);
v_value_809_ = lean_ctor_get(v___y_790_, 2);
lean_inc_ref(v_value_809_);
v_body_810_ = lean_ctor_get(v___y_790_, 3);
lean_inc_ref(v_body_810_);
v_nondep_811_ = lean_ctor_get_uint8(v___y_790_, sizeof(void*)*4 + 8);
v___x_812_ = lean_box(v_nondep_811_);
lean_inc(v_toBind_784_);
lean_inc(v___y_783_);
lean_inc(v_x_782_);
lean_inc(v_post_780_);
lean_inc(v_pre_779_);
lean_inc_ref(v_inst_778_);
lean_inc(v_inst_777_);
lean_inc_ref(v_inst_776_);
v___f_813_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__14___boxed), 16, 15);
lean_closure_set(v___f_813_, 0, v_declName_807_);
lean_closure_set(v___f_813_, 1, v___x_812_);
lean_closure_set(v___f_813_, 2, v_inst_776_);
lean_closure_set(v___f_813_, 3, v_inst_777_);
lean_closure_set(v___f_813_, 4, v_inst_778_);
lean_closure_set(v___f_813_, 5, v_pre_779_);
lean_closure_set(v___f_813_, 6, v_post_780_);
lean_closure_set(v___f_813_, 7, v_x_781_);
lean_closure_set(v___f_813_, 8, v_x_782_);
lean_closure_set(v___f_813_, 9, v___y_783_);
lean_closure_set(v___f_813_, 10, v_body_810_);
lean_closure_set(v___f_813_, 11, v___y_790_);
lean_closure_set(v___f_813_, 12, v_type_808_);
lean_closure_set(v___f_813_, 13, v_value_809_);
lean_closure_set(v___f_813_, 14, v_toBind_784_);
v___x_814_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_776_, v_inst_777_, v_inst_778_, v_pre_779_, v_post_780_, v_x_781_, v_x_782_, v_type_808_, v___y_783_);
v___x_815_ = lean_apply_4(v_toBind_784_, lean_box(0), lean_box(0), v___x_814_, v___f_813_);
return v___x_815_;
}
case 5:
{
lean_object* v_dummy_816_; lean_object* v_nargs_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_3055__overap_821_; lean_object* v___x_822_; 
lean_dec(v_toBind_784_);
lean_dec(v_x_782_);
lean_dec(v_post_780_);
lean_dec(v_pre_779_);
lean_dec_ref(v_inst_778_);
lean_dec(v_inst_777_);
lean_dec_ref(v_inst_776_);
v_dummy_816_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_817_ = l_Lean_Expr_getAppNumArgs(v___y_790_);
lean_inc(v_nargs_817_);
v___x_818_ = lean_mk_array(v_nargs_817_, v_dummy_816_);
v___x_819_ = lean_unsigned_to_nat(1u);
v___x_820_ = lean_nat_sub(v_nargs_817_, v___x_819_);
lean_dec(v_nargs_817_);
v___x_3055__overap_821_ = l_Lean_Expr_withAppAux___redArg(v___f_786_, v___y_790_, v___x_818_, v___x_820_);
lean_inc(v___y_783_);
v___x_822_ = lean_apply_1(v___x_3055__overap_821_, v___y_783_);
return v___x_822_;
}
case 10:
{
lean_object* v_data_823_; lean_object* v_expr_824_; lean_object* v___f_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
lean_dec(v___f_786_);
v_data_823_ = lean_ctor_get(v___y_790_, 0);
lean_inc(v_data_823_);
v_expr_824_ = lean_ctor_get(v___y_790_, 1);
lean_inc_ref_n(v_expr_824_, 2);
lean_inc(v___y_783_);
lean_inc(v_x_782_);
lean_inc(v_post_780_);
lean_inc(v_pre_779_);
lean_inc_ref(v_inst_778_);
lean_inc(v_inst_777_);
lean_inc_ref(v_inst_776_);
v___f_825_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__15___boxed), 12, 11);
lean_closure_set(v___f_825_, 0, v_expr_824_);
lean_closure_set(v___f_825_, 1, v_data_823_);
lean_closure_set(v___f_825_, 2, v_inst_776_);
lean_closure_set(v___f_825_, 3, v_inst_777_);
lean_closure_set(v___f_825_, 4, v_inst_778_);
lean_closure_set(v___f_825_, 5, v_pre_779_);
lean_closure_set(v___f_825_, 6, v_post_780_);
lean_closure_set(v___f_825_, 7, v_x_781_);
lean_closure_set(v___f_825_, 8, v_x_782_);
lean_closure_set(v___f_825_, 9, v___y_783_);
lean_closure_set(v___f_825_, 10, v___y_790_);
v___x_826_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_776_, v_inst_777_, v_inst_778_, v_pre_779_, v_post_780_, v_x_781_, v_x_782_, v_expr_824_, v___y_783_);
v___x_827_ = lean_apply_4(v_toBind_784_, lean_box(0), lean_box(0), v___x_826_, v___f_825_);
return v___x_827_;
}
case 11:
{
lean_object* v_typeName_828_; lean_object* v_idx_829_; lean_object* v_struct_830_; lean_object* v___f_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
lean_dec(v___f_786_);
v_typeName_828_ = lean_ctor_get(v___y_790_, 0);
lean_inc(v_typeName_828_);
v_idx_829_ = lean_ctor_get(v___y_790_, 1);
lean_inc(v_idx_829_);
v_struct_830_ = lean_ctor_get(v___y_790_, 2);
lean_inc_ref_n(v_struct_830_, 2);
lean_inc(v___y_783_);
lean_inc(v_x_782_);
lean_inc(v_post_780_);
lean_inc(v_pre_779_);
lean_inc_ref(v_inst_778_);
lean_inc(v_inst_777_);
lean_inc_ref(v_inst_776_);
v___f_831_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__16___boxed), 13, 12);
lean_closure_set(v___f_831_, 0, v_struct_830_);
lean_closure_set(v___f_831_, 1, v_typeName_828_);
lean_closure_set(v___f_831_, 2, v_idx_829_);
lean_closure_set(v___f_831_, 3, v_inst_776_);
lean_closure_set(v___f_831_, 4, v_inst_777_);
lean_closure_set(v___f_831_, 5, v_inst_778_);
lean_closure_set(v___f_831_, 6, v_pre_779_);
lean_closure_set(v___f_831_, 7, v_post_780_);
lean_closure_set(v___f_831_, 8, v_x_781_);
lean_closure_set(v___f_831_, 9, v_x_782_);
lean_closure_set(v___f_831_, 10, v___y_783_);
lean_closure_set(v___f_831_, 11, v___y_790_);
v___x_832_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_776_, v_inst_777_, v_inst_778_, v_pre_779_, v_post_780_, v_x_781_, v_x_782_, v_struct_830_, v___y_783_);
v___x_833_ = lean_apply_4(v_toBind_784_, lean_box(0), lean_box(0), v___x_832_, v___f_831_);
return v___x_833_;
}
default: 
{
lean_object* v___x_834_; 
lean_dec(v___f_786_);
lean_dec(v_toBind_784_);
v___x_834_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_776_, v_inst_777_, v_inst_778_, v_pre_779_, v_post_780_, v_x_781_, v_x_782_, v___y_790_, v___y_783_);
return v___x_834_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___boxed(lean_object* v_toApplicative_843_, lean_object* v_inst_844_, lean_object* v_inst_845_, lean_object* v_inst_846_, lean_object* v_pre_847_, lean_object* v_post_848_, lean_object* v_x_849_, lean_object* v_x_850_, lean_object* v___y_851_, lean_object* v_toBind_852_, lean_object* v___f_853_, lean_object* v___f_854_, lean_object* v_e_855_, lean_object* v_a_856_){
_start:
{
lean_object* v_res_857_; 
v_res_857_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17(v_toApplicative_843_, v_inst_844_, v_inst_845_, v_inst_846_, v_pre_847_, v_post_848_, v_x_849_, v_x_850_, v___y_851_, v_toBind_852_, v___f_853_, v___f_854_, v_e_855_, v_a_856_);
lean_dec(v___y_851_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__18(lean_object* v_inst_858_, lean_object* v_inst_859_, lean_object* v_inst_860_, lean_object* v_pre_861_, lean_object* v_post_862_, lean_object* v_x_863_, lean_object* v_x_864_, lean_object* v_toApplicative_865_, lean_object* v_toBind_866_, lean_object* v___f_867_, lean_object* v_e_868_, lean_object* v_____r_869_, lean_object* v___y_870_){
_start:
{
lean_object* v___f_871_; lean_object* v___f_872_; lean_object* v___x_873_; lean_object* v___x_874_; 
lean_inc_n(v___y_870_, 2);
lean_inc(v_x_864_);
lean_inc(v_post_862_);
lean_inc_n(v_pre_861_, 2);
lean_inc_ref(v_inst_860_);
lean_inc(v_inst_859_);
lean_inc_ref(v_inst_858_);
v___f_871_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__7___boxed), 9, 8);
lean_closure_set(v___f_871_, 0, v_inst_858_);
lean_closure_set(v___f_871_, 1, v_inst_859_);
lean_closure_set(v___f_871_, 2, v_inst_860_);
lean_closure_set(v___f_871_, 3, v_pre_861_);
lean_closure_set(v___f_871_, 4, v_post_862_);
lean_closure_set(v___f_871_, 5, v_x_863_);
lean_closure_set(v___f_871_, 6, v_x_864_);
lean_closure_set(v___f_871_, 7, v___y_870_);
lean_inc_ref(v_e_868_);
lean_inc(v_toBind_866_);
v___f_872_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___boxed), 14, 13);
lean_closure_set(v___f_872_, 0, v_toApplicative_865_);
lean_closure_set(v___f_872_, 1, v_inst_858_);
lean_closure_set(v___f_872_, 2, v_inst_859_);
lean_closure_set(v___f_872_, 3, v_inst_860_);
lean_closure_set(v___f_872_, 4, v_pre_861_);
lean_closure_set(v___f_872_, 5, v_post_862_);
lean_closure_set(v___f_872_, 6, v_x_863_);
lean_closure_set(v___f_872_, 7, v_x_864_);
lean_closure_set(v___f_872_, 8, v___y_870_);
lean_closure_set(v___f_872_, 9, v_toBind_866_);
lean_closure_set(v___f_872_, 10, v___f_871_);
lean_closure_set(v___f_872_, 11, v___f_867_);
lean_closure_set(v___f_872_, 12, v_e_868_);
v___x_873_ = lean_apply_1(v_pre_861_, v_e_868_);
v___x_874_ = lean_apply_4(v_toBind_866_, lean_box(0), lean_box(0), v___x_873_, v___f_872_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__18___boxed(lean_object* v_inst_875_, lean_object* v_inst_876_, lean_object* v_inst_877_, lean_object* v_pre_878_, lean_object* v_post_879_, lean_object* v_x_880_, lean_object* v_x_881_, lean_object* v_toApplicative_882_, lean_object* v_toBind_883_, lean_object* v___f_884_, lean_object* v_e_885_, lean_object* v_____r_886_, lean_object* v___y_887_){
_start:
{
lean_object* v_res_888_; 
v_res_888_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__18(v_inst_875_, v_inst_876_, v_inst_877_, v_pre_878_, v_post_879_, v_x_880_, v_x_881_, v_toApplicative_882_, v_toBind_883_, v___f_884_, v_e_885_, v_____r_886_, v___y_887_);
lean_dec(v___y_887_);
return v_res_888_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(lean_object* v_inst_889_, lean_object* v_inst_890_, lean_object* v_inst_891_, lean_object* v_pre_892_, lean_object* v_post_893_, lean_object* v_x_894_, lean_object* v_x_895_, lean_object* v_e_896_, lean_object* v_a_897_){
_start:
{
lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___f_902_; lean_object* v___f_903_; lean_object* v___x_904_; lean_object* v_toApplicative_905_; lean_object* v_toBind_906_; lean_object* v___f_907_; lean_object* v___f_908_; lean_object* v___f_909_; lean_object* v___f_910_; lean_object* v___f_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_898_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0));
v___x_899_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1));
lean_inc_ref_n(v_inst_889_, 3);
v___x_900_ = l_Lean_MonadCacheT_instMonad___redArg(v_x_894_, v___x_898_, v___x_899_, v_inst_889_);
v___x_901_ = l_Lean_MonadCacheT_instMonadControl___redArg(v_x_894_, v___x_898_, v___x_899_);
lean_inc_ref_n(v_inst_891_, 3);
lean_inc_ref(v___x_901_);
v___f_902_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_902_, 0, v___x_901_);
lean_closure_set(v___f_902_, 1, v_inst_891_);
v___f_903_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_903_, 0, v___x_901_);
lean_closure_set(v___f_903_, 1, v_inst_891_);
v___x_904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_904_, 0, v___f_902_);
lean_ctor_set(v___x_904_, 1, v___f_903_);
v_toApplicative_905_ = lean_ctor_get(v_inst_889_, 0);
lean_inc_ref_n(v_toApplicative_905_, 4);
v_toBind_906_ = lean_ctor_get(v_inst_889_, 1);
lean_inc_n(v_toBind_906_, 6);
lean_inc_n(v_x_895_, 3);
lean_inc_n(v_a_897_, 3);
lean_inc_ref_n(v_e_896_, 2);
v___f_907_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_907_, 0, v_toApplicative_905_);
lean_closure_set(v___f_907_, 1, v___x_898_);
lean_closure_set(v___f_907_, 2, v___x_899_);
lean_closure_set(v___f_907_, 3, v_e_896_);
lean_closure_set(v___f_907_, 4, v_a_897_);
lean_closure_set(v___f_907_, 5, v_x_895_);
lean_closure_set(v___f_907_, 6, v_toBind_906_);
v___f_908_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__3___boxed), 5, 4);
lean_closure_set(v___f_908_, 0, v_toApplicative_905_);
lean_closure_set(v___f_908_, 1, v___x_898_);
lean_closure_set(v___f_908_, 2, v___x_899_);
lean_closure_set(v___f_908_, 3, v_e_896_);
lean_inc_ref(v___x_900_);
lean_inc(v_post_893_);
lean_inc(v_pre_892_);
lean_inc_n(v_inst_890_, 2);
v___f_909_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__6___boxed), 12, 9);
lean_closure_set(v___f_909_, 0, v_inst_889_);
lean_closure_set(v___f_909_, 1, v_inst_890_);
lean_closure_set(v___f_909_, 2, v_inst_891_);
lean_closure_set(v___f_909_, 3, v_pre_892_);
lean_closure_set(v___f_909_, 4, v_post_893_);
lean_closure_set(v___f_909_, 5, v_x_894_);
lean_closure_set(v___f_909_, 6, v_x_895_);
lean_closure_set(v___f_909_, 7, v___x_900_);
lean_closure_set(v___f_909_, 8, v_toBind_906_);
v___f_910_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__18___boxed), 13, 11);
lean_closure_set(v___f_910_, 0, v_inst_889_);
lean_closure_set(v___f_910_, 1, v_inst_890_);
lean_closure_set(v___f_910_, 2, v_inst_891_);
lean_closure_set(v___f_910_, 3, v_pre_892_);
lean_closure_set(v___f_910_, 4, v_post_893_);
lean_closure_set(v___f_910_, 5, v_x_894_);
lean_closure_set(v___f_910_, 6, v_x_895_);
lean_closure_set(v___f_910_, 7, v_toApplicative_905_);
lean_closure_set(v___f_910_, 8, v_toBind_906_);
lean_closure_set(v___f_910_, 9, v___f_909_);
lean_closure_set(v___f_910_, 10, v_e_896_);
v___f_911_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__19___boxed), 13, 12);
lean_closure_set(v___f_911_, 0, v_inst_890_);
lean_closure_set(v___f_911_, 1, v_x_894_);
lean_closure_set(v___f_911_, 2, v___x_898_);
lean_closure_set(v___f_911_, 3, v___x_899_);
lean_closure_set(v___f_911_, 4, v_inst_889_);
lean_closure_set(v___f_911_, 5, v___f_910_);
lean_closure_set(v___f_911_, 6, v___x_900_);
lean_closure_set(v___f_911_, 7, v___x_904_);
lean_closure_set(v___f_911_, 8, v_a_897_);
lean_closure_set(v___f_911_, 9, v_toBind_906_);
lean_closure_set(v___f_911_, 10, v___f_907_);
lean_closure_set(v___f_911_, 11, v_toApplicative_905_);
v___x_912_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_912_, 0, lean_box(0));
lean_closure_set(v___x_912_, 1, lean_box(0));
lean_closure_set(v___x_912_, 2, v_a_897_);
v___x_913_ = lean_apply_2(v_x_895_, lean_box(0), v___x_912_);
v___x_914_ = lean_apply_4(v_toBind_906_, lean_box(0), lean_box(0), v___x_913_, v___f_908_);
v___x_915_ = lean_apply_4(v_toBind_906_, lean_box(0), lean_box(0), v___x_914_, v___f_911_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg___lam__0(lean_object* v_toApplicative_916_, lean_object* v_inst_917_, lean_object* v_inst_918_, lean_object* v_inst_919_, lean_object* v_pre_920_, lean_object* v_post_921_, lean_object* v_x_922_, lean_object* v_x_923_, lean_object* v_a_924_, lean_object* v_e_925_, lean_object* v_a_926_){
_start:
{
lean_object* v___y_928_; 
switch(lean_obj_tag(v_a_926_))
{
case 0:
{
lean_object* v_e_931_; lean_object* v_toPure_932_; lean_object* v___x_933_; 
lean_dec_ref(v_e_925_);
lean_dec(v_x_923_);
lean_dec(v_post_921_);
lean_dec(v_pre_920_);
lean_dec_ref(v_inst_919_);
lean_dec(v_inst_918_);
lean_dec_ref(v_inst_917_);
v_e_931_ = lean_ctor_get(v_a_926_, 0);
lean_inc_ref(v_e_931_);
lean_dec_ref_known(v_a_926_, 1);
v_toPure_932_ = lean_ctor_get(v_toApplicative_916_, 1);
lean_inc(v_toPure_932_);
lean_dec_ref(v_toApplicative_916_);
v___x_933_ = lean_apply_2(v_toPure_932_, lean_box(0), v_e_931_);
return v___x_933_;
}
case 1:
{
lean_object* v_e_934_; lean_object* v___x_935_; 
lean_dec_ref(v_e_925_);
lean_dec_ref(v_toApplicative_916_);
v_e_934_ = lean_ctor_get(v_a_926_, 0);
lean_inc_ref(v_e_934_);
lean_dec_ref_known(v_a_926_, 1);
v___x_935_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_917_, v_inst_918_, v_inst_919_, v_pre_920_, v_post_921_, v_x_922_, v_x_923_, v_e_934_, v_a_924_);
return v___x_935_;
}
default: 
{
lean_object* v_e_x3f_936_; 
lean_dec(v_x_923_);
lean_dec(v_post_921_);
lean_dec(v_pre_920_);
lean_dec_ref(v_inst_919_);
lean_dec(v_inst_918_);
lean_dec_ref(v_inst_917_);
v_e_x3f_936_ = lean_ctor_get(v_a_926_, 0);
lean_inc(v_e_x3f_936_);
lean_dec_ref_known(v_a_926_, 1);
if (lean_obj_tag(v_e_x3f_936_) == 0)
{
v___y_928_ = v_e_925_;
goto v___jp_927_;
}
else
{
lean_object* v_val_937_; 
lean_dec_ref(v_e_925_);
v_val_937_ = lean_ctor_get(v_e_x3f_936_, 0);
lean_inc(v_val_937_);
lean_dec_ref_known(v_e_x3f_936_, 1);
v___y_928_ = v_val_937_;
goto v___jp_927_;
}
}
}
v___jp_927_:
{
lean_object* v_toPure_929_; lean_object* v___x_930_; 
v_toPure_929_ = lean_ctor_get(v_toApplicative_916_, 1);
lean_inc(v_toPure_929_);
lean_dec_ref(v_toApplicative_916_);
v___x_930_ = lean_apply_2(v_toPure_929_, lean_box(0), v___y_928_);
return v___x_930_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg___lam__0___boxed(lean_object* v_toApplicative_938_, lean_object* v_inst_939_, lean_object* v_inst_940_, lean_object* v_inst_941_, lean_object* v_pre_942_, lean_object* v_post_943_, lean_object* v_x_944_, lean_object* v_x_945_, lean_object* v_a_946_, lean_object* v_e_947_, lean_object* v_a_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg___lam__0(v_toApplicative_938_, v_inst_939_, v_inst_940_, v_inst_941_, v_pre_942_, v_post_943_, v_x_944_, v_x_945_, v_a_946_, v_e_947_, v_a_948_);
lean_dec(v_a_946_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(lean_object* v_inst_950_, lean_object* v_inst_951_, lean_object* v_inst_952_, lean_object* v_pre_953_, lean_object* v_post_954_, lean_object* v_x_955_, lean_object* v_x_956_, lean_object* v_e_957_, lean_object* v_a_958_){
_start:
{
lean_object* v_toApplicative_959_; lean_object* v_toBind_960_; lean_object* v___f_961_; lean_object* v___x_962_; lean_object* v___x_963_; 
v_toApplicative_959_ = lean_ctor_get(v_inst_950_, 0);
lean_inc_ref(v_toApplicative_959_);
v_toBind_960_ = lean_ctor_get(v_inst_950_, 1);
lean_inc(v_toBind_960_);
lean_inc_ref(v_e_957_);
lean_inc(v_a_958_);
lean_inc(v_post_954_);
v___f_961_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg___lam__0___boxed), 11, 10);
lean_closure_set(v___f_961_, 0, v_toApplicative_959_);
lean_closure_set(v___f_961_, 1, v_inst_950_);
lean_closure_set(v___f_961_, 2, v_inst_951_);
lean_closure_set(v___f_961_, 3, v_inst_952_);
lean_closure_set(v___f_961_, 4, v_pre_953_);
lean_closure_set(v___f_961_, 5, v_post_954_);
lean_closure_set(v___f_961_, 6, v_x_955_);
lean_closure_set(v___f_961_, 7, v_x_956_);
lean_closure_set(v___f_961_, 8, v_a_958_);
lean_closure_set(v___f_961_, 9, v_e_957_);
v___x_962_ = lean_apply_1(v_post_954_, v_e_957_);
v___x_963_ = lean_apply_4(v_toBind_960_, lean_box(0), lean_box(0), v___x_962_, v___f_961_);
return v___x_963_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__7(lean_object* v_inst_964_, lean_object* v_inst_965_, lean_object* v_inst_966_, lean_object* v_pre_967_, lean_object* v_post_968_, lean_object* v_x_969_, lean_object* v_x_970_, lean_object* v___y_971_, lean_object* v_a_972_){
_start:
{
lean_object* v___x_973_; 
v___x_973_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_964_, v_inst_965_, v_inst_966_, v_pre_967_, v_post_968_, v_x_969_, v_x_970_, v_a_972_, v___y_971_);
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg___boxed(lean_object* v_inst_974_, lean_object* v_inst_975_, lean_object* v_inst_976_, lean_object* v_pre_977_, lean_object* v_post_978_, lean_object* v_x_979_, lean_object* v_x_980_, lean_object* v_e_981_, lean_object* v_a_982_){
_start:
{
lean_object* v_res_983_; 
v_res_983_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_974_, v_inst_975_, v_inst_976_, v_pre_977_, v_post_978_, v_x_979_, v_x_980_, v_e_981_, v_a_982_);
lean_dec(v_a_982_);
return v_res_983_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit(lean_object* v_m_984_, lean_object* v_inst_985_, lean_object* v_inst_986_, lean_object* v_inst_987_, lean_object* v_pre_988_, lean_object* v_post_989_, lean_object* v_x_990_, lean_object* v_x_991_, lean_object* v_e_992_, lean_object* v_a_993_){
_start:
{
lean_object* v___x_994_; 
v___x_994_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_985_, v_inst_986_, v_inst_987_, v_pre_988_, v_post_989_, v_x_990_, v_x_991_, v_e_992_, v_a_993_);
return v___x_994_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___boxed(lean_object* v_m_995_, lean_object* v_inst_996_, lean_object* v_inst_997_, lean_object* v_inst_998_, lean_object* v_pre_999_, lean_object* v_post_1000_, lean_object* v_x_1001_, lean_object* v_x_1002_, lean_object* v_e_1003_, lean_object* v_a_1004_){
_start:
{
lean_object* v_res_1005_; 
v_res_1005_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit(v_m_995_, v_inst_996_, v_inst_997_, v_inst_998_, v_pre_999_, v_post_1000_, v_x_1001_, v_x_1002_, v_e_1003_, v_a_1004_);
lean_dec(v_a_1004_);
return v_res_1005_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost(lean_object* v_m_1006_, lean_object* v_inst_1007_, lean_object* v_inst_1008_, lean_object* v_inst_1009_, lean_object* v_pre_1010_, lean_object* v_post_1011_, lean_object* v_x_1012_, lean_object* v_x_1013_, lean_object* v_e_1014_, lean_object* v_a_1015_){
_start:
{
lean_object* v___x_1016_; 
v___x_1016_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_1007_, v_inst_1008_, v_inst_1009_, v_pre_1010_, v_post_1011_, v_x_1012_, v_x_1013_, v_e_1014_, v_a_1015_);
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___boxed(lean_object* v_m_1017_, lean_object* v_inst_1018_, lean_object* v_inst_1019_, lean_object* v_inst_1020_, lean_object* v_pre_1021_, lean_object* v_post_1022_, lean_object* v_x_1023_, lean_object* v_x_1024_, lean_object* v_e_1025_, lean_object* v_a_1026_){
_start:
{
lean_object* v_res_1027_; 
v_res_1027_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost(v_m_1017_, v_inst_1018_, v_inst_1019_, v_inst_1020_, v_pre_1021_, v_post_1022_, v_x_1023_, v_x_1024_, v_e_1025_, v_a_1026_);
lean_dec(v_a_1026_);
return v_res_1027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___redArg___lam__0(lean_object* v_x_1028_){
_start:
{
lean_object* v___x_1030_; lean_object* v___x_1031_; 
v___x_1030_ = lean_apply_1(v_x_1028_, lean_box(0));
v___x_1031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1030_);
return v___x_1031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___redArg___lam__0___boxed(lean_object* v_x_1032_, lean_object* v___y_1033_){
_start:
{
lean_object* v_res_1034_; 
v_res_1034_ = l_Lean_Core_transform___redArg___lam__0(v_x_1032_);
return v_res_1034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___redArg___lam__1(lean_object* v_inst_1035_, lean_object* v_00_u03b1_1036_, lean_object* v_x_1037_){
_start:
{
lean_object* v___f_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___f_1038_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1038_, 0, v_x_1037_);
v___x_1039_ = lean_alloc_closure((void*)(l_Lean_Core_liftIOCore___boxed), 5, 2);
lean_closure_set(v___x_1039_, 0, lean_box(0));
lean_closure_set(v___x_1039_, 1, v___f_1038_);
v___x_1040_ = lean_apply_2(v_inst_1035_, lean_box(0), v___x_1039_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___redArg___lam__2(lean_object* v_toPure_1041_, lean_object* v_____x_1042_){
_start:
{
lean_object* v_fst_1043_; lean_object* v___x_1044_; 
v_fst_1043_ = lean_ctor_get(v_____x_1042_, 0);
lean_inc(v_fst_1043_);
lean_dec_ref(v_____x_1042_);
v___x_1044_ = lean_apply_2(v_toPure_1041_, lean_box(0), v_fst_1043_);
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___redArg___lam__3(lean_object* v_a_1045_, lean_object* v_toPure_1046_, lean_object* v_s_1047_){
_start:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1048_, 0, v_a_1045_);
lean_ctor_set(v___x_1048_, 1, v_s_1047_);
v___x_1049_ = lean_apply_2(v_toPure_1046_, lean_box(0), v___x_1048_);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___redArg___lam__4(lean_object* v_toPure_1050_, lean_object* v_ref_1051_, lean_object* v_x_1052_, lean_object* v_toBind_1053_, lean_object* v_a_1054_){
_start:
{
lean_object* v___f_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___f_1055_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__3), 3, 2);
lean_closure_set(v___f_1055_, 0, v_a_1054_);
lean_closure_set(v___f_1055_, 1, v_toPure_1050_);
v___x_1056_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1056_, 0, lean_box(0));
lean_closure_set(v___x_1056_, 1, lean_box(0));
lean_closure_set(v___x_1056_, 2, v_ref_1051_);
v___x_1057_ = lean_apply_2(v_x_1052_, lean_box(0), v___x_1056_);
v___x_1058_ = lean_apply_4(v_toBind_1053_, lean_box(0), lean_box(0), v___x_1057_, v___f_1055_);
return v___x_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___redArg___lam__5(lean_object* v_toPure_1059_, lean_object* v_x_1060_, lean_object* v_toBind_1061_, lean_object* v_inst_1062_, lean_object* v_inst_1063_, lean_object* v_inst_1064_, lean_object* v_pre_1065_, lean_object* v_post_1066_, lean_object* v_x_1067_, lean_object* v_input_1068_, lean_object* v_ref_1069_){
_start:
{
lean_object* v___f_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; 
lean_inc(v_toBind_1061_);
lean_inc(v_x_1060_);
lean_inc(v_ref_1069_);
v___f_1070_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__4), 5, 4);
lean_closure_set(v___f_1070_, 0, v_toPure_1059_);
lean_closure_set(v___f_1070_, 1, v_ref_1069_);
lean_closure_set(v___f_1070_, 2, v_x_1060_);
lean_closure_set(v___f_1070_, 3, v_toBind_1061_);
v___x_1071_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_1062_, v_inst_1063_, v_inst_1064_, v_pre_1065_, v_post_1066_, v_x_1067_, v_x_1060_, v_input_1068_, v_ref_1069_);
lean_dec(v_ref_1069_);
v___x_1072_ = lean_apply_4(v_toBind_1061_, lean_box(0), lean_box(0), v___x_1071_, v___f_1070_);
return v___x_1072_;
}
}
static lean_object* _init_l_Lean_Core_transform___redArg___closed__0(void){
_start:
{
lean_object* v_cellCount_1073_; lean_object* v___x_1074_; 
v_cellCount_1073_ = lean_unsigned_to_nat(16u);
v___x_1074_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1073_);
return v___x_1074_;
}
}
static lean_object* _init_l_Lean_Core_transform___redArg___closed__1(void){
_start:
{
lean_object* v_cellCount_1075_; lean_object* v___x_1076_; 
v_cellCount_1075_ = lean_unsigned_to_nat(16u);
v___x_1076_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_1075_);
return v___x_1076_;
}
}
static lean_object* _init_l_Lean_Core_transform___redArg___closed__2(void){
_start:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; 
v___x_1077_ = lean_obj_once(&l_Lean_Core_transform___redArg___closed__1, &l_Lean_Core_transform___redArg___closed__1_once, _init_l_Lean_Core_transform___redArg___closed__1);
v___x_1078_ = lean_obj_once(&l_Lean_Core_transform___redArg___closed__0, &l_Lean_Core_transform___redArg___closed__0_once, _init_l_Lean_Core_transform___redArg___closed__0);
v___x_1079_ = lean_unsigned_to_nat(0u);
v___x_1080_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1079_);
lean_ctor_set(v___x_1080_, 1, v___x_1078_);
lean_ctor_set(v___x_1080_, 2, v___x_1077_);
return v___x_1080_;
}
}
static lean_object* _init_l_Lean_Core_transform___redArg___closed__3(void){
_start:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1081_ = lean_obj_once(&l_Lean_Core_transform___redArg___closed__2, &l_Lean_Core_transform___redArg___closed__2_once, _init_l_Lean_Core_transform___redArg___closed__2);
v___x_1082_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1082_, 0, lean_box(0));
lean_closure_set(v___x_1082_, 1, lean_box(0));
lean_closure_set(v___x_1082_, 2, v___x_1081_);
return v___x_1082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___redArg(lean_object* v_inst_1083_, lean_object* v_inst_1084_, lean_object* v_inst_1085_, lean_object* v_input_1086_, lean_object* v_pre_1087_, lean_object* v_post_1088_){
_start:
{
lean_object* v_x_1089_; lean_object* v_toApplicative_1090_; lean_object* v_toBind_1091_; lean_object* v_toPure_1092_; lean_object* v_x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___f_1096_; lean_object* v___f_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; 
v_x_1089_ = lean_box(0);
v_toApplicative_1090_ = lean_ctor_get(v_inst_1083_, 0);
v_toBind_1091_ = lean_ctor_get(v_inst_1083_, 1);
lean_inc_n(v_toBind_1091_, 3);
v_toPure_1092_ = lean_ctor_get(v_toApplicative_1090_, 1);
lean_inc_n(v_toPure_1092_, 2);
lean_inc_n(v_inst_1084_, 2);
v_x_1093_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__1), 3, 1);
lean_closure_set(v_x_1093_, 0, v_inst_1084_);
v___x_1094_ = lean_obj_once(&l_Lean_Core_transform___redArg___closed__3, &l_Lean_Core_transform___redArg___closed__3_once, _init_l_Lean_Core_transform___redArg___closed__3);
v___x_1095_ = l_Lean_Core_transform___redArg___lam__1(v_inst_1084_, lean_box(0), v___x_1094_);
v___f_1096_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__2), 2, 1);
lean_closure_set(v___f_1096_, 0, v_toPure_1092_);
v___f_1097_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__5), 11, 10);
lean_closure_set(v___f_1097_, 0, v_toPure_1092_);
lean_closure_set(v___f_1097_, 1, v_x_1093_);
lean_closure_set(v___f_1097_, 2, v_toBind_1091_);
lean_closure_set(v___f_1097_, 3, v_inst_1083_);
lean_closure_set(v___f_1097_, 4, v_inst_1084_);
lean_closure_set(v___f_1097_, 5, v_inst_1085_);
lean_closure_set(v___f_1097_, 6, v_pre_1087_);
lean_closure_set(v___f_1097_, 7, v_post_1088_);
lean_closure_set(v___f_1097_, 8, v_x_1089_);
lean_closure_set(v___f_1097_, 9, v_input_1086_);
v___x_1098_ = lean_apply_4(v_toBind_1091_, lean_box(0), lean_box(0), v___x_1095_, v___f_1097_);
v___x_1099_ = lean_apply_4(v_toBind_1091_, lean_box(0), lean_box(0), v___x_1098_, v___f_1096_);
return v___x_1099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform(lean_object* v_m_1100_, lean_object* v_inst_1101_, lean_object* v_inst_1102_, lean_object* v_inst_1103_, lean_object* v_input_1104_, lean_object* v_pre_1105_, lean_object* v_post_1106_){
_start:
{
lean_object* v___x_1107_; 
v___x_1107_ = l_Lean_Core_transform___redArg(v_inst_1101_, v_inst_1102_, v_inst_1103_, v_input_1104_, v_pre_1105_, v_post_1106_);
return v___x_1107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_betaReduce___lam__0(lean_object* v_e_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_){
_start:
{
uint8_t v___x_1114_; uint8_t v___x_1115_; 
v___x_1114_ = 0;
v___x_1115_ = l_Lean_Expr_isHeadBetaTarget(v_e_1110_, v___x_1114_);
if (v___x_1115_ == 0)
{
lean_object* v___x_1116_; lean_object* v___x_1117_; 
lean_dec_ref(v_e_1110_);
v___x_1116_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_1117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1117_, 0, v___x_1116_);
return v___x_1117_;
}
else
{
lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1118_ = l_Lean_Expr_headBeta(v_e_1110_);
v___x_1119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1118_);
v___x_1120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1119_);
return v___x_1120_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_betaReduce___lam__0___boxed(lean_object* v_e_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_){
_start:
{
lean_object* v_res_1125_; 
v_res_1125_ = l_Lean_Core_betaReduce___lam__0(v_e_1121_, v___y_1122_, v___y_1123_);
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
return v_res_1125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_betaReduce___lam__1(lean_object* v_e_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_){
_start:
{
lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1130_, 0, v_e_1126_);
v___x_1131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1131_, 0, v___x_1130_);
return v___x_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_betaReduce___lam__1___boxed(lean_object* v_e_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_){
_start:
{
lean_object* v_res_1136_; 
v_res_1136_ = l_Lean_Core_betaReduce___lam__1(v_e_1132_, v___y_1133_, v___y_1134_);
lean_dec(v___y_1134_);
lean_dec_ref(v___y_1133_);
return v_res_1136_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1137_ = lean_box(0);
v___x_1138_ = l_Lean_interruptExceptionId;
v___x_1139_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1139_, 0, v___x_1138_);
lean_ctor_set(v___x_1139_, 1, v___x_1137_);
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___redArg(){
_start:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1141_ = lean_obj_once(&l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___redArg___closed__0, &l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___redArg___closed__0);
v___x_1142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1141_);
return v___x_1142_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___redArg___boxed(lean_object* v___y_1143_){
_start:
{
lean_object* v_res_1144_; 
v_res_1144_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___redArg();
return v_res_1144_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1150_ = l_Lean_maxRecDepthErrorMessage;
v___x_1151_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1151_, 0, v___x_1150_);
return v___x_1151_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___x_1152_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__3);
v___x_1153_ = l_Lean_MessageData_ofFormat(v___x_1152_);
return v___x_1153_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; 
v___x_1154_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__4);
v___x_1155_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__2));
v___x_1156_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1155_);
lean_ctor_set(v___x_1156_, 1, v___x_1154_);
return v___x_1156_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg(lean_object* v_ref_1157_){
_start:
{
lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; 
v___x_1159_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5);
v___x_1160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1160_, 0, v_ref_1157_);
lean_ctor_set(v___x_1160_, 1, v___x_1159_);
v___x_1161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1161_, 0, v___x_1160_);
return v___x_1161_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object* v_ref_1162_, lean_object* v___y_1163_){
_start:
{
lean_object* v_res_1164_; 
v_res_1164_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_1162_);
return v_res_1164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___redArg(lean_object* v_x_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_){
_start:
{
lean_object* v___y_1171_; lean_object* v___y_1181_; lean_object* v___y_1182_; lean_object* v___y_1183_; lean_object* v___y_1184_; lean_object* v___y_1185_; lean_object* v___y_1186_; lean_object* v___y_1187_; lean_object* v___y_1188_; uint8_t v___y_1189_; lean_object* v___y_1190_; lean_object* v___y_1191_; lean_object* v___y_1192_; lean_object* v___y_1193_; uint8_t v___y_1194_; lean_object* v___y_1195_; lean_object* v___y_1196_; lean_object* v_fileName_1201_; lean_object* v_fileMap_1202_; lean_object* v_options_1203_; lean_object* v_currRecDepth_1204_; lean_object* v_maxRecDepth_1205_; lean_object* v_ref_1206_; lean_object* v_currNamespace_1207_; lean_object* v_openDecls_1208_; lean_object* v_initHeartbeats_1209_; lean_object* v_maxHeartbeats_1210_; lean_object* v_quotContext_1211_; lean_object* v_currMacroScope_1212_; uint8_t v_diag_1213_; lean_object* v_cancelTk_x3f_1214_; uint8_t v_suppressElabErrors_1215_; lean_object* v_inheritedTraceOptions_1216_; 
v_fileName_1201_ = lean_ctor_get(v___y_1167_, 0);
v_fileMap_1202_ = lean_ctor_get(v___y_1167_, 1);
v_options_1203_ = lean_ctor_get(v___y_1167_, 2);
v_currRecDepth_1204_ = lean_ctor_get(v___y_1167_, 3);
v_maxRecDepth_1205_ = lean_ctor_get(v___y_1167_, 4);
v_ref_1206_ = lean_ctor_get(v___y_1167_, 5);
v_currNamespace_1207_ = lean_ctor_get(v___y_1167_, 6);
v_openDecls_1208_ = lean_ctor_get(v___y_1167_, 7);
v_initHeartbeats_1209_ = lean_ctor_get(v___y_1167_, 8);
v_maxHeartbeats_1210_ = lean_ctor_get(v___y_1167_, 9);
v_quotContext_1211_ = lean_ctor_get(v___y_1167_, 10);
v_currMacroScope_1212_ = lean_ctor_get(v___y_1167_, 11);
v_diag_1213_ = lean_ctor_get_uint8(v___y_1167_, sizeof(void*)*14);
v_cancelTk_x3f_1214_ = lean_ctor_get(v___y_1167_, 12);
v_suppressElabErrors_1215_ = lean_ctor_get_uint8(v___y_1167_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1216_ = lean_ctor_get(v___y_1167_, 13);
if (lean_obj_tag(v_cancelTk_x3f_1214_) == 1)
{
lean_object* v_val_1222_; uint8_t v___x_1223_; 
v_val_1222_ = lean_ctor_get(v_cancelTk_x3f_1214_, 0);
v___x_1223_ = l_IO_CancelToken_isSet(v_val_1222_);
if (v___x_1223_ == 0)
{
goto v___jp_1217_;
}
else
{
lean_object* v___x_1224_; lean_object* v_a_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1232_; 
lean_dec_ref(v_x_1165_);
v___x_1224_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___redArg();
v_a_1225_ = lean_ctor_get(v___x_1224_, 0);
v_isSharedCheck_1232_ = !lean_is_exclusive(v___x_1224_);
if (v_isSharedCheck_1232_ == 0)
{
v___x_1227_ = v___x_1224_;
v_isShared_1228_ = v_isSharedCheck_1232_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_a_1225_);
lean_dec(v___x_1224_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1232_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v___x_1230_; 
if (v_isShared_1228_ == 0)
{
v___x_1230_ = v___x_1227_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v_a_1225_);
v___x_1230_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
return v___x_1230_;
}
}
}
}
else
{
goto v___jp_1217_;
}
v___jp_1170_:
{
if (lean_obj_tag(v___y_1171_) == 0)
{
return v___y_1171_;
}
else
{
lean_object* v_a_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1179_; 
v_a_1172_ = lean_ctor_get(v___y_1171_, 0);
v_isSharedCheck_1179_ = !lean_is_exclusive(v___y_1171_);
if (v_isSharedCheck_1179_ == 0)
{
v___x_1174_ = v___y_1171_;
v_isShared_1175_ = v_isSharedCheck_1179_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_a_1172_);
lean_dec(v___y_1171_);
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
v_reuseFailAlloc_1178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v_a_1172_);
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
v___jp_1180_:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1197_ = lean_unsigned_to_nat(1u);
v___x_1198_ = lean_nat_add(v___y_1186_, v___x_1197_);
lean_inc_ref(v___y_1195_);
lean_inc(v___y_1185_);
lean_inc(v___y_1182_);
lean_inc(v___y_1192_);
lean_inc(v___y_1188_);
lean_inc(v___y_1181_);
lean_inc(v___y_1193_);
lean_inc(v___y_1191_);
lean_inc(v___y_1184_);
lean_inc_ref(v___y_1196_);
lean_inc_ref(v___y_1183_);
lean_inc_ref(v___y_1187_);
v___x_1199_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1199_, 0, v___y_1187_);
lean_ctor_set(v___x_1199_, 1, v___y_1183_);
lean_ctor_set(v___x_1199_, 2, v___y_1196_);
lean_ctor_set(v___x_1199_, 3, v___x_1198_);
lean_ctor_set(v___x_1199_, 4, v___y_1184_);
lean_ctor_set(v___x_1199_, 5, v___y_1190_);
lean_ctor_set(v___x_1199_, 6, v___y_1191_);
lean_ctor_set(v___x_1199_, 7, v___y_1193_);
lean_ctor_set(v___x_1199_, 8, v___y_1181_);
lean_ctor_set(v___x_1199_, 9, v___y_1188_);
lean_ctor_set(v___x_1199_, 10, v___y_1192_);
lean_ctor_set(v___x_1199_, 11, v___y_1182_);
lean_ctor_set(v___x_1199_, 12, v___y_1185_);
lean_ctor_set(v___x_1199_, 13, v___y_1195_);
lean_ctor_set_uint8(v___x_1199_, sizeof(void*)*14, v___y_1189_);
lean_ctor_set_uint8(v___x_1199_, sizeof(void*)*14 + 1, v___y_1194_);
lean_inc(v___y_1168_);
lean_inc(v___y_1166_);
v___x_1200_ = lean_apply_4(v_x_1165_, v___y_1166_, v___x_1199_, v___y_1168_, lean_box(0));
v___y_1171_ = v___x_1200_;
goto v___jp_1170_;
}
v___jp_1217_:
{
lean_object* v___x_1218_; uint8_t v___x_1219_; 
v___x_1218_ = lean_unsigned_to_nat(0u);
v___x_1219_ = lean_nat_dec_eq(v_maxRecDepth_1205_, v___x_1218_);
if (v___x_1219_ == 0)
{
uint8_t v___x_1220_; 
v___x_1220_ = lean_nat_dec_eq(v_currRecDepth_1204_, v_maxRecDepth_1205_);
if (v___x_1220_ == 0)
{
lean_inc(v_ref_1206_);
v___y_1181_ = v_initHeartbeats_1209_;
v___y_1182_ = v_currMacroScope_1212_;
v___y_1183_ = v_fileMap_1202_;
v___y_1184_ = v_maxRecDepth_1205_;
v___y_1185_ = v_cancelTk_x3f_1214_;
v___y_1186_ = v_currRecDepth_1204_;
v___y_1187_ = v_fileName_1201_;
v___y_1188_ = v_maxHeartbeats_1210_;
v___y_1189_ = v_diag_1213_;
v___y_1190_ = v_ref_1206_;
v___y_1191_ = v_currNamespace_1207_;
v___y_1192_ = v_quotContext_1211_;
v___y_1193_ = v_openDecls_1208_;
v___y_1194_ = v_suppressElabErrors_1215_;
v___y_1195_ = v_inheritedTraceOptions_1216_;
v___y_1196_ = v_options_1203_;
goto v___jp_1180_;
}
else
{
lean_object* v___x_1221_; 
lean_dec_ref(v_x_1165_);
lean_inc(v_ref_1206_);
v___x_1221_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_1206_);
v___y_1171_ = v___x_1221_;
goto v___jp_1170_;
}
}
else
{
lean_inc(v_ref_1206_);
v___y_1181_ = v_initHeartbeats_1209_;
v___y_1182_ = v_currMacroScope_1212_;
v___y_1183_ = v_fileMap_1202_;
v___y_1184_ = v_maxRecDepth_1205_;
v___y_1185_ = v_cancelTk_x3f_1214_;
v___y_1186_ = v_currRecDepth_1204_;
v___y_1187_ = v_fileName_1201_;
v___y_1188_ = v_maxHeartbeats_1210_;
v___y_1189_ = v_diag_1213_;
v___y_1190_ = v_ref_1206_;
v___y_1191_ = v_currNamespace_1207_;
v___y_1192_ = v_quotContext_1211_;
v___y_1193_ = v_openDecls_1208_;
v___y_1194_ = v_suppressElabErrors_1215_;
v___y_1195_ = v_inheritedTraceOptions_1216_;
v___y_1196_ = v_options_1203_;
goto v___jp_1180_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___redArg___boxed(lean_object* v_x_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_){
_start:
{
lean_object* v_res_1238_; 
v_res_1238_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___redArg(v_x_1233_, v___y_1234_, v___y_1235_, v___y_1236_);
lean_dec(v___y_1236_);
lean_dec_ref(v___y_1235_);
lean_dec(v___y_1234_);
return v_res_1238_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_1239_, lean_object* v_x_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_){
_start:
{
lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1244_ = lean_apply_1(v_x_1240_, lean_box(0));
v___x_1245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1245_, 0, v___x_1244_);
return v___x_1245_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_1246_, lean_object* v_x_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_){
_start:
{
lean_object* v_res_1251_; 
v_res_1251_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__0(v_00_u03b1_1246_, v_x_1247_, v___y_1248_, v___y_1249_);
lean_dec(v___y_1249_);
lean_dec_ref(v___y_1248_);
return v_res_1251_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___redArg(lean_object* v_m_1252_, lean_object* v_query_1253_, lean_object* v_x_1254_, lean_object* v_x_1255_, lean_object* v_x_1256_){
_start:
{
lean_object* v_zero_1257_; uint8_t v_isZero_1258_; 
v_zero_1257_ = lean_unsigned_to_nat(0u);
v_isZero_1258_ = lean_nat_dec_eq(v_x_1255_, v_zero_1257_);
if (v_isZero_1258_ == 1)
{
lean_dec(v_x_1256_);
lean_dec(v_x_1255_);
if (lean_obj_tag(v_x_1254_) == 0)
{
lean_object* v___x_1259_; 
v___x_1259_ = lean_box(2);
return v___x_1259_;
}
else
{
lean_object* v_val_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1267_; 
v_val_1260_ = lean_ctor_get(v_x_1254_, 0);
v_isSharedCheck_1267_ = !lean_is_exclusive(v_x_1254_);
if (v_isSharedCheck_1267_ == 0)
{
v___x_1262_ = v_x_1254_;
v_isShared_1263_ = v_isSharedCheck_1267_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_val_1260_);
lean_dec(v_x_1254_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1267_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v___x_1265_; 
if (v_isShared_1263_ == 0)
{
v___x_1265_ = v___x_1262_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v_val_1260_);
v___x_1265_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
return v___x_1265_;
}
}
}
}
else
{
lean_object* v_keyArray_1268_; lean_object* v_valueArray_1269_; lean_object* v___x_1270_; uint8_t v_isSome_1271_; 
v_keyArray_1268_ = lean_ctor_get(v_m_1252_, 1);
v_valueArray_1269_ = lean_ctor_get(v_m_1252_, 2);
v___x_1270_ = lean_array_fget_borrowed(v_keyArray_1268_, v_x_1256_);
v_isSome_1271_ = lean_noption_is_some(v___x_1270_);
if (v_isSome_1271_ == 0)
{
lean_dec(v_x_1255_);
if (lean_obj_tag(v_x_1254_) == 0)
{
lean_object* v___x_1272_; 
v___x_1272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1272_, 0, v_x_1256_);
return v___x_1272_;
}
else
{
lean_object* v_val_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1280_; 
lean_dec(v_x_1256_);
v_val_1273_ = lean_ctor_get(v_x_1254_, 0);
v_isSharedCheck_1280_ = !lean_is_exclusive(v_x_1254_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1275_ = v_x_1254_;
v_isShared_1276_ = v_isSharedCheck_1280_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_val_1273_);
lean_dec(v_x_1254_);
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
v_reuseFailAlloc_1279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v_val_1273_);
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
else
{
lean_object* v_one_1281_; lean_object* v_n_1282_; lean_object* v___y_1284_; 
v_one_1281_ = lean_unsigned_to_nat(1u);
v_n_1282_ = lean_nat_sub(v_x_1255_, v_one_1281_);
lean_dec(v_x_1255_);
if (v_isSome_1271_ == 0)
{
goto v___jp_1290_;
}
else
{
lean_object* v___x_1292_; uint8_t v_isSome_1293_; 
v___x_1292_ = lean_array_fget_borrowed(v_valueArray_1269_, v_x_1256_);
v_isSome_1293_ = lean_noption_is_some(v___x_1292_);
if (v_isSome_1293_ == 0)
{
goto v___jp_1290_;
}
else
{
lean_object* v_val_1294_; uint8_t v___x_1295_; 
lean_inc(v___x_1270_);
v_val_1294_ = lean_noption_get(v___x_1270_);
v___x_1295_ = l_Lean_ExprStructEq_beq(v_val_1294_, v_query_1253_);
if (v___x_1295_ == 0)
{
lean_object* v___x_1296_; lean_object* v___x_1297_; uint8_t v___x_1298_; 
lean_dec(v_val_1294_);
v___x_1296_ = lean_array_get_size(v_keyArray_1268_);
v___x_1297_ = lean_nat_add(v_x_1256_, v_one_1281_);
lean_dec(v_x_1256_);
v___x_1298_ = lean_nat_dec_lt(v___x_1297_, v___x_1296_);
if (v___x_1298_ == 0)
{
lean_dec(v___x_1297_);
v_x_1255_ = v_n_1282_;
v_x_1256_ = v_zero_1257_;
goto _start;
}
else
{
v_x_1255_ = v_n_1282_;
v_x_1256_ = v___x_1297_;
goto _start;
}
}
else
{
lean_object* v_val_1301_; lean_object* v___x_1302_; 
lean_dec(v_n_1282_);
lean_dec(v_x_1254_);
lean_inc(v___x_1292_);
v_val_1301_ = lean_noption_get(v___x_1292_);
v___x_1302_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1302_, 0, v_x_1256_);
lean_ctor_set(v___x_1302_, 1, v_val_1294_);
lean_ctor_set(v___x_1302_, 2, v_val_1301_);
return v___x_1302_;
}
}
}
v___jp_1283_:
{
lean_object* v___x_1285_; lean_object* v___x_1286_; uint8_t v___x_1287_; 
v___x_1285_ = lean_array_get_size(v_keyArray_1268_);
v___x_1286_ = lean_nat_add(v_x_1256_, v_one_1281_);
lean_dec(v_x_1256_);
v___x_1287_ = lean_nat_dec_lt(v___x_1286_, v___x_1285_);
if (v___x_1287_ == 0)
{
lean_dec(v___x_1286_);
v_x_1254_ = v___y_1284_;
v_x_1255_ = v_n_1282_;
v_x_1256_ = v_zero_1257_;
goto _start;
}
else
{
v_x_1254_ = v___y_1284_;
v_x_1255_ = v_n_1282_;
v_x_1256_ = v___x_1286_;
goto _start;
}
}
v___jp_1290_:
{
if (lean_obj_tag(v_x_1254_) == 0)
{
lean_object* v___x_1291_; 
lean_inc(v_x_1256_);
v___x_1291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1291_, 0, v_x_1256_);
v___y_1284_ = v___x_1291_;
goto v___jp_1283_;
}
else
{
v___y_1284_ = v_x_1254_;
goto v___jp_1283_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___redArg___boxed(lean_object* v_m_1303_, lean_object* v_query_1304_, lean_object* v_x_1305_, lean_object* v_x_1306_, lean_object* v_x_1307_){
_start:
{
lean_object* v_res_1308_; 
v_res_1308_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___redArg(v_m_1303_, v_query_1304_, v_x_1305_, v_x_1306_, v_x_1307_);
lean_dec_ref(v_query_1304_);
lean_dec_ref(v_m_1303_);
return v_res_1308_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6___redArg(lean_object* v_m_1309_, lean_object* v_query_1310_){
_start:
{
lean_object* v_keyArray_1311_; lean_object* v___x_1312_; uint64_t v___x_1313_; uint64_t v___x_1314_; uint64_t v___x_1315_; uint64_t v_fold_1316_; uint64_t v___x_1317_; uint64_t v___x_1318_; uint64_t v___x_1319_; size_t v___x_1320_; size_t v___x_1321_; size_t v___x_1322_; size_t v___x_1323_; size_t v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; 
v_keyArray_1311_ = lean_ctor_get(v_m_1309_, 1);
v___x_1312_ = lean_array_get_size(v_keyArray_1311_);
v___x_1313_ = l_Lean_ExprStructEq_hash(v_query_1310_);
v___x_1314_ = 32ULL;
v___x_1315_ = lean_uint64_shift_right(v___x_1313_, v___x_1314_);
v_fold_1316_ = lean_uint64_xor(v___x_1313_, v___x_1315_);
v___x_1317_ = 16ULL;
v___x_1318_ = lean_uint64_shift_right(v_fold_1316_, v___x_1317_);
v___x_1319_ = lean_uint64_xor(v_fold_1316_, v___x_1318_);
v___x_1320_ = lean_uint64_to_usize(v___x_1319_);
v___x_1321_ = lean_usize_of_nat(v___x_1312_);
v___x_1322_ = ((size_t)1ULL);
v___x_1323_ = lean_usize_sub(v___x_1321_, v___x_1322_);
v___x_1324_ = lean_usize_land(v___x_1320_, v___x_1323_);
v___x_1325_ = lean_usize_to_nat(v___x_1324_);
v___x_1326_ = lean_box(0);
v___x_1327_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___redArg(v_m_1309_, v_query_1310_, v___x_1326_, v___x_1312_, v___x_1325_);
return v___x_1327_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6___redArg___boxed(lean_object* v_m_1328_, lean_object* v_query_1329_){
_start:
{
lean_object* v_res_1330_; 
v_res_1330_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6___redArg(v_m_1328_, v_query_1329_);
lean_dec_ref(v_query_1329_);
lean_dec_ref(v_m_1328_);
return v_res_1330_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___redArg(lean_object* v_m_1331_, lean_object* v_query_1332_){
_start:
{
lean_object* v___x_1333_; 
v___x_1333_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6___redArg(v_m_1331_, v_query_1332_);
if (lean_obj_tag(v___x_1333_) == 0)
{
lean_object* v_index_1334_; lean_object* v_key_1335_; lean_object* v_value_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1343_; 
v_index_1334_ = lean_ctor_get(v___x_1333_, 0);
v_key_1335_ = lean_ctor_get(v___x_1333_, 1);
v_value_1336_ = lean_ctor_get(v___x_1333_, 2);
v_isSharedCheck_1343_ = !lean_is_exclusive(v___x_1333_);
if (v_isSharedCheck_1343_ == 0)
{
v___x_1338_ = v___x_1333_;
v_isShared_1339_ = v_isSharedCheck_1343_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_value_1336_);
lean_inc(v_key_1335_);
lean_inc(v_index_1334_);
lean_dec(v___x_1333_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1343_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
lean_object* v___x_1341_; 
if (v_isShared_1339_ == 0)
{
v___x_1341_ = v___x_1338_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v_index_1334_);
lean_ctor_set(v_reuseFailAlloc_1342_, 1, v_key_1335_);
lean_ctor_set(v_reuseFailAlloc_1342_, 2, v_value_1336_);
v___x_1341_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
return v___x_1341_;
}
}
}
else
{
lean_object* v___x_1344_; 
lean_dec(v___x_1333_);
v___x_1344_ = lean_box(1);
return v___x_1344_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___redArg___boxed(lean_object* v_m_1345_, lean_object* v_query_1346_){
_start:
{
lean_object* v_res_1347_; 
v_res_1347_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___redArg(v_m_1345_, v_query_1346_);
lean_dec_ref(v_query_1346_);
lean_dec_ref(v_m_1345_);
return v_res_1347_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg(lean_object* v_m_1348_, lean_object* v_a_1349_){
_start:
{
lean_object* v___x_1350_; 
v___x_1350_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___redArg(v_m_1348_, v_a_1349_);
if (lean_obj_tag(v___x_1350_) == 0)
{
lean_object* v_value_1351_; lean_object* v___x_1352_; 
v_value_1351_ = lean_ctor_get(v___x_1350_, 2);
lean_inc(v_value_1351_);
lean_dec_ref_known(v___x_1350_, 3);
v___x_1352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1352_, 0, v_value_1351_);
return v___x_1352_;
}
else
{
lean_object* v___x_1353_; 
v___x_1353_ = lean_box(0);
return v___x_1353_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_m_1354_, lean_object* v_a_1355_){
_start:
{
lean_object* v_res_1356_; 
v_res_1356_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg(v_m_1354_, v_a_1355_);
lean_dec_ref(v_a_1355_);
lean_dec_ref(v_m_1354_);
return v_res_1356_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__7_spec__12_spec__13___redArg(lean_object* v_b_1357_, lean_object* v_acc_1358_, lean_object* v_i_1359_){
_start:
{
lean_object* v___y_1361_; lean_object* v_keyArray_1369_; lean_object* v_valueArray_1370_; lean_object* v___x_1371_; uint8_t v___x_1372_; 
v_keyArray_1369_ = lean_ctor_get(v_b_1357_, 1);
v_valueArray_1370_ = lean_ctor_get(v_b_1357_, 2);
v___x_1371_ = lean_array_get_size(v_keyArray_1369_);
v___x_1372_ = lean_nat_dec_lt(v_i_1359_, v___x_1371_);
if (v___x_1372_ == 0)
{
lean_dec(v_i_1359_);
return v_acc_1358_;
}
else
{
lean_object* v___x_1373_; uint8_t v_isSome_1374_; 
v___x_1373_ = lean_array_fget_borrowed(v_keyArray_1369_, v_i_1359_);
v_isSome_1374_ = lean_noption_is_some(v___x_1373_);
if (v_isSome_1374_ == 0)
{
goto v___jp_1365_;
}
else
{
lean_object* v___x_1375_; uint8_t v_isSome_1376_; 
v___x_1375_ = lean_array_fget_borrowed(v_valueArray_1370_, v_i_1359_);
v_isSome_1376_ = lean_noption_is_some(v___x_1375_);
if (v_isSome_1376_ == 0)
{
goto v___jp_1365_;
}
else
{
lean_object* v_val_1377_; lean_object* v_val_1378_; lean_object* v_i_1380_; lean_object* v___x_1385_; 
lean_inc(v___x_1373_);
v_val_1377_ = lean_noption_get(v___x_1373_);
lean_inc(v___x_1375_);
v_val_1378_ = lean_noption_get(v___x_1375_);
v___x_1385_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6___redArg(v_acc_1358_, v_val_1377_);
switch(lean_obj_tag(v___x_1385_))
{
case 0:
{
lean_object* v_index_1386_; lean_object* v_size_1387_; lean_object* v___x_1388_; 
v_index_1386_ = lean_ctor_get(v___x_1385_, 0);
lean_inc(v_index_1386_);
lean_dec_ref_known(v___x_1385_, 3);
v_size_1387_ = lean_ctor_get(v_acc_1358_, 0);
lean_inc(v_size_1387_);
v___x_1388_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_1358_, v_size_1387_, v_index_1386_, v_val_1377_, v_val_1378_);
lean_dec(v_index_1386_);
v___y_1361_ = v___x_1388_;
goto v___jp_1360_;
}
case 1:
{
lean_object* v_index_1389_; 
v_index_1389_ = lean_ctor_get(v___x_1385_, 0);
lean_inc(v_index_1389_);
lean_dec_ref_known(v___x_1385_, 1);
v_i_1380_ = v_index_1389_;
goto v___jp_1379_;
}
default: 
{
lean_object* v___x_1390_; lean_object* v___x_1391_; 
v___x_1390_ = lean_unsigned_to_nat(0u);
v___x_1391_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_1358_, v___x_1390_);
if (lean_obj_tag(v___x_1391_) == 0)
{
lean_object* v_index_1392_; 
v_index_1392_ = lean_ctor_get(v___x_1391_, 0);
lean_inc(v_index_1392_);
lean_dec_ref_known(v___x_1391_, 1);
v_i_1380_ = v_index_1392_;
goto v___jp_1379_;
}
else
{
lean_dec(v_val_1378_);
lean_dec(v_val_1377_);
v___y_1361_ = v_acc_1358_;
goto v___jp_1360_;
}
}
}
v___jp_1379_:
{
lean_object* v_size_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; 
v_size_1381_ = lean_ctor_get(v_acc_1358_, 0);
v___x_1382_ = lean_unsigned_to_nat(1u);
v___x_1383_ = lean_nat_add(v_size_1381_, v___x_1382_);
v___x_1384_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_1358_, v___x_1383_, v_i_1380_, v_val_1377_, v_val_1378_);
lean_dec(v_i_1380_);
v___y_1361_ = v___x_1384_;
goto v___jp_1360_;
}
}
}
}
v___jp_1360_:
{
lean_object* v___x_1362_; lean_object* v___x_1363_; 
v___x_1362_ = lean_unsigned_to_nat(1u);
v___x_1363_ = lean_nat_add(v_i_1359_, v___x_1362_);
lean_dec(v_i_1359_);
v_acc_1358_ = v___y_1361_;
v_i_1359_ = v___x_1363_;
goto _start;
}
v___jp_1365_:
{
lean_object* v___x_1366_; lean_object* v___x_1367_; 
v___x_1366_ = lean_unsigned_to_nat(1u);
v___x_1367_ = lean_nat_add(v_i_1359_, v___x_1366_);
lean_dec(v_i_1359_);
v_i_1359_ = v___x_1367_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__7_spec__12_spec__13___redArg___boxed(lean_object* v_b_1393_, lean_object* v_acc_1394_, lean_object* v_i_1395_){
_start:
{
lean_object* v_res_1396_; 
v_res_1396_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__7_spec__12_spec__13___redArg(v_b_1393_, v_acc_1394_, v_i_1395_);
lean_dec_ref(v_b_1393_);
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__7_spec__12___redArg(lean_object* v_init_1397_, lean_object* v_b_1398_){
_start:
{
lean_object* v___x_1399_; lean_object* v___x_1400_; 
v___x_1399_ = lean_unsigned_to_nat(0u);
v___x_1400_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__7_spec__12_spec__13___redArg(v_b_1398_, v_init_1397_, v___x_1399_);
return v___x_1400_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__7_spec__12___redArg___boxed(lean_object* v_init_1401_, lean_object* v_b_1402_){
_start:
{
lean_object* v_res_1403_; 
v_res_1403_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__7_spec__12___redArg(v_init_1401_, v_b_1402_);
lean_dec_ref(v_b_1402_);
return v_res_1403_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__7___redArg(lean_object* v_m_1404_){
_start:
{
lean_object* v_keyArray_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v_cellCount_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v_target_1412_; lean_object* v___x_1413_; 
v_keyArray_1405_ = lean_ctor_get(v_m_1404_, 1);
v___x_1406_ = lean_array_get_size(v_keyArray_1405_);
v___x_1407_ = lean_unsigned_to_nat(2u);
v_cellCount_1408_ = lean_nat_mul(v___x_1406_, v___x_1407_);
v___x_1409_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_1408_);
v___x_1410_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1408_);
v___x_1411_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_1408_);
v_target_1412_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_1412_, 0, v___x_1409_);
lean_ctor_set(v_target_1412_, 1, v___x_1410_);
lean_ctor_set(v_target_1412_, 2, v___x_1411_);
v___x_1413_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__7_spec__12___redArg(v_target_1412_, v_m_1404_);
return v___x_1413_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__7___redArg___boxed(lean_object* v_m_1414_){
_start:
{
lean_object* v_res_1415_; 
v_res_1415_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__7___redArg(v_m_1414_);
lean_dec_ref(v_m_1414_);
return v_res_1415_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__2(lean_object* v_a_1416_, lean_object* v_e_1417_, lean_object* v_a_1418_){
_start:
{
lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___y_1423_; lean_object* v___y_1426_; lean_object* v_i_1427_; lean_object* v___y_1443_; lean_object* v_i_1444_; lean_object* v___y_1450_; lean_object* v___x_1459_; 
v___x_1420_ = lean_st_ref_take(v_a_1416_);
v___x_1421_ = lean_box(0);
v___x_1459_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6___redArg(v___x_1420_, v_e_1417_);
switch(lean_obj_tag(v___x_1459_))
{
case 0:
{
lean_object* v_index_1460_; lean_object* v_size_1461_; lean_object* v___x_1462_; 
v_index_1460_ = lean_ctor_get(v___x_1459_, 0);
lean_inc(v_index_1460_);
lean_dec_ref_known(v___x_1459_, 3);
v_size_1461_ = lean_ctor_get(v___x_1420_, 0);
lean_inc(v_size_1461_);
v___x_1462_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1420_, v_size_1461_, v_index_1460_, v_e_1417_, v_a_1418_);
lean_dec(v_index_1460_);
v___y_1423_ = v___x_1462_;
goto v___jp_1422_;
}
case 1:
{
lean_object* v_index_1463_; lean_object* v_size_1464_; lean_object* v_keyArray_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; uint8_t v___x_1469_; 
v_index_1463_ = lean_ctor_get(v___x_1459_, 0);
lean_inc(v_index_1463_);
lean_dec_ref_known(v___x_1459_, 1);
v_size_1464_ = lean_ctor_get(v___x_1420_, 0);
lean_inc(v_size_1464_);
v_keyArray_1465_ = lean_ctor_get(v___x_1420_, 1);
lean_inc_ref(v_keyArray_1465_);
v___x_1466_ = lean_unsigned_to_nat(1u);
v___x_1467_ = lean_nat_add(v_size_1464_, v___x_1466_);
lean_dec(v_size_1464_);
v___x_1468_ = lean_array_get_size(v_keyArray_1465_);
lean_dec_ref(v_keyArray_1465_);
v___x_1469_ = lean_nat_dec_lt(v___x_1467_, v___x_1468_);
if (v___x_1469_ == 0)
{
lean_dec(v___x_1467_);
lean_dec(v_index_1463_);
goto v___jp_1432_;
}
else
{
lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; uint8_t v___x_1474_; 
v___x_1470_ = lean_unsigned_to_nat(4u);
v___x_1471_ = lean_nat_mul(v___x_1467_, v___x_1470_);
v___x_1472_ = lean_unsigned_to_nat(3u);
v___x_1473_ = lean_nat_mul(v___x_1468_, v___x_1472_);
v___x_1474_ = lean_nat_dec_le(v___x_1471_, v___x_1473_);
lean_dec(v___x_1473_);
lean_dec(v___x_1471_);
if (v___x_1474_ == 0)
{
lean_dec(v___x_1467_);
lean_dec(v_index_1463_);
goto v___jp_1432_;
}
else
{
lean_object* v___x_1475_; 
v___x_1475_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1420_, v___x_1467_, v_index_1463_, v_e_1417_, v_a_1418_);
lean_dec(v_index_1463_);
v___y_1423_ = v___x_1475_;
goto v___jp_1422_;
}
}
}
default: 
{
lean_object* v_size_1476_; lean_object* v_keyArray_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; uint8_t v___x_1481_; 
v_size_1476_ = lean_ctor_get(v___x_1420_, 0);
lean_inc(v_size_1476_);
v_keyArray_1477_ = lean_ctor_get(v___x_1420_, 1);
lean_inc_ref(v_keyArray_1477_);
v___x_1478_ = lean_unsigned_to_nat(1u);
v___x_1479_ = lean_nat_add(v_size_1476_, v___x_1478_);
lean_dec(v_size_1476_);
v___x_1480_ = lean_array_get_size(v_keyArray_1477_);
lean_dec_ref(v_keyArray_1477_);
v___x_1481_ = lean_nat_dec_lt(v___x_1479_, v___x_1480_);
if (v___x_1481_ == 0)
{
lean_object* v___x_1482_; 
lean_dec(v___x_1479_);
v___x_1482_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__7___redArg(v___x_1420_);
lean_dec(v___x_1420_);
v___y_1450_ = v___x_1482_;
goto v___jp_1449_;
}
else
{
lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; uint8_t v___x_1487_; 
v___x_1483_ = lean_unsigned_to_nat(4u);
v___x_1484_ = lean_nat_mul(v___x_1479_, v___x_1483_);
lean_dec(v___x_1479_);
v___x_1485_ = lean_unsigned_to_nat(3u);
v___x_1486_ = lean_nat_mul(v___x_1480_, v___x_1485_);
v___x_1487_ = lean_nat_dec_le(v___x_1484_, v___x_1486_);
lean_dec(v___x_1486_);
lean_dec(v___x_1484_);
if (v___x_1487_ == 0)
{
lean_object* v___x_1488_; 
v___x_1488_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__7___redArg(v___x_1420_);
lean_dec(v___x_1420_);
v___y_1450_ = v___x_1488_;
goto v___jp_1449_;
}
else
{
v___y_1450_ = v___x_1420_;
goto v___jp_1449_;
}
}
}
}
v___jp_1422_:
{
lean_object* v___x_1424_; 
v___x_1424_ = lean_st_ref_put(v_a_1416_, v___y_1423_);
return v___x_1421_;
}
v___jp_1425_:
{
lean_object* v_size_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; 
v_size_1428_ = lean_ctor_get(v___y_1426_, 0);
v___x_1429_ = lean_unsigned_to_nat(1u);
v___x_1430_ = lean_nat_add(v_size_1428_, v___x_1429_);
v___x_1431_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1426_, v___x_1430_, v_i_1427_, v_e_1417_, v_a_1418_);
lean_dec(v_i_1427_);
v___y_1423_ = v___x_1431_;
goto v___jp_1422_;
}
v___jp_1432_:
{
lean_object* v___x_1433_; lean_object* v___x_1434_; 
v___x_1433_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__7___redArg(v___x_1420_);
lean_dec(v___x_1420_);
v___x_1434_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6___redArg(v___x_1433_, v_e_1417_);
switch(lean_obj_tag(v___x_1434_))
{
case 0:
{
lean_object* v_index_1435_; lean_object* v_size_1436_; lean_object* v___x_1437_; 
v_index_1435_ = lean_ctor_get(v___x_1434_, 0);
lean_inc(v_index_1435_);
lean_dec_ref_known(v___x_1434_, 3);
v_size_1436_ = lean_ctor_get(v___x_1433_, 0);
lean_inc(v_size_1436_);
v___x_1437_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1433_, v_size_1436_, v_index_1435_, v_e_1417_, v_a_1418_);
lean_dec(v_index_1435_);
v___y_1423_ = v___x_1437_;
goto v___jp_1422_;
}
case 1:
{
lean_object* v_index_1438_; 
v_index_1438_ = lean_ctor_get(v___x_1434_, 0);
lean_inc(v_index_1438_);
lean_dec_ref_known(v___x_1434_, 1);
v___y_1426_ = v___x_1433_;
v_i_1427_ = v_index_1438_;
goto v___jp_1425_;
}
default: 
{
lean_object* v___x_1439_; lean_object* v___x_1440_; 
v___x_1439_ = lean_unsigned_to_nat(0u);
v___x_1440_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1433_, v___x_1439_);
if (lean_obj_tag(v___x_1440_) == 0)
{
lean_object* v_index_1441_; 
v_index_1441_ = lean_ctor_get(v___x_1440_, 0);
lean_inc(v_index_1441_);
lean_dec_ref_known(v___x_1440_, 1);
v___y_1426_ = v___x_1433_;
v_i_1427_ = v_index_1441_;
goto v___jp_1425_;
}
else
{
lean_dec_ref(v_a_1418_);
lean_dec_ref(v_e_1417_);
v___y_1423_ = v___x_1433_;
goto v___jp_1422_;
}
}
}
}
v___jp_1442_:
{
lean_object* v_size_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; 
v_size_1445_ = lean_ctor_get(v___y_1443_, 0);
v___x_1446_ = lean_unsigned_to_nat(1u);
v___x_1447_ = lean_nat_add(v_size_1445_, v___x_1446_);
v___x_1448_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1443_, v___x_1447_, v_i_1444_, v_e_1417_, v_a_1418_);
lean_dec(v_i_1444_);
v___y_1423_ = v___x_1448_;
goto v___jp_1422_;
}
v___jp_1449_:
{
lean_object* v___x_1451_; 
v___x_1451_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6___redArg(v___y_1450_, v_e_1417_);
switch(lean_obj_tag(v___x_1451_))
{
case 0:
{
lean_object* v_index_1452_; lean_object* v_size_1453_; lean_object* v___x_1454_; 
v_index_1452_ = lean_ctor_get(v___x_1451_, 0);
lean_inc(v_index_1452_);
lean_dec_ref_known(v___x_1451_, 3);
v_size_1453_ = lean_ctor_get(v___y_1450_, 0);
lean_inc(v_size_1453_);
v___x_1454_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1450_, v_size_1453_, v_index_1452_, v_e_1417_, v_a_1418_);
lean_dec(v_index_1452_);
v___y_1423_ = v___x_1454_;
goto v___jp_1422_;
}
case 1:
{
lean_object* v_index_1455_; 
v_index_1455_ = lean_ctor_get(v___x_1451_, 0);
lean_inc(v_index_1455_);
lean_dec_ref_known(v___x_1451_, 1);
v___y_1443_ = v___y_1450_;
v_i_1444_ = v_index_1455_;
goto v___jp_1442_;
}
default: 
{
lean_object* v___x_1456_; lean_object* v___x_1457_; 
v___x_1456_ = lean_unsigned_to_nat(0u);
v___x_1457_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1450_, v___x_1456_);
if (lean_obj_tag(v___x_1457_) == 0)
{
lean_object* v_index_1458_; 
v_index_1458_ = lean_ctor_get(v___x_1457_, 0);
lean_inc(v_index_1458_);
lean_dec_ref_known(v___x_1457_, 1);
v___y_1443_ = v___y_1450_;
v_i_1444_ = v_index_1458_;
goto v___jp_1442_;
}
else
{
lean_dec_ref(v_a_1418_);
lean_dec_ref(v_e_1417_);
v___y_1423_ = v___y_1450_;
goto v___jp_1422_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__2___boxed(lean_object* v_a_1489_, lean_object* v_e_1490_, lean_object* v_a_1491_, lean_object* v___y_1492_){
_start:
{
lean_object* v_res_1493_; 
v_res_1493_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__2(v_a_1489_, v_e_1490_, v_a_1491_);
lean_dec(v_a_1489_);
return v_res_1493_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1(lean_object* v_pre_1494_, lean_object* v_post_1495_, size_t v_sz_1496_, size_t v_i_1497_, lean_object* v_bs_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_){
_start:
{
uint8_t v___x_1503_; 
v___x_1503_ = lean_usize_dec_lt(v_i_1497_, v_sz_1496_);
if (v___x_1503_ == 0)
{
lean_object* v___x_1504_; 
lean_dec_ref(v_post_1495_);
lean_dec_ref(v_pre_1494_);
v___x_1504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1504_, 0, v_bs_1498_);
return v___x_1504_;
}
else
{
lean_object* v_v_1505_; lean_object* v___x_1506_; 
v_v_1505_ = lean_array_uget_borrowed(v_bs_1498_, v_i_1497_);
lean_inc(v_v_1505_);
lean_inc_ref(v_post_1495_);
lean_inc_ref(v_pre_1494_);
v___x_1506_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1494_, v_post_1495_, v_v_1505_, v___y_1499_, v___y_1500_, v___y_1501_);
if (lean_obj_tag(v___x_1506_) == 0)
{
lean_object* v_a_1507_; lean_object* v___x_1508_; lean_object* v_bs_x27_1509_; size_t v___x_1510_; size_t v___x_1511_; lean_object* v___x_1512_; 
v_a_1507_ = lean_ctor_get(v___x_1506_, 0);
lean_inc(v_a_1507_);
lean_dec_ref_known(v___x_1506_, 1);
v___x_1508_ = lean_unsigned_to_nat(0u);
v_bs_x27_1509_ = lean_array_uset(v_bs_1498_, v_i_1497_, v___x_1508_);
v___x_1510_ = ((size_t)1ULL);
v___x_1511_ = lean_usize_add(v_i_1497_, v___x_1510_);
v___x_1512_ = lean_array_uset(v_bs_x27_1509_, v_i_1497_, v_a_1507_);
v_i_1497_ = v___x_1511_;
v_bs_1498_ = v___x_1512_;
goto _start;
}
else
{
lean_object* v_a_1514_; lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1521_; 
lean_dec_ref(v_bs_1498_);
lean_dec_ref(v_post_1495_);
lean_dec_ref(v_pre_1494_);
v_a_1514_ = lean_ctor_get(v___x_1506_, 0);
v_isSharedCheck_1521_ = !lean_is_exclusive(v___x_1506_);
if (v_isSharedCheck_1521_ == 0)
{
v___x_1516_ = v___x_1506_;
v_isShared_1517_ = v_isSharedCheck_1521_;
goto v_resetjp_1515_;
}
else
{
lean_inc(v_a_1514_);
lean_dec(v___x_1506_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1521_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
lean_object* v___x_1519_; 
if (v_isShared_1517_ == 0)
{
v___x_1519_ = v___x_1516_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v_a_1514_);
v___x_1519_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
return v___x_1519_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__4(lean_object* v_pre_1522_, lean_object* v_post_1523_, lean_object* v_x_1524_, lean_object* v_x_1525_, lean_object* v_x_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_){
_start:
{
if (lean_obj_tag(v_x_1524_) == 5)
{
lean_object* v_fn_1531_; lean_object* v_arg_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; 
v_fn_1531_ = lean_ctor_get(v_x_1524_, 0);
lean_inc_ref(v_fn_1531_);
v_arg_1532_ = lean_ctor_get(v_x_1524_, 1);
lean_inc_ref(v_arg_1532_);
lean_dec_ref_known(v_x_1524_, 2);
v___x_1533_ = lean_array_set(v_x_1525_, v_x_1526_, v_arg_1532_);
v___x_1534_ = lean_unsigned_to_nat(1u);
v___x_1535_ = lean_nat_sub(v_x_1526_, v___x_1534_);
lean_dec(v_x_1526_);
v_x_1524_ = v_fn_1531_;
v_x_1525_ = v___x_1533_;
v_x_1526_ = v___x_1535_;
goto _start;
}
else
{
lean_object* v___x_1537_; 
lean_dec(v_x_1526_);
lean_inc_ref(v_post_1523_);
lean_inc_ref(v_pre_1522_);
v___x_1537_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1522_, v_post_1523_, v_x_1524_, v___y_1527_, v___y_1528_, v___y_1529_);
if (lean_obj_tag(v___x_1537_) == 0)
{
lean_object* v_a_1538_; size_t v_sz_1539_; size_t v___x_1540_; lean_object* v___x_1541_; 
v_a_1538_ = lean_ctor_get(v___x_1537_, 0);
lean_inc(v_a_1538_);
lean_dec_ref_known(v___x_1537_, 1);
v_sz_1539_ = lean_array_size(v_x_1525_);
v___x_1540_ = ((size_t)0ULL);
lean_inc_ref(v_post_1523_);
lean_inc_ref(v_pre_1522_);
v___x_1541_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1(v_pre_1522_, v_post_1523_, v_sz_1539_, v___x_1540_, v_x_1525_, v___y_1527_, v___y_1528_, v___y_1529_);
if (lean_obj_tag(v___x_1541_) == 0)
{
lean_object* v_a_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; 
v_a_1542_ = lean_ctor_get(v___x_1541_, 0);
lean_inc(v_a_1542_);
lean_dec_ref_known(v___x_1541_, 1);
v___x_1543_ = l_Lean_mkAppN(v_a_1538_, v_a_1542_);
lean_dec(v_a_1542_);
v___x_1544_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1522_, v_post_1523_, v___x_1543_, v___y_1527_, v___y_1528_, v___y_1529_);
return v___x_1544_;
}
else
{
lean_object* v_a_1545_; lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1552_; 
lean_dec(v_a_1538_);
lean_dec_ref(v_post_1523_);
lean_dec_ref(v_pre_1522_);
v_a_1545_ = lean_ctor_get(v___x_1541_, 0);
v_isSharedCheck_1552_ = !lean_is_exclusive(v___x_1541_);
if (v_isSharedCheck_1552_ == 0)
{
v___x_1547_ = v___x_1541_;
v_isShared_1548_ = v_isSharedCheck_1552_;
goto v_resetjp_1546_;
}
else
{
lean_inc(v_a_1545_);
lean_dec(v___x_1541_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1552_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
lean_object* v___x_1550_; 
if (v_isShared_1548_ == 0)
{
v___x_1550_ = v___x_1547_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v_a_1545_);
v___x_1550_ = v_reuseFailAlloc_1551_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
return v___x_1550_;
}
}
}
}
else
{
lean_dec_ref(v_x_1525_);
lean_dec_ref(v_post_1523_);
lean_dec_ref(v_pre_1522_);
return v___x_1537_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__1(lean_object* v___x_1553_, lean_object* v_pre_1554_, lean_object* v_e_1555_, lean_object* v_post_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_){
_start:
{
lean_object* v___y_1562_; lean_object* v___y_1563_; lean_object* v___y_1564_; lean_object* v___y_1565_; lean_object* v___y_1566_; lean_object* v___y_1567_; uint8_t v___y_1568_; uint8_t v___y_1569_; uint8_t v___y_1579_; lean_object* v___y_1580_; lean_object* v___y_1581_; lean_object* v___y_1582_; lean_object* v___y_1583_; uint8_t v___y_1584_; lean_object* v___y_1592_; lean_object* v___y_1593_; uint8_t v___y_1594_; lean_object* v___y_1595_; lean_object* v___y_1596_; uint8_t v___y_1597_; lean_object* v___x_1604_; 
v___x_1604_ = l_Lean_Core_checkSystem(v___x_1553_, v___y_1558_, v___y_1559_);
if (lean_obj_tag(v___x_1604_) == 0)
{
lean_object* v___x_1605_; 
lean_dec_ref_known(v___x_1604_, 1);
lean_inc_ref(v_pre_1554_);
lean_inc(v___y_1559_);
lean_inc_ref(v___y_1558_);
lean_inc_ref(v_e_1555_);
v___x_1605_ = lean_apply_4(v_pre_1554_, v_e_1555_, v___y_1558_, v___y_1559_, lean_box(0));
if (lean_obj_tag(v___x_1605_) == 0)
{
lean_object* v_a_1606_; lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1695_; 
v_a_1606_ = lean_ctor_get(v___x_1605_, 0);
v_isSharedCheck_1695_ = !lean_is_exclusive(v___x_1605_);
if (v_isSharedCheck_1695_ == 0)
{
v___x_1608_ = v___x_1605_;
v_isShared_1609_ = v_isSharedCheck_1695_;
goto v_resetjp_1607_;
}
else
{
lean_inc(v_a_1606_);
lean_dec(v___x_1605_);
v___x_1608_ = lean_box(0);
v_isShared_1609_ = v_isSharedCheck_1695_;
goto v_resetjp_1607_;
}
v_resetjp_1607_:
{
lean_object* v___y_1611_; 
switch(lean_obj_tag(v_a_1606_))
{
case 0:
{
lean_object* v_e_1685_; lean_object* v___x_1687_; 
lean_dec_ref(v_post_1556_);
lean_dec_ref(v_e_1555_);
lean_dec_ref(v_pre_1554_);
v_e_1685_ = lean_ctor_get(v_a_1606_, 0);
lean_inc_ref(v_e_1685_);
lean_dec_ref_known(v_a_1606_, 1);
if (v_isShared_1609_ == 0)
{
lean_ctor_set(v___x_1608_, 0, v_e_1685_);
v___x_1687_ = v___x_1608_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v_e_1685_);
v___x_1687_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
return v___x_1687_;
}
}
case 1:
{
lean_object* v_e_1689_; lean_object* v___x_1690_; 
lean_del_object(v___x_1608_);
lean_dec_ref(v_e_1555_);
v_e_1689_ = lean_ctor_get(v_a_1606_, 0);
lean_inc_ref(v_e_1689_);
lean_dec_ref_known(v_a_1606_, 1);
lean_inc_ref(v_post_1556_);
lean_inc_ref(v_pre_1554_);
v___x_1690_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1554_, v_post_1556_, v_e_1689_, v___y_1557_, v___y_1558_, v___y_1559_);
if (lean_obj_tag(v___x_1690_) == 0)
{
lean_object* v_a_1691_; lean_object* v___x_1692_; 
v_a_1691_ = lean_ctor_get(v___x_1690_, 0);
lean_inc(v_a_1691_);
lean_dec_ref_known(v___x_1690_, 1);
v___x_1692_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1554_, v_post_1556_, v_a_1691_, v___y_1557_, v___y_1558_, v___y_1559_);
return v___x_1692_;
}
else
{
lean_dec_ref(v_post_1556_);
lean_dec_ref(v_pre_1554_);
return v___x_1690_;
}
}
default: 
{
lean_object* v_e_x3f_1693_; 
lean_del_object(v___x_1608_);
v_e_x3f_1693_ = lean_ctor_get(v_a_1606_, 0);
lean_inc(v_e_x3f_1693_);
lean_dec_ref_known(v_a_1606_, 1);
if (lean_obj_tag(v_e_x3f_1693_) == 0)
{
v___y_1611_ = v_e_1555_;
goto v___jp_1610_;
}
else
{
lean_object* v_val_1694_; 
lean_dec_ref(v_e_1555_);
v_val_1694_ = lean_ctor_get(v_e_x3f_1693_, 0);
lean_inc(v_val_1694_);
lean_dec_ref_known(v_e_x3f_1693_, 1);
v___y_1611_ = v_val_1694_;
goto v___jp_1610_;
}
}
}
v___jp_1610_:
{
switch(lean_obj_tag(v___y_1611_))
{
case 7:
{
lean_object* v_binderName_1612_; lean_object* v_binderType_1613_; lean_object* v_body_1614_; uint8_t v_binderInfo_1615_; lean_object* v___x_1616_; 
v_binderName_1612_ = lean_ctor_get(v___y_1611_, 0);
lean_inc(v_binderName_1612_);
v_binderType_1613_ = lean_ctor_get(v___y_1611_, 1);
v_body_1614_ = lean_ctor_get(v___y_1611_, 2);
v_binderInfo_1615_ = lean_ctor_get_uint8(v___y_1611_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1613_);
lean_inc_ref(v_post_1556_);
lean_inc_ref(v_pre_1554_);
v___x_1616_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1554_, v_post_1556_, v_binderType_1613_, v___y_1557_, v___y_1558_, v___y_1559_);
if (lean_obj_tag(v___x_1616_) == 0)
{
lean_object* v_a_1617_; lean_object* v___x_1618_; 
v_a_1617_ = lean_ctor_get(v___x_1616_, 0);
lean_inc(v_a_1617_);
lean_dec_ref_known(v___x_1616_, 1);
lean_inc_ref(v_body_1614_);
lean_inc_ref(v_post_1556_);
lean_inc_ref(v_pre_1554_);
v___x_1618_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1554_, v_post_1556_, v_body_1614_, v___y_1557_, v___y_1558_, v___y_1559_);
if (lean_obj_tag(v___x_1618_) == 0)
{
lean_object* v_a_1619_; size_t v___x_1620_; size_t v___x_1621_; uint8_t v___x_1622_; 
v_a_1619_ = lean_ctor_get(v___x_1618_, 0);
lean_inc(v_a_1619_);
lean_dec_ref_known(v___x_1618_, 1);
v___x_1620_ = lean_ptr_addr(v_binderType_1613_);
v___x_1621_ = lean_ptr_addr(v_a_1617_);
v___x_1622_ = lean_usize_dec_eq(v___x_1620_, v___x_1621_);
if (v___x_1622_ == 0)
{
v___y_1592_ = v_binderName_1612_;
v___y_1593_ = v_a_1617_;
v___y_1594_ = v_binderInfo_1615_;
v___y_1595_ = v_a_1619_;
v___y_1596_ = v___y_1611_;
v___y_1597_ = v___x_1622_;
goto v___jp_1591_;
}
else
{
size_t v___x_1623_; size_t v___x_1624_; uint8_t v___x_1625_; 
v___x_1623_ = lean_ptr_addr(v_body_1614_);
v___x_1624_ = lean_ptr_addr(v_a_1619_);
v___x_1625_ = lean_usize_dec_eq(v___x_1623_, v___x_1624_);
v___y_1592_ = v_binderName_1612_;
v___y_1593_ = v_a_1617_;
v___y_1594_ = v_binderInfo_1615_;
v___y_1595_ = v_a_1619_;
v___y_1596_ = v___y_1611_;
v___y_1597_ = v___x_1625_;
goto v___jp_1591_;
}
}
else
{
lean_dec(v_a_1617_);
lean_dec(v_binderName_1612_);
lean_dec_ref_known(v___y_1611_, 3);
lean_dec_ref(v_post_1556_);
lean_dec_ref(v_pre_1554_);
return v___x_1618_;
}
}
else
{
lean_dec_ref_known(v___y_1611_, 3);
lean_dec(v_binderName_1612_);
lean_dec_ref(v_post_1556_);
lean_dec_ref(v_pre_1554_);
return v___x_1616_;
}
}
case 6:
{
lean_object* v_binderName_1626_; lean_object* v_binderType_1627_; lean_object* v_body_1628_; uint8_t v_binderInfo_1629_; lean_object* v___x_1630_; 
v_binderName_1626_ = lean_ctor_get(v___y_1611_, 0);
lean_inc(v_binderName_1626_);
v_binderType_1627_ = lean_ctor_get(v___y_1611_, 1);
v_body_1628_ = lean_ctor_get(v___y_1611_, 2);
v_binderInfo_1629_ = lean_ctor_get_uint8(v___y_1611_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1627_);
lean_inc_ref(v_post_1556_);
lean_inc_ref(v_pre_1554_);
v___x_1630_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1554_, v_post_1556_, v_binderType_1627_, v___y_1557_, v___y_1558_, v___y_1559_);
if (lean_obj_tag(v___x_1630_) == 0)
{
lean_object* v_a_1631_; lean_object* v___x_1632_; 
v_a_1631_ = lean_ctor_get(v___x_1630_, 0);
lean_inc(v_a_1631_);
lean_dec_ref_known(v___x_1630_, 1);
lean_inc_ref(v_body_1628_);
lean_inc_ref(v_post_1556_);
lean_inc_ref(v_pre_1554_);
v___x_1632_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1554_, v_post_1556_, v_body_1628_, v___y_1557_, v___y_1558_, v___y_1559_);
if (lean_obj_tag(v___x_1632_) == 0)
{
lean_object* v_a_1633_; size_t v___x_1634_; size_t v___x_1635_; uint8_t v___x_1636_; 
v_a_1633_ = lean_ctor_get(v___x_1632_, 0);
lean_inc(v_a_1633_);
lean_dec_ref_known(v___x_1632_, 1);
v___x_1634_ = lean_ptr_addr(v_binderType_1627_);
v___x_1635_ = lean_ptr_addr(v_a_1631_);
v___x_1636_ = lean_usize_dec_eq(v___x_1634_, v___x_1635_);
if (v___x_1636_ == 0)
{
v___y_1579_ = v_binderInfo_1629_;
v___y_1580_ = v_binderName_1626_;
v___y_1581_ = v___y_1611_;
v___y_1582_ = v_a_1631_;
v___y_1583_ = v_a_1633_;
v___y_1584_ = v___x_1636_;
goto v___jp_1578_;
}
else
{
size_t v___x_1637_; size_t v___x_1638_; uint8_t v___x_1639_; 
v___x_1637_ = lean_ptr_addr(v_body_1628_);
v___x_1638_ = lean_ptr_addr(v_a_1633_);
v___x_1639_ = lean_usize_dec_eq(v___x_1637_, v___x_1638_);
v___y_1579_ = v_binderInfo_1629_;
v___y_1580_ = v_binderName_1626_;
v___y_1581_ = v___y_1611_;
v___y_1582_ = v_a_1631_;
v___y_1583_ = v_a_1633_;
v___y_1584_ = v___x_1639_;
goto v___jp_1578_;
}
}
else
{
lean_dec(v_a_1631_);
lean_dec(v_binderName_1626_);
lean_dec_ref_known(v___y_1611_, 3);
lean_dec_ref(v_post_1556_);
lean_dec_ref(v_pre_1554_);
return v___x_1632_;
}
}
else
{
lean_dec(v_binderName_1626_);
lean_dec_ref_known(v___y_1611_, 3);
lean_dec_ref(v_post_1556_);
lean_dec_ref(v_pre_1554_);
return v___x_1630_;
}
}
case 8:
{
lean_object* v_declName_1640_; lean_object* v_type_1641_; lean_object* v_value_1642_; lean_object* v_body_1643_; uint8_t v_nondep_1644_; lean_object* v___x_1645_; 
v_declName_1640_ = lean_ctor_get(v___y_1611_, 0);
lean_inc(v_declName_1640_);
v_type_1641_ = lean_ctor_get(v___y_1611_, 1);
v_value_1642_ = lean_ctor_get(v___y_1611_, 2);
v_body_1643_ = lean_ctor_get(v___y_1611_, 3);
lean_inc_ref(v_body_1643_);
v_nondep_1644_ = lean_ctor_get_uint8(v___y_1611_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_1641_);
lean_inc_ref(v_post_1556_);
lean_inc_ref(v_pre_1554_);
v___x_1645_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1554_, v_post_1556_, v_type_1641_, v___y_1557_, v___y_1558_, v___y_1559_);
if (lean_obj_tag(v___x_1645_) == 0)
{
lean_object* v_a_1646_; lean_object* v___x_1647_; 
v_a_1646_ = lean_ctor_get(v___x_1645_, 0);
lean_inc(v_a_1646_);
lean_dec_ref_known(v___x_1645_, 1);
lean_inc_ref(v_value_1642_);
lean_inc_ref(v_post_1556_);
lean_inc_ref(v_pre_1554_);
v___x_1647_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1554_, v_post_1556_, v_value_1642_, v___y_1557_, v___y_1558_, v___y_1559_);
if (lean_obj_tag(v___x_1647_) == 0)
{
lean_object* v_a_1648_; lean_object* v___x_1649_; 
v_a_1648_ = lean_ctor_get(v___x_1647_, 0);
lean_inc(v_a_1648_);
lean_dec_ref_known(v___x_1647_, 1);
lean_inc_ref(v_body_1643_);
lean_inc_ref(v_post_1556_);
lean_inc_ref(v_pre_1554_);
v___x_1649_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1554_, v_post_1556_, v_body_1643_, v___y_1557_, v___y_1558_, v___y_1559_);
if (lean_obj_tag(v___x_1649_) == 0)
{
lean_object* v_a_1650_; size_t v___x_1651_; size_t v___x_1652_; uint8_t v___x_1653_; 
v_a_1650_ = lean_ctor_get(v___x_1649_, 0);
lean_inc(v_a_1650_);
lean_dec_ref_known(v___x_1649_, 1);
v___x_1651_ = lean_ptr_addr(v_type_1641_);
v___x_1652_ = lean_ptr_addr(v_a_1646_);
v___x_1653_ = lean_usize_dec_eq(v___x_1651_, v___x_1652_);
if (v___x_1653_ == 0)
{
v___y_1562_ = v_declName_1640_;
v___y_1563_ = v_a_1648_;
v___y_1564_ = v_a_1650_;
v___y_1565_ = v___y_1611_;
v___y_1566_ = v_body_1643_;
v___y_1567_ = v_a_1646_;
v___y_1568_ = v_nondep_1644_;
v___y_1569_ = v___x_1653_;
goto v___jp_1561_;
}
else
{
size_t v___x_1654_; size_t v___x_1655_; uint8_t v___x_1656_; 
v___x_1654_ = lean_ptr_addr(v_value_1642_);
v___x_1655_ = lean_ptr_addr(v_a_1648_);
v___x_1656_ = lean_usize_dec_eq(v___x_1654_, v___x_1655_);
v___y_1562_ = v_declName_1640_;
v___y_1563_ = v_a_1648_;
v___y_1564_ = v_a_1650_;
v___y_1565_ = v___y_1611_;
v___y_1566_ = v_body_1643_;
v___y_1567_ = v_a_1646_;
v___y_1568_ = v_nondep_1644_;
v___y_1569_ = v___x_1656_;
goto v___jp_1561_;
}
}
else
{
lean_dec(v_a_1648_);
lean_dec(v_a_1646_);
lean_dec_ref(v_body_1643_);
lean_dec_ref_known(v___y_1611_, 4);
lean_dec(v_declName_1640_);
lean_dec_ref(v_post_1556_);
lean_dec_ref(v_pre_1554_);
return v___x_1649_;
}
}
else
{
lean_dec(v_a_1646_);
lean_dec_ref(v_body_1643_);
lean_dec(v_declName_1640_);
lean_dec_ref_known(v___y_1611_, 4);
lean_dec_ref(v_post_1556_);
lean_dec_ref(v_pre_1554_);
return v___x_1647_;
}
}
else
{
lean_dec_ref(v_body_1643_);
lean_dec(v_declName_1640_);
lean_dec_ref_known(v___y_1611_, 4);
lean_dec_ref(v_post_1556_);
lean_dec_ref(v_pre_1554_);
return v___x_1645_;
}
}
case 5:
{
lean_object* v_dummy_1657_; lean_object* v_nargs_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; 
v_dummy_1657_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_1658_ = l_Lean_Expr_getAppNumArgs(v___y_1611_);
lean_inc(v_nargs_1658_);
v___x_1659_ = lean_mk_array(v_nargs_1658_, v_dummy_1657_);
v___x_1660_ = lean_unsigned_to_nat(1u);
v___x_1661_ = lean_nat_sub(v_nargs_1658_, v___x_1660_);
lean_dec(v_nargs_1658_);
v___x_1662_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__4(v_pre_1554_, v_post_1556_, v___y_1611_, v___x_1659_, v___x_1661_, v___y_1557_, v___y_1558_, v___y_1559_);
return v___x_1662_;
}
case 10:
{
lean_object* v_data_1663_; lean_object* v_expr_1664_; lean_object* v___x_1665_; 
v_data_1663_ = lean_ctor_get(v___y_1611_, 0);
v_expr_1664_ = lean_ctor_get(v___y_1611_, 1);
lean_inc_ref(v_expr_1664_);
lean_inc_ref(v_post_1556_);
lean_inc_ref(v_pre_1554_);
v___x_1665_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1554_, v_post_1556_, v_expr_1664_, v___y_1557_, v___y_1558_, v___y_1559_);
if (lean_obj_tag(v___x_1665_) == 0)
{
lean_object* v_a_1666_; size_t v___x_1667_; size_t v___x_1668_; uint8_t v___x_1669_; 
v_a_1666_ = lean_ctor_get(v___x_1665_, 0);
lean_inc(v_a_1666_);
lean_dec_ref_known(v___x_1665_, 1);
v___x_1667_ = lean_ptr_addr(v_expr_1664_);
v___x_1668_ = lean_ptr_addr(v_a_1666_);
v___x_1669_ = lean_usize_dec_eq(v___x_1667_, v___x_1668_);
if (v___x_1669_ == 0)
{
lean_object* v___x_1670_; lean_object* v___x_1671_; 
lean_inc(v_data_1663_);
lean_dec_ref_known(v___y_1611_, 2);
v___x_1670_ = l_Lean_Expr_mdata___override(v_data_1663_, v_a_1666_);
v___x_1671_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1554_, v_post_1556_, v___x_1670_, v___y_1557_, v___y_1558_, v___y_1559_);
return v___x_1671_;
}
else
{
lean_object* v___x_1672_; 
lean_dec(v_a_1666_);
v___x_1672_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1554_, v_post_1556_, v___y_1611_, v___y_1557_, v___y_1558_, v___y_1559_);
return v___x_1672_;
}
}
else
{
lean_dec_ref_known(v___y_1611_, 2);
lean_dec_ref(v_post_1556_);
lean_dec_ref(v_pre_1554_);
return v___x_1665_;
}
}
case 11:
{
lean_object* v_typeName_1673_; lean_object* v_idx_1674_; lean_object* v_struct_1675_; lean_object* v___x_1676_; 
v_typeName_1673_ = lean_ctor_get(v___y_1611_, 0);
v_idx_1674_ = lean_ctor_get(v___y_1611_, 1);
v_struct_1675_ = lean_ctor_get(v___y_1611_, 2);
lean_inc_ref(v_struct_1675_);
lean_inc_ref(v_post_1556_);
lean_inc_ref(v_pre_1554_);
v___x_1676_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1554_, v_post_1556_, v_struct_1675_, v___y_1557_, v___y_1558_, v___y_1559_);
if (lean_obj_tag(v___x_1676_) == 0)
{
lean_object* v_a_1677_; size_t v___x_1678_; size_t v___x_1679_; uint8_t v___x_1680_; 
v_a_1677_ = lean_ctor_get(v___x_1676_, 0);
lean_inc(v_a_1677_);
lean_dec_ref_known(v___x_1676_, 1);
v___x_1678_ = lean_ptr_addr(v_struct_1675_);
v___x_1679_ = lean_ptr_addr(v_a_1677_);
v___x_1680_ = lean_usize_dec_eq(v___x_1678_, v___x_1679_);
if (v___x_1680_ == 0)
{
lean_object* v___x_1681_; lean_object* v___x_1682_; 
lean_inc(v_idx_1674_);
lean_inc(v_typeName_1673_);
lean_dec_ref_known(v___y_1611_, 3);
v___x_1681_ = l_Lean_Expr_proj___override(v_typeName_1673_, v_idx_1674_, v_a_1677_);
v___x_1682_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1554_, v_post_1556_, v___x_1681_, v___y_1557_, v___y_1558_, v___y_1559_);
return v___x_1682_;
}
else
{
lean_object* v___x_1683_; 
lean_dec(v_a_1677_);
v___x_1683_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1554_, v_post_1556_, v___y_1611_, v___y_1557_, v___y_1558_, v___y_1559_);
return v___x_1683_;
}
}
else
{
lean_dec_ref_known(v___y_1611_, 3);
lean_dec_ref(v_post_1556_);
lean_dec_ref(v_pre_1554_);
return v___x_1676_;
}
}
default: 
{
lean_object* v___x_1684_; 
v___x_1684_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1554_, v_post_1556_, v___y_1611_, v___y_1557_, v___y_1558_, v___y_1559_);
return v___x_1684_;
}
}
}
}
}
else
{
lean_object* v_a_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1703_; 
lean_dec_ref(v_post_1556_);
lean_dec_ref(v_e_1555_);
lean_dec_ref(v_pre_1554_);
v_a_1696_ = lean_ctor_get(v___x_1605_, 0);
v_isSharedCheck_1703_ = !lean_is_exclusive(v___x_1605_);
if (v_isSharedCheck_1703_ == 0)
{
v___x_1698_ = v___x_1605_;
v_isShared_1699_ = v_isSharedCheck_1703_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_a_1696_);
lean_dec(v___x_1605_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1703_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v___x_1701_; 
if (v_isShared_1699_ == 0)
{
v___x_1701_ = v___x_1698_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v_a_1696_);
v___x_1701_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
return v___x_1701_;
}
}
}
}
else
{
lean_object* v_a_1704_; lean_object* v___x_1706_; uint8_t v_isShared_1707_; uint8_t v_isSharedCheck_1711_; 
lean_dec_ref(v_post_1556_);
lean_dec_ref(v_e_1555_);
lean_dec_ref(v_pre_1554_);
v_a_1704_ = lean_ctor_get(v___x_1604_, 0);
v_isSharedCheck_1711_ = !lean_is_exclusive(v___x_1604_);
if (v_isSharedCheck_1711_ == 0)
{
v___x_1706_ = v___x_1604_;
v_isShared_1707_ = v_isSharedCheck_1711_;
goto v_resetjp_1705_;
}
else
{
lean_inc(v_a_1704_);
lean_dec(v___x_1604_);
v___x_1706_ = lean_box(0);
v_isShared_1707_ = v_isSharedCheck_1711_;
goto v_resetjp_1705_;
}
v_resetjp_1705_:
{
lean_object* v___x_1709_; 
if (v_isShared_1707_ == 0)
{
v___x_1709_ = v___x_1706_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v_a_1704_);
v___x_1709_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
return v___x_1709_;
}
}
}
v___jp_1561_:
{
if (v___y_1569_ == 0)
{
lean_object* v___x_1570_; lean_object* v___x_1571_; 
lean_dec_ref(v___y_1566_);
lean_dec_ref(v___y_1565_);
v___x_1570_ = l_Lean_Expr_letE___override(v___y_1562_, v___y_1567_, v___y_1563_, v___y_1564_, v___y_1568_);
v___x_1571_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1554_, v_post_1556_, v___x_1570_, v___y_1557_, v___y_1558_, v___y_1559_);
return v___x_1571_;
}
else
{
size_t v___x_1572_; size_t v___x_1573_; uint8_t v___x_1574_; 
v___x_1572_ = lean_ptr_addr(v___y_1566_);
lean_dec_ref(v___y_1566_);
v___x_1573_ = lean_ptr_addr(v___y_1564_);
v___x_1574_ = lean_usize_dec_eq(v___x_1572_, v___x_1573_);
if (v___x_1574_ == 0)
{
lean_object* v___x_1575_; lean_object* v___x_1576_; 
lean_dec_ref(v___y_1565_);
v___x_1575_ = l_Lean_Expr_letE___override(v___y_1562_, v___y_1567_, v___y_1563_, v___y_1564_, v___y_1568_);
v___x_1576_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1554_, v_post_1556_, v___x_1575_, v___y_1557_, v___y_1558_, v___y_1559_);
return v___x_1576_;
}
else
{
lean_object* v___x_1577_; 
lean_dec_ref(v___y_1567_);
lean_dec_ref(v___y_1564_);
lean_dec_ref(v___y_1563_);
lean_dec(v___y_1562_);
v___x_1577_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1554_, v_post_1556_, v___y_1565_, v___y_1557_, v___y_1558_, v___y_1559_);
return v___x_1577_;
}
}
}
v___jp_1578_:
{
if (v___y_1584_ == 0)
{
lean_object* v___x_1585_; lean_object* v___x_1586_; 
lean_dec_ref(v___y_1581_);
v___x_1585_ = l_Lean_Expr_lam___override(v___y_1580_, v___y_1582_, v___y_1583_, v___y_1579_);
v___x_1586_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1554_, v_post_1556_, v___x_1585_, v___y_1557_, v___y_1558_, v___y_1559_);
return v___x_1586_;
}
else
{
uint8_t v___x_1587_; 
v___x_1587_ = l_Lean_instBEqBinderInfo_beq(v___y_1579_, v___y_1579_);
if (v___x_1587_ == 0)
{
lean_object* v___x_1588_; lean_object* v___x_1589_; 
lean_dec_ref(v___y_1581_);
v___x_1588_ = l_Lean_Expr_lam___override(v___y_1580_, v___y_1582_, v___y_1583_, v___y_1579_);
v___x_1589_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1554_, v_post_1556_, v___x_1588_, v___y_1557_, v___y_1558_, v___y_1559_);
return v___x_1589_;
}
else
{
lean_object* v___x_1590_; 
lean_dec_ref(v___y_1583_);
lean_dec_ref(v___y_1582_);
lean_dec(v___y_1580_);
v___x_1590_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1554_, v_post_1556_, v___y_1581_, v___y_1557_, v___y_1558_, v___y_1559_);
return v___x_1590_;
}
}
}
v___jp_1591_:
{
if (v___y_1597_ == 0)
{
lean_object* v___x_1598_; lean_object* v___x_1599_; 
lean_dec_ref(v___y_1596_);
v___x_1598_ = l_Lean_Expr_forallE___override(v___y_1592_, v___y_1593_, v___y_1595_, v___y_1594_);
v___x_1599_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1554_, v_post_1556_, v___x_1598_, v___y_1557_, v___y_1558_, v___y_1559_);
return v___x_1599_;
}
else
{
uint8_t v___x_1600_; 
v___x_1600_ = l_Lean_instBEqBinderInfo_beq(v___y_1594_, v___y_1594_);
if (v___x_1600_ == 0)
{
lean_object* v___x_1601_; lean_object* v___x_1602_; 
lean_dec_ref(v___y_1596_);
v___x_1601_ = l_Lean_Expr_forallE___override(v___y_1592_, v___y_1593_, v___y_1595_, v___y_1594_);
v___x_1602_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1554_, v_post_1556_, v___x_1601_, v___y_1557_, v___y_1558_, v___y_1559_);
return v___x_1602_;
}
else
{
lean_object* v___x_1603_; 
lean_dec_ref(v___y_1595_);
lean_dec_ref(v___y_1593_);
lean_dec(v___y_1592_);
v___x_1603_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1554_, v_post_1556_, v___y_1596_, v___y_1557_, v___y_1558_, v___y_1559_);
return v___x_1603_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__1___boxed(lean_object* v___x_1712_, lean_object* v_pre_1713_, lean_object* v_e_1714_, lean_object* v_post_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_){
_start:
{
lean_object* v_res_1720_; 
v_res_1720_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__1(v___x_1712_, v_pre_1713_, v_e_1714_, v_post_1715_, v___y_1716_, v___y_1717_, v___y_1718_);
lean_dec(v___y_1718_);
lean_dec_ref(v___y_1717_);
lean_dec(v___y_1716_);
return v_res_1720_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(lean_object* v_pre_1721_, lean_object* v_post_1722_, lean_object* v_e_1723_, lean_object* v_a_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_){
_start:
{
lean_object* v___x_1728_; lean_object* v___x_1729_; 
lean_inc(v_a_1724_);
v___x_1728_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1728_, 0, lean_box(0));
lean_closure_set(v___x_1728_, 1, lean_box(0));
lean_closure_set(v___x_1728_, 2, v_a_1724_);
v___x_1729_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__0(lean_box(0), v___x_1728_, v___y_1725_, v___y_1726_);
if (lean_obj_tag(v___x_1729_) == 0)
{
lean_object* v_a_1730_; lean_object* v___x_1732_; uint8_t v_isShared_1733_; uint8_t v_isSharedCheck_1761_; 
v_a_1730_ = lean_ctor_get(v___x_1729_, 0);
v_isSharedCheck_1761_ = !lean_is_exclusive(v___x_1729_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1732_ = v___x_1729_;
v_isShared_1733_ = v_isSharedCheck_1761_;
goto v_resetjp_1731_;
}
else
{
lean_inc(v_a_1730_);
lean_dec(v___x_1729_);
v___x_1732_ = lean_box(0);
v_isShared_1733_ = v_isSharedCheck_1761_;
goto v_resetjp_1731_;
}
v_resetjp_1731_:
{
lean_object* v___x_1734_; 
v___x_1734_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg(v_a_1730_, v_e_1723_);
lean_dec(v_a_1730_);
if (lean_obj_tag(v___x_1734_) == 0)
{
lean_object* v___x_1735_; lean_object* v___f_1736_; lean_object* v___x_1737_; 
lean_del_object(v___x_1732_);
v___x_1735_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__19___closed__0));
lean_inc_ref(v_e_1723_);
v___f_1736_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__1___boxed), 8, 4);
lean_closure_set(v___f_1736_, 0, v___x_1735_);
lean_closure_set(v___f_1736_, 1, v_pre_1721_);
lean_closure_set(v___f_1736_, 2, v_e_1723_);
lean_closure_set(v___f_1736_, 3, v_post_1722_);
v___x_1737_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___redArg(v___f_1736_, v_a_1724_, v___y_1725_, v___y_1726_);
if (lean_obj_tag(v___x_1737_) == 0)
{
lean_object* v_a_1738_; lean_object* v___f_1739_; lean_object* v___x_1740_; 
v_a_1738_ = lean_ctor_get(v___x_1737_, 0);
lean_inc_n(v_a_1738_, 2);
lean_dec_ref_known(v___x_1737_, 1);
lean_inc(v_a_1724_);
v___f_1739_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1739_, 0, v_a_1724_);
lean_closure_set(v___f_1739_, 1, v_e_1723_);
lean_closure_set(v___f_1739_, 2, v_a_1738_);
v___x_1740_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__0(lean_box(0), v___f_1739_, v___y_1725_, v___y_1726_);
if (lean_obj_tag(v___x_1740_) == 0)
{
lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1747_; 
v_isSharedCheck_1747_ = !lean_is_exclusive(v___x_1740_);
if (v_isSharedCheck_1747_ == 0)
{
lean_object* v_unused_1748_; 
v_unused_1748_ = lean_ctor_get(v___x_1740_, 0);
lean_dec(v_unused_1748_);
v___x_1742_ = v___x_1740_;
v_isShared_1743_ = v_isSharedCheck_1747_;
goto v_resetjp_1741_;
}
else
{
lean_dec(v___x_1740_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1747_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
lean_object* v___x_1745_; 
if (v_isShared_1743_ == 0)
{
lean_ctor_set(v___x_1742_, 0, v_a_1738_);
v___x_1745_ = v___x_1742_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v_a_1738_);
v___x_1745_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
return v___x_1745_;
}
}
}
else
{
lean_object* v_a_1749_; lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1756_; 
lean_dec(v_a_1738_);
v_a_1749_ = lean_ctor_get(v___x_1740_, 0);
v_isSharedCheck_1756_ = !lean_is_exclusive(v___x_1740_);
if (v_isSharedCheck_1756_ == 0)
{
v___x_1751_ = v___x_1740_;
v_isShared_1752_ = v_isSharedCheck_1756_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_a_1749_);
lean_dec(v___x_1740_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1756_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
lean_object* v___x_1754_; 
if (v_isShared_1752_ == 0)
{
v___x_1754_ = v___x_1751_;
goto v_reusejp_1753_;
}
else
{
lean_object* v_reuseFailAlloc_1755_; 
v_reuseFailAlloc_1755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1755_, 0, v_a_1749_);
v___x_1754_ = v_reuseFailAlloc_1755_;
goto v_reusejp_1753_;
}
v_reusejp_1753_:
{
return v___x_1754_;
}
}
}
}
else
{
lean_dec_ref(v_e_1723_);
return v___x_1737_;
}
}
else
{
lean_object* v_val_1757_; lean_object* v___x_1759_; 
lean_dec_ref(v_e_1723_);
lean_dec_ref(v_post_1722_);
lean_dec_ref(v_pre_1721_);
v_val_1757_ = lean_ctor_get(v___x_1734_, 0);
lean_inc(v_val_1757_);
lean_dec_ref_known(v___x_1734_, 1);
if (v_isShared_1733_ == 0)
{
lean_ctor_set(v___x_1732_, 0, v_val_1757_);
v___x_1759_ = v___x_1732_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v_val_1757_);
v___x_1759_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
return v___x_1759_;
}
}
}
}
else
{
lean_object* v_a_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1769_; 
lean_dec_ref(v_e_1723_);
lean_dec_ref(v_post_1722_);
lean_dec_ref(v_pre_1721_);
v_a_1762_ = lean_ctor_get(v___x_1729_, 0);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1729_);
if (v_isSharedCheck_1769_ == 0)
{
v___x_1764_ = v___x_1729_;
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_a_1762_);
lean_dec(v___x_1729_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v___x_1767_; 
if (v_isShared_1765_ == 0)
{
v___x_1767_ = v___x_1764_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v_a_1762_);
v___x_1767_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
return v___x_1767_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(lean_object* v_pre_1770_, lean_object* v_post_1771_, lean_object* v_e_1772_, lean_object* v_a_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_){
_start:
{
lean_object* v___x_1777_; 
lean_inc_ref(v_post_1771_);
lean_inc(v___y_1775_);
lean_inc_ref(v___y_1774_);
lean_inc_ref(v_e_1772_);
v___x_1777_ = lean_apply_4(v_post_1771_, v_e_1772_, v___y_1774_, v___y_1775_, lean_box(0));
if (lean_obj_tag(v___x_1777_) == 0)
{
lean_object* v_a_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1796_; 
v_a_1778_ = lean_ctor_get(v___x_1777_, 0);
v_isSharedCheck_1796_ = !lean_is_exclusive(v___x_1777_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1780_ = v___x_1777_;
v_isShared_1781_ = v_isSharedCheck_1796_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_a_1778_);
lean_dec(v___x_1777_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1796_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
switch(lean_obj_tag(v_a_1778_))
{
case 0:
{
lean_object* v_e_1782_; lean_object* v___x_1784_; 
lean_dec_ref(v_e_1772_);
lean_dec_ref(v_post_1771_);
lean_dec_ref(v_pre_1770_);
v_e_1782_ = lean_ctor_get(v_a_1778_, 0);
lean_inc_ref(v_e_1782_);
lean_dec_ref_known(v_a_1778_, 1);
if (v_isShared_1781_ == 0)
{
lean_ctor_set(v___x_1780_, 0, v_e_1782_);
v___x_1784_ = v___x_1780_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_e_1782_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
}
}
case 1:
{
lean_object* v_e_1786_; lean_object* v___x_1787_; 
lean_del_object(v___x_1780_);
lean_dec_ref(v_e_1772_);
v_e_1786_ = lean_ctor_get(v_a_1778_, 0);
lean_inc_ref(v_e_1786_);
lean_dec_ref_known(v_a_1778_, 1);
v___x_1787_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1770_, v_post_1771_, v_e_1786_, v_a_1773_, v___y_1774_, v___y_1775_);
return v___x_1787_;
}
default: 
{
lean_object* v_e_x3f_1788_; 
lean_dec_ref(v_post_1771_);
lean_dec_ref(v_pre_1770_);
v_e_x3f_1788_ = lean_ctor_get(v_a_1778_, 0);
lean_inc(v_e_x3f_1788_);
lean_dec_ref_known(v_a_1778_, 1);
if (lean_obj_tag(v_e_x3f_1788_) == 0)
{
lean_object* v___x_1790_; 
if (v_isShared_1781_ == 0)
{
lean_ctor_set(v___x_1780_, 0, v_e_1772_);
v___x_1790_ = v___x_1780_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v_e_1772_);
v___x_1790_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1789_;
}
v_reusejp_1789_:
{
return v___x_1790_;
}
}
else
{
lean_object* v_val_1792_; lean_object* v___x_1794_; 
lean_dec_ref(v_e_1772_);
v_val_1792_ = lean_ctor_get(v_e_x3f_1788_, 0);
lean_inc(v_val_1792_);
lean_dec_ref_known(v_e_x3f_1788_, 1);
if (v_isShared_1781_ == 0)
{
lean_ctor_set(v___x_1780_, 0, v_val_1792_);
v___x_1794_ = v___x_1780_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v_val_1792_);
v___x_1794_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
return v___x_1794_;
}
}
}
}
}
}
else
{
lean_object* v_a_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1804_; 
lean_dec_ref(v_e_1772_);
lean_dec_ref(v_post_1771_);
lean_dec_ref(v_pre_1770_);
v_a_1797_ = lean_ctor_get(v___x_1777_, 0);
v_isSharedCheck_1804_ = !lean_is_exclusive(v___x_1777_);
if (v_isSharedCheck_1804_ == 0)
{
v___x_1799_ = v___x_1777_;
v_isShared_1800_ = v_isSharedCheck_1804_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_a_1797_);
lean_dec(v___x_1777_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1804_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
lean_object* v___x_1802_; 
if (v_isShared_1800_ == 0)
{
v___x_1802_ = v___x_1799_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1803_; 
v_reuseFailAlloc_1803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1803_, 0, v_a_1797_);
v___x_1802_ = v_reuseFailAlloc_1803_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
return v___x_1802_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_1805_, lean_object* v_post_1806_, lean_object* v_e_1807_, lean_object* v_a_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_){
_start:
{
lean_object* v_res_1812_; 
v_res_1812_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1805_, v_post_1806_, v_e_1807_, v_a_1808_, v___y_1809_, v___y_1810_);
lean_dec(v___y_1810_);
lean_dec_ref(v___y_1809_);
lean_dec(v_a_1808_);
return v_res_1812_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_1813_, lean_object* v_post_1814_, lean_object* v_sz_1815_, lean_object* v_i_1816_, lean_object* v_bs_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_){
_start:
{
size_t v_sz_boxed_1822_; size_t v_i_boxed_1823_; lean_object* v_res_1824_; 
v_sz_boxed_1822_ = lean_unbox_usize(v_sz_1815_);
lean_dec(v_sz_1815_);
v_i_boxed_1823_ = lean_unbox_usize(v_i_1816_);
lean_dec(v_i_1816_);
v_res_1824_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1(v_pre_1813_, v_post_1814_, v_sz_boxed_1822_, v_i_boxed_1823_, v_bs_1817_, v___y_1818_, v___y_1819_, v___y_1820_);
lean_dec(v___y_1820_);
lean_dec_ref(v___y_1819_);
lean_dec(v___y_1818_);
return v_res_1824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__4___boxed(lean_object* v_pre_1825_, lean_object* v_post_1826_, lean_object* v_x_1827_, lean_object* v_x_1828_, lean_object* v_x_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_){
_start:
{
lean_object* v_res_1834_; 
v_res_1834_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__4(v_pre_1825_, v_post_1826_, v_x_1827_, v_x_1828_, v_x_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
lean_dec(v___y_1832_);
lean_dec_ref(v___y_1831_);
lean_dec(v___y_1830_);
return v_res_1834_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___boxed(lean_object* v_pre_1835_, lean_object* v_post_1836_, lean_object* v_e_1837_, lean_object* v_a_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_){
_start:
{
lean_object* v_res_1842_; 
v_res_1842_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1835_, v_post_1836_, v_e_1837_, v_a_1838_, v___y_1839_, v___y_1840_);
lean_dec(v___y_1840_);
lean_dec_ref(v___y_1839_);
lean_dec(v_a_1838_);
return v_res_1842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___lam__0(lean_object* v_00_u03b1_1843_, lean_object* v_x_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_){
_start:
{
lean_object* v___x_1848_; lean_object* v___x_1849_; 
v___x_1848_ = lean_apply_1(v_x_1844_, lean_box(0));
v___x_1849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1849_, 0, v___x_1848_);
return v___x_1849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___lam__0___boxed(lean_object* v_00_u03b1_1850_, lean_object* v_x_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_){
_start:
{
lean_object* v_res_1855_; 
v_res_1855_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___lam__0(v_00_u03b1_1850_, v_x_1851_, v___y_1852_, v___y_1853_);
lean_dec(v___y_1853_);
lean_dec_ref(v___y_1852_);
return v_res_1855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(lean_object* v_input_1856_, lean_object* v_pre_1857_, lean_object* v_post_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_){
_start:
{
lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v_a_1864_; lean_object* v___x_1865_; 
v___x_1862_ = lean_obj_once(&l_Lean_Core_transform___redArg___closed__3, &l_Lean_Core_transform___redArg___closed__3_once, _init_l_Lean_Core_transform___redArg___closed__3);
v___x_1863_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___lam__0(lean_box(0), v___x_1862_, v___y_1859_, v___y_1860_);
v_a_1864_ = lean_ctor_get(v___x_1863_, 0);
lean_inc(v_a_1864_);
lean_dec_ref(v___x_1863_);
v___x_1865_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1857_, v_post_1858_, v_input_1856_, v_a_1864_, v___y_1859_, v___y_1860_);
if (lean_obj_tag(v___x_1865_) == 0)
{
lean_object* v_a_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1875_; 
v_a_1866_ = lean_ctor_get(v___x_1865_, 0);
lean_inc(v_a_1866_);
lean_dec_ref_known(v___x_1865_, 1);
v___x_1867_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1867_, 0, lean_box(0));
lean_closure_set(v___x_1867_, 1, lean_box(0));
lean_closure_set(v___x_1867_, 2, v_a_1864_);
v___x_1868_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___lam__0(lean_box(0), v___x_1867_, v___y_1859_, v___y_1860_);
v_isSharedCheck_1875_ = !lean_is_exclusive(v___x_1868_);
if (v_isSharedCheck_1875_ == 0)
{
lean_object* v_unused_1876_; 
v_unused_1876_ = lean_ctor_get(v___x_1868_, 0);
lean_dec(v_unused_1876_);
v___x_1870_ = v___x_1868_;
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
else
{
lean_dec(v___x_1868_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
lean_object* v___x_1873_; 
if (v_isShared_1871_ == 0)
{
lean_ctor_set(v___x_1870_, 0, v_a_1866_);
v___x_1873_ = v___x_1870_;
goto v_reusejp_1872_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v_a_1866_);
v___x_1873_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1872_;
}
v_reusejp_1872_:
{
return v___x_1873_;
}
}
}
else
{
lean_dec(v_a_1864_);
return v___x_1865_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___boxed(lean_object* v_input_1877_, lean_object* v_pre_1878_, lean_object* v_post_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_){
_start:
{
lean_object* v_res_1883_; 
v_res_1883_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_input_1877_, v_pre_1878_, v_post_1879_, v___y_1880_, v___y_1881_);
lean_dec(v___y_1881_);
lean_dec_ref(v___y_1880_);
return v_res_1883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_betaReduce(lean_object* v_e_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_){
_start:
{
lean_object* v___f_1890_; lean_object* v___f_1891_; lean_object* v___x_1892_; 
v___f_1890_ = ((lean_object*)(l_Lean_Core_betaReduce___closed__0));
v___f_1891_ = ((lean_object*)(l_Lean_Core_betaReduce___closed__1));
v___x_1892_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_1886_, v___f_1890_, v___f_1891_, v_a_1887_, v_a_1888_);
return v___x_1892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_betaReduce___boxed(lean_object* v_e_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_){
_start:
{
lean_object* v_res_1897_; 
v_res_1897_ = l_Lean_Core_betaReduce(v_e_1893_, v_a_1894_, v_a_1895_);
lean_dec(v_a_1895_);
lean_dec_ref(v_a_1894_);
return v_res_1897_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_1898_, lean_object* v_m_1899_, lean_object* v_a_1900_){
_start:
{
lean_object* v___x_1901_; 
v___x_1901_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg(v_m_1899_, v_a_1900_);
return v___x_1901_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_1902_, lean_object* v_m_1903_, lean_object* v_a_1904_){
_start:
{
lean_object* v_res_1905_; 
v_res_1905_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3(v_00_u03b2_1902_, v_m_1903_, v_a_1904_);
lean_dec_ref(v_a_1904_);
lean_dec_ref(v_m_1903_);
return v_res_1905_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_1906_, lean_object* v_ref_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_){
_start:
{
lean_object* v___x_1911_; 
v___x_1911_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_1907_);
return v___x_1911_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1912_, lean_object* v_ref_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_){
_start:
{
lean_object* v_res_1917_; 
v_res_1917_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_1912_, v_ref_1913_, v___y_1914_, v___y_1915_);
lean_dec(v___y_1915_);
lean_dec_ref(v___y_1914_);
return v_res_1917_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8(lean_object* v_00_u03b1_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_){
_start:
{
lean_object* v___x_1922_; 
v___x_1922_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___redArg();
return v___x_1922_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___boxed(lean_object* v_00_u03b1_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_){
_start:
{
lean_object* v_res_1927_; 
v_res_1927_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8(v_00_u03b1_1923_, v___y_1924_, v___y_1925_);
lean_dec(v___y_1925_);
lean_dec_ref(v___y_1924_);
return v_res_1927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5(lean_object* v_00_u03b1_1928_, lean_object* v_x_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_){
_start:
{
lean_object* v___x_1934_; 
v___x_1934_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___redArg(v_x_1929_, v___y_1930_, v___y_1931_, v___y_1932_);
return v___x_1934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b1_1935_, lean_object* v_x_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_){
_start:
{
lean_object* v_res_1941_; 
v_res_1941_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5(v_00_u03b1_1935_, v_x_1936_, v___y_1937_, v___y_1938_, v___y_1939_);
lean_dec(v___y_1939_);
lean_dec_ref(v___y_1938_);
lean_dec(v___y_1937_);
return v_res_1941_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6(lean_object* v_00_u03b2_1942_, lean_object* v_m_1943_, lean_object* v_query_1944_){
_start:
{
lean_object* v___x_1945_; 
v___x_1945_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6___redArg(v_m_1943_, v_query_1944_);
return v___x_1945_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6___boxed(lean_object* v_00_u03b2_1946_, lean_object* v_m_1947_, lean_object* v_query_1948_){
_start:
{
lean_object* v_res_1949_; 
v_res_1949_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6(v_00_u03b2_1946_, v_m_1947_, v_query_1948_);
lean_dec_ref(v_query_1948_);
lean_dec_ref(v_m_1947_);
return v_res_1949_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__7(lean_object* v_00_u03b2_1950_, lean_object* v_m_1951_){
_start:
{
lean_object* v___x_1952_; 
v___x_1952_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__7___redArg(v_m_1951_);
return v___x_1952_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__7___boxed(lean_object* v_00_u03b2_1953_, lean_object* v_m_1954_){
_start:
{
lean_object* v_res_1955_; 
v_res_1955_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__7(v_00_u03b2_1953_, v_m_1954_);
lean_dec_ref(v_m_1954_);
return v_res_1955_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4(lean_object* v_00_u03b2_1956_, lean_object* v_m_1957_, lean_object* v_query_1958_){
_start:
{
lean_object* v___x_1959_; 
v___x_1959_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___redArg(v_m_1957_, v_query_1958_);
return v___x_1959_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___boxed(lean_object* v_00_u03b2_1960_, lean_object* v_m_1961_, lean_object* v_query_1962_){
_start:
{
lean_object* v_res_1963_; 
v_res_1963_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4(v_00_u03b2_1960_, v_m_1961_, v_query_1962_);
lean_dec_ref(v_query_1962_);
lean_dec_ref(v_m_1961_);
return v_res_1963_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10(lean_object* v_00_u03b2_1964_, lean_object* v_m_1965_, lean_object* v_query_1966_, lean_object* v_x_1967_, lean_object* v_x_1968_, lean_object* v_x_1969_, lean_object* v_x_1970_){
_start:
{
lean_object* v___x_1971_; 
v___x_1971_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___redArg(v_m_1965_, v_query_1966_, v_x_1967_, v_x_1968_, v_x_1969_);
return v___x_1971_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___boxed(lean_object* v_00_u03b2_1972_, lean_object* v_m_1973_, lean_object* v_query_1974_, lean_object* v_x_1975_, lean_object* v_x_1976_, lean_object* v_x_1977_, lean_object* v_x_1978_){
_start:
{
lean_object* v_res_1979_; 
v_res_1979_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10(v_00_u03b2_1972_, v_m_1973_, v_query_1974_, v_x_1975_, v_x_1976_, v_x_1977_, v_x_1978_);
lean_dec_ref(v_query_1974_);
lean_dec_ref(v_m_1973_);
return v_res_1979_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__7_spec__12(lean_object* v_00_u03b2_1980_, lean_object* v_init_1981_, lean_object* v_b_1982_){
_start:
{
lean_object* v___x_1983_; 
v___x_1983_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__7_spec__12___redArg(v_init_1981_, v_b_1982_);
return v___x_1983_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__7_spec__12___boxed(lean_object* v_00_u03b2_1984_, lean_object* v_init_1985_, lean_object* v_b_1986_){
_start:
{
lean_object* v_res_1987_; 
v_res_1987_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__7_spec__12(v_00_u03b2_1984_, v_init_1985_, v_b_1986_);
lean_dec_ref(v_b_1986_);
return v_res_1987_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__7_spec__12_spec__13(lean_object* v_00_u03b2_1988_, lean_object* v_b_1989_, lean_object* v_acc_1990_, lean_object* v_i_1991_){
_start:
{
lean_object* v___x_1992_; 
v___x_1992_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__7_spec__12_spec__13___redArg(v_b_1989_, v_acc_1990_, v_i_1991_);
return v___x_1992_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__7_spec__12_spec__13___boxed(lean_object* v_00_u03b2_1993_, lean_object* v_b_1994_, lean_object* v_acc_1995_, lean_object* v_i_1996_){
_start:
{
lean_object* v_res_1997_; 
v_res_1997_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__7_spec__12_spec__13(v_00_u03b2_1993_, v_b_1994_, v_acc_1995_, v_i_1996_);
lean_dec_ref(v_b_1994_);
return v_res_1997_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__0(lean_object* v_toApplicative_1998_, lean_object* v_a_1999_){
_start:
{
lean_object* v_toPure_2000_; lean_object* v___x_2001_; 
v_toPure_2000_ = lean_ctor_get(v_toApplicative_1998_, 1);
lean_inc(v_toPure_2000_);
lean_dec_ref(v_toApplicative_1998_);
v___x_2001_ = lean_apply_2(v_toPure_2000_, lean_box(0), v_a_1999_);
return v___x_2001_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__13(lean_object* v___x_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_){
_start:
{
lean_object* v___x_2008_; 
v___x_2008_ = l_Lean_Core_checkSystem(v___x_2002_, v___y_2005_, v___y_2006_);
return v___x_2008_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__13___boxed(lean_object* v___x_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_){
_start:
{
lean_object* v_res_2015_; 
v_res_2015_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__13(v___x_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_);
lean_dec(v___y_2013_);
lean_dec_ref(v___y_2012_);
lean_dec(v___y_2011_);
lean_dec_ref(v___y_2010_);
return v_res_2015_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14(lean_object* v_inst_2018_, lean_object* v_x_2019_, lean_object* v___x_2020_, lean_object* v___x_2021_, lean_object* v_inst_2022_, lean_object* v___f_2023_, lean_object* v___x_2024_, lean_object* v___x_2025_, lean_object* v_a_2026_, lean_object* v_toBind_2027_, lean_object* v___f_2028_, lean_object* v_toApplicative_2029_, lean_object* v_a_2030_){
_start:
{
if (lean_obj_tag(v_a_2030_) == 0)
{
lean_object* v___f_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_4451__overap_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; 
lean_dec_ref(v_toApplicative_2029_);
v___f_2031_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14___closed__0));
v___x_2032_ = lean_apply_2(v_inst_2018_, lean_box(0), v___f_2031_);
lean_inc_ref(v___x_2021_);
lean_inc_ref(v___x_2020_);
v___x_2033_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonadLift___aux__1___boxed), 10, 9);
lean_closure_set(v___x_2033_, 0, lean_box(0));
lean_closure_set(v___x_2033_, 1, lean_box(0));
lean_closure_set(v___x_2033_, 2, lean_box(0));
lean_closure_set(v___x_2033_, 3, lean_box(0));
lean_closure_set(v___x_2033_, 4, v_x_2019_);
lean_closure_set(v___x_2033_, 5, v___x_2020_);
lean_closure_set(v___x_2033_, 6, v___x_2021_);
lean_closure_set(v___x_2033_, 7, lean_box(0));
lean_closure_set(v___x_2033_, 8, v___x_2032_);
v___x_2034_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonad___aux__13___boxed), 13, 12);
lean_closure_set(v___x_2034_, 0, lean_box(0));
lean_closure_set(v___x_2034_, 1, lean_box(0));
lean_closure_set(v___x_2034_, 2, lean_box(0));
lean_closure_set(v___x_2034_, 3, lean_box(0));
lean_closure_set(v___x_2034_, 4, v_x_2019_);
lean_closure_set(v___x_2034_, 5, v___x_2020_);
lean_closure_set(v___x_2034_, 6, v___x_2021_);
lean_closure_set(v___x_2034_, 7, v_inst_2022_);
lean_closure_set(v___x_2034_, 8, lean_box(0));
lean_closure_set(v___x_2034_, 9, lean_box(0));
lean_closure_set(v___x_2034_, 10, v___x_2033_);
lean_closure_set(v___x_2034_, 11, v___f_2023_);
v___x_4451__overap_2035_ = l_Lean_Meta_withIncRecDepth___redArg(v___x_2024_, v___x_2025_, v___x_2034_);
lean_inc(v_a_2026_);
v___x_2036_ = lean_apply_1(v___x_4451__overap_2035_, v_a_2026_);
v___x_2037_ = lean_apply_4(v_toBind_2027_, lean_box(0), lean_box(0), v___x_2036_, v___f_2028_);
return v___x_2037_;
}
else
{
lean_object* v_val_2038_; lean_object* v_toPure_2039_; lean_object* v___x_2040_; 
lean_dec(v___f_2028_);
lean_dec(v_toBind_2027_);
lean_dec_ref(v___x_2025_);
lean_dec_ref(v___x_2024_);
lean_dec(v___f_2023_);
lean_dec_ref(v_inst_2022_);
lean_dec_ref(v___x_2021_);
lean_dec_ref(v___x_2020_);
lean_dec(v_inst_2018_);
v_val_2038_ = lean_ctor_get(v_a_2030_, 0);
lean_inc(v_val_2038_);
lean_dec_ref_known(v_a_2030_, 1);
v_toPure_2039_ = lean_ctor_get(v_toApplicative_2029_, 1);
lean_inc(v_toPure_2039_);
lean_dec_ref(v_toApplicative_2029_);
v___x_2040_ = lean_apply_2(v_toPure_2039_, lean_box(0), v_val_2038_);
return v___x_2040_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14___boxed(lean_object* v_inst_2041_, lean_object* v_x_2042_, lean_object* v___x_2043_, lean_object* v___x_2044_, lean_object* v_inst_2045_, lean_object* v___f_2046_, lean_object* v___x_2047_, lean_object* v___x_2048_, lean_object* v_a_2049_, lean_object* v_toBind_2050_, lean_object* v___f_2051_, lean_object* v_toApplicative_2052_, lean_object* v_a_2053_){
_start:
{
lean_object* v_res_2054_; 
v_res_2054_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14(v_inst_2041_, v_x_2042_, v___x_2043_, v___x_2044_, v_inst_2045_, v___f_2046_, v___x_2047_, v___x_2048_, v_a_2049_, v_toBind_2050_, v___f_2051_, v_toApplicative_2052_, v_a_2053_);
lean_dec(v_a_2049_);
return v_res_2054_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__1(lean_object* v___x_2055_, lean_object* v___x_2056_, lean_object* v_declName_2057_, lean_object* v_a_2058_, lean_object* v___f_2059_, uint8_t v_nondep_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_){
_start:
{
uint8_t v___x_2063_; lean_object* v___x_4470__overap_2064_; lean_object* v___x_2065_; 
v___x_2063_ = 0;
v___x_4470__overap_2064_ = l_Lean_Meta_withLetDecl___redArg(v___x_2055_, v___x_2056_, v_declName_2057_, v_a_2058_, v_a_2062_, v___f_2059_, v_nondep_2060_, v___x_2063_);
lean_inc(v_a_2061_);
v___x_2065_ = lean_apply_1(v___x_4470__overap_2064_, v_a_2061_);
return v___x_2065_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__1___boxed(lean_object* v___x_2066_, lean_object* v___x_2067_, lean_object* v_declName_2068_, lean_object* v_a_2069_, lean_object* v___f_2070_, lean_object* v_nondep_2071_, lean_object* v_a_2072_, lean_object* v_a_2073_){
_start:
{
uint8_t v_nondep_4649__boxed_2074_; lean_object* v_res_2075_; 
v_nondep_4649__boxed_2074_ = lean_unbox(v_nondep_2071_);
v_res_2075_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__1(v___x_2066_, v___x_2067_, v_declName_2068_, v_a_2069_, v___f_2070_, v_nondep_4649__boxed_2074_, v_a_2072_, v_a_2073_);
lean_dec(v_a_2072_);
return v_res_2075_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__4(lean_object* v_fvars_2076_, uint8_t v_usedLetOnly_2077_, lean_object* v_inst_2078_, lean_object* v_toBind_2079_, lean_object* v___f_2080_, lean_object* v_a_2081_){
_start:
{
uint8_t v___x_2082_; uint8_t v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; 
v___x_2082_ = 0;
v___x_2083_ = 1;
v___x_2084_ = lean_box(v_usedLetOnly_2077_);
v___x_2085_ = lean_box(v___x_2082_);
v___x_2086_ = lean_box(v___x_2083_);
v___x_2087_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLetFVars___boxed), 10, 5);
lean_closure_set(v___x_2087_, 0, v_fvars_2076_);
lean_closure_set(v___x_2087_, 1, v_a_2081_);
lean_closure_set(v___x_2087_, 2, v___x_2084_);
lean_closure_set(v___x_2087_, 3, v___x_2085_);
lean_closure_set(v___x_2087_, 4, v___x_2086_);
v___x_2088_ = lean_apply_2(v_inst_2078_, lean_box(0), v___x_2087_);
v___x_2089_ = lean_apply_4(v_toBind_2079_, lean_box(0), lean_box(0), v___x_2088_, v___f_2080_);
return v___x_2089_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__4___boxed(lean_object* v_fvars_2090_, lean_object* v_usedLetOnly_2091_, lean_object* v_inst_2092_, lean_object* v_toBind_2093_, lean_object* v___f_2094_, lean_object* v_a_2095_){
_start:
{
uint8_t v_usedLetOnly_boxed_2096_; lean_object* v_res_2097_; 
v_usedLetOnly_boxed_2096_ = lean_unbox(v_usedLetOnly_2091_);
v_res_2097_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__4(v_fvars_2090_, v_usedLetOnly_boxed_2096_, v_inst_2092_, v_toBind_2093_, v___f_2094_, v_a_2095_);
return v_res_2097_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__3(lean_object* v_fvars_2098_, uint8_t v_usedLetOnly_2099_, lean_object* v_inst_2100_, lean_object* v_toBind_2101_, lean_object* v___f_2102_, lean_object* v_a_2103_){
_start:
{
uint8_t v___x_2104_; uint8_t v___x_2105_; uint8_t v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; 
v___x_2104_ = 0;
v___x_2105_ = 1;
v___x_2106_ = 1;
v___x_2107_ = lean_box(v___x_2104_);
v___x_2108_ = lean_box(v_usedLetOnly_2099_);
v___x_2109_ = lean_box(v___x_2104_);
v___x_2110_ = lean_box(v___x_2105_);
v___x_2111_ = lean_box(v___x_2106_);
v___x_2112_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(v___x_2112_, 0, v_fvars_2098_);
lean_closure_set(v___x_2112_, 1, v_a_2103_);
lean_closure_set(v___x_2112_, 2, v___x_2107_);
lean_closure_set(v___x_2112_, 3, v___x_2108_);
lean_closure_set(v___x_2112_, 4, v___x_2109_);
lean_closure_set(v___x_2112_, 5, v___x_2110_);
lean_closure_set(v___x_2112_, 6, v___x_2111_);
v___x_2113_ = lean_apply_2(v_inst_2100_, lean_box(0), v___x_2112_);
v___x_2114_ = lean_apply_4(v_toBind_2101_, lean_box(0), lean_box(0), v___x_2113_, v___f_2102_);
return v___x_2114_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__3___boxed(lean_object* v_fvars_2115_, lean_object* v_usedLetOnly_2116_, lean_object* v_inst_2117_, lean_object* v_toBind_2118_, lean_object* v___f_2119_, lean_object* v_a_2120_){
_start:
{
uint8_t v_usedLetOnly_boxed_2121_; lean_object* v_res_2122_; 
v_usedLetOnly_boxed_2121_ = lean_unbox(v_usedLetOnly_2116_);
v_res_2122_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__3(v_fvars_2115_, v_usedLetOnly_boxed_2121_, v_inst_2117_, v_toBind_2118_, v___f_2119_, v_a_2120_);
return v_res_2122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1(lean_object* v___x_2123_, lean_object* v___x_2124_, lean_object* v_binderName_2125_, uint8_t v_binderInfo_2126_, lean_object* v___f_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_){
_start:
{
uint8_t v___x_2130_; lean_object* v___x_4528__overap_2131_; lean_object* v___x_2132_; 
v___x_2130_ = 0;
v___x_4528__overap_2131_ = l_Lean_Meta_withLocalDecl___redArg(v___x_2123_, v___x_2124_, v_binderName_2125_, v_binderInfo_2126_, v_a_2129_, v___f_2127_, v___x_2130_);
lean_inc(v_a_2128_);
v___x_2132_ = lean_apply_1(v___x_4528__overap_2131_, v_a_2128_);
return v___x_2132_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1___boxed(lean_object* v___x_2133_, lean_object* v___x_2134_, lean_object* v_binderName_2135_, lean_object* v_binderInfo_2136_, lean_object* v___f_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_){
_start:
{
uint8_t v_binderInfo_4717__boxed_2140_; lean_object* v_res_2141_; 
v_binderInfo_4717__boxed_2140_ = lean_unbox(v_binderInfo_2136_);
v_res_2141_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1(v___x_2133_, v___x_2134_, v_binderName_2135_, v_binderInfo_4717__boxed_2140_, v___f_2137_, v_a_2138_, v_a_2139_);
lean_dec(v_a_2138_);
return v_res_2141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__3(lean_object* v_fvars_2142_, uint8_t v_usedLetOnly_2143_, lean_object* v_inst_2144_, lean_object* v_toBind_2145_, lean_object* v___f_2146_, lean_object* v_a_2147_){
_start:
{
uint8_t v___x_2148_; uint8_t v___x_2149_; uint8_t v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; 
v___x_2148_ = 0;
v___x_2149_ = 1;
v___x_2150_ = 1;
v___x_2151_ = lean_box(v___x_2148_);
v___x_2152_ = lean_box(v_usedLetOnly_2143_);
v___x_2153_ = lean_box(v___x_2149_);
v___x_2154_ = lean_box(v___x_2150_);
v___x_2155_ = lean_alloc_closure((void*)(l_Lean_Meta_mkForallFVars___boxed), 11, 6);
lean_closure_set(v___x_2155_, 0, v_fvars_2142_);
lean_closure_set(v___x_2155_, 1, v_a_2147_);
lean_closure_set(v___x_2155_, 2, v___x_2151_);
lean_closure_set(v___x_2155_, 3, v___x_2152_);
lean_closure_set(v___x_2155_, 4, v___x_2153_);
lean_closure_set(v___x_2155_, 5, v___x_2154_);
v___x_2156_ = lean_apply_2(v_inst_2144_, lean_box(0), v___x_2155_);
v___x_2157_ = lean_apply_4(v_toBind_2145_, lean_box(0), lean_box(0), v___x_2156_, v___f_2146_);
return v___x_2157_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__3___boxed(lean_object* v_fvars_2158_, lean_object* v_usedLetOnly_2159_, lean_object* v_inst_2160_, lean_object* v_toBind_2161_, lean_object* v___f_2162_, lean_object* v_a_2163_){
_start:
{
uint8_t v_usedLetOnly_boxed_2164_; lean_object* v_res_2165_; 
v_usedLetOnly_boxed_2164_ = lean_unbox(v_usedLetOnly_2159_);
v_res_2165_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__3(v_fvars_2158_, v_usedLetOnly_boxed_2164_, v_inst_2160_, v_toBind_2161_, v___f_2162_, v_a_2163_);
return v_res_2165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1(lean_object* v_toApplicative_2166_, lean_object* v_acc_2167_, lean_object* v_next_2168_, lean_object* v_a_2169_){
_start:
{
lean_object* v_toPure_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; 
v_toPure_2170_ = lean_ctor_get(v_toApplicative_2166_, 1);
lean_inc(v_toPure_2170_);
lean_dec_ref(v_toApplicative_2166_);
v___x_2171_ = lean_array_fset(v_acc_2167_, v_next_2168_, v_a_2169_);
v___x_2172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2172_, 0, v___x_2171_);
v___x_2173_ = lean_apply_2(v_toPure_2170_, lean_box(0), v___x_2172_);
return v___x_2173_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1___boxed(lean_object* v_toApplicative_2174_, lean_object* v_acc_2175_, lean_object* v_next_2176_, lean_object* v_a_2177_){
_start:
{
lean_object* v_res_2178_; 
v_res_2178_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1(v_toApplicative_2174_, v_acc_2175_, v_next_2176_, v_a_2177_);
lean_dec(v_next_2176_);
return v_res_2178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__2(lean_object* v_toApplicative_2179_, lean_object* v_next_2180_, lean_object* v_G_2181_, lean_object* v___y_2182_, lean_object* v_a_2183_){
_start:
{
if (lean_obj_tag(v_a_2183_) == 0)
{
lean_object* v_a_2184_; lean_object* v_toPure_2185_; lean_object* v___x_2186_; 
lean_dec(v_G_2181_);
v_a_2184_ = lean_ctor_get(v_a_2183_, 0);
lean_inc(v_a_2184_);
lean_dec_ref_known(v_a_2183_, 1);
v_toPure_2185_ = lean_ctor_get(v_toApplicative_2179_, 1);
lean_inc(v_toPure_2185_);
lean_dec_ref(v_toApplicative_2179_);
v___x_2186_ = lean_apply_2(v_toPure_2185_, lean_box(0), v_a_2184_);
return v___x_2186_;
}
else
{
lean_object* v_a_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; 
lean_dec_ref(v_toApplicative_2179_);
v_a_2187_ = lean_ctor_get(v_a_2183_, 0);
lean_inc(v_a_2187_);
lean_dec_ref_known(v_a_2183_, 1);
v___x_2188_ = lean_unsigned_to_nat(1u);
v___x_2189_ = lean_nat_add(v_next_2180_, v___x_2188_);
lean_inc(v___y_2182_);
v___x_2190_ = lean_apply_5(v_G_2181_, v___x_2189_, v_a_2187_, lean_box(0), lean_box(0), v___y_2182_);
return v___x_2190_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__2___boxed(lean_object* v_toApplicative_2191_, lean_object* v_next_2192_, lean_object* v_G_2193_, lean_object* v___y_2194_, lean_object* v_a_2195_){
_start:
{
lean_object* v_res_2196_; 
v_res_2196_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__2(v_toApplicative_2191_, v_next_2192_, v_G_2193_, v___y_2194_, v_a_2195_);
lean_dec(v___y_2194_);
lean_dec(v_next_2192_);
return v_res_2196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__7(lean_object* v___f_2197_, lean_object* v___y_2198_, lean_object* v_a_2199_){
_start:
{
lean_object* v___x_2200_; 
lean_inc(v___y_2198_);
v___x_2200_ = lean_apply_2(v___f_2197_, v_a_2199_, v___y_2198_);
return v___x_2200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__7___boxed(lean_object* v___f_2201_, lean_object* v___y_2202_, lean_object* v_a_2203_){
_start:
{
lean_object* v_res_2204_; 
v_res_2204_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__7(v___f_2201_, v___y_2202_, v_a_2203_);
lean_dec(v___y_2202_);
return v_res_2204_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5(lean_object* v_f_2205_, lean_object* v_inst_2206_, lean_object* v_inst_2207_, lean_object* v_inst_2208_, lean_object* v_pre_2209_, lean_object* v_post_2210_, uint8_t v_usedLetOnly_2211_, uint8_t v_skipConstInApp_2212_, uint8_t v_skipInstances_2213_, lean_object* v_x_2214_, lean_object* v_x_2215_, lean_object* v___y_2216_, lean_object* v_a_2217_){
_start:
{
lean_object* v___x_2218_; lean_object* v___x_2219_; 
v___x_2218_ = l_Lean_mkAppN(v_f_2205_, v_a_2217_);
v___x_2219_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2206_, v_inst_2207_, v_inst_2208_, v_pre_2209_, v_post_2210_, v_usedLetOnly_2211_, v_skipConstInApp_2212_, v_skipInstances_2213_, v_x_2214_, v_x_2215_, v___x_2218_, v___y_2216_);
return v___x_2219_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5___boxed(lean_object* v_f_2220_, lean_object* v_inst_2221_, lean_object* v_inst_2222_, lean_object* v_inst_2223_, lean_object* v_pre_2224_, lean_object* v_post_2225_, lean_object* v_usedLetOnly_2226_, lean_object* v_skipConstInApp_2227_, lean_object* v_skipInstances_2228_, lean_object* v_x_2229_, lean_object* v_x_2230_, lean_object* v___y_2231_, lean_object* v_a_2232_){
_start:
{
uint8_t v_usedLetOnly_boxed_2233_; uint8_t v_skipConstInApp_boxed_2234_; uint8_t v_skipInstances_boxed_2235_; lean_object* v_res_2236_; 
v_usedLetOnly_boxed_2233_ = lean_unbox(v_usedLetOnly_2226_);
v_skipConstInApp_boxed_2234_ = lean_unbox(v_skipConstInApp_2227_);
v_skipInstances_boxed_2235_ = lean_unbox(v_skipInstances_2228_);
v_res_2236_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5(v_f_2220_, v_inst_2221_, v_inst_2222_, v_inst_2223_, v_pre_2224_, v_post_2225_, v_usedLetOnly_boxed_2233_, v_skipConstInApp_boxed_2234_, v_skipInstances_boxed_2235_, v_x_2229_, v_x_2230_, v___y_2231_, v_a_2232_);
lean_dec_ref(v_a_2232_);
lean_dec(v___y_2231_);
return v_res_2236_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___boxed(lean_object* v_inst_2237_, lean_object* v_inst_2238_, lean_object* v_inst_2239_, lean_object* v_pre_2240_, lean_object* v_post_2241_, lean_object* v_usedLetOnly_2242_, lean_object* v_skipConstInApp_2243_, lean_object* v_skipInstances_2244_, lean_object* v_x_2245_, lean_object* v_x_2246_, lean_object* v_e_2247_, lean_object* v_a_2248_){
_start:
{
uint8_t v_usedLetOnly_boxed_2249_; uint8_t v_skipConstInApp_boxed_2250_; uint8_t v_skipInstances_boxed_2251_; lean_object* v_res_2252_; 
v_usedLetOnly_boxed_2249_ = lean_unbox(v_usedLetOnly_2242_);
v_skipConstInApp_boxed_2250_ = lean_unbox(v_skipConstInApp_2243_);
v_skipInstances_boxed_2251_ = lean_unbox(v_skipInstances_2244_);
v_res_2252_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2237_, v_inst_2238_, v_inst_2239_, v_pre_2240_, v_post_2241_, v_usedLetOnly_boxed_2249_, v_skipConstInApp_boxed_2250_, v_skipInstances_boxed_2251_, v_x_2245_, v_x_2246_, v_e_2247_, v_a_2248_);
lean_dec(v_a_2248_);
return v_res_2252_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__4(lean_object* v___x_2253_, lean_object* v_toApplicative_2254_, lean_object* v_toBind_2255_, lean_object* v___f_2256_, lean_object* v_paramInfo_2257_, lean_object* v_inst_2258_, lean_object* v_inst_2259_, lean_object* v_inst_2260_, lean_object* v_pre_2261_, lean_object* v_post_2262_, uint8_t v_usedLetOnly_2263_, uint8_t v_skipConstInApp_2264_, uint8_t v_skipInstances_2265_, lean_object* v_x_2266_, lean_object* v_x_2267_, lean_object* v_next_2268_, lean_object* v_acc_2269_, lean_object* v_h_2270_, lean_object* v_G_2271_, lean_object* v___y_2272_){
_start:
{
uint8_t v___x_2273_; 
v___x_2273_ = lean_nat_dec_lt(v_next_2268_, v___x_2253_);
if (v___x_2273_ == 0)
{
lean_object* v_toPure_2274_; lean_object* v___x_2275_; 
lean_dec(v_G_2271_);
lean_dec(v_next_2268_);
lean_dec(v_x_2267_);
lean_dec(v_post_2262_);
lean_dec(v_pre_2261_);
lean_dec_ref(v_inst_2260_);
lean_dec(v_inst_2259_);
lean_dec_ref(v_inst_2258_);
lean_dec(v___f_2256_);
lean_dec(v_toBind_2255_);
v_toPure_2274_ = lean_ctor_get(v_toApplicative_2254_, 1);
lean_inc(v_toPure_2274_);
lean_dec_ref(v_toApplicative_2254_);
v___x_2275_ = lean_apply_2(v_toPure_2274_, lean_box(0), v_acc_2269_);
return v___x_2275_;
}
else
{
lean_object* v___f_2276_; lean_object* v___y_2278_; lean_object* v___x_2281_; lean_object* v___x_2282_; uint8_t v___x_2283_; 
lean_inc(v___y_2272_);
lean_inc(v_next_2268_);
lean_inc_ref(v_toApplicative_2254_);
v___f_2276_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__2___boxed), 5, 4);
lean_closure_set(v___f_2276_, 0, v_toApplicative_2254_);
lean_closure_set(v___f_2276_, 1, v_next_2268_);
lean_closure_set(v___f_2276_, 2, v_G_2271_);
lean_closure_set(v___f_2276_, 3, v___y_2272_);
v___x_2281_ = lean_array_fget_borrowed(v_acc_2269_, v_next_2268_);
v___x_2282_ = lean_array_get_size(v_paramInfo_2257_);
v___x_2283_ = lean_nat_dec_lt(v_next_2268_, v___x_2282_);
if (v___x_2283_ == 0)
{
lean_object* v___f_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; 
lean_inc(v___x_2281_);
v___f_2284_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2284_, 0, v_toApplicative_2254_);
lean_closure_set(v___f_2284_, 1, v_acc_2269_);
lean_closure_set(v___f_2284_, 2, v_next_2268_);
v___x_2285_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2258_, v_inst_2259_, v_inst_2260_, v_pre_2261_, v_post_2262_, v_usedLetOnly_2263_, v_skipConstInApp_2264_, v_skipInstances_2265_, v_x_2266_, v_x_2267_, v___x_2281_, v___y_2272_);
lean_inc(v_toBind_2255_);
v___x_2286_ = lean_apply_4(v_toBind_2255_, lean_box(0), lean_box(0), v___x_2285_, v___f_2284_);
v___y_2278_ = v___x_2286_;
goto v___jp_2277_;
}
else
{
lean_object* v___x_2287_; uint8_t v_isInstance_2288_; 
v___x_2287_ = lean_array_fget_borrowed(v_paramInfo_2257_, v_next_2268_);
v_isInstance_2288_ = lean_ctor_get_uint8(v___x_2287_, sizeof(void*)*1 + 4);
if (v_isInstance_2288_ == 0)
{
lean_object* v___f_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; 
lean_inc(v___x_2281_);
v___f_2289_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2289_, 0, v_toApplicative_2254_);
lean_closure_set(v___f_2289_, 1, v_acc_2269_);
lean_closure_set(v___f_2289_, 2, v_next_2268_);
v___x_2290_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2258_, v_inst_2259_, v_inst_2260_, v_pre_2261_, v_post_2262_, v_usedLetOnly_2263_, v_skipConstInApp_2264_, v_skipInstances_2265_, v_x_2266_, v_x_2267_, v___x_2281_, v___y_2272_);
lean_inc(v_toBind_2255_);
v___x_2291_ = lean_apply_4(v_toBind_2255_, lean_box(0), lean_box(0), v___x_2290_, v___f_2289_);
v___y_2278_ = v___x_2291_;
goto v___jp_2277_;
}
else
{
lean_object* v_toPure_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; 
lean_dec(v_next_2268_);
lean_dec(v_x_2267_);
lean_dec(v_post_2262_);
lean_dec(v_pre_2261_);
lean_dec_ref(v_inst_2260_);
lean_dec(v_inst_2259_);
lean_dec_ref(v_inst_2258_);
v_toPure_2292_ = lean_ctor_get(v_toApplicative_2254_, 1);
lean_inc(v_toPure_2292_);
lean_dec_ref(v_toApplicative_2254_);
v___x_2293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2293_, 0, v_acc_2269_);
v___x_2294_ = lean_apply_2(v_toPure_2292_, lean_box(0), v___x_2293_);
v___y_2278_ = v___x_2294_;
goto v___jp_2277_;
}
}
v___jp_2277_:
{
lean_object* v___x_2279_; lean_object* v___x_2280_; 
lean_inc(v_toBind_2255_);
v___x_2279_ = lean_apply_4(v_toBind_2255_, lean_box(0), lean_box(0), v___y_2278_, v___f_2256_);
v___x_2280_ = lean_apply_4(v_toBind_2255_, lean_box(0), lean_box(0), v___x_2279_, v___f_2276_);
return v___x_2280_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__4___boxed(lean_object** _args){
lean_object* v___x_2295_ = _args[0];
lean_object* v_toApplicative_2296_ = _args[1];
lean_object* v_toBind_2297_ = _args[2];
lean_object* v___f_2298_ = _args[3];
lean_object* v_paramInfo_2299_ = _args[4];
lean_object* v_inst_2300_ = _args[5];
lean_object* v_inst_2301_ = _args[6];
lean_object* v_inst_2302_ = _args[7];
lean_object* v_pre_2303_ = _args[8];
lean_object* v_post_2304_ = _args[9];
lean_object* v_usedLetOnly_2305_ = _args[10];
lean_object* v_skipConstInApp_2306_ = _args[11];
lean_object* v_skipInstances_2307_ = _args[12];
lean_object* v_x_2308_ = _args[13];
lean_object* v_x_2309_ = _args[14];
lean_object* v_next_2310_ = _args[15];
lean_object* v_acc_2311_ = _args[16];
lean_object* v_h_2312_ = _args[17];
lean_object* v_G_2313_ = _args[18];
lean_object* v___y_2314_ = _args[19];
_start:
{
uint8_t v_usedLetOnly_boxed_2315_; uint8_t v_skipConstInApp_boxed_2316_; uint8_t v_skipInstances_boxed_2317_; lean_object* v_res_2318_; 
v_usedLetOnly_boxed_2315_ = lean_unbox(v_usedLetOnly_2305_);
v_skipConstInApp_boxed_2316_ = lean_unbox(v_skipConstInApp_2306_);
v_skipInstances_boxed_2317_ = lean_unbox(v_skipInstances_2307_);
v_res_2318_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__4(v___x_2295_, v_toApplicative_2296_, v_toBind_2297_, v___f_2298_, v_paramInfo_2299_, v_inst_2300_, v_inst_2301_, v_inst_2302_, v_pre_2303_, v_post_2304_, v_usedLetOnly_boxed_2315_, v_skipConstInApp_boxed_2316_, v_skipInstances_boxed_2317_, v_x_2308_, v_x_2309_, v_next_2310_, v_acc_2311_, v_h_2312_, v_G_2313_, v___y_2314_);
lean_dec(v___y_2314_);
lean_dec_ref(v_paramInfo_2299_);
lean_dec(v___x_2295_);
return v_res_2318_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__3(lean_object* v___x_2319_, lean_object* v_toApplicative_2320_, lean_object* v_toBind_2321_, lean_object* v___f_2322_, lean_object* v_inst_2323_, lean_object* v_inst_2324_, lean_object* v_inst_2325_, lean_object* v_pre_2326_, lean_object* v_post_2327_, uint8_t v_usedLetOnly_2328_, uint8_t v_skipConstInApp_2329_, uint8_t v_skipInstances_2330_, lean_object* v_x_2331_, lean_object* v_x_2332_, lean_object* v_args_2333_, lean_object* v___y_2334_, lean_object* v___f_2335_, lean_object* v_a_2336_){
_start:
{
lean_object* v_paramInfo_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___f_2342_; lean_object* v___x_4288__overap_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; 
v_paramInfo_2337_ = lean_ctor_get(v_a_2336_, 0);
lean_inc_ref(v_paramInfo_2337_);
lean_dec_ref(v_a_2336_);
v___x_2338_ = lean_unsigned_to_nat(0u);
v___x_2339_ = lean_box(v_usedLetOnly_2328_);
v___x_2340_ = lean_box(v_skipConstInApp_2329_);
v___x_2341_ = lean_box(v_skipInstances_2330_);
lean_inc(v_toBind_2321_);
v___f_2342_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__4___boxed), 20, 15);
lean_closure_set(v___f_2342_, 0, v___x_2319_);
lean_closure_set(v___f_2342_, 1, v_toApplicative_2320_);
lean_closure_set(v___f_2342_, 2, v_toBind_2321_);
lean_closure_set(v___f_2342_, 3, v___f_2322_);
lean_closure_set(v___f_2342_, 4, v_paramInfo_2337_);
lean_closure_set(v___f_2342_, 5, v_inst_2323_);
lean_closure_set(v___f_2342_, 6, v_inst_2324_);
lean_closure_set(v___f_2342_, 7, v_inst_2325_);
lean_closure_set(v___f_2342_, 8, v_pre_2326_);
lean_closure_set(v___f_2342_, 9, v_post_2327_);
lean_closure_set(v___f_2342_, 10, v___x_2339_);
lean_closure_set(v___f_2342_, 11, v___x_2340_);
lean_closure_set(v___f_2342_, 12, v___x_2341_);
lean_closure_set(v___f_2342_, 13, v_x_2331_);
lean_closure_set(v___f_2342_, 14, v_x_2332_);
v___x_4288__overap_2343_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_2342_, v___x_2338_, v_args_2333_, lean_box(0));
lean_inc(v___y_2334_);
v___x_2344_ = lean_apply_1(v___x_4288__overap_2343_, v___y_2334_);
v___x_2345_ = lean_apply_4(v_toBind_2321_, lean_box(0), lean_box(0), v___x_2344_, v___f_2335_);
return v___x_2345_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__3___boxed(lean_object** _args){
lean_object* v___x_2346_ = _args[0];
lean_object* v_toApplicative_2347_ = _args[1];
lean_object* v_toBind_2348_ = _args[2];
lean_object* v___f_2349_ = _args[3];
lean_object* v_inst_2350_ = _args[4];
lean_object* v_inst_2351_ = _args[5];
lean_object* v_inst_2352_ = _args[6];
lean_object* v_pre_2353_ = _args[7];
lean_object* v_post_2354_ = _args[8];
lean_object* v_usedLetOnly_2355_ = _args[9];
lean_object* v_skipConstInApp_2356_ = _args[10];
lean_object* v_skipInstances_2357_ = _args[11];
lean_object* v_x_2358_ = _args[12];
lean_object* v_x_2359_ = _args[13];
lean_object* v_args_2360_ = _args[14];
lean_object* v___y_2361_ = _args[15];
lean_object* v___f_2362_ = _args[16];
lean_object* v_a_2363_ = _args[17];
_start:
{
uint8_t v_usedLetOnly_boxed_2364_; uint8_t v_skipConstInApp_boxed_2365_; uint8_t v_skipInstances_boxed_2366_; lean_object* v_res_2367_; 
v_usedLetOnly_boxed_2364_ = lean_unbox(v_usedLetOnly_2355_);
v_skipConstInApp_boxed_2365_ = lean_unbox(v_skipConstInApp_2356_);
v_skipInstances_boxed_2366_ = lean_unbox(v_skipInstances_2357_);
v_res_2367_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__3(v___x_2346_, v_toApplicative_2347_, v_toBind_2348_, v___f_2349_, v_inst_2350_, v_inst_2351_, v_inst_2352_, v_pre_2353_, v_post_2354_, v_usedLetOnly_boxed_2364_, v_skipConstInApp_boxed_2365_, v_skipInstances_boxed_2366_, v_x_2358_, v_x_2359_, v_args_2360_, v___y_2361_, v___f_2362_, v_a_2363_);
lean_dec(v___y_2361_);
return v_res_2367_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__6(uint8_t v_skipInstances_2368_, lean_object* v_inst_2369_, lean_object* v_inst_2370_, lean_object* v_inst_2371_, lean_object* v_pre_2372_, lean_object* v_post_2373_, uint8_t v_usedLetOnly_2374_, uint8_t v_skipConstInApp_2375_, lean_object* v_x_2376_, lean_object* v_x_2377_, lean_object* v_args_2378_, lean_object* v___x_2379_, lean_object* v_toBind_2380_, lean_object* v_toApplicative_2381_, lean_object* v___f_2382_, lean_object* v_f_2383_, lean_object* v___y_2384_){
_start:
{
if (v_skipInstances_2368_ == 0)
{
lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___f_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; size_t v_sz_2393_; size_t v___x_2394_; lean_object* v___x_4301__overap_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; 
lean_dec(v___f_2382_);
lean_dec_ref(v_toApplicative_2381_);
v___x_2385_ = lean_box(v_usedLetOnly_2374_);
v___x_2386_ = lean_box(v_skipConstInApp_2375_);
v___x_2387_ = lean_box(v_skipInstances_2368_);
lean_inc_n(v___y_2384_, 2);
lean_inc(v_x_2377_);
lean_inc(v_post_2373_);
lean_inc(v_pre_2372_);
lean_inc_ref(v_inst_2371_);
lean_inc(v_inst_2370_);
lean_inc_ref(v_inst_2369_);
v___f_2388_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5___boxed), 13, 12);
lean_closure_set(v___f_2388_, 0, v_f_2383_);
lean_closure_set(v___f_2388_, 1, v_inst_2369_);
lean_closure_set(v___f_2388_, 2, v_inst_2370_);
lean_closure_set(v___f_2388_, 3, v_inst_2371_);
lean_closure_set(v___f_2388_, 4, v_pre_2372_);
lean_closure_set(v___f_2388_, 5, v_post_2373_);
lean_closure_set(v___f_2388_, 6, v___x_2385_);
lean_closure_set(v___f_2388_, 7, v___x_2386_);
lean_closure_set(v___f_2388_, 8, v___x_2387_);
lean_closure_set(v___f_2388_, 9, v_x_2376_);
lean_closure_set(v___f_2388_, 10, v_x_2377_);
lean_closure_set(v___f_2388_, 11, v___y_2384_);
v___x_2389_ = lean_box(v_usedLetOnly_2374_);
v___x_2390_ = lean_box(v_skipConstInApp_2375_);
v___x_2391_ = lean_box(v_skipInstances_2368_);
v___x_2392_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___boxed), 12, 10);
lean_closure_set(v___x_2392_, 0, v_inst_2369_);
lean_closure_set(v___x_2392_, 1, v_inst_2370_);
lean_closure_set(v___x_2392_, 2, v_inst_2371_);
lean_closure_set(v___x_2392_, 3, v_pre_2372_);
lean_closure_set(v___x_2392_, 4, v_post_2373_);
lean_closure_set(v___x_2392_, 5, v___x_2389_);
lean_closure_set(v___x_2392_, 6, v___x_2390_);
lean_closure_set(v___x_2392_, 7, v___x_2391_);
lean_closure_set(v___x_2392_, 8, v_x_2376_);
lean_closure_set(v___x_2392_, 9, v_x_2377_);
v_sz_2393_ = lean_array_size(v_args_2378_);
v___x_2394_ = ((size_t)0ULL);
v___x_4301__overap_2395_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2379_, v___x_2392_, v_sz_2393_, v___x_2394_, v_args_2378_);
v___x_2396_ = lean_apply_1(v___x_4301__overap_2395_, v___y_2384_);
v___x_2397_ = lean_apply_4(v_toBind_2380_, lean_box(0), lean_box(0), v___x_2396_, v___f_2388_);
return v___x_2397_;
}
else
{
lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___f_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___f_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; 
lean_dec_ref(v___x_2379_);
v___x_2398_ = lean_box(v_usedLetOnly_2374_);
v___x_2399_ = lean_box(v_skipConstInApp_2375_);
v___x_2400_ = lean_box(v_skipInstances_2368_);
lean_inc_n(v___y_2384_, 2);
lean_inc(v_x_2377_);
lean_inc(v_post_2373_);
lean_inc(v_pre_2372_);
lean_inc_ref(v_inst_2371_);
lean_inc_n(v_inst_2370_, 2);
lean_inc_ref(v_inst_2369_);
lean_inc_ref(v_f_2383_);
v___f_2401_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5___boxed), 13, 12);
lean_closure_set(v___f_2401_, 0, v_f_2383_);
lean_closure_set(v___f_2401_, 1, v_inst_2369_);
lean_closure_set(v___f_2401_, 2, v_inst_2370_);
lean_closure_set(v___f_2401_, 3, v_inst_2371_);
lean_closure_set(v___f_2401_, 4, v_pre_2372_);
lean_closure_set(v___f_2401_, 5, v_post_2373_);
lean_closure_set(v___f_2401_, 6, v___x_2398_);
lean_closure_set(v___f_2401_, 7, v___x_2399_);
lean_closure_set(v___f_2401_, 8, v___x_2400_);
lean_closure_set(v___f_2401_, 9, v_x_2376_);
lean_closure_set(v___f_2401_, 10, v_x_2377_);
lean_closure_set(v___f_2401_, 11, v___y_2384_);
v___x_2402_ = lean_array_get_size(v_args_2378_);
v___x_2403_ = lean_box(v_usedLetOnly_2374_);
v___x_2404_ = lean_box(v_skipConstInApp_2375_);
v___x_2405_ = lean_box(v_skipInstances_2368_);
lean_inc(v_toBind_2380_);
v___f_2406_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__3___boxed), 18, 17);
lean_closure_set(v___f_2406_, 0, v___x_2402_);
lean_closure_set(v___f_2406_, 1, v_toApplicative_2381_);
lean_closure_set(v___f_2406_, 2, v_toBind_2380_);
lean_closure_set(v___f_2406_, 3, v___f_2382_);
lean_closure_set(v___f_2406_, 4, v_inst_2369_);
lean_closure_set(v___f_2406_, 5, v_inst_2370_);
lean_closure_set(v___f_2406_, 6, v_inst_2371_);
lean_closure_set(v___f_2406_, 7, v_pre_2372_);
lean_closure_set(v___f_2406_, 8, v_post_2373_);
lean_closure_set(v___f_2406_, 9, v___x_2403_);
lean_closure_set(v___f_2406_, 10, v___x_2404_);
lean_closure_set(v___f_2406_, 11, v___x_2405_);
lean_closure_set(v___f_2406_, 12, v_x_2376_);
lean_closure_set(v___f_2406_, 13, v_x_2377_);
lean_closure_set(v___f_2406_, 14, v_args_2378_);
lean_closure_set(v___f_2406_, 15, v___y_2384_);
lean_closure_set(v___f_2406_, 16, v___f_2401_);
v___x_2407_ = lean_alloc_closure((void*)(l_Lean_Meta_getFunInfoNArgs___boxed), 7, 2);
lean_closure_set(v___x_2407_, 0, v_f_2383_);
lean_closure_set(v___x_2407_, 1, v___x_2402_);
v___x_2408_ = lean_apply_2(v_inst_2370_, lean_box(0), v___x_2407_);
v___x_2409_ = lean_apply_4(v_toBind_2380_, lean_box(0), lean_box(0), v___x_2408_, v___f_2406_);
return v___x_2409_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__6___boxed(lean_object** _args){
lean_object* v_skipInstances_2410_ = _args[0];
lean_object* v_inst_2411_ = _args[1];
lean_object* v_inst_2412_ = _args[2];
lean_object* v_inst_2413_ = _args[3];
lean_object* v_pre_2414_ = _args[4];
lean_object* v_post_2415_ = _args[5];
lean_object* v_usedLetOnly_2416_ = _args[6];
lean_object* v_skipConstInApp_2417_ = _args[7];
lean_object* v_x_2418_ = _args[8];
lean_object* v_x_2419_ = _args[9];
lean_object* v_args_2420_ = _args[10];
lean_object* v___x_2421_ = _args[11];
lean_object* v_toBind_2422_ = _args[12];
lean_object* v_toApplicative_2423_ = _args[13];
lean_object* v___f_2424_ = _args[14];
lean_object* v_f_2425_ = _args[15];
lean_object* v___y_2426_ = _args[16];
_start:
{
uint8_t v_skipInstances_boxed_2427_; uint8_t v_usedLetOnly_boxed_2428_; uint8_t v_skipConstInApp_boxed_2429_; lean_object* v_res_2430_; 
v_skipInstances_boxed_2427_ = lean_unbox(v_skipInstances_2410_);
v_usedLetOnly_boxed_2428_ = lean_unbox(v_usedLetOnly_2416_);
v_skipConstInApp_boxed_2429_ = lean_unbox(v_skipConstInApp_2417_);
v_res_2430_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__6(v_skipInstances_boxed_2427_, v_inst_2411_, v_inst_2412_, v_inst_2413_, v_pre_2414_, v_post_2415_, v_usedLetOnly_boxed_2428_, v_skipConstInApp_boxed_2429_, v_x_2418_, v_x_2419_, v_args_2420_, v___x_2421_, v_toBind_2422_, v_toApplicative_2423_, v___f_2424_, v_f_2425_, v___y_2426_);
lean_dec(v___y_2426_);
return v_res_2430_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__9(uint8_t v_skipInstances_2431_, lean_object* v_inst_2432_, lean_object* v_inst_2433_, lean_object* v_inst_2434_, lean_object* v_pre_2435_, lean_object* v_post_2436_, uint8_t v_usedLetOnly_2437_, uint8_t v_skipConstInApp_2438_, lean_object* v_x_2439_, lean_object* v_x_2440_, lean_object* v___x_2441_, lean_object* v_toBind_2442_, lean_object* v_toApplicative_2443_, lean_object* v___f_2444_, lean_object* v_f_2445_, lean_object* v_args_2446_, lean_object* v___y_2447_){
_start:
{
lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___f_2451_; lean_object* v___f_2452_; 
v___x_2448_ = lean_box(v_skipInstances_2431_);
v___x_2449_ = lean_box(v_usedLetOnly_2437_);
v___x_2450_ = lean_box(v_skipConstInApp_2438_);
lean_inc_ref(v_toApplicative_2443_);
lean_inc(v_toBind_2442_);
lean_inc(v_x_2440_);
lean_inc(v_post_2436_);
lean_inc(v_pre_2435_);
lean_inc_ref(v_inst_2434_);
lean_inc(v_inst_2433_);
lean_inc_ref(v_inst_2432_);
v___f_2451_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__6___boxed), 17, 15);
lean_closure_set(v___f_2451_, 0, v___x_2448_);
lean_closure_set(v___f_2451_, 1, v_inst_2432_);
lean_closure_set(v___f_2451_, 2, v_inst_2433_);
lean_closure_set(v___f_2451_, 3, v_inst_2434_);
lean_closure_set(v___f_2451_, 4, v_pre_2435_);
lean_closure_set(v___f_2451_, 5, v_post_2436_);
lean_closure_set(v___f_2451_, 6, v___x_2449_);
lean_closure_set(v___f_2451_, 7, v___x_2450_);
lean_closure_set(v___f_2451_, 8, v_x_2439_);
lean_closure_set(v___f_2451_, 9, v_x_2440_);
lean_closure_set(v___f_2451_, 10, v_args_2446_);
lean_closure_set(v___f_2451_, 11, v___x_2441_);
lean_closure_set(v___f_2451_, 12, v_toBind_2442_);
lean_closure_set(v___f_2451_, 13, v_toApplicative_2443_);
lean_closure_set(v___f_2451_, 14, v___f_2444_);
lean_inc(v___y_2447_);
v___f_2452_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__7___boxed), 3, 2);
lean_closure_set(v___f_2452_, 0, v___f_2451_);
lean_closure_set(v___f_2452_, 1, v___y_2447_);
if (v_skipConstInApp_2438_ == 0)
{
lean_dec_ref(v_toApplicative_2443_);
goto v___jp_2453_;
}
else
{
uint8_t v___x_2456_; 
v___x_2456_ = l_Lean_Expr_isConst(v_f_2445_);
if (v___x_2456_ == 0)
{
lean_dec_ref(v_toApplicative_2443_);
goto v___jp_2453_;
}
else
{
lean_object* v_toPure_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; 
lean_dec(v_x_2440_);
lean_dec(v_post_2436_);
lean_dec(v_pre_2435_);
lean_dec_ref(v_inst_2434_);
lean_dec(v_inst_2433_);
lean_dec_ref(v_inst_2432_);
v_toPure_2457_ = lean_ctor_get(v_toApplicative_2443_, 1);
lean_inc(v_toPure_2457_);
lean_dec_ref(v_toApplicative_2443_);
v___x_2458_ = lean_apply_2(v_toPure_2457_, lean_box(0), v_f_2445_);
v___x_2459_ = lean_apply_4(v_toBind_2442_, lean_box(0), lean_box(0), v___x_2458_, v___f_2452_);
return v___x_2459_;
}
}
v___jp_2453_:
{
lean_object* v___x_2454_; lean_object* v___x_2455_; 
v___x_2454_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2432_, v_inst_2433_, v_inst_2434_, v_pre_2435_, v_post_2436_, v_usedLetOnly_2437_, v_skipConstInApp_2438_, v_skipInstances_2431_, v_x_2439_, v_x_2440_, v_f_2445_, v___y_2447_);
v___x_2455_ = lean_apply_4(v_toBind_2442_, lean_box(0), lean_box(0), v___x_2454_, v___f_2452_);
return v___x_2455_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__9___boxed(lean_object** _args){
lean_object* v_skipInstances_2460_ = _args[0];
lean_object* v_inst_2461_ = _args[1];
lean_object* v_inst_2462_ = _args[2];
lean_object* v_inst_2463_ = _args[3];
lean_object* v_pre_2464_ = _args[4];
lean_object* v_post_2465_ = _args[5];
lean_object* v_usedLetOnly_2466_ = _args[6];
lean_object* v_skipConstInApp_2467_ = _args[7];
lean_object* v_x_2468_ = _args[8];
lean_object* v_x_2469_ = _args[9];
lean_object* v___x_2470_ = _args[10];
lean_object* v_toBind_2471_ = _args[11];
lean_object* v_toApplicative_2472_ = _args[12];
lean_object* v___f_2473_ = _args[13];
lean_object* v_f_2474_ = _args[14];
lean_object* v_args_2475_ = _args[15];
lean_object* v___y_2476_ = _args[16];
_start:
{
uint8_t v_skipInstances_boxed_2477_; uint8_t v_usedLetOnly_boxed_2478_; uint8_t v_skipConstInApp_boxed_2479_; lean_object* v_res_2480_; 
v_skipInstances_boxed_2477_ = lean_unbox(v_skipInstances_2460_);
v_usedLetOnly_boxed_2478_ = lean_unbox(v_usedLetOnly_2466_);
v_skipConstInApp_boxed_2479_ = lean_unbox(v_skipConstInApp_2467_);
v_res_2480_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__9(v_skipInstances_boxed_2477_, v_inst_2461_, v_inst_2462_, v_inst_2463_, v_pre_2464_, v_post_2465_, v_usedLetOnly_boxed_2478_, v_skipConstInApp_boxed_2479_, v_x_2468_, v_x_2469_, v___x_2470_, v_toBind_2471_, v_toApplicative_2472_, v___f_2473_, v_f_2474_, v_args_2475_, v___y_2476_);
lean_dec(v___y_2476_);
return v_res_2480_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__0(lean_object* v_fvars_2483_, lean_object* v_inst_2484_, lean_object* v_inst_2485_, lean_object* v_inst_2486_, lean_object* v_pre_2487_, lean_object* v_post_2488_, uint8_t v_usedLetOnly_2489_, uint8_t v_skipConstInApp_2490_, uint8_t v_skipInstances_2491_, lean_object* v_x_2492_, lean_object* v_x_2493_, lean_object* v_body_2494_, lean_object* v_x_2495_, lean_object* v___y_2496_){
_start:
{
lean_object* v___x_2497_; lean_object* v___x_2498_; 
v___x_2497_ = lean_array_push(v_fvars_2483_, v_x_2495_);
v___x_2498_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(v_inst_2484_, v_inst_2485_, v_inst_2486_, v_pre_2487_, v_post_2488_, v_usedLetOnly_2489_, v_skipConstInApp_2490_, v_skipInstances_2491_, v_x_2492_, v_x_2493_, v___x_2497_, v_body_2494_, v___y_2496_);
return v___x_2498_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__0___boxed(lean_object* v_fvars_2499_, lean_object* v_inst_2500_, lean_object* v_inst_2501_, lean_object* v_inst_2502_, lean_object* v_pre_2503_, lean_object* v_post_2504_, lean_object* v_usedLetOnly_2505_, lean_object* v_skipConstInApp_2506_, lean_object* v_skipInstances_2507_, lean_object* v_x_2508_, lean_object* v_x_2509_, lean_object* v_body_2510_, lean_object* v_x_2511_, lean_object* v___y_2512_){
_start:
{
uint8_t v_usedLetOnly_boxed_2513_; uint8_t v_skipConstInApp_boxed_2514_; uint8_t v_skipInstances_boxed_2515_; lean_object* v_res_2516_; 
v_usedLetOnly_boxed_2513_ = lean_unbox(v_usedLetOnly_2505_);
v_skipConstInApp_boxed_2514_ = lean_unbox(v_skipConstInApp_2506_);
v_skipInstances_boxed_2515_ = lean_unbox(v_skipInstances_2507_);
v_res_2516_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__0(v_fvars_2499_, v_inst_2500_, v_inst_2501_, v_inst_2502_, v_pre_2503_, v_post_2504_, v_usedLetOnly_boxed_2513_, v_skipConstInApp_boxed_2514_, v_skipInstances_boxed_2515_, v_x_2508_, v_x_2509_, v_body_2510_, v_x_2511_, v___y_2512_);
lean_dec(v___y_2512_);
return v_res_2516_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3___boxed(lean_object* v_inst_2517_, lean_object* v_inst_2518_, lean_object* v_inst_2519_, lean_object* v_pre_2520_, lean_object* v_post_2521_, lean_object* v_usedLetOnly_2522_, lean_object* v_skipConstInApp_2523_, lean_object* v_skipInstances_2524_, lean_object* v_x_2525_, lean_object* v_x_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_){
_start:
{
uint8_t v_usedLetOnly_boxed_2529_; uint8_t v_skipConstInApp_boxed_2530_; uint8_t v_skipInstances_boxed_2531_; lean_object* v_res_2532_; 
v_usedLetOnly_boxed_2529_ = lean_unbox(v_usedLetOnly_2522_);
v_skipConstInApp_boxed_2530_ = lean_unbox(v_skipConstInApp_2523_);
v_skipInstances_boxed_2531_ = lean_unbox(v_skipInstances_2524_);
v_res_2532_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3(v_inst_2517_, v_inst_2518_, v_inst_2519_, v_pre_2520_, v_post_2521_, v_usedLetOnly_boxed_2529_, v_skipConstInApp_boxed_2530_, v_skipInstances_boxed_2531_, v_x_2525_, v_x_2526_, v_a_2527_, v_a_2528_);
lean_dec(v_a_2527_);
return v_res_2532_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(lean_object* v_inst_2533_, lean_object* v_inst_2534_, lean_object* v_inst_2535_, lean_object* v_pre_2536_, lean_object* v_post_2537_, uint8_t v_usedLetOnly_2538_, uint8_t v_skipConstInApp_2539_, uint8_t v_skipInstances_2540_, lean_object* v_x_2541_, lean_object* v_x_2542_, lean_object* v_fvars_2543_, lean_object* v_e_2544_, lean_object* v_a_2545_){
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
if (lean_obj_tag(v_e_2544_) == 7)
{
lean_object* v_binderName_2553_; lean_object* v_binderType_2554_; lean_object* v_body_2555_; uint8_t v_binderInfo_2556_; lean_object* v_toBind_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___f_2561_; lean_object* v___x_2562_; lean_object* v___f_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; 
v_binderName_2553_ = lean_ctor_get(v_e_2544_, 0);
lean_inc(v_binderName_2553_);
v_binderType_2554_ = lean_ctor_get(v_e_2544_, 1);
lean_inc_ref(v_binderType_2554_);
v_body_2555_ = lean_ctor_get(v_e_2544_, 2);
lean_inc_ref(v_body_2555_);
v_binderInfo_2556_ = lean_ctor_get_uint8(v_e_2544_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2544_, 3);
v_toBind_2557_ = lean_ctor_get(v_inst_2533_, 1);
lean_inc(v_toBind_2557_);
v___x_2558_ = lean_box(v_usedLetOnly_2538_);
v___x_2559_ = lean_box(v_skipConstInApp_2539_);
v___x_2560_ = lean_box(v_skipInstances_2540_);
lean_inc(v_x_2542_);
lean_inc(v_post_2537_);
lean_inc(v_pre_2536_);
lean_inc_ref(v_inst_2535_);
lean_inc(v_inst_2534_);
lean_inc_ref(v_inst_2533_);
lean_inc_ref(v_fvars_2543_);
v___f_2561_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__0___boxed), 14, 12);
lean_closure_set(v___f_2561_, 0, v_fvars_2543_);
lean_closure_set(v___f_2561_, 1, v_inst_2533_);
lean_closure_set(v___f_2561_, 2, v_inst_2534_);
lean_closure_set(v___f_2561_, 3, v_inst_2535_);
lean_closure_set(v___f_2561_, 4, v_pre_2536_);
lean_closure_set(v___f_2561_, 5, v_post_2537_);
lean_closure_set(v___f_2561_, 6, v___x_2558_);
lean_closure_set(v___f_2561_, 7, v___x_2559_);
lean_closure_set(v___f_2561_, 8, v___x_2560_);
lean_closure_set(v___f_2561_, 9, v_x_2541_);
lean_closure_set(v___f_2561_, 10, v_x_2542_);
lean_closure_set(v___f_2561_, 11, v_body_2555_);
v___x_2562_ = lean_box(v_binderInfo_2556_);
lean_inc(v_a_2545_);
v___f_2563_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_2563_, 0, v___x_2552_);
lean_closure_set(v___f_2563_, 1, v___x_2548_);
lean_closure_set(v___f_2563_, 2, v_binderName_2553_);
lean_closure_set(v___f_2563_, 3, v___x_2562_);
lean_closure_set(v___f_2563_, 4, v___f_2561_);
lean_closure_set(v___f_2563_, 5, v_a_2545_);
v___x_2564_ = lean_expr_instantiate_rev(v_binderType_2554_, v_fvars_2543_);
lean_dec_ref(v_fvars_2543_);
lean_dec_ref(v_binderType_2554_);
v___x_2565_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2533_, v_inst_2534_, v_inst_2535_, v_pre_2536_, v_post_2537_, v_usedLetOnly_2538_, v_skipConstInApp_2539_, v_skipInstances_2540_, v_x_2541_, v_x_2542_, v___x_2564_, v_a_2545_);
v___x_2566_ = lean_apply_4(v_toBind_2557_, lean_box(0), lean_box(0), v___x_2565_, v___f_2563_);
return v___x_2566_;
}
else
{
lean_object* v_toBind_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___f_2571_; lean_object* v___x_2572_; lean_object* v___f_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; 
lean_dec_ref_known(v___x_2552_, 2);
lean_dec_ref(v___x_2548_);
v_toBind_2567_ = lean_ctor_get(v_inst_2533_, 1);
lean_inc_n(v_toBind_2567_, 2);
v___x_2568_ = lean_box(v_usedLetOnly_2538_);
v___x_2569_ = lean_box(v_skipConstInApp_2539_);
v___x_2570_ = lean_box(v_skipInstances_2540_);
lean_inc(v_a_2545_);
lean_inc(v_x_2542_);
lean_inc(v_post_2537_);
lean_inc(v_pre_2536_);
lean_inc_ref(v_inst_2535_);
lean_inc_n(v_inst_2534_, 2);
lean_inc_ref(v_inst_2533_);
v___f_2571_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3___boxed), 12, 11);
lean_closure_set(v___f_2571_, 0, v_inst_2533_);
lean_closure_set(v___f_2571_, 1, v_inst_2534_);
lean_closure_set(v___f_2571_, 2, v_inst_2535_);
lean_closure_set(v___f_2571_, 3, v_pre_2536_);
lean_closure_set(v___f_2571_, 4, v_post_2537_);
lean_closure_set(v___f_2571_, 5, v___x_2568_);
lean_closure_set(v___f_2571_, 6, v___x_2569_);
lean_closure_set(v___f_2571_, 7, v___x_2570_);
lean_closure_set(v___f_2571_, 8, v_x_2541_);
lean_closure_set(v___f_2571_, 9, v_x_2542_);
lean_closure_set(v___f_2571_, 10, v_a_2545_);
v___x_2572_ = lean_box(v_usedLetOnly_2538_);
lean_inc_ref(v_fvars_2543_);
v___f_2573_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__3___boxed), 6, 5);
lean_closure_set(v___f_2573_, 0, v_fvars_2543_);
lean_closure_set(v___f_2573_, 1, v___x_2572_);
lean_closure_set(v___f_2573_, 2, v_inst_2534_);
lean_closure_set(v___f_2573_, 3, v_toBind_2567_);
lean_closure_set(v___f_2573_, 4, v___f_2571_);
v___x_2574_ = lean_expr_instantiate_rev(v_e_2544_, v_fvars_2543_);
lean_dec_ref(v_fvars_2543_);
lean_dec_ref(v_e_2544_);
v___x_2575_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2533_, v_inst_2534_, v_inst_2535_, v_pre_2536_, v_post_2537_, v_usedLetOnly_2538_, v_skipConstInApp_2539_, v_skipInstances_2540_, v_x_2541_, v_x_2542_, v___x_2574_, v_a_2545_);
v___x_2576_ = lean_apply_4(v_toBind_2567_, lean_box(0), lean_box(0), v___x_2575_, v___f_2573_);
return v___x_2576_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__0(lean_object* v_fvars_2577_, lean_object* v_inst_2578_, lean_object* v_inst_2579_, lean_object* v_inst_2580_, lean_object* v_pre_2581_, lean_object* v_post_2582_, uint8_t v_usedLetOnly_2583_, uint8_t v_skipConstInApp_2584_, uint8_t v_skipInstances_2585_, lean_object* v_x_2586_, lean_object* v_x_2587_, lean_object* v_body_2588_, lean_object* v_x_2589_, lean_object* v___y_2590_){
_start:
{
lean_object* v___x_2591_; lean_object* v___x_2592_; 
v___x_2591_ = lean_array_push(v_fvars_2577_, v_x_2589_);
v___x_2592_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(v_inst_2578_, v_inst_2579_, v_inst_2580_, v_pre_2581_, v_post_2582_, v_usedLetOnly_2583_, v_skipConstInApp_2584_, v_skipInstances_2585_, v_x_2586_, v_x_2587_, v___x_2591_, v_body_2588_, v___y_2590_);
return v___x_2592_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__0___boxed(lean_object* v_fvars_2593_, lean_object* v_inst_2594_, lean_object* v_inst_2595_, lean_object* v_inst_2596_, lean_object* v_pre_2597_, lean_object* v_post_2598_, lean_object* v_usedLetOnly_2599_, lean_object* v_skipConstInApp_2600_, lean_object* v_skipInstances_2601_, lean_object* v_x_2602_, lean_object* v_x_2603_, lean_object* v_body_2604_, lean_object* v_x_2605_, lean_object* v___y_2606_){
_start:
{
uint8_t v_usedLetOnly_boxed_2607_; uint8_t v_skipConstInApp_boxed_2608_; uint8_t v_skipInstances_boxed_2609_; lean_object* v_res_2610_; 
v_usedLetOnly_boxed_2607_ = lean_unbox(v_usedLetOnly_2599_);
v_skipConstInApp_boxed_2608_ = lean_unbox(v_skipConstInApp_2600_);
v_skipInstances_boxed_2609_ = lean_unbox(v_skipInstances_2601_);
v_res_2610_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__0(v_fvars_2593_, v_inst_2594_, v_inst_2595_, v_inst_2596_, v_pre_2597_, v_post_2598_, v_usedLetOnly_boxed_2607_, v_skipConstInApp_boxed_2608_, v_skipInstances_boxed_2609_, v_x_2602_, v_x_2603_, v_body_2604_, v_x_2605_, v___y_2606_);
lean_dec(v___y_2606_);
return v_res_2610_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(lean_object* v_inst_2611_, lean_object* v_inst_2612_, lean_object* v_inst_2613_, lean_object* v_pre_2614_, lean_object* v_post_2615_, uint8_t v_usedLetOnly_2616_, uint8_t v_skipConstInApp_2617_, uint8_t v_skipInstances_2618_, lean_object* v_x_2619_, lean_object* v_x_2620_, lean_object* v_fvars_2621_, lean_object* v_e_2622_, lean_object* v_a_2623_){
_start:
{
lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___f_2628_; lean_object* v___f_2629_; lean_object* v___x_2630_; 
v___x_2624_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0));
v___x_2625_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1));
lean_inc_ref(v_inst_2611_);
v___x_2626_ = l_Lean_MonadCacheT_instMonad___redArg(v_x_2619_, v___x_2624_, v___x_2625_, v_inst_2611_);
v___x_2627_ = l_Lean_MonadCacheT_instMonadControl___redArg(v_x_2619_, v___x_2624_, v___x_2625_);
lean_inc_ref_n(v_inst_2613_, 2);
lean_inc_ref(v___x_2627_);
v___f_2628_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_2628_, 0, v___x_2627_);
lean_closure_set(v___f_2628_, 1, v_inst_2613_);
v___f_2629_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_2629_, 0, v___x_2627_);
lean_closure_set(v___f_2629_, 1, v_inst_2613_);
v___x_2630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2630_, 0, v___f_2628_);
lean_ctor_set(v___x_2630_, 1, v___f_2629_);
if (lean_obj_tag(v_e_2622_) == 6)
{
lean_object* v_binderName_2631_; lean_object* v_binderType_2632_; lean_object* v_body_2633_; uint8_t v_binderInfo_2634_; lean_object* v_toBind_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___f_2639_; lean_object* v___x_2640_; lean_object* v___f_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; 
v_binderName_2631_ = lean_ctor_get(v_e_2622_, 0);
lean_inc(v_binderName_2631_);
v_binderType_2632_ = lean_ctor_get(v_e_2622_, 1);
lean_inc_ref(v_binderType_2632_);
v_body_2633_ = lean_ctor_get(v_e_2622_, 2);
lean_inc_ref(v_body_2633_);
v_binderInfo_2634_ = lean_ctor_get_uint8(v_e_2622_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2622_, 3);
v_toBind_2635_ = lean_ctor_get(v_inst_2611_, 1);
lean_inc(v_toBind_2635_);
v___x_2636_ = lean_box(v_usedLetOnly_2616_);
v___x_2637_ = lean_box(v_skipConstInApp_2617_);
v___x_2638_ = lean_box(v_skipInstances_2618_);
lean_inc(v_x_2620_);
lean_inc(v_post_2615_);
lean_inc(v_pre_2614_);
lean_inc_ref(v_inst_2613_);
lean_inc(v_inst_2612_);
lean_inc_ref(v_inst_2611_);
lean_inc_ref(v_fvars_2621_);
v___f_2639_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__0___boxed), 14, 12);
lean_closure_set(v___f_2639_, 0, v_fvars_2621_);
lean_closure_set(v___f_2639_, 1, v_inst_2611_);
lean_closure_set(v___f_2639_, 2, v_inst_2612_);
lean_closure_set(v___f_2639_, 3, v_inst_2613_);
lean_closure_set(v___f_2639_, 4, v_pre_2614_);
lean_closure_set(v___f_2639_, 5, v_post_2615_);
lean_closure_set(v___f_2639_, 6, v___x_2636_);
lean_closure_set(v___f_2639_, 7, v___x_2637_);
lean_closure_set(v___f_2639_, 8, v___x_2638_);
lean_closure_set(v___f_2639_, 9, v_x_2619_);
lean_closure_set(v___f_2639_, 10, v_x_2620_);
lean_closure_set(v___f_2639_, 11, v_body_2633_);
v___x_2640_ = lean_box(v_binderInfo_2634_);
lean_inc(v_a_2623_);
v___f_2641_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_2641_, 0, v___x_2630_);
lean_closure_set(v___f_2641_, 1, v___x_2626_);
lean_closure_set(v___f_2641_, 2, v_binderName_2631_);
lean_closure_set(v___f_2641_, 3, v___x_2640_);
lean_closure_set(v___f_2641_, 4, v___f_2639_);
lean_closure_set(v___f_2641_, 5, v_a_2623_);
v___x_2642_ = lean_expr_instantiate_rev(v_binderType_2632_, v_fvars_2621_);
lean_dec_ref(v_fvars_2621_);
lean_dec_ref(v_binderType_2632_);
v___x_2643_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2611_, v_inst_2612_, v_inst_2613_, v_pre_2614_, v_post_2615_, v_usedLetOnly_2616_, v_skipConstInApp_2617_, v_skipInstances_2618_, v_x_2619_, v_x_2620_, v___x_2642_, v_a_2623_);
v___x_2644_ = lean_apply_4(v_toBind_2635_, lean_box(0), lean_box(0), v___x_2643_, v___f_2641_);
return v___x_2644_;
}
else
{
lean_object* v_toBind_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___f_2649_; lean_object* v___x_2650_; lean_object* v___f_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; 
lean_dec_ref_known(v___x_2630_, 2);
lean_dec_ref(v___x_2626_);
v_toBind_2645_ = lean_ctor_get(v_inst_2611_, 1);
lean_inc_n(v_toBind_2645_, 2);
v___x_2646_ = lean_box(v_usedLetOnly_2616_);
v___x_2647_ = lean_box(v_skipConstInApp_2617_);
v___x_2648_ = lean_box(v_skipInstances_2618_);
lean_inc(v_a_2623_);
lean_inc(v_x_2620_);
lean_inc(v_post_2615_);
lean_inc(v_pre_2614_);
lean_inc_ref(v_inst_2613_);
lean_inc_n(v_inst_2612_, 2);
lean_inc_ref(v_inst_2611_);
v___f_2649_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3___boxed), 12, 11);
lean_closure_set(v___f_2649_, 0, v_inst_2611_);
lean_closure_set(v___f_2649_, 1, v_inst_2612_);
lean_closure_set(v___f_2649_, 2, v_inst_2613_);
lean_closure_set(v___f_2649_, 3, v_pre_2614_);
lean_closure_set(v___f_2649_, 4, v_post_2615_);
lean_closure_set(v___f_2649_, 5, v___x_2646_);
lean_closure_set(v___f_2649_, 6, v___x_2647_);
lean_closure_set(v___f_2649_, 7, v___x_2648_);
lean_closure_set(v___f_2649_, 8, v_x_2619_);
lean_closure_set(v___f_2649_, 9, v_x_2620_);
lean_closure_set(v___f_2649_, 10, v_a_2623_);
v___x_2650_ = lean_box(v_usedLetOnly_2616_);
lean_inc_ref(v_fvars_2621_);
v___f_2651_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__3___boxed), 6, 5);
lean_closure_set(v___f_2651_, 0, v_fvars_2621_);
lean_closure_set(v___f_2651_, 1, v___x_2650_);
lean_closure_set(v___f_2651_, 2, v_inst_2612_);
lean_closure_set(v___f_2651_, 3, v_toBind_2645_);
lean_closure_set(v___f_2651_, 4, v___f_2649_);
v___x_2652_ = lean_expr_instantiate_rev(v_e_2622_, v_fvars_2621_);
lean_dec_ref(v_fvars_2621_);
lean_dec_ref(v_e_2622_);
v___x_2653_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2611_, v_inst_2612_, v_inst_2613_, v_pre_2614_, v_post_2615_, v_usedLetOnly_2616_, v_skipConstInApp_2617_, v_skipInstances_2618_, v_x_2619_, v_x_2620_, v___x_2652_, v_a_2623_);
v___x_2654_ = lean_apply_4(v_toBind_2645_, lean_box(0), lean_box(0), v___x_2653_, v___f_2651_);
return v___x_2654_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__0(lean_object* v_fvars_2655_, lean_object* v_inst_2656_, lean_object* v_inst_2657_, lean_object* v_inst_2658_, lean_object* v_pre_2659_, lean_object* v_post_2660_, uint8_t v_usedLetOnly_2661_, uint8_t v_skipConstInApp_2662_, uint8_t v_skipInstances_2663_, lean_object* v_x_2664_, lean_object* v_x_2665_, lean_object* v_body_2666_, lean_object* v_x_2667_, lean_object* v___y_2668_){
_start:
{
lean_object* v___x_2669_; lean_object* v___x_2670_; 
v___x_2669_ = lean_array_push(v_fvars_2655_, v_x_2667_);
v___x_2670_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(v_inst_2656_, v_inst_2657_, v_inst_2658_, v_pre_2659_, v_post_2660_, v_usedLetOnly_2661_, v_skipConstInApp_2662_, v_skipInstances_2663_, v_x_2664_, v_x_2665_, v___x_2669_, v_body_2666_, v___y_2668_);
return v___x_2670_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__0___boxed(lean_object* v_fvars_2671_, lean_object* v_inst_2672_, lean_object* v_inst_2673_, lean_object* v_inst_2674_, lean_object* v_pre_2675_, lean_object* v_post_2676_, lean_object* v_usedLetOnly_2677_, lean_object* v_skipConstInApp_2678_, lean_object* v_skipInstances_2679_, lean_object* v_x_2680_, lean_object* v_x_2681_, lean_object* v_body_2682_, lean_object* v_x_2683_, lean_object* v___y_2684_){
_start:
{
uint8_t v_usedLetOnly_boxed_2685_; uint8_t v_skipConstInApp_boxed_2686_; uint8_t v_skipInstances_boxed_2687_; lean_object* v_res_2688_; 
v_usedLetOnly_boxed_2685_ = lean_unbox(v_usedLetOnly_2677_);
v_skipConstInApp_boxed_2686_ = lean_unbox(v_skipConstInApp_2678_);
v_skipInstances_boxed_2687_ = lean_unbox(v_skipInstances_2679_);
v_res_2688_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__0(v_fvars_2671_, v_inst_2672_, v_inst_2673_, v_inst_2674_, v_pre_2675_, v_post_2676_, v_usedLetOnly_boxed_2685_, v_skipConstInApp_boxed_2686_, v_skipInstances_boxed_2687_, v_x_2680_, v_x_2681_, v_body_2682_, v_x_2683_, v___y_2684_);
lean_dec(v___y_2684_);
return v_res_2688_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__2(lean_object* v___x_2689_, lean_object* v___x_2690_, lean_object* v_declName_2691_, lean_object* v___f_2692_, uint8_t v_nondep_2693_, lean_object* v_a_2694_, lean_object* v_value_2695_, lean_object* v_fvars_2696_, lean_object* v_inst_2697_, lean_object* v_inst_2698_, lean_object* v_inst_2699_, lean_object* v_pre_2700_, lean_object* v_post_2701_, uint8_t v_usedLetOnly_2702_, uint8_t v_skipConstInApp_2703_, uint8_t v_skipInstances_2704_, lean_object* v_x_2705_, lean_object* v_x_2706_, lean_object* v_toBind_2707_, lean_object* v_a_2708_){
_start:
{
lean_object* v___x_2709_; lean_object* v___f_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; 
v___x_2709_ = lean_box(v_nondep_2693_);
lean_inc(v_a_2694_);
v___f_2710_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_2710_, 0, v___x_2689_);
lean_closure_set(v___f_2710_, 1, v___x_2690_);
lean_closure_set(v___f_2710_, 2, v_declName_2691_);
lean_closure_set(v___f_2710_, 3, v_a_2708_);
lean_closure_set(v___f_2710_, 4, v___f_2692_);
lean_closure_set(v___f_2710_, 5, v___x_2709_);
lean_closure_set(v___f_2710_, 6, v_a_2694_);
v___x_2711_ = lean_expr_instantiate_rev(v_value_2695_, v_fvars_2696_);
v___x_2712_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2697_, v_inst_2698_, v_inst_2699_, v_pre_2700_, v_post_2701_, v_usedLetOnly_2702_, v_skipConstInApp_2703_, v_skipInstances_2704_, v_x_2705_, v_x_2706_, v___x_2711_, v_a_2694_);
v___x_2713_ = lean_apply_4(v_toBind_2707_, lean_box(0), lean_box(0), v___x_2712_, v___f_2710_);
return v___x_2713_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__2___boxed(lean_object** _args){
lean_object* v___x_2714_ = _args[0];
lean_object* v___x_2715_ = _args[1];
lean_object* v_declName_2716_ = _args[2];
lean_object* v___f_2717_ = _args[3];
lean_object* v_nondep_2718_ = _args[4];
lean_object* v_a_2719_ = _args[5];
lean_object* v_value_2720_ = _args[6];
lean_object* v_fvars_2721_ = _args[7];
lean_object* v_inst_2722_ = _args[8];
lean_object* v_inst_2723_ = _args[9];
lean_object* v_inst_2724_ = _args[10];
lean_object* v_pre_2725_ = _args[11];
lean_object* v_post_2726_ = _args[12];
lean_object* v_usedLetOnly_2727_ = _args[13];
lean_object* v_skipConstInApp_2728_ = _args[14];
lean_object* v_skipInstances_2729_ = _args[15];
lean_object* v_x_2730_ = _args[16];
lean_object* v_x_2731_ = _args[17];
lean_object* v_toBind_2732_ = _args[18];
lean_object* v_a_2733_ = _args[19];
_start:
{
uint8_t v_nondep_4859__boxed_2734_; uint8_t v_usedLetOnly_boxed_2735_; uint8_t v_skipConstInApp_boxed_2736_; uint8_t v_skipInstances_boxed_2737_; lean_object* v_res_2738_; 
v_nondep_4859__boxed_2734_ = lean_unbox(v_nondep_2718_);
v_usedLetOnly_boxed_2735_ = lean_unbox(v_usedLetOnly_2727_);
v_skipConstInApp_boxed_2736_ = lean_unbox(v_skipConstInApp_2728_);
v_skipInstances_boxed_2737_ = lean_unbox(v_skipInstances_2729_);
v_res_2738_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__2(v___x_2714_, v___x_2715_, v_declName_2716_, v___f_2717_, v_nondep_4859__boxed_2734_, v_a_2719_, v_value_2720_, v_fvars_2721_, v_inst_2722_, v_inst_2723_, v_inst_2724_, v_pre_2725_, v_post_2726_, v_usedLetOnly_boxed_2735_, v_skipConstInApp_boxed_2736_, v_skipInstances_boxed_2737_, v_x_2730_, v_x_2731_, v_toBind_2732_, v_a_2733_);
lean_dec_ref(v_fvars_2721_);
lean_dec_ref(v_value_2720_);
lean_dec(v_a_2719_);
return v_res_2738_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(lean_object* v_inst_2739_, lean_object* v_inst_2740_, lean_object* v_inst_2741_, lean_object* v_pre_2742_, lean_object* v_post_2743_, uint8_t v_usedLetOnly_2744_, uint8_t v_skipConstInApp_2745_, uint8_t v_skipInstances_2746_, lean_object* v_x_2747_, lean_object* v_x_2748_, lean_object* v_fvars_2749_, lean_object* v_e_2750_, lean_object* v_a_2751_){
_start:
{
lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___f_2756_; lean_object* v___f_2757_; lean_object* v___x_2758_; 
v___x_2752_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0));
v___x_2753_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1));
lean_inc_ref(v_inst_2739_);
v___x_2754_ = l_Lean_MonadCacheT_instMonad___redArg(v_x_2747_, v___x_2752_, v___x_2753_, v_inst_2739_);
v___x_2755_ = l_Lean_MonadCacheT_instMonadControl___redArg(v_x_2747_, v___x_2752_, v___x_2753_);
lean_inc_ref_n(v_inst_2741_, 2);
lean_inc_ref(v___x_2755_);
v___f_2756_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_2756_, 0, v___x_2755_);
lean_closure_set(v___f_2756_, 1, v_inst_2741_);
v___f_2757_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_2757_, 0, v___x_2755_);
lean_closure_set(v___f_2757_, 1, v_inst_2741_);
v___x_2758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2758_, 0, v___f_2756_);
lean_ctor_set(v___x_2758_, 1, v___f_2757_);
if (lean_obj_tag(v_e_2750_) == 8)
{
lean_object* v_declName_2759_; lean_object* v_type_2760_; lean_object* v_value_2761_; lean_object* v_body_2762_; uint8_t v_nondep_2763_; lean_object* v_toBind_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___f_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___f_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; 
v_declName_2759_ = lean_ctor_get(v_e_2750_, 0);
lean_inc(v_declName_2759_);
v_type_2760_ = lean_ctor_get(v_e_2750_, 1);
lean_inc_ref(v_type_2760_);
v_value_2761_ = lean_ctor_get(v_e_2750_, 2);
lean_inc_ref(v_value_2761_);
v_body_2762_ = lean_ctor_get(v_e_2750_, 3);
lean_inc_ref(v_body_2762_);
v_nondep_2763_ = lean_ctor_get_uint8(v_e_2750_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_2750_, 4);
v_toBind_2764_ = lean_ctor_get(v_inst_2739_, 1);
lean_inc_n(v_toBind_2764_, 2);
v___x_2765_ = lean_box(v_usedLetOnly_2744_);
v___x_2766_ = lean_box(v_skipConstInApp_2745_);
v___x_2767_ = lean_box(v_skipInstances_2746_);
lean_inc_n(v_x_2748_, 2);
lean_inc_n(v_post_2743_, 2);
lean_inc_n(v_pre_2742_, 2);
lean_inc_ref_n(v_inst_2741_, 2);
lean_inc_n(v_inst_2740_, 2);
lean_inc_ref_n(v_inst_2739_, 2);
lean_inc_ref_n(v_fvars_2749_, 2);
v___f_2768_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__0___boxed), 14, 12);
lean_closure_set(v___f_2768_, 0, v_fvars_2749_);
lean_closure_set(v___f_2768_, 1, v_inst_2739_);
lean_closure_set(v___f_2768_, 2, v_inst_2740_);
lean_closure_set(v___f_2768_, 3, v_inst_2741_);
lean_closure_set(v___f_2768_, 4, v_pre_2742_);
lean_closure_set(v___f_2768_, 5, v_post_2743_);
lean_closure_set(v___f_2768_, 6, v___x_2765_);
lean_closure_set(v___f_2768_, 7, v___x_2766_);
lean_closure_set(v___f_2768_, 8, v___x_2767_);
lean_closure_set(v___f_2768_, 9, v_x_2747_);
lean_closure_set(v___f_2768_, 10, v_x_2748_);
lean_closure_set(v___f_2768_, 11, v_body_2762_);
v___x_2769_ = lean_box(v_nondep_2763_);
v___x_2770_ = lean_box(v_usedLetOnly_2744_);
v___x_2771_ = lean_box(v_skipConstInApp_2745_);
v___x_2772_ = lean_box(v_skipInstances_2746_);
lean_inc(v_a_2751_);
v___f_2773_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__2___boxed), 20, 19);
lean_closure_set(v___f_2773_, 0, v___x_2758_);
lean_closure_set(v___f_2773_, 1, v___x_2754_);
lean_closure_set(v___f_2773_, 2, v_declName_2759_);
lean_closure_set(v___f_2773_, 3, v___f_2768_);
lean_closure_set(v___f_2773_, 4, v___x_2769_);
lean_closure_set(v___f_2773_, 5, v_a_2751_);
lean_closure_set(v___f_2773_, 6, v_value_2761_);
lean_closure_set(v___f_2773_, 7, v_fvars_2749_);
lean_closure_set(v___f_2773_, 8, v_inst_2739_);
lean_closure_set(v___f_2773_, 9, v_inst_2740_);
lean_closure_set(v___f_2773_, 10, v_inst_2741_);
lean_closure_set(v___f_2773_, 11, v_pre_2742_);
lean_closure_set(v___f_2773_, 12, v_post_2743_);
lean_closure_set(v___f_2773_, 13, v___x_2770_);
lean_closure_set(v___f_2773_, 14, v___x_2771_);
lean_closure_set(v___f_2773_, 15, v___x_2772_);
lean_closure_set(v___f_2773_, 16, v_x_2747_);
lean_closure_set(v___f_2773_, 17, v_x_2748_);
lean_closure_set(v___f_2773_, 18, v_toBind_2764_);
v___x_2774_ = lean_expr_instantiate_rev(v_type_2760_, v_fvars_2749_);
lean_dec_ref(v_fvars_2749_);
lean_dec_ref(v_type_2760_);
v___x_2775_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2739_, v_inst_2740_, v_inst_2741_, v_pre_2742_, v_post_2743_, v_usedLetOnly_2744_, v_skipConstInApp_2745_, v_skipInstances_2746_, v_x_2747_, v_x_2748_, v___x_2774_, v_a_2751_);
v___x_2776_ = lean_apply_4(v_toBind_2764_, lean_box(0), lean_box(0), v___x_2775_, v___f_2773_);
return v___x_2776_;
}
else
{
lean_object* v_toBind_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___f_2781_; lean_object* v___x_2782_; lean_object* v___f_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; 
lean_dec_ref_known(v___x_2758_, 2);
lean_dec_ref(v___x_2754_);
v_toBind_2777_ = lean_ctor_get(v_inst_2739_, 1);
lean_inc_n(v_toBind_2777_, 2);
v___x_2778_ = lean_box(v_usedLetOnly_2744_);
v___x_2779_ = lean_box(v_skipConstInApp_2745_);
v___x_2780_ = lean_box(v_skipInstances_2746_);
lean_inc(v_a_2751_);
lean_inc(v_x_2748_);
lean_inc(v_post_2743_);
lean_inc(v_pre_2742_);
lean_inc_ref(v_inst_2741_);
lean_inc_n(v_inst_2740_, 2);
lean_inc_ref(v_inst_2739_);
v___f_2781_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3___boxed), 12, 11);
lean_closure_set(v___f_2781_, 0, v_inst_2739_);
lean_closure_set(v___f_2781_, 1, v_inst_2740_);
lean_closure_set(v___f_2781_, 2, v_inst_2741_);
lean_closure_set(v___f_2781_, 3, v_pre_2742_);
lean_closure_set(v___f_2781_, 4, v_post_2743_);
lean_closure_set(v___f_2781_, 5, v___x_2778_);
lean_closure_set(v___f_2781_, 6, v___x_2779_);
lean_closure_set(v___f_2781_, 7, v___x_2780_);
lean_closure_set(v___f_2781_, 8, v_x_2747_);
lean_closure_set(v___f_2781_, 9, v_x_2748_);
lean_closure_set(v___f_2781_, 10, v_a_2751_);
v___x_2782_ = lean_box(v_usedLetOnly_2744_);
lean_inc_ref(v_fvars_2749_);
v___f_2783_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__4___boxed), 6, 5);
lean_closure_set(v___f_2783_, 0, v_fvars_2749_);
lean_closure_set(v___f_2783_, 1, v___x_2782_);
lean_closure_set(v___f_2783_, 2, v_inst_2740_);
lean_closure_set(v___f_2783_, 3, v_toBind_2777_);
lean_closure_set(v___f_2783_, 4, v___f_2781_);
v___x_2784_ = lean_expr_instantiate_rev(v_e_2750_, v_fvars_2749_);
lean_dec_ref(v_fvars_2749_);
lean_dec_ref(v_e_2750_);
v___x_2785_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2739_, v_inst_2740_, v_inst_2741_, v_pre_2742_, v_post_2743_, v_usedLetOnly_2744_, v_skipConstInApp_2745_, v_skipInstances_2746_, v_x_2747_, v_x_2748_, v___x_2784_, v_a_2751_);
v___x_2786_ = lean_apply_4(v_toBind_2777_, lean_box(0), lean_box(0), v___x_2785_, v___f_2783_);
return v___x_2786_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__8(lean_object* v_expr_2787_, lean_object* v_data_2788_, lean_object* v_inst_2789_, lean_object* v_inst_2790_, lean_object* v_inst_2791_, lean_object* v_pre_2792_, lean_object* v_post_2793_, uint8_t v_usedLetOnly_2794_, uint8_t v_skipConstInApp_2795_, uint8_t v_skipInstances_2796_, lean_object* v_x_2797_, lean_object* v_x_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v_a_2801_){
_start:
{
size_t v___x_2802_; size_t v___x_2803_; uint8_t v___x_2804_; 
v___x_2802_ = lean_ptr_addr(v_expr_2787_);
v___x_2803_ = lean_ptr_addr(v_a_2801_);
v___x_2804_ = lean_usize_dec_eq(v___x_2802_, v___x_2803_);
if (v___x_2804_ == 0)
{
lean_object* v___x_2805_; lean_object* v___x_2806_; 
lean_dec_ref(v___y_2800_);
v___x_2805_ = l_Lean_Expr_mdata___override(v_data_2788_, v_a_2801_);
v___x_2806_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2789_, v_inst_2790_, v_inst_2791_, v_pre_2792_, v_post_2793_, v_usedLetOnly_2794_, v_skipConstInApp_2795_, v_skipInstances_2796_, v_x_2797_, v_x_2798_, v___x_2805_, v___y_2799_);
return v___x_2806_;
}
else
{
lean_object* v___x_2807_; 
lean_dec_ref(v_a_2801_);
lean_dec(v_data_2788_);
v___x_2807_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2789_, v_inst_2790_, v_inst_2791_, v_pre_2792_, v_post_2793_, v_usedLetOnly_2794_, v_skipConstInApp_2795_, v_skipInstances_2796_, v_x_2797_, v_x_2798_, v___y_2800_, v___y_2799_);
return v___x_2807_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__8___boxed(lean_object* v_expr_2808_, lean_object* v_data_2809_, lean_object* v_inst_2810_, lean_object* v_inst_2811_, lean_object* v_inst_2812_, lean_object* v_pre_2813_, lean_object* v_post_2814_, lean_object* v_usedLetOnly_2815_, lean_object* v_skipConstInApp_2816_, lean_object* v_skipInstances_2817_, lean_object* v_x_2818_, lean_object* v_x_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v_a_2822_){
_start:
{
uint8_t v_usedLetOnly_boxed_2823_; uint8_t v_skipConstInApp_boxed_2824_; uint8_t v_skipInstances_boxed_2825_; lean_object* v_res_2826_; 
v_usedLetOnly_boxed_2823_ = lean_unbox(v_usedLetOnly_2815_);
v_skipConstInApp_boxed_2824_ = lean_unbox(v_skipConstInApp_2816_);
v_skipInstances_boxed_2825_ = lean_unbox(v_skipInstances_2817_);
v_res_2826_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__8(v_expr_2808_, v_data_2809_, v_inst_2810_, v_inst_2811_, v_inst_2812_, v_pre_2813_, v_post_2814_, v_usedLetOnly_boxed_2823_, v_skipConstInApp_boxed_2824_, v_skipInstances_boxed_2825_, v_x_2818_, v_x_2819_, v___y_2820_, v___y_2821_, v_a_2822_);
lean_dec(v___y_2820_);
lean_dec_ref(v_expr_2808_);
return v_res_2826_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__10(lean_object* v_struct_2827_, lean_object* v_typeName_2828_, lean_object* v_idx_2829_, lean_object* v_inst_2830_, lean_object* v_inst_2831_, lean_object* v_inst_2832_, lean_object* v_pre_2833_, lean_object* v_post_2834_, uint8_t v_usedLetOnly_2835_, uint8_t v_skipConstInApp_2836_, uint8_t v_skipInstances_2837_, lean_object* v_x_2838_, lean_object* v_x_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v_a_2842_){
_start:
{
size_t v___x_2843_; size_t v___x_2844_; uint8_t v___x_2845_; 
v___x_2843_ = lean_ptr_addr(v_struct_2827_);
v___x_2844_ = lean_ptr_addr(v_a_2842_);
v___x_2845_ = lean_usize_dec_eq(v___x_2843_, v___x_2844_);
if (v___x_2845_ == 0)
{
lean_object* v___x_2846_; lean_object* v___x_2847_; 
lean_dec_ref(v___y_2841_);
v___x_2846_ = l_Lean_Expr_proj___override(v_typeName_2828_, v_idx_2829_, v_a_2842_);
v___x_2847_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2830_, v_inst_2831_, v_inst_2832_, v_pre_2833_, v_post_2834_, v_usedLetOnly_2835_, v_skipConstInApp_2836_, v_skipInstances_2837_, v_x_2838_, v_x_2839_, v___x_2846_, v___y_2840_);
return v___x_2847_;
}
else
{
lean_object* v___x_2848_; 
lean_dec_ref(v_a_2842_);
lean_dec(v_idx_2829_);
lean_dec(v_typeName_2828_);
v___x_2848_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2830_, v_inst_2831_, v_inst_2832_, v_pre_2833_, v_post_2834_, v_usedLetOnly_2835_, v_skipConstInApp_2836_, v_skipInstances_2837_, v_x_2838_, v_x_2839_, v___y_2841_, v___y_2840_);
return v___x_2848_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__10___boxed(lean_object* v_struct_2849_, lean_object* v_typeName_2850_, lean_object* v_idx_2851_, lean_object* v_inst_2852_, lean_object* v_inst_2853_, lean_object* v_inst_2854_, lean_object* v_pre_2855_, lean_object* v_post_2856_, lean_object* v_usedLetOnly_2857_, lean_object* v_skipConstInApp_2858_, lean_object* v_skipInstances_2859_, lean_object* v_x_2860_, lean_object* v_x_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v_a_2864_){
_start:
{
uint8_t v_usedLetOnly_boxed_2865_; uint8_t v_skipConstInApp_boxed_2866_; uint8_t v_skipInstances_boxed_2867_; lean_object* v_res_2868_; 
v_usedLetOnly_boxed_2865_ = lean_unbox(v_usedLetOnly_2857_);
v_skipConstInApp_boxed_2866_ = lean_unbox(v_skipConstInApp_2858_);
v_skipInstances_boxed_2867_ = lean_unbox(v_skipInstances_2859_);
v_res_2868_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__10(v_struct_2849_, v_typeName_2850_, v_idx_2851_, v_inst_2852_, v_inst_2853_, v_inst_2854_, v_pre_2855_, v_post_2856_, v_usedLetOnly_boxed_2865_, v_skipConstInApp_boxed_2866_, v_skipInstances_boxed_2867_, v_x_2860_, v_x_2861_, v___y_2862_, v___y_2863_, v_a_2864_);
lean_dec(v___y_2862_);
lean_dec_ref(v_struct_2849_);
return v_res_2868_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11(lean_object* v_toApplicative_2869_, lean_object* v_inst_2870_, lean_object* v_inst_2871_, lean_object* v_inst_2872_, lean_object* v_pre_2873_, lean_object* v_post_2874_, uint8_t v_usedLetOnly_2875_, uint8_t v_skipConstInApp_2876_, uint8_t v_skipInstances_2877_, lean_object* v_x_2878_, lean_object* v_x_2879_, lean_object* v___y_2880_, lean_object* v___f_2881_, lean_object* v_toBind_2882_, lean_object* v_e_2883_, lean_object* v_a_2884_){
_start:
{
lean_object* v___y_2886_; 
switch(lean_obj_tag(v_a_2884_))
{
case 0:
{
lean_object* v_e_2918_; lean_object* v_toPure_2919_; lean_object* v___x_2920_; 
lean_dec_ref(v_e_2883_);
lean_dec(v_toBind_2882_);
lean_dec(v___f_2881_);
lean_dec(v_x_2879_);
lean_dec(v_post_2874_);
lean_dec(v_pre_2873_);
lean_dec_ref(v_inst_2872_);
lean_dec(v_inst_2871_);
lean_dec_ref(v_inst_2870_);
v_e_2918_ = lean_ctor_get(v_a_2884_, 0);
lean_inc_ref(v_e_2918_);
lean_dec_ref_known(v_a_2884_, 1);
v_toPure_2919_ = lean_ctor_get(v_toApplicative_2869_, 1);
lean_inc(v_toPure_2919_);
lean_dec_ref(v_toApplicative_2869_);
v___x_2920_ = lean_apply_2(v_toPure_2919_, lean_box(0), v_e_2918_);
return v___x_2920_;
}
case 1:
{
lean_object* v_e_2921_; lean_object* v___x_2922_; 
lean_dec_ref(v_e_2883_);
lean_dec(v_toBind_2882_);
lean_dec(v___f_2881_);
lean_dec_ref(v_toApplicative_2869_);
v_e_2921_ = lean_ctor_get(v_a_2884_, 0);
lean_inc_ref(v_e_2921_);
lean_dec_ref_known(v_a_2884_, 1);
v___x_2922_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2870_, v_inst_2871_, v_inst_2872_, v_pre_2873_, v_post_2874_, v_usedLetOnly_2875_, v_skipConstInApp_2876_, v_skipInstances_2877_, v_x_2878_, v_x_2879_, v_e_2921_, v___y_2880_);
return v___x_2922_;
}
default: 
{
lean_object* v_e_x3f_2923_; 
lean_dec_ref(v_toApplicative_2869_);
v_e_x3f_2923_ = lean_ctor_get(v_a_2884_, 0);
lean_inc(v_e_x3f_2923_);
lean_dec_ref_known(v_a_2884_, 1);
if (lean_obj_tag(v_e_x3f_2923_) == 0)
{
v___y_2886_ = v_e_2883_;
goto v___jp_2885_;
}
else
{
lean_object* v_val_2924_; 
lean_dec_ref(v_e_2883_);
v_val_2924_ = lean_ctor_get(v_e_x3f_2923_, 0);
lean_inc(v_val_2924_);
lean_dec_ref_known(v_e_x3f_2923_, 1);
v___y_2886_ = v_val_2924_;
goto v___jp_2885_;
}
}
}
v___jp_2885_:
{
switch(lean_obj_tag(v___y_2886_))
{
case 7:
{
lean_object* v___x_2887_; lean_object* v___x_2888_; 
lean_dec(v_toBind_2882_);
lean_dec(v___f_2881_);
v___x_2887_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_2888_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(v_inst_2870_, v_inst_2871_, v_inst_2872_, v_pre_2873_, v_post_2874_, v_usedLetOnly_2875_, v_skipConstInApp_2876_, v_skipInstances_2877_, v_x_2878_, v_x_2879_, v___x_2887_, v___y_2886_, v___y_2880_);
return v___x_2888_;
}
case 6:
{
lean_object* v___x_2889_; lean_object* v___x_2890_; 
lean_dec(v_toBind_2882_);
lean_dec(v___f_2881_);
v___x_2889_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_2890_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(v_inst_2870_, v_inst_2871_, v_inst_2872_, v_pre_2873_, v_post_2874_, v_usedLetOnly_2875_, v_skipConstInApp_2876_, v_skipInstances_2877_, v_x_2878_, v_x_2879_, v___x_2889_, v___y_2886_, v___y_2880_);
return v___x_2890_;
}
case 8:
{
lean_object* v___x_2891_; lean_object* v___x_2892_; 
lean_dec(v_toBind_2882_);
lean_dec(v___f_2881_);
v___x_2891_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_2892_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(v_inst_2870_, v_inst_2871_, v_inst_2872_, v_pre_2873_, v_post_2874_, v_usedLetOnly_2875_, v_skipConstInApp_2876_, v_skipInstances_2877_, v_x_2878_, v_x_2879_, v___x_2891_, v___y_2886_, v___y_2880_);
return v___x_2892_;
}
case 5:
{
lean_object* v_dummy_2893_; lean_object* v_nargs_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_4405__overap_2898_; lean_object* v___x_2899_; 
lean_dec(v_toBind_2882_);
lean_dec(v_x_2879_);
lean_dec(v_post_2874_);
lean_dec(v_pre_2873_);
lean_dec_ref(v_inst_2872_);
lean_dec(v_inst_2871_);
lean_dec_ref(v_inst_2870_);
v_dummy_2893_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_2894_ = l_Lean_Expr_getAppNumArgs(v___y_2886_);
lean_inc(v_nargs_2894_);
v___x_2895_ = lean_mk_array(v_nargs_2894_, v_dummy_2893_);
v___x_2896_ = lean_unsigned_to_nat(1u);
v___x_2897_ = lean_nat_sub(v_nargs_2894_, v___x_2896_);
lean_dec(v_nargs_2894_);
v___x_4405__overap_2898_ = l_Lean_Expr_withAppAux___redArg(v___f_2881_, v___y_2886_, v___x_2895_, v___x_2897_);
lean_inc(v___y_2880_);
v___x_2899_ = lean_apply_1(v___x_4405__overap_2898_, v___y_2880_);
return v___x_2899_;
}
case 10:
{
lean_object* v_data_2900_; lean_object* v_expr_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___f_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; 
lean_dec(v___f_2881_);
v_data_2900_ = lean_ctor_get(v___y_2886_, 0);
lean_inc(v_data_2900_);
v_expr_2901_ = lean_ctor_get(v___y_2886_, 1);
lean_inc_ref_n(v_expr_2901_, 2);
v___x_2902_ = lean_box(v_usedLetOnly_2875_);
v___x_2903_ = lean_box(v_skipConstInApp_2876_);
v___x_2904_ = lean_box(v_skipInstances_2877_);
lean_inc(v___y_2880_);
lean_inc(v_x_2879_);
lean_inc(v_post_2874_);
lean_inc(v_pre_2873_);
lean_inc_ref(v_inst_2872_);
lean_inc(v_inst_2871_);
lean_inc_ref(v_inst_2870_);
v___f_2905_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__8___boxed), 15, 14);
lean_closure_set(v___f_2905_, 0, v_expr_2901_);
lean_closure_set(v___f_2905_, 1, v_data_2900_);
lean_closure_set(v___f_2905_, 2, v_inst_2870_);
lean_closure_set(v___f_2905_, 3, v_inst_2871_);
lean_closure_set(v___f_2905_, 4, v_inst_2872_);
lean_closure_set(v___f_2905_, 5, v_pre_2873_);
lean_closure_set(v___f_2905_, 6, v_post_2874_);
lean_closure_set(v___f_2905_, 7, v___x_2902_);
lean_closure_set(v___f_2905_, 8, v___x_2903_);
lean_closure_set(v___f_2905_, 9, v___x_2904_);
lean_closure_set(v___f_2905_, 10, v_x_2878_);
lean_closure_set(v___f_2905_, 11, v_x_2879_);
lean_closure_set(v___f_2905_, 12, v___y_2880_);
lean_closure_set(v___f_2905_, 13, v___y_2886_);
v___x_2906_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2870_, v_inst_2871_, v_inst_2872_, v_pre_2873_, v_post_2874_, v_usedLetOnly_2875_, v_skipConstInApp_2876_, v_skipInstances_2877_, v_x_2878_, v_x_2879_, v_expr_2901_, v___y_2880_);
v___x_2907_ = lean_apply_4(v_toBind_2882_, lean_box(0), lean_box(0), v___x_2906_, v___f_2905_);
return v___x_2907_;
}
case 11:
{
lean_object* v_typeName_2908_; lean_object* v_idx_2909_; lean_object* v_struct_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___f_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; 
lean_dec(v___f_2881_);
v_typeName_2908_ = lean_ctor_get(v___y_2886_, 0);
lean_inc(v_typeName_2908_);
v_idx_2909_ = lean_ctor_get(v___y_2886_, 1);
lean_inc(v_idx_2909_);
v_struct_2910_ = lean_ctor_get(v___y_2886_, 2);
lean_inc_ref_n(v_struct_2910_, 2);
v___x_2911_ = lean_box(v_usedLetOnly_2875_);
v___x_2912_ = lean_box(v_skipConstInApp_2876_);
v___x_2913_ = lean_box(v_skipInstances_2877_);
lean_inc(v___y_2880_);
lean_inc(v_x_2879_);
lean_inc(v_post_2874_);
lean_inc(v_pre_2873_);
lean_inc_ref(v_inst_2872_);
lean_inc(v_inst_2871_);
lean_inc_ref(v_inst_2870_);
v___f_2914_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__10___boxed), 16, 15);
lean_closure_set(v___f_2914_, 0, v_struct_2910_);
lean_closure_set(v___f_2914_, 1, v_typeName_2908_);
lean_closure_set(v___f_2914_, 2, v_idx_2909_);
lean_closure_set(v___f_2914_, 3, v_inst_2870_);
lean_closure_set(v___f_2914_, 4, v_inst_2871_);
lean_closure_set(v___f_2914_, 5, v_inst_2872_);
lean_closure_set(v___f_2914_, 6, v_pre_2873_);
lean_closure_set(v___f_2914_, 7, v_post_2874_);
lean_closure_set(v___f_2914_, 8, v___x_2911_);
lean_closure_set(v___f_2914_, 9, v___x_2912_);
lean_closure_set(v___f_2914_, 10, v___x_2913_);
lean_closure_set(v___f_2914_, 11, v_x_2878_);
lean_closure_set(v___f_2914_, 12, v_x_2879_);
lean_closure_set(v___f_2914_, 13, v___y_2880_);
lean_closure_set(v___f_2914_, 14, v___y_2886_);
v___x_2915_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2870_, v_inst_2871_, v_inst_2872_, v_pre_2873_, v_post_2874_, v_usedLetOnly_2875_, v_skipConstInApp_2876_, v_skipInstances_2877_, v_x_2878_, v_x_2879_, v_struct_2910_, v___y_2880_);
v___x_2916_ = lean_apply_4(v_toBind_2882_, lean_box(0), lean_box(0), v___x_2915_, v___f_2914_);
return v___x_2916_;
}
default: 
{
lean_object* v___x_2917_; 
lean_dec(v_toBind_2882_);
lean_dec(v___f_2881_);
v___x_2917_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2870_, v_inst_2871_, v_inst_2872_, v_pre_2873_, v_post_2874_, v_usedLetOnly_2875_, v_skipConstInApp_2876_, v_skipInstances_2877_, v_x_2878_, v_x_2879_, v___y_2886_, v___y_2880_);
return v___x_2917_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___boxed(lean_object* v_toApplicative_2925_, lean_object* v_inst_2926_, lean_object* v_inst_2927_, lean_object* v_inst_2928_, lean_object* v_pre_2929_, lean_object* v_post_2930_, lean_object* v_usedLetOnly_2931_, lean_object* v_skipConstInApp_2932_, lean_object* v_skipInstances_2933_, lean_object* v_x_2934_, lean_object* v_x_2935_, lean_object* v___y_2936_, lean_object* v___f_2937_, lean_object* v_toBind_2938_, lean_object* v_e_2939_, lean_object* v_a_2940_){
_start:
{
uint8_t v_usedLetOnly_boxed_2941_; uint8_t v_skipConstInApp_boxed_2942_; uint8_t v_skipInstances_boxed_2943_; lean_object* v_res_2944_; 
v_usedLetOnly_boxed_2941_ = lean_unbox(v_usedLetOnly_2931_);
v_skipConstInApp_boxed_2942_ = lean_unbox(v_skipConstInApp_2932_);
v_skipInstances_boxed_2943_ = lean_unbox(v_skipInstances_2933_);
v_res_2944_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11(v_toApplicative_2925_, v_inst_2926_, v_inst_2927_, v_inst_2928_, v_pre_2929_, v_post_2930_, v_usedLetOnly_boxed_2941_, v_skipConstInApp_boxed_2942_, v_skipInstances_boxed_2943_, v_x_2934_, v_x_2935_, v___y_2936_, v___f_2937_, v_toBind_2938_, v_e_2939_, v_a_2940_);
lean_dec(v___y_2936_);
return v_res_2944_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12(lean_object* v_toApplicative_2945_, lean_object* v_inst_2946_, lean_object* v_inst_2947_, lean_object* v_inst_2948_, lean_object* v_pre_2949_, lean_object* v_post_2950_, uint8_t v_usedLetOnly_2951_, uint8_t v_skipConstInApp_2952_, uint8_t v_skipInstances_2953_, lean_object* v_x_2954_, lean_object* v_x_2955_, lean_object* v___f_2956_, lean_object* v_toBind_2957_, lean_object* v_e_2958_, lean_object* v_____r_2959_, lean_object* v___y_2960_){
_start:
{
lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___f_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; 
v___x_2961_ = lean_box(v_usedLetOnly_2951_);
v___x_2962_ = lean_box(v_skipConstInApp_2952_);
v___x_2963_ = lean_box(v_skipInstances_2953_);
lean_inc_ref(v_e_2958_);
lean_inc(v_toBind_2957_);
lean_inc(v___y_2960_);
lean_inc(v_pre_2949_);
v___f_2964_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___boxed), 16, 15);
lean_closure_set(v___f_2964_, 0, v_toApplicative_2945_);
lean_closure_set(v___f_2964_, 1, v_inst_2946_);
lean_closure_set(v___f_2964_, 2, v_inst_2947_);
lean_closure_set(v___f_2964_, 3, v_inst_2948_);
lean_closure_set(v___f_2964_, 4, v_pre_2949_);
lean_closure_set(v___f_2964_, 5, v_post_2950_);
lean_closure_set(v___f_2964_, 6, v___x_2961_);
lean_closure_set(v___f_2964_, 7, v___x_2962_);
lean_closure_set(v___f_2964_, 8, v___x_2963_);
lean_closure_set(v___f_2964_, 9, v_x_2954_);
lean_closure_set(v___f_2964_, 10, v_x_2955_);
lean_closure_set(v___f_2964_, 11, v___y_2960_);
lean_closure_set(v___f_2964_, 12, v___f_2956_);
lean_closure_set(v___f_2964_, 13, v_toBind_2957_);
lean_closure_set(v___f_2964_, 14, v_e_2958_);
v___x_2965_ = lean_apply_1(v_pre_2949_, v_e_2958_);
v___x_2966_ = lean_apply_4(v_toBind_2957_, lean_box(0), lean_box(0), v___x_2965_, v___f_2964_);
return v___x_2966_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12___boxed(lean_object* v_toApplicative_2967_, lean_object* v_inst_2968_, lean_object* v_inst_2969_, lean_object* v_inst_2970_, lean_object* v_pre_2971_, lean_object* v_post_2972_, lean_object* v_usedLetOnly_2973_, lean_object* v_skipConstInApp_2974_, lean_object* v_skipInstances_2975_, lean_object* v_x_2976_, lean_object* v_x_2977_, lean_object* v___f_2978_, lean_object* v_toBind_2979_, lean_object* v_e_2980_, lean_object* v_____r_2981_, lean_object* v___y_2982_){
_start:
{
uint8_t v_usedLetOnly_boxed_2983_; uint8_t v_skipConstInApp_boxed_2984_; uint8_t v_skipInstances_boxed_2985_; lean_object* v_res_2986_; 
v_usedLetOnly_boxed_2983_ = lean_unbox(v_usedLetOnly_2973_);
v_skipConstInApp_boxed_2984_ = lean_unbox(v_skipConstInApp_2974_);
v_skipInstances_boxed_2985_ = lean_unbox(v_skipInstances_2975_);
v_res_2986_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12(v_toApplicative_2967_, v_inst_2968_, v_inst_2969_, v_inst_2970_, v_pre_2971_, v_post_2972_, v_usedLetOnly_boxed_2983_, v_skipConstInApp_boxed_2984_, v_skipInstances_boxed_2985_, v_x_2976_, v_x_2977_, v___f_2978_, v_toBind_2979_, v_e_2980_, v_____r_2981_, v___y_2982_);
lean_dec(v___y_2982_);
return v_res_2986_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(lean_object* v_inst_2987_, lean_object* v_inst_2988_, lean_object* v_inst_2989_, lean_object* v_pre_2990_, lean_object* v_post_2991_, uint8_t v_usedLetOnly_2992_, uint8_t v_skipConstInApp_2993_, uint8_t v_skipInstances_2994_, lean_object* v_x_2995_, lean_object* v_x_2996_, lean_object* v_e_2997_, lean_object* v_a_2998_){
_start:
{
lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___f_3003_; lean_object* v___f_3004_; lean_object* v___x_3005_; lean_object* v_toApplicative_3006_; lean_object* v_toBind_3007_; lean_object* v___f_3008_; lean_object* v___f_3009_; lean_object* v___f_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___f_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___f_3018_; lean_object* v___f_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; 
v___x_2999_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0));
v___x_3000_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1));
lean_inc_ref_n(v_inst_2987_, 3);
v___x_3001_ = l_Lean_MonadCacheT_instMonad___redArg(v_x_2995_, v___x_2999_, v___x_3000_, v_inst_2987_);
v___x_3002_ = l_Lean_MonadCacheT_instMonadControl___redArg(v_x_2995_, v___x_2999_, v___x_3000_);
lean_inc_ref_n(v_inst_2989_, 3);
lean_inc_ref(v___x_3002_);
v___f_3003_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_3003_, 0, v___x_3002_);
lean_closure_set(v___f_3003_, 1, v_inst_2989_);
v___f_3004_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_3004_, 0, v___x_3002_);
lean_closure_set(v___f_3004_, 1, v_inst_2989_);
v___x_3005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3005_, 0, v___f_3003_);
lean_ctor_set(v___x_3005_, 1, v___f_3004_);
v_toApplicative_3006_ = lean_ctor_get(v_inst_2987_, 0);
lean_inc_ref_n(v_toApplicative_3006_, 6);
v_toBind_3007_ = lean_ctor_get(v_inst_2987_, 1);
lean_inc_n(v_toBind_3007_, 6);
v___f_3008_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3008_, 0, v_toApplicative_3006_);
lean_inc_n(v_x_2996_, 3);
lean_inc_n(v_a_2998_, 3);
lean_inc_ref_n(v_e_2997_, 2);
v___f_3009_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_3009_, 0, v_toApplicative_3006_);
lean_closure_set(v___f_3009_, 1, v___x_2999_);
lean_closure_set(v___f_3009_, 2, v___x_3000_);
lean_closure_set(v___f_3009_, 3, v_e_2997_);
lean_closure_set(v___f_3009_, 4, v_a_2998_);
lean_closure_set(v___f_3009_, 5, v_x_2996_);
lean_closure_set(v___f_3009_, 6, v_toBind_3007_);
v___f_3010_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__3___boxed), 5, 4);
lean_closure_set(v___f_3010_, 0, v_toApplicative_3006_);
lean_closure_set(v___f_3010_, 1, v___x_2999_);
lean_closure_set(v___f_3010_, 2, v___x_3000_);
lean_closure_set(v___f_3010_, 3, v_e_2997_);
v___x_3011_ = lean_box(v_skipInstances_2994_);
v___x_3012_ = lean_box(v_usedLetOnly_2992_);
v___x_3013_ = lean_box(v_skipConstInApp_2993_);
lean_inc_ref(v___x_3001_);
lean_inc(v_post_2991_);
lean_inc(v_pre_2990_);
lean_inc_n(v_inst_2988_, 2);
v___f_3014_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__9___boxed), 17, 14);
lean_closure_set(v___f_3014_, 0, v___x_3011_);
lean_closure_set(v___f_3014_, 1, v_inst_2987_);
lean_closure_set(v___f_3014_, 2, v_inst_2988_);
lean_closure_set(v___f_3014_, 3, v_inst_2989_);
lean_closure_set(v___f_3014_, 4, v_pre_2990_);
lean_closure_set(v___f_3014_, 5, v_post_2991_);
lean_closure_set(v___f_3014_, 6, v___x_3012_);
lean_closure_set(v___f_3014_, 7, v___x_3013_);
lean_closure_set(v___f_3014_, 8, v_x_2995_);
lean_closure_set(v___f_3014_, 9, v_x_2996_);
lean_closure_set(v___f_3014_, 10, v___x_3001_);
lean_closure_set(v___f_3014_, 11, v_toBind_3007_);
lean_closure_set(v___f_3014_, 12, v_toApplicative_3006_);
lean_closure_set(v___f_3014_, 13, v___f_3008_);
v___x_3015_ = lean_box(v_usedLetOnly_2992_);
v___x_3016_ = lean_box(v_skipConstInApp_2993_);
v___x_3017_ = lean_box(v_skipInstances_2994_);
v___f_3018_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12___boxed), 16, 14);
lean_closure_set(v___f_3018_, 0, v_toApplicative_3006_);
lean_closure_set(v___f_3018_, 1, v_inst_2987_);
lean_closure_set(v___f_3018_, 2, v_inst_2988_);
lean_closure_set(v___f_3018_, 3, v_inst_2989_);
lean_closure_set(v___f_3018_, 4, v_pre_2990_);
lean_closure_set(v___f_3018_, 5, v_post_2991_);
lean_closure_set(v___f_3018_, 6, v___x_3015_);
lean_closure_set(v___f_3018_, 7, v___x_3016_);
lean_closure_set(v___f_3018_, 8, v___x_3017_);
lean_closure_set(v___f_3018_, 9, v_x_2995_);
lean_closure_set(v___f_3018_, 10, v_x_2996_);
lean_closure_set(v___f_3018_, 11, v___f_3014_);
lean_closure_set(v___f_3018_, 12, v_toBind_3007_);
lean_closure_set(v___f_3018_, 13, v_e_2997_);
v___f_3019_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14___boxed), 13, 12);
lean_closure_set(v___f_3019_, 0, v_inst_2988_);
lean_closure_set(v___f_3019_, 1, v_x_2995_);
lean_closure_set(v___f_3019_, 2, v___x_2999_);
lean_closure_set(v___f_3019_, 3, v___x_3000_);
lean_closure_set(v___f_3019_, 4, v_inst_2987_);
lean_closure_set(v___f_3019_, 5, v___f_3018_);
lean_closure_set(v___f_3019_, 6, v___x_3005_);
lean_closure_set(v___f_3019_, 7, v___x_3001_);
lean_closure_set(v___f_3019_, 8, v_a_2998_);
lean_closure_set(v___f_3019_, 9, v_toBind_3007_);
lean_closure_set(v___f_3019_, 10, v___f_3009_);
lean_closure_set(v___f_3019_, 11, v_toApplicative_3006_);
v___x_3020_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3020_, 0, lean_box(0));
lean_closure_set(v___x_3020_, 1, lean_box(0));
lean_closure_set(v___x_3020_, 2, v_a_2998_);
v___x_3021_ = lean_apply_2(v_x_2996_, lean_box(0), v___x_3020_);
v___x_3022_ = lean_apply_4(v_toBind_3007_, lean_box(0), lean_box(0), v___x_3021_, v___f_3010_);
v___x_3023_ = lean_apply_4(v_toBind_3007_, lean_box(0), lean_box(0), v___x_3022_, v___f_3019_);
return v___x_3023_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___lam__0(lean_object* v_toApplicative_3024_, lean_object* v_inst_3025_, lean_object* v_inst_3026_, lean_object* v_inst_3027_, lean_object* v_pre_3028_, lean_object* v_post_3029_, uint8_t v_usedLetOnly_3030_, uint8_t v_skipConstInApp_3031_, uint8_t v_skipInstances_3032_, lean_object* v_x_3033_, lean_object* v_x_3034_, lean_object* v_a_3035_, lean_object* v_e_3036_, lean_object* v_a_3037_){
_start:
{
lean_object* v___y_3039_; 
switch(lean_obj_tag(v_a_3037_))
{
case 0:
{
lean_object* v_e_3042_; lean_object* v_toPure_3043_; lean_object* v___x_3044_; 
lean_dec_ref(v_e_3036_);
lean_dec(v_x_3034_);
lean_dec(v_post_3029_);
lean_dec(v_pre_3028_);
lean_dec_ref(v_inst_3027_);
lean_dec(v_inst_3026_);
lean_dec_ref(v_inst_3025_);
v_e_3042_ = lean_ctor_get(v_a_3037_, 0);
lean_inc_ref(v_e_3042_);
lean_dec_ref_known(v_a_3037_, 1);
v_toPure_3043_ = lean_ctor_get(v_toApplicative_3024_, 1);
lean_inc(v_toPure_3043_);
lean_dec_ref(v_toApplicative_3024_);
v___x_3044_ = lean_apply_2(v_toPure_3043_, lean_box(0), v_e_3042_);
return v___x_3044_;
}
case 1:
{
lean_object* v_e_3045_; lean_object* v___x_3046_; 
lean_dec_ref(v_e_3036_);
lean_dec_ref(v_toApplicative_3024_);
v_e_3045_ = lean_ctor_get(v_a_3037_, 0);
lean_inc_ref(v_e_3045_);
lean_dec_ref_known(v_a_3037_, 1);
v___x_3046_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_3025_, v_inst_3026_, v_inst_3027_, v_pre_3028_, v_post_3029_, v_usedLetOnly_3030_, v_skipConstInApp_3031_, v_skipInstances_3032_, v_x_3033_, v_x_3034_, v_e_3045_, v_a_3035_);
return v___x_3046_;
}
default: 
{
lean_object* v_e_x3f_3047_; 
lean_dec(v_x_3034_);
lean_dec(v_post_3029_);
lean_dec(v_pre_3028_);
lean_dec_ref(v_inst_3027_);
lean_dec(v_inst_3026_);
lean_dec_ref(v_inst_3025_);
v_e_x3f_3047_ = lean_ctor_get(v_a_3037_, 0);
lean_inc(v_e_x3f_3047_);
lean_dec_ref_known(v_a_3037_, 1);
if (lean_obj_tag(v_e_x3f_3047_) == 0)
{
v___y_3039_ = v_e_3036_;
goto v___jp_3038_;
}
else
{
lean_object* v_val_3048_; 
lean_dec_ref(v_e_3036_);
v_val_3048_ = lean_ctor_get(v_e_x3f_3047_, 0);
lean_inc(v_val_3048_);
lean_dec_ref_known(v_e_x3f_3047_, 1);
v___y_3039_ = v_val_3048_;
goto v___jp_3038_;
}
}
}
v___jp_3038_:
{
lean_object* v_toPure_3040_; lean_object* v___x_3041_; 
v_toPure_3040_ = lean_ctor_get(v_toApplicative_3024_, 1);
lean_inc(v_toPure_3040_);
lean_dec_ref(v_toApplicative_3024_);
v___x_3041_ = lean_apply_2(v_toPure_3040_, lean_box(0), v___y_3039_);
return v___x_3041_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___lam__0___boxed(lean_object* v_toApplicative_3049_, lean_object* v_inst_3050_, lean_object* v_inst_3051_, lean_object* v_inst_3052_, lean_object* v_pre_3053_, lean_object* v_post_3054_, lean_object* v_usedLetOnly_3055_, lean_object* v_skipConstInApp_3056_, lean_object* v_skipInstances_3057_, lean_object* v_x_3058_, lean_object* v_x_3059_, lean_object* v_a_3060_, lean_object* v_e_3061_, lean_object* v_a_3062_){
_start:
{
uint8_t v_usedLetOnly_boxed_3063_; uint8_t v_skipConstInApp_boxed_3064_; uint8_t v_skipInstances_boxed_3065_; lean_object* v_res_3066_; 
v_usedLetOnly_boxed_3063_ = lean_unbox(v_usedLetOnly_3055_);
v_skipConstInApp_boxed_3064_ = lean_unbox(v_skipConstInApp_3056_);
v_skipInstances_boxed_3065_ = lean_unbox(v_skipInstances_3057_);
v_res_3066_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___lam__0(v_toApplicative_3049_, v_inst_3050_, v_inst_3051_, v_inst_3052_, v_pre_3053_, v_post_3054_, v_usedLetOnly_boxed_3063_, v_skipConstInApp_boxed_3064_, v_skipInstances_boxed_3065_, v_x_3058_, v_x_3059_, v_a_3060_, v_e_3061_, v_a_3062_);
lean_dec(v_a_3060_);
return v_res_3066_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(lean_object* v_inst_3067_, lean_object* v_inst_3068_, lean_object* v_inst_3069_, lean_object* v_pre_3070_, lean_object* v_post_3071_, uint8_t v_usedLetOnly_3072_, uint8_t v_skipConstInApp_3073_, uint8_t v_skipInstances_3074_, lean_object* v_x_3075_, lean_object* v_x_3076_, lean_object* v_e_3077_, lean_object* v_a_3078_){
_start:
{
lean_object* v_toApplicative_3079_; lean_object* v_toBind_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___f_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; 
v_toApplicative_3079_ = lean_ctor_get(v_inst_3067_, 0);
lean_inc_ref(v_toApplicative_3079_);
v_toBind_3080_ = lean_ctor_get(v_inst_3067_, 1);
lean_inc(v_toBind_3080_);
v___x_3081_ = lean_box(v_usedLetOnly_3072_);
v___x_3082_ = lean_box(v_skipConstInApp_3073_);
v___x_3083_ = lean_box(v_skipInstances_3074_);
lean_inc_ref(v_e_3077_);
lean_inc(v_a_3078_);
lean_inc(v_post_3071_);
v___f_3084_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___lam__0___boxed), 14, 13);
lean_closure_set(v___f_3084_, 0, v_toApplicative_3079_);
lean_closure_set(v___f_3084_, 1, v_inst_3067_);
lean_closure_set(v___f_3084_, 2, v_inst_3068_);
lean_closure_set(v___f_3084_, 3, v_inst_3069_);
lean_closure_set(v___f_3084_, 4, v_pre_3070_);
lean_closure_set(v___f_3084_, 5, v_post_3071_);
lean_closure_set(v___f_3084_, 6, v___x_3081_);
lean_closure_set(v___f_3084_, 7, v___x_3082_);
lean_closure_set(v___f_3084_, 8, v___x_3083_);
lean_closure_set(v___f_3084_, 9, v_x_3075_);
lean_closure_set(v___f_3084_, 10, v_x_3076_);
lean_closure_set(v___f_3084_, 11, v_a_3078_);
lean_closure_set(v___f_3084_, 12, v_e_3077_);
v___x_3085_ = lean_apply_1(v_post_3071_, v_e_3077_);
v___x_3086_ = lean_apply_4(v_toBind_3080_, lean_box(0), lean_box(0), v___x_3085_, v___f_3084_);
return v___x_3086_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3(lean_object* v_inst_3087_, lean_object* v_inst_3088_, lean_object* v_inst_3089_, lean_object* v_pre_3090_, lean_object* v_post_3091_, uint8_t v_usedLetOnly_3092_, uint8_t v_skipConstInApp_3093_, uint8_t v_skipInstances_3094_, lean_object* v_x_3095_, lean_object* v_x_3096_, lean_object* v_a_3097_, lean_object* v_a_3098_){
_start:
{
lean_object* v___x_3099_; 
v___x_3099_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_3087_, v_inst_3088_, v_inst_3089_, v_pre_3090_, v_post_3091_, v_usedLetOnly_3092_, v_skipConstInApp_3093_, v_skipInstances_3094_, v_x_3095_, v_x_3096_, v_a_3098_, v_a_3097_);
return v___x_3099_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___boxed(lean_object* v_inst_3100_, lean_object* v_inst_3101_, lean_object* v_inst_3102_, lean_object* v_pre_3103_, lean_object* v_post_3104_, lean_object* v_usedLetOnly_3105_, lean_object* v_skipConstInApp_3106_, lean_object* v_skipInstances_3107_, lean_object* v_x_3108_, lean_object* v_x_3109_, lean_object* v_e_3110_, lean_object* v_a_3111_){
_start:
{
uint8_t v_usedLetOnly_boxed_3112_; uint8_t v_skipConstInApp_boxed_3113_; uint8_t v_skipInstances_boxed_3114_; lean_object* v_res_3115_; 
v_usedLetOnly_boxed_3112_ = lean_unbox(v_usedLetOnly_3105_);
v_skipConstInApp_boxed_3113_ = lean_unbox(v_skipConstInApp_3106_);
v_skipInstances_boxed_3114_ = lean_unbox(v_skipInstances_3107_);
v_res_3115_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_3100_, v_inst_3101_, v_inst_3102_, v_pre_3103_, v_post_3104_, v_usedLetOnly_boxed_3112_, v_skipConstInApp_boxed_3113_, v_skipInstances_boxed_3114_, v_x_3108_, v_x_3109_, v_e_3110_, v_a_3111_);
lean_dec(v_a_3111_);
return v_res_3115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___boxed(lean_object* v_inst_3116_, lean_object* v_inst_3117_, lean_object* v_inst_3118_, lean_object* v_pre_3119_, lean_object* v_post_3120_, lean_object* v_usedLetOnly_3121_, lean_object* v_skipConstInApp_3122_, lean_object* v_skipInstances_3123_, lean_object* v_x_3124_, lean_object* v_x_3125_, lean_object* v_fvars_3126_, lean_object* v_e_3127_, lean_object* v_a_3128_){
_start:
{
uint8_t v_usedLetOnly_boxed_3129_; uint8_t v_skipConstInApp_boxed_3130_; uint8_t v_skipInstances_boxed_3131_; lean_object* v_res_3132_; 
v_usedLetOnly_boxed_3129_ = lean_unbox(v_usedLetOnly_3121_);
v_skipConstInApp_boxed_3130_ = lean_unbox(v_skipConstInApp_3122_);
v_skipInstances_boxed_3131_ = lean_unbox(v_skipInstances_3123_);
v_res_3132_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(v_inst_3116_, v_inst_3117_, v_inst_3118_, v_pre_3119_, v_post_3120_, v_usedLetOnly_boxed_3129_, v_skipConstInApp_boxed_3130_, v_skipInstances_boxed_3131_, v_x_3124_, v_x_3125_, v_fvars_3126_, v_e_3127_, v_a_3128_);
lean_dec(v_a_3128_);
return v_res_3132_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___boxed(lean_object* v_inst_3133_, lean_object* v_inst_3134_, lean_object* v_inst_3135_, lean_object* v_pre_3136_, lean_object* v_post_3137_, lean_object* v_usedLetOnly_3138_, lean_object* v_skipConstInApp_3139_, lean_object* v_skipInstances_3140_, lean_object* v_x_3141_, lean_object* v_x_3142_, lean_object* v_fvars_3143_, lean_object* v_e_3144_, lean_object* v_a_3145_){
_start:
{
uint8_t v_usedLetOnly_boxed_3146_; uint8_t v_skipConstInApp_boxed_3147_; uint8_t v_skipInstances_boxed_3148_; lean_object* v_res_3149_; 
v_usedLetOnly_boxed_3146_ = lean_unbox(v_usedLetOnly_3138_);
v_skipConstInApp_boxed_3147_ = lean_unbox(v_skipConstInApp_3139_);
v_skipInstances_boxed_3148_ = lean_unbox(v_skipInstances_3140_);
v_res_3149_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(v_inst_3133_, v_inst_3134_, v_inst_3135_, v_pre_3136_, v_post_3137_, v_usedLetOnly_boxed_3146_, v_skipConstInApp_boxed_3147_, v_skipInstances_boxed_3148_, v_x_3141_, v_x_3142_, v_fvars_3143_, v_e_3144_, v_a_3145_);
lean_dec(v_a_3145_);
return v_res_3149_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___boxed(lean_object* v_inst_3150_, lean_object* v_inst_3151_, lean_object* v_inst_3152_, lean_object* v_pre_3153_, lean_object* v_post_3154_, lean_object* v_usedLetOnly_3155_, lean_object* v_skipConstInApp_3156_, lean_object* v_skipInstances_3157_, lean_object* v_x_3158_, lean_object* v_x_3159_, lean_object* v_fvars_3160_, lean_object* v_e_3161_, lean_object* v_a_3162_){
_start:
{
uint8_t v_usedLetOnly_boxed_3163_; uint8_t v_skipConstInApp_boxed_3164_; uint8_t v_skipInstances_boxed_3165_; lean_object* v_res_3166_; 
v_usedLetOnly_boxed_3163_ = lean_unbox(v_usedLetOnly_3155_);
v_skipConstInApp_boxed_3164_ = lean_unbox(v_skipConstInApp_3156_);
v_skipInstances_boxed_3165_ = lean_unbox(v_skipInstances_3157_);
v_res_3166_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(v_inst_3150_, v_inst_3151_, v_inst_3152_, v_pre_3153_, v_post_3154_, v_usedLetOnly_boxed_3163_, v_skipConstInApp_boxed_3164_, v_skipInstances_boxed_3165_, v_x_3158_, v_x_3159_, v_fvars_3160_, v_e_3161_, v_a_3162_);
lean_dec(v_a_3162_);
return v_res_3166_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit(lean_object* v_m_3167_, lean_object* v_inst_3168_, lean_object* v_inst_3169_, lean_object* v_inst_3170_, lean_object* v_pre_3171_, lean_object* v_post_3172_, uint8_t v_usedLetOnly_3173_, uint8_t v_skipConstInApp_3174_, uint8_t v_skipInstances_3175_, lean_object* v_x_3176_, lean_object* v_x_3177_, lean_object* v_e_3178_, lean_object* v_a_3179_){
_start:
{
lean_object* v___x_3180_; 
v___x_3180_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_3168_, v_inst_3169_, v_inst_3170_, v_pre_3171_, v_post_3172_, v_usedLetOnly_3173_, v_skipConstInApp_3174_, v_skipInstances_3175_, v_x_3176_, v_x_3177_, v_e_3178_, v_a_3179_);
return v___x_3180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___boxed(lean_object* v_m_3181_, lean_object* v_inst_3182_, lean_object* v_inst_3183_, lean_object* v_inst_3184_, lean_object* v_pre_3185_, lean_object* v_post_3186_, lean_object* v_usedLetOnly_3187_, lean_object* v_skipConstInApp_3188_, lean_object* v_skipInstances_3189_, lean_object* v_x_3190_, lean_object* v_x_3191_, lean_object* v_e_3192_, lean_object* v_a_3193_){
_start:
{
uint8_t v_usedLetOnly_boxed_3194_; uint8_t v_skipConstInApp_boxed_3195_; uint8_t v_skipInstances_boxed_3196_; lean_object* v_res_3197_; 
v_usedLetOnly_boxed_3194_ = lean_unbox(v_usedLetOnly_3187_);
v_skipConstInApp_boxed_3195_ = lean_unbox(v_skipConstInApp_3188_);
v_skipInstances_boxed_3196_ = lean_unbox(v_skipInstances_3189_);
v_res_3197_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit(v_m_3181_, v_inst_3182_, v_inst_3183_, v_inst_3184_, v_pre_3185_, v_post_3186_, v_usedLetOnly_boxed_3194_, v_skipConstInApp_boxed_3195_, v_skipInstances_boxed_3196_, v_x_3190_, v_x_3191_, v_e_3192_, v_a_3193_);
lean_dec(v_a_3193_);
return v_res_3197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet(lean_object* v_m_3198_, lean_object* v_inst_3199_, lean_object* v_inst_3200_, lean_object* v_inst_3201_, lean_object* v_pre_3202_, lean_object* v_post_3203_, uint8_t v_usedLetOnly_3204_, uint8_t v_skipConstInApp_3205_, uint8_t v_skipInstances_3206_, lean_object* v_x_3207_, lean_object* v_x_3208_, lean_object* v_fvars_3209_, lean_object* v_e_3210_, lean_object* v_a_3211_){
_start:
{
lean_object* v___x_3212_; 
v___x_3212_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(v_inst_3199_, v_inst_3200_, v_inst_3201_, v_pre_3202_, v_post_3203_, v_usedLetOnly_3204_, v_skipConstInApp_3205_, v_skipInstances_3206_, v_x_3207_, v_x_3208_, v_fvars_3209_, v_e_3210_, v_a_3211_);
return v___x_3212_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___boxed(lean_object* v_m_3213_, lean_object* v_inst_3214_, lean_object* v_inst_3215_, lean_object* v_inst_3216_, lean_object* v_pre_3217_, lean_object* v_post_3218_, lean_object* v_usedLetOnly_3219_, lean_object* v_skipConstInApp_3220_, lean_object* v_skipInstances_3221_, lean_object* v_x_3222_, lean_object* v_x_3223_, lean_object* v_fvars_3224_, lean_object* v_e_3225_, lean_object* v_a_3226_){
_start:
{
uint8_t v_usedLetOnly_boxed_3227_; uint8_t v_skipConstInApp_boxed_3228_; uint8_t v_skipInstances_boxed_3229_; lean_object* v_res_3230_; 
v_usedLetOnly_boxed_3227_ = lean_unbox(v_usedLetOnly_3219_);
v_skipConstInApp_boxed_3228_ = lean_unbox(v_skipConstInApp_3220_);
v_skipInstances_boxed_3229_ = lean_unbox(v_skipInstances_3221_);
v_res_3230_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet(v_m_3213_, v_inst_3214_, v_inst_3215_, v_inst_3216_, v_pre_3217_, v_post_3218_, v_usedLetOnly_boxed_3227_, v_skipConstInApp_boxed_3228_, v_skipInstances_boxed_3229_, v_x_3222_, v_x_3223_, v_fvars_3224_, v_e_3225_, v_a_3226_);
lean_dec(v_a_3226_);
return v_res_3230_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost(lean_object* v_m_3231_, lean_object* v_inst_3232_, lean_object* v_inst_3233_, lean_object* v_inst_3234_, lean_object* v_pre_3235_, lean_object* v_post_3236_, uint8_t v_usedLetOnly_3237_, uint8_t v_skipConstInApp_3238_, uint8_t v_skipInstances_3239_, lean_object* v_x_3240_, lean_object* v_x_3241_, lean_object* v_e_3242_, lean_object* v_a_3243_){
_start:
{
lean_object* v___x_3244_; 
v___x_3244_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_3232_, v_inst_3233_, v_inst_3234_, v_pre_3235_, v_post_3236_, v_usedLetOnly_3237_, v_skipConstInApp_3238_, v_skipInstances_3239_, v_x_3240_, v_x_3241_, v_e_3242_, v_a_3243_);
return v___x_3244_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___boxed(lean_object* v_m_3245_, lean_object* v_inst_3246_, lean_object* v_inst_3247_, lean_object* v_inst_3248_, lean_object* v_pre_3249_, lean_object* v_post_3250_, lean_object* v_usedLetOnly_3251_, lean_object* v_skipConstInApp_3252_, lean_object* v_skipInstances_3253_, lean_object* v_x_3254_, lean_object* v_x_3255_, lean_object* v_e_3256_, lean_object* v_a_3257_){
_start:
{
uint8_t v_usedLetOnly_boxed_3258_; uint8_t v_skipConstInApp_boxed_3259_; uint8_t v_skipInstances_boxed_3260_; lean_object* v_res_3261_; 
v_usedLetOnly_boxed_3258_ = lean_unbox(v_usedLetOnly_3251_);
v_skipConstInApp_boxed_3259_ = lean_unbox(v_skipConstInApp_3252_);
v_skipInstances_boxed_3260_ = lean_unbox(v_skipInstances_3253_);
v_res_3261_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost(v_m_3245_, v_inst_3246_, v_inst_3247_, v_inst_3248_, v_pre_3249_, v_post_3250_, v_usedLetOnly_boxed_3258_, v_skipConstInApp_boxed_3259_, v_skipInstances_boxed_3260_, v_x_3254_, v_x_3255_, v_e_3256_, v_a_3257_);
lean_dec(v_a_3257_);
return v_res_3261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda(lean_object* v_m_3262_, lean_object* v_inst_3263_, lean_object* v_inst_3264_, lean_object* v_inst_3265_, lean_object* v_pre_3266_, lean_object* v_post_3267_, uint8_t v_usedLetOnly_3268_, uint8_t v_skipConstInApp_3269_, uint8_t v_skipInstances_3270_, lean_object* v_x_3271_, lean_object* v_x_3272_, lean_object* v_fvars_3273_, lean_object* v_e_3274_, lean_object* v_a_3275_){
_start:
{
lean_object* v___x_3276_; 
v___x_3276_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(v_inst_3263_, v_inst_3264_, v_inst_3265_, v_pre_3266_, v_post_3267_, v_usedLetOnly_3268_, v_skipConstInApp_3269_, v_skipInstances_3270_, v_x_3271_, v_x_3272_, v_fvars_3273_, v_e_3274_, v_a_3275_);
return v___x_3276_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___boxed(lean_object* v_m_3277_, lean_object* v_inst_3278_, lean_object* v_inst_3279_, lean_object* v_inst_3280_, lean_object* v_pre_3281_, lean_object* v_post_3282_, lean_object* v_usedLetOnly_3283_, lean_object* v_skipConstInApp_3284_, lean_object* v_skipInstances_3285_, lean_object* v_x_3286_, lean_object* v_x_3287_, lean_object* v_fvars_3288_, lean_object* v_e_3289_, lean_object* v_a_3290_){
_start:
{
uint8_t v_usedLetOnly_boxed_3291_; uint8_t v_skipConstInApp_boxed_3292_; uint8_t v_skipInstances_boxed_3293_; lean_object* v_res_3294_; 
v_usedLetOnly_boxed_3291_ = lean_unbox(v_usedLetOnly_3283_);
v_skipConstInApp_boxed_3292_ = lean_unbox(v_skipConstInApp_3284_);
v_skipInstances_boxed_3293_ = lean_unbox(v_skipInstances_3285_);
v_res_3294_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda(v_m_3277_, v_inst_3278_, v_inst_3279_, v_inst_3280_, v_pre_3281_, v_post_3282_, v_usedLetOnly_boxed_3291_, v_skipConstInApp_boxed_3292_, v_skipInstances_boxed_3293_, v_x_3286_, v_x_3287_, v_fvars_3288_, v_e_3289_, v_a_3290_);
lean_dec(v_a_3290_);
return v_res_3294_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall(lean_object* v_m_3295_, lean_object* v_inst_3296_, lean_object* v_inst_3297_, lean_object* v_inst_3298_, lean_object* v_pre_3299_, lean_object* v_post_3300_, uint8_t v_usedLetOnly_3301_, uint8_t v_skipConstInApp_3302_, uint8_t v_skipInstances_3303_, lean_object* v_x_3304_, lean_object* v_x_3305_, lean_object* v_fvars_3306_, lean_object* v_e_3307_, lean_object* v_a_3308_){
_start:
{
lean_object* v___x_3309_; 
v___x_3309_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(v_inst_3296_, v_inst_3297_, v_inst_3298_, v_pre_3299_, v_post_3300_, v_usedLetOnly_3301_, v_skipConstInApp_3302_, v_skipInstances_3303_, v_x_3304_, v_x_3305_, v_fvars_3306_, v_e_3307_, v_a_3308_);
return v___x_3309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___boxed(lean_object* v_m_3310_, lean_object* v_inst_3311_, lean_object* v_inst_3312_, lean_object* v_inst_3313_, lean_object* v_pre_3314_, lean_object* v_post_3315_, lean_object* v_usedLetOnly_3316_, lean_object* v_skipConstInApp_3317_, lean_object* v_skipInstances_3318_, lean_object* v_x_3319_, lean_object* v_x_3320_, lean_object* v_fvars_3321_, lean_object* v_e_3322_, lean_object* v_a_3323_){
_start:
{
uint8_t v_usedLetOnly_boxed_3324_; uint8_t v_skipConstInApp_boxed_3325_; uint8_t v_skipInstances_boxed_3326_; lean_object* v_res_3327_; 
v_usedLetOnly_boxed_3324_ = lean_unbox(v_usedLetOnly_3316_);
v_skipConstInApp_boxed_3325_ = lean_unbox(v_skipConstInApp_3317_);
v_skipInstances_boxed_3326_ = lean_unbox(v_skipInstances_3318_);
v_res_3327_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall(v_m_3310_, v_inst_3311_, v_inst_3312_, v_inst_3313_, v_pre_3314_, v_post_3315_, v_usedLetOnly_boxed_3324_, v_skipConstInApp_boxed_3325_, v_skipInstances_boxed_3326_, v_x_3319_, v_x_3320_, v_fvars_3321_, v_e_3322_, v_a_3323_);
lean_dec(v_a_3323_);
return v_res_3327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__0(lean_object* v_x_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_){
_start:
{
lean_object* v___x_3334_; lean_object* v___x_3335_; 
v___x_3334_ = lean_apply_1(v_x_3328_, lean_box(0));
v___x_3335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3335_, 0, v___x_3334_);
return v___x_3335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__0___boxed(lean_object* v_x_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_){
_start:
{
lean_object* v_res_3342_; 
v_res_3342_ = l_Lean_Meta_transformWithCache___redArg___lam__0(v_x_3336_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_);
lean_dec(v___y_3340_);
lean_dec_ref(v___y_3339_);
lean_dec(v___y_3338_);
lean_dec_ref(v___y_3337_);
return v_res_3342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__1(lean_object* v_inst_3343_, lean_object* v_00_u03b1_3344_, lean_object* v_x_3345_){
_start:
{
lean_object* v___f_3346_; lean_object* v___x_3347_; 
v___f_3346_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_3346_, 0, v_x_3345_);
v___x_3347_ = lean_apply_2(v_inst_3343_, lean_box(0), v___f_3346_);
return v___x_3347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__4(lean_object* v_toPure_3348_, lean_object* v_x_3349_, lean_object* v_toBind_3350_, lean_object* v_inst_3351_, lean_object* v_inst_3352_, lean_object* v_inst_3353_, lean_object* v_pre_3354_, lean_object* v_post_3355_, uint8_t v_usedLetOnly_3356_, uint8_t v_skipConstInApp_3357_, uint8_t v_skipInstances_3358_, lean_object* v_x_3359_, lean_object* v_input_3360_, lean_object* v_ref_3361_){
_start:
{
lean_object* v___f_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; 
lean_inc(v_toBind_3350_);
lean_inc(v_x_3349_);
lean_inc(v_ref_3361_);
v___f_3362_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__4), 5, 4);
lean_closure_set(v___f_3362_, 0, v_toPure_3348_);
lean_closure_set(v___f_3362_, 1, v_ref_3361_);
lean_closure_set(v___f_3362_, 2, v_x_3349_);
lean_closure_set(v___f_3362_, 3, v_toBind_3350_);
v___x_3363_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_3351_, v_inst_3352_, v_inst_3353_, v_pre_3354_, v_post_3355_, v_usedLetOnly_3356_, v_skipConstInApp_3357_, v_skipInstances_3358_, v_x_3359_, v_x_3349_, v_input_3360_, v_ref_3361_);
lean_dec(v_ref_3361_);
v___x_3364_ = lean_apply_4(v_toBind_3350_, lean_box(0), lean_box(0), v___x_3363_, v___f_3362_);
return v___x_3364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__4___boxed(lean_object* v_toPure_3365_, lean_object* v_x_3366_, lean_object* v_toBind_3367_, lean_object* v_inst_3368_, lean_object* v_inst_3369_, lean_object* v_inst_3370_, lean_object* v_pre_3371_, lean_object* v_post_3372_, lean_object* v_usedLetOnly_3373_, lean_object* v_skipConstInApp_3374_, lean_object* v_skipInstances_3375_, lean_object* v_x_3376_, lean_object* v_input_3377_, lean_object* v_ref_3378_){
_start:
{
uint8_t v_usedLetOnly_boxed_3379_; uint8_t v_skipConstInApp_boxed_3380_; uint8_t v_skipInstances_boxed_3381_; lean_object* v_res_3382_; 
v_usedLetOnly_boxed_3379_ = lean_unbox(v_usedLetOnly_3373_);
v_skipConstInApp_boxed_3380_ = lean_unbox(v_skipConstInApp_3374_);
v_skipInstances_boxed_3381_ = lean_unbox(v_skipInstances_3375_);
v_res_3382_ = l_Lean_Meta_transformWithCache___redArg___lam__4(v_toPure_3365_, v_x_3366_, v_toBind_3367_, v_inst_3368_, v_inst_3369_, v_inst_3370_, v_pre_3371_, v_post_3372_, v_usedLetOnly_boxed_3379_, v_skipConstInApp_boxed_3380_, v_skipInstances_boxed_3381_, v_x_3376_, v_input_3377_, v_ref_3378_);
return v_res_3382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg(lean_object* v_inst_3383_, lean_object* v_inst_3384_, lean_object* v_inst_3385_, lean_object* v_input_3386_, lean_object* v_cache_3387_, lean_object* v_pre_3388_, lean_object* v_post_3389_, uint8_t v_usedLetOnly_3390_, uint8_t v_skipConstInApp_3391_, uint8_t v_skipInstances_3392_){
_start:
{
lean_object* v_x_3393_; lean_object* v_toApplicative_3394_; lean_object* v_toBind_3395_; lean_object* v_toPure_3396_; lean_object* v_x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___f_3403_; lean_object* v___x_3404_; 
v_x_3393_ = lean_box(0);
v_toApplicative_3394_ = lean_ctor_get(v_inst_3383_, 0);
v_toBind_3395_ = lean_ctor_get(v_inst_3383_, 1);
lean_inc_n(v_toBind_3395_, 2);
v_toPure_3396_ = lean_ctor_get(v_toApplicative_3394_, 1);
lean_inc(v_toPure_3396_);
lean_inc_n(v_inst_3384_, 2);
v_x_3397_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__1), 3, 1);
lean_closure_set(v_x_3397_, 0, v_inst_3384_);
v___x_3398_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_3398_, 0, lean_box(0));
lean_closure_set(v___x_3398_, 1, lean_box(0));
lean_closure_set(v___x_3398_, 2, v_cache_3387_);
v___x_3399_ = l_Lean_Meta_transformWithCache___redArg___lam__1(v_inst_3384_, lean_box(0), v___x_3398_);
v___x_3400_ = lean_box(v_usedLetOnly_3390_);
v___x_3401_ = lean_box(v_skipConstInApp_3391_);
v___x_3402_ = lean_box(v_skipInstances_3392_);
v___f_3403_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__4___boxed), 14, 13);
lean_closure_set(v___f_3403_, 0, v_toPure_3396_);
lean_closure_set(v___f_3403_, 1, v_x_3397_);
lean_closure_set(v___f_3403_, 2, v_toBind_3395_);
lean_closure_set(v___f_3403_, 3, v_inst_3383_);
lean_closure_set(v___f_3403_, 4, v_inst_3384_);
lean_closure_set(v___f_3403_, 5, v_inst_3385_);
lean_closure_set(v___f_3403_, 6, v_pre_3388_);
lean_closure_set(v___f_3403_, 7, v_post_3389_);
lean_closure_set(v___f_3403_, 8, v___x_3400_);
lean_closure_set(v___f_3403_, 9, v___x_3401_);
lean_closure_set(v___f_3403_, 10, v___x_3402_);
lean_closure_set(v___f_3403_, 11, v_x_3393_);
lean_closure_set(v___f_3403_, 12, v_input_3386_);
v___x_3404_ = lean_apply_4(v_toBind_3395_, lean_box(0), lean_box(0), v___x_3399_, v___f_3403_);
return v___x_3404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___boxed(lean_object* v_inst_3405_, lean_object* v_inst_3406_, lean_object* v_inst_3407_, lean_object* v_input_3408_, lean_object* v_cache_3409_, lean_object* v_pre_3410_, lean_object* v_post_3411_, lean_object* v_usedLetOnly_3412_, lean_object* v_skipConstInApp_3413_, lean_object* v_skipInstances_3414_){
_start:
{
uint8_t v_usedLetOnly_boxed_3415_; uint8_t v_skipConstInApp_boxed_3416_; uint8_t v_skipInstances_boxed_3417_; lean_object* v_res_3418_; 
v_usedLetOnly_boxed_3415_ = lean_unbox(v_usedLetOnly_3412_);
v_skipConstInApp_boxed_3416_ = lean_unbox(v_skipConstInApp_3413_);
v_skipInstances_boxed_3417_ = lean_unbox(v_skipInstances_3414_);
v_res_3418_ = l_Lean_Meta_transformWithCache___redArg(v_inst_3405_, v_inst_3406_, v_inst_3407_, v_input_3408_, v_cache_3409_, v_pre_3410_, v_post_3411_, v_usedLetOnly_boxed_3415_, v_skipConstInApp_boxed_3416_, v_skipInstances_boxed_3417_);
return v_res_3418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache(lean_object* v_m_3419_, lean_object* v_inst_3420_, lean_object* v_inst_3421_, lean_object* v_inst_3422_, lean_object* v_input_3423_, lean_object* v_cache_3424_, lean_object* v_pre_3425_, lean_object* v_post_3426_, uint8_t v_usedLetOnly_3427_, uint8_t v_skipConstInApp_3428_, uint8_t v_skipInstances_3429_){
_start:
{
lean_object* v_x_3430_; lean_object* v_toApplicative_3431_; lean_object* v_toBind_3432_; lean_object* v_toPure_3433_; lean_object* v_x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___f_3440_; lean_object* v___x_3441_; 
v_x_3430_ = lean_box(0);
v_toApplicative_3431_ = lean_ctor_get(v_inst_3420_, 0);
v_toBind_3432_ = lean_ctor_get(v_inst_3420_, 1);
lean_inc_n(v_toBind_3432_, 2);
v_toPure_3433_ = lean_ctor_get(v_toApplicative_3431_, 1);
lean_inc(v_toPure_3433_);
lean_inc_n(v_inst_3421_, 2);
v_x_3434_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__1), 3, 1);
lean_closure_set(v_x_3434_, 0, v_inst_3421_);
v___x_3435_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_3435_, 0, lean_box(0));
lean_closure_set(v___x_3435_, 1, lean_box(0));
lean_closure_set(v___x_3435_, 2, v_cache_3424_);
v___x_3436_ = l_Lean_Meta_transformWithCache___redArg___lam__1(v_inst_3421_, lean_box(0), v___x_3435_);
v___x_3437_ = lean_box(v_usedLetOnly_3427_);
v___x_3438_ = lean_box(v_skipConstInApp_3428_);
v___x_3439_ = lean_box(v_skipInstances_3429_);
v___f_3440_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__4___boxed), 14, 13);
lean_closure_set(v___f_3440_, 0, v_toPure_3433_);
lean_closure_set(v___f_3440_, 1, v_x_3434_);
lean_closure_set(v___f_3440_, 2, v_toBind_3432_);
lean_closure_set(v___f_3440_, 3, v_inst_3420_);
lean_closure_set(v___f_3440_, 4, v_inst_3421_);
lean_closure_set(v___f_3440_, 5, v_inst_3422_);
lean_closure_set(v___f_3440_, 6, v_pre_3425_);
lean_closure_set(v___f_3440_, 7, v_post_3426_);
lean_closure_set(v___f_3440_, 8, v___x_3437_);
lean_closure_set(v___f_3440_, 9, v___x_3438_);
lean_closure_set(v___f_3440_, 10, v___x_3439_);
lean_closure_set(v___f_3440_, 11, v_x_3430_);
lean_closure_set(v___f_3440_, 12, v_input_3423_);
v___x_3441_ = lean_apply_4(v_toBind_3432_, lean_box(0), lean_box(0), v___x_3436_, v___f_3440_);
return v___x_3441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___boxed(lean_object* v_m_3442_, lean_object* v_inst_3443_, lean_object* v_inst_3444_, lean_object* v_inst_3445_, lean_object* v_input_3446_, lean_object* v_cache_3447_, lean_object* v_pre_3448_, lean_object* v_post_3449_, lean_object* v_usedLetOnly_3450_, lean_object* v_skipConstInApp_3451_, lean_object* v_skipInstances_3452_){
_start:
{
uint8_t v_usedLetOnly_boxed_3453_; uint8_t v_skipConstInApp_boxed_3454_; uint8_t v_skipInstances_boxed_3455_; lean_object* v_res_3456_; 
v_usedLetOnly_boxed_3453_ = lean_unbox(v_usedLetOnly_3450_);
v_skipConstInApp_boxed_3454_ = lean_unbox(v_skipConstInApp_3451_);
v_skipInstances_boxed_3455_ = lean_unbox(v_skipInstances_3452_);
v_res_3456_ = l_Lean_Meta_transformWithCache(v_m_3442_, v_inst_3443_, v_inst_3444_, v_inst_3445_, v_input_3446_, v_cache_3447_, v_pre_3448_, v_post_3449_, v_usedLetOnly_boxed_3453_, v_skipConstInApp_boxed_3454_, v_skipInstances_boxed_3455_);
return v_res_3456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___redArg___lam__5(lean_object* v_toPure_3457_, lean_object* v_x_3458_, lean_object* v_toBind_3459_, lean_object* v_inst_3460_, lean_object* v_inst_3461_, lean_object* v_inst_3462_, lean_object* v_pre_3463_, lean_object* v_post_3464_, uint8_t v_usedLetOnly_3465_, uint8_t v_skipConstInApp_3466_, uint8_t v___x_3467_, lean_object* v_x_3468_, lean_object* v_input_3469_, lean_object* v_ref_3470_){
_start:
{
lean_object* v___f_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; 
lean_inc(v_toBind_3459_);
lean_inc(v_x_3458_);
lean_inc(v_ref_3470_);
v___f_3471_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__4), 5, 4);
lean_closure_set(v___f_3471_, 0, v_toPure_3457_);
lean_closure_set(v___f_3471_, 1, v_ref_3470_);
lean_closure_set(v___f_3471_, 2, v_x_3458_);
lean_closure_set(v___f_3471_, 3, v_toBind_3459_);
v___x_3472_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_3460_, v_inst_3461_, v_inst_3462_, v_pre_3463_, v_post_3464_, v_usedLetOnly_3465_, v_skipConstInApp_3466_, v___x_3467_, v_x_3468_, v_x_3458_, v_input_3469_, v_ref_3470_);
lean_dec(v_ref_3470_);
v___x_3473_ = lean_apply_4(v_toBind_3459_, lean_box(0), lean_box(0), v___x_3472_, v___f_3471_);
return v___x_3473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___redArg___lam__5___boxed(lean_object* v_toPure_3474_, lean_object* v_x_3475_, lean_object* v_toBind_3476_, lean_object* v_inst_3477_, lean_object* v_inst_3478_, lean_object* v_inst_3479_, lean_object* v_pre_3480_, lean_object* v_post_3481_, lean_object* v_usedLetOnly_3482_, lean_object* v_skipConstInApp_3483_, lean_object* v___x_3484_, lean_object* v_x_3485_, lean_object* v_input_3486_, lean_object* v_ref_3487_){
_start:
{
uint8_t v_usedLetOnly_boxed_3488_; uint8_t v_skipConstInApp_boxed_3489_; uint8_t v___x_113__boxed_3490_; lean_object* v_res_3491_; 
v_usedLetOnly_boxed_3488_ = lean_unbox(v_usedLetOnly_3482_);
v_skipConstInApp_boxed_3489_ = lean_unbox(v_skipConstInApp_3483_);
v___x_113__boxed_3490_ = lean_unbox(v___x_3484_);
v_res_3491_ = l_Lean_Meta_transform___redArg___lam__5(v_toPure_3474_, v_x_3475_, v_toBind_3476_, v_inst_3477_, v_inst_3478_, v_inst_3479_, v_pre_3480_, v_post_3481_, v_usedLetOnly_boxed_3488_, v_skipConstInApp_boxed_3489_, v___x_113__boxed_3490_, v_x_3485_, v_input_3486_, v_ref_3487_);
return v_res_3491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___redArg(lean_object* v_inst_3492_, lean_object* v_inst_3493_, lean_object* v_inst_3494_, lean_object* v_input_3495_, lean_object* v_pre_3496_, lean_object* v_post_3497_, uint8_t v_usedLetOnly_3498_, uint8_t v_skipConstInApp_3499_){
_start:
{
lean_object* v_toApplicative_3500_; lean_object* v_toBind_3501_; lean_object* v_x_3502_; lean_object* v_toPure_3503_; lean_object* v_x_3504_; uint8_t v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___f_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___f_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; 
v_toApplicative_3500_ = lean_ctor_get(v_inst_3492_, 0);
v_toBind_3501_ = lean_ctor_get(v_inst_3492_, 1);
lean_inc_n(v_toBind_3501_, 3);
v_x_3502_ = lean_box(0);
v_toPure_3503_ = lean_ctor_get(v_toApplicative_3500_, 1);
lean_inc_n(v_toPure_3503_, 2);
lean_inc_n(v_inst_3493_, 2);
v_x_3504_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__1), 3, 1);
lean_closure_set(v_x_3504_, 0, v_inst_3493_);
v___x_3505_ = 0;
v___x_3506_ = lean_obj_once(&l_Lean_Core_transform___redArg___closed__3, &l_Lean_Core_transform___redArg___closed__3_once, _init_l_Lean_Core_transform___redArg___closed__3);
v___x_3507_ = l_Lean_Meta_transformWithCache___redArg___lam__1(v_inst_3493_, lean_box(0), v___x_3506_);
v___f_3508_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__2), 2, 1);
lean_closure_set(v___f_3508_, 0, v_toPure_3503_);
v___x_3509_ = lean_box(v_usedLetOnly_3498_);
v___x_3510_ = lean_box(v_skipConstInApp_3499_);
v___x_3511_ = lean_box(v___x_3505_);
v___f_3512_ = lean_alloc_closure((void*)(l_Lean_Meta_transform___redArg___lam__5___boxed), 14, 13);
lean_closure_set(v___f_3512_, 0, v_toPure_3503_);
lean_closure_set(v___f_3512_, 1, v_x_3504_);
lean_closure_set(v___f_3512_, 2, v_toBind_3501_);
lean_closure_set(v___f_3512_, 3, v_inst_3492_);
lean_closure_set(v___f_3512_, 4, v_inst_3493_);
lean_closure_set(v___f_3512_, 5, v_inst_3494_);
lean_closure_set(v___f_3512_, 6, v_pre_3496_);
lean_closure_set(v___f_3512_, 7, v_post_3497_);
lean_closure_set(v___f_3512_, 8, v___x_3509_);
lean_closure_set(v___f_3512_, 9, v___x_3510_);
lean_closure_set(v___f_3512_, 10, v___x_3511_);
lean_closure_set(v___f_3512_, 11, v_x_3502_);
lean_closure_set(v___f_3512_, 12, v_input_3495_);
v___x_3513_ = lean_apply_4(v_toBind_3501_, lean_box(0), lean_box(0), v___x_3507_, v___f_3512_);
v___x_3514_ = lean_apply_4(v_toBind_3501_, lean_box(0), lean_box(0), v___x_3513_, v___f_3508_);
return v___x_3514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___redArg___boxed(lean_object* v_inst_3515_, lean_object* v_inst_3516_, lean_object* v_inst_3517_, lean_object* v_input_3518_, lean_object* v_pre_3519_, lean_object* v_post_3520_, lean_object* v_usedLetOnly_3521_, lean_object* v_skipConstInApp_3522_){
_start:
{
uint8_t v_usedLetOnly_boxed_3523_; uint8_t v_skipConstInApp_boxed_3524_; lean_object* v_res_3525_; 
v_usedLetOnly_boxed_3523_ = lean_unbox(v_usedLetOnly_3521_);
v_skipConstInApp_boxed_3524_ = lean_unbox(v_skipConstInApp_3522_);
v_res_3525_ = l_Lean_Meta_transform___redArg(v_inst_3515_, v_inst_3516_, v_inst_3517_, v_input_3518_, v_pre_3519_, v_post_3520_, v_usedLetOnly_boxed_3523_, v_skipConstInApp_boxed_3524_);
return v_res_3525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform(lean_object* v_m_3526_, lean_object* v_inst_3527_, lean_object* v_inst_3528_, lean_object* v_inst_3529_, lean_object* v_input_3530_, lean_object* v_pre_3531_, lean_object* v_post_3532_, uint8_t v_usedLetOnly_3533_, uint8_t v_skipConstInApp_3534_){
_start:
{
lean_object* v___x_3535_; 
v___x_3535_ = l_Lean_Meta_transform___redArg(v_inst_3527_, v_inst_3528_, v_inst_3529_, v_input_3530_, v_pre_3531_, v_post_3532_, v_usedLetOnly_3533_, v_skipConstInApp_3534_);
return v___x_3535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___boxed(lean_object* v_m_3536_, lean_object* v_inst_3537_, lean_object* v_inst_3538_, lean_object* v_inst_3539_, lean_object* v_input_3540_, lean_object* v_pre_3541_, lean_object* v_post_3542_, lean_object* v_usedLetOnly_3543_, lean_object* v_skipConstInApp_3544_){
_start:
{
uint8_t v_usedLetOnly_boxed_3545_; uint8_t v_skipConstInApp_boxed_3546_; lean_object* v_res_3547_; 
v_usedLetOnly_boxed_3545_ = lean_unbox(v_usedLetOnly_3543_);
v_skipConstInApp_boxed_3546_ = lean_unbox(v_skipConstInApp_3544_);
v_res_3547_ = l_Lean_Meta_transform(v_m_3536_, v_inst_3537_, v_inst_3538_, v_inst_3539_, v_input_3540_, v_pre_3541_, v_post_3542_, v_usedLetOnly_boxed_3545_, v_skipConstInApp_boxed_3546_);
return v_res_3547_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(lean_object* v_e_3548_, lean_object* v___y_3549_){
_start:
{
uint8_t v___x_3551_; 
v___x_3551_ = l_Lean_Expr_hasMVar(v_e_3548_);
if (v___x_3551_ == 0)
{
lean_object* v___x_3552_; 
v___x_3552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3552_, 0, v_e_3548_);
return v___x_3552_;
}
else
{
lean_object* v___x_3553_; lean_object* v_mctx_3554_; lean_object* v___x_3555_; lean_object* v_fst_3556_; lean_object* v_snd_3557_; lean_object* v___x_3558_; lean_object* v_cache_3559_; lean_object* v_zetaDeltaFVarIds_3560_; lean_object* v_postponed_3561_; lean_object* v_diag_3562_; lean_object* v___x_3564_; uint8_t v_isShared_3565_; uint8_t v_isSharedCheck_3571_; 
v___x_3553_ = lean_st_ref_get(v___y_3549_);
v_mctx_3554_ = lean_ctor_get(v___x_3553_, 0);
lean_inc_ref(v_mctx_3554_);
lean_dec(v___x_3553_);
v___x_3555_ = l_Lean_instantiateMVarsCore(v_mctx_3554_, v_e_3548_);
v_fst_3556_ = lean_ctor_get(v___x_3555_, 0);
lean_inc(v_fst_3556_);
v_snd_3557_ = lean_ctor_get(v___x_3555_, 1);
lean_inc(v_snd_3557_);
lean_dec_ref(v___x_3555_);
v___x_3558_ = lean_st_ref_take(v___y_3549_);
v_cache_3559_ = lean_ctor_get(v___x_3558_, 1);
v_zetaDeltaFVarIds_3560_ = lean_ctor_get(v___x_3558_, 2);
v_postponed_3561_ = lean_ctor_get(v___x_3558_, 3);
v_diag_3562_ = lean_ctor_get(v___x_3558_, 4);
v_isSharedCheck_3571_ = !lean_is_exclusive(v___x_3558_);
if (v_isSharedCheck_3571_ == 0)
{
lean_object* v_unused_3572_; 
v_unused_3572_ = lean_ctor_get(v___x_3558_, 0);
lean_dec(v_unused_3572_);
v___x_3564_ = v___x_3558_;
v_isShared_3565_ = v_isSharedCheck_3571_;
goto v_resetjp_3563_;
}
else
{
lean_inc(v_diag_3562_);
lean_inc(v_postponed_3561_);
lean_inc(v_zetaDeltaFVarIds_3560_);
lean_inc(v_cache_3559_);
lean_dec(v___x_3558_);
v___x_3564_ = lean_box(0);
v_isShared_3565_ = v_isSharedCheck_3571_;
goto v_resetjp_3563_;
}
v_resetjp_3563_:
{
lean_object* v___x_3567_; 
if (v_isShared_3565_ == 0)
{
lean_ctor_set(v___x_3564_, 0, v_snd_3557_);
v___x_3567_ = v___x_3564_;
goto v_reusejp_3566_;
}
else
{
lean_object* v_reuseFailAlloc_3570_; 
v_reuseFailAlloc_3570_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3570_, 0, v_snd_3557_);
lean_ctor_set(v_reuseFailAlloc_3570_, 1, v_cache_3559_);
lean_ctor_set(v_reuseFailAlloc_3570_, 2, v_zetaDeltaFVarIds_3560_);
lean_ctor_set(v_reuseFailAlloc_3570_, 3, v_postponed_3561_);
lean_ctor_set(v_reuseFailAlloc_3570_, 4, v_diag_3562_);
v___x_3567_ = v_reuseFailAlloc_3570_;
goto v_reusejp_3566_;
}
v_reusejp_3566_:
{
lean_object* v___x_3568_; lean_object* v___x_3569_; 
v___x_3568_ = lean_st_ref_put(v___y_3549_, v___x_3567_);
v___x_3569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3569_, 0, v_fst_3556_);
return v___x_3569_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg___boxed(lean_object* v_e_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_){
_start:
{
lean_object* v_res_3576_; 
v_res_3576_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(v_e_3573_, v___y_3574_);
lean_dec(v___y_3574_);
return v_res_3576_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0(lean_object* v_e_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_){
_start:
{
lean_object* v___x_3583_; 
v___x_3583_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(v_e_3577_, v___y_3579_);
return v___x_3583_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___boxed(lean_object* v_e_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_){
_start:
{
lean_object* v_res_3590_; 
v_res_3590_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0(v_e_3584_, v___y_3585_, v___y_3586_, v___y_3587_, v___y_3588_);
lean_dec(v___y_3588_);
lean_dec_ref(v___y_3587_);
lean_dec(v___y_3586_);
lean_dec_ref(v___y_3585_);
return v_res_3590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__0(uint8_t v_zetaHave_3591_, lean_object* v___x_3592_, uint8_t v_zetaDelta_3593_, lean_object* v_fvarId_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_){
_start:
{
lean_object* v___x_3600_; 
v___x_3600_ = l_Lean_FVarId_findDecl_x3f___redArg(v_fvarId_3594_, v___y_3595_);
if (lean_obj_tag(v___x_3600_) == 0)
{
lean_object* v_a_3601_; lean_object* v___x_3603_; uint8_t v_isShared_3604_; uint8_t v_isSharedCheck_3629_; 
v_a_3601_ = lean_ctor_get(v___x_3600_, 0);
v_isSharedCheck_3629_ = !lean_is_exclusive(v___x_3600_);
if (v_isSharedCheck_3629_ == 0)
{
v___x_3603_ = v___x_3600_;
v_isShared_3604_ = v_isSharedCheck_3629_;
goto v_resetjp_3602_;
}
else
{
lean_inc(v_a_3601_);
lean_dec(v___x_3600_);
v___x_3603_ = lean_box(0);
v_isShared_3604_ = v_isSharedCheck_3629_;
goto v_resetjp_3602_;
}
v_resetjp_3602_:
{
if (lean_obj_tag(v_a_3601_) == 1)
{
lean_object* v_val_3605_; lean_object* v___x_3607_; uint8_t v_isShared_3608_; uint8_t v_isSharedCheck_3624_; 
v_val_3605_ = lean_ctor_get(v_a_3601_, 0);
v_isSharedCheck_3624_ = !lean_is_exclusive(v_a_3601_);
if (v_isSharedCheck_3624_ == 0)
{
v___x_3607_ = v_a_3601_;
v_isShared_3608_ = v_isSharedCheck_3624_;
goto v_resetjp_3606_;
}
else
{
lean_inc(v_val_3605_);
lean_dec(v_a_3601_);
v___x_3607_ = lean_box(0);
v_isShared_3608_ = v_isSharedCheck_3624_;
goto v_resetjp_3606_;
}
v_resetjp_3606_:
{
uint8_t v___y_3610_; 
if (v_zetaDelta_3593_ == 0)
{
lean_object* v___x_3618_; uint8_t v___x_3619_; 
v___x_3618_ = l_Lean_LocalDecl_index(v_val_3605_);
v___x_3619_ = lean_nat_dec_lt(v___x_3618_, v___x_3592_);
lean_dec(v___x_3618_);
if (v___x_3619_ == 0)
{
lean_del_object(v___x_3607_);
goto v___jp_3615_;
}
else
{
lean_object* v___x_3620_; lean_object* v___x_3622_; 
lean_dec(v_val_3605_);
lean_del_object(v___x_3603_);
v___x_3620_ = lean_box(0);
if (v_isShared_3608_ == 0)
{
lean_ctor_set_tag(v___x_3607_, 0);
lean_ctor_set(v___x_3607_, 0, v___x_3620_);
v___x_3622_ = v___x_3607_;
goto v_reusejp_3621_;
}
else
{
lean_object* v_reuseFailAlloc_3623_; 
v_reuseFailAlloc_3623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3623_, 0, v___x_3620_);
v___x_3622_ = v_reuseFailAlloc_3623_;
goto v_reusejp_3621_;
}
v_reusejp_3621_:
{
return v___x_3622_;
}
}
}
else
{
lean_del_object(v___x_3607_);
goto v___jp_3615_;
}
v___jp_3609_:
{
lean_object* v___x_3611_; lean_object* v___x_3613_; 
v___x_3611_ = l_Lean_LocalDecl_value_x3f(v_val_3605_, v___y_3610_);
lean_dec(v_val_3605_);
if (v_isShared_3604_ == 0)
{
lean_ctor_set(v___x_3603_, 0, v___x_3611_);
v___x_3613_ = v___x_3603_;
goto v_reusejp_3612_;
}
else
{
lean_object* v_reuseFailAlloc_3614_; 
v_reuseFailAlloc_3614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3614_, 0, v___x_3611_);
v___x_3613_ = v_reuseFailAlloc_3614_;
goto v_reusejp_3612_;
}
v_reusejp_3612_:
{
return v___x_3613_;
}
}
v___jp_3615_:
{
if (v_zetaHave_3591_ == 0)
{
v___y_3610_ = v_zetaHave_3591_;
goto v___jp_3609_;
}
else
{
lean_object* v___x_3616_; uint8_t v___x_3617_; 
v___x_3616_ = l_Lean_LocalDecl_index(v_val_3605_);
v___x_3617_ = lean_nat_dec_le(v___x_3592_, v___x_3616_);
lean_dec(v___x_3616_);
v___y_3610_ = v___x_3617_;
goto v___jp_3609_;
}
}
}
}
else
{
lean_object* v___x_3625_; lean_object* v___x_3627_; 
lean_dec(v_a_3601_);
v___x_3625_ = lean_box(0);
if (v_isShared_3604_ == 0)
{
lean_ctor_set(v___x_3603_, 0, v___x_3625_);
v___x_3627_ = v___x_3603_;
goto v_reusejp_3626_;
}
else
{
lean_object* v_reuseFailAlloc_3628_; 
v_reuseFailAlloc_3628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3628_, 0, v___x_3625_);
v___x_3627_ = v_reuseFailAlloc_3628_;
goto v_reusejp_3626_;
}
v_reusejp_3626_:
{
return v___x_3627_;
}
}
}
}
else
{
lean_object* v_a_3630_; lean_object* v___x_3632_; uint8_t v_isShared_3633_; uint8_t v_isSharedCheck_3637_; 
v_a_3630_ = lean_ctor_get(v___x_3600_, 0);
v_isSharedCheck_3637_ = !lean_is_exclusive(v___x_3600_);
if (v_isSharedCheck_3637_ == 0)
{
v___x_3632_ = v___x_3600_;
v_isShared_3633_ = v_isSharedCheck_3637_;
goto v_resetjp_3631_;
}
else
{
lean_inc(v_a_3630_);
lean_dec(v___x_3600_);
v___x_3632_ = lean_box(0);
v_isShared_3633_ = v_isSharedCheck_3637_;
goto v_resetjp_3631_;
}
v_resetjp_3631_:
{
lean_object* v___x_3635_; 
if (v_isShared_3633_ == 0)
{
v___x_3635_ = v___x_3632_;
goto v_reusejp_3634_;
}
else
{
lean_object* v_reuseFailAlloc_3636_; 
v_reuseFailAlloc_3636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3636_, 0, v_a_3630_);
v___x_3635_ = v_reuseFailAlloc_3636_;
goto v_reusejp_3634_;
}
v_reusejp_3634_:
{
return v___x_3635_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__0___boxed(lean_object* v_zetaHave_3638_, lean_object* v___x_3639_, lean_object* v_zetaDelta_3640_, lean_object* v_fvarId_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_){
_start:
{
uint8_t v_zetaHave_boxed_3647_; uint8_t v_zetaDelta_boxed_3648_; lean_object* v_res_3649_; 
v_zetaHave_boxed_3647_ = lean_unbox(v_zetaHave_3638_);
v_zetaDelta_boxed_3648_ = lean_unbox(v_zetaDelta_3640_);
v_res_3649_ = l_Lean_Meta_zetaReduce___lam__0(v_zetaHave_boxed_3647_, v___x_3639_, v_zetaDelta_boxed_3648_, v_fvarId_3641_, v___y_3642_, v___y_3643_, v___y_3644_, v___y_3645_);
lean_dec(v___y_3645_);
lean_dec_ref(v___y_3644_);
lean_dec(v___y_3643_);
lean_dec_ref(v___y_3642_);
lean_dec(v___x_3639_);
return v_res_3649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__1(lean_object* v_e_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_){
_start:
{
lean_object* v___x_3656_; lean_object* v___x_3657_; 
v___x_3656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3656_, 0, v_e_3650_);
v___x_3657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3657_, 0, v___x_3656_);
return v___x_3657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__1___boxed(lean_object* v_e_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_){
_start:
{
lean_object* v_res_3664_; 
v_res_3664_ = l_Lean_Meta_zetaReduce___lam__1(v_e_3658_, v___y_3659_, v___y_3660_, v___y_3661_, v___y_3662_);
lean_dec(v___y_3662_);
lean_dec_ref(v___y_3661_);
lean_dec(v___y_3660_);
lean_dec_ref(v___y_3659_);
return v_res_3664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__2(lean_object* v___f_3665_, lean_object* v_e_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_){
_start:
{
if (lean_obj_tag(v_e_3666_) == 1)
{
lean_object* v_fvarId_3672_; lean_object* v___x_3673_; 
v_fvarId_3672_ = lean_ctor_get(v_e_3666_, 0);
lean_inc(v___y_3670_);
lean_inc_ref(v___y_3669_);
lean_inc(v___y_3668_);
lean_inc_ref(v___y_3667_);
lean_inc(v_fvarId_3672_);
v___x_3673_ = lean_apply_6(v___f_3665_, v_fvarId_3672_, v___y_3667_, v___y_3668_, v___y_3669_, v___y_3670_, lean_box(0));
if (lean_obj_tag(v___x_3673_) == 0)
{
lean_object* v_a_3674_; lean_object* v___x_3676_; uint8_t v_isShared_3677_; uint8_t v_isSharedCheck_3699_; 
v_a_3674_ = lean_ctor_get(v___x_3673_, 0);
v_isSharedCheck_3699_ = !lean_is_exclusive(v___x_3673_);
if (v_isSharedCheck_3699_ == 0)
{
v___x_3676_ = v___x_3673_;
v_isShared_3677_ = v_isSharedCheck_3699_;
goto v_resetjp_3675_;
}
else
{
lean_inc(v_a_3674_);
lean_dec(v___x_3673_);
v___x_3676_ = lean_box(0);
v_isShared_3677_ = v_isSharedCheck_3699_;
goto v_resetjp_3675_;
}
v_resetjp_3675_:
{
if (lean_obj_tag(v_a_3674_) == 1)
{
lean_object* v_val_3678_; lean_object* v___x_3680_; uint8_t v_isShared_3681_; uint8_t v_isSharedCheck_3694_; 
lean_del_object(v___x_3676_);
lean_dec_ref_known(v_e_3666_, 1);
v_val_3678_ = lean_ctor_get(v_a_3674_, 0);
v_isSharedCheck_3694_ = !lean_is_exclusive(v_a_3674_);
if (v_isSharedCheck_3694_ == 0)
{
v___x_3680_ = v_a_3674_;
v_isShared_3681_ = v_isSharedCheck_3694_;
goto v_resetjp_3679_;
}
else
{
lean_inc(v_val_3678_);
lean_dec(v_a_3674_);
v___x_3680_ = lean_box(0);
v_isShared_3681_ = v_isSharedCheck_3694_;
goto v_resetjp_3679_;
}
v_resetjp_3679_:
{
lean_object* v___x_3682_; lean_object* v_a_3683_; lean_object* v___x_3685_; uint8_t v_isShared_3686_; uint8_t v_isSharedCheck_3693_; 
v___x_3682_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(v_val_3678_, v___y_3668_);
v_a_3683_ = lean_ctor_get(v___x_3682_, 0);
v_isSharedCheck_3693_ = !lean_is_exclusive(v___x_3682_);
if (v_isSharedCheck_3693_ == 0)
{
v___x_3685_ = v___x_3682_;
v_isShared_3686_ = v_isSharedCheck_3693_;
goto v_resetjp_3684_;
}
else
{
lean_inc(v_a_3683_);
lean_dec(v___x_3682_);
v___x_3685_ = lean_box(0);
v_isShared_3686_ = v_isSharedCheck_3693_;
goto v_resetjp_3684_;
}
v_resetjp_3684_:
{
lean_object* v___x_3688_; 
if (v_isShared_3681_ == 0)
{
lean_ctor_set(v___x_3680_, 0, v_a_3683_);
v___x_3688_ = v___x_3680_;
goto v_reusejp_3687_;
}
else
{
lean_object* v_reuseFailAlloc_3692_; 
v_reuseFailAlloc_3692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3692_, 0, v_a_3683_);
v___x_3688_ = v_reuseFailAlloc_3692_;
goto v_reusejp_3687_;
}
v_reusejp_3687_:
{
lean_object* v___x_3690_; 
if (v_isShared_3686_ == 0)
{
lean_ctor_set(v___x_3685_, 0, v___x_3688_);
v___x_3690_ = v___x_3685_;
goto v_reusejp_3689_;
}
else
{
lean_object* v_reuseFailAlloc_3691_; 
v_reuseFailAlloc_3691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3691_, 0, v___x_3688_);
v___x_3690_ = v_reuseFailAlloc_3691_;
goto v_reusejp_3689_;
}
v_reusejp_3689_:
{
return v___x_3690_;
}
}
}
}
}
else
{
lean_object* v___x_3695_; lean_object* v___x_3697_; 
lean_dec(v_a_3674_);
v___x_3695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3695_, 0, v_e_3666_);
if (v_isShared_3677_ == 0)
{
lean_ctor_set(v___x_3676_, 0, v___x_3695_);
v___x_3697_ = v___x_3676_;
goto v_reusejp_3696_;
}
else
{
lean_object* v_reuseFailAlloc_3698_; 
v_reuseFailAlloc_3698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3698_, 0, v___x_3695_);
v___x_3697_ = v_reuseFailAlloc_3698_;
goto v_reusejp_3696_;
}
v_reusejp_3696_:
{
return v___x_3697_;
}
}
}
}
else
{
lean_object* v_a_3700_; lean_object* v___x_3702_; uint8_t v_isShared_3703_; uint8_t v_isSharedCheck_3707_; 
lean_dec_ref_known(v_e_3666_, 1);
v_a_3700_ = lean_ctor_get(v___x_3673_, 0);
v_isSharedCheck_3707_ = !lean_is_exclusive(v___x_3673_);
if (v_isSharedCheck_3707_ == 0)
{
v___x_3702_ = v___x_3673_;
v_isShared_3703_ = v_isSharedCheck_3707_;
goto v_resetjp_3701_;
}
else
{
lean_inc(v_a_3700_);
lean_dec(v___x_3673_);
v___x_3702_ = lean_box(0);
v_isShared_3703_ = v_isSharedCheck_3707_;
goto v_resetjp_3701_;
}
v_resetjp_3701_:
{
lean_object* v___x_3705_; 
if (v_isShared_3703_ == 0)
{
v___x_3705_ = v___x_3702_;
goto v_reusejp_3704_;
}
else
{
lean_object* v_reuseFailAlloc_3706_; 
v_reuseFailAlloc_3706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3706_, 0, v_a_3700_);
v___x_3705_ = v_reuseFailAlloc_3706_;
goto v_reusejp_3704_;
}
v_reusejp_3704_:
{
return v___x_3705_;
}
}
}
}
else
{
lean_object* v___x_3708_; lean_object* v___x_3709_; 
lean_dec_ref(v_e_3666_);
lean_dec_ref(v___f_3665_);
v___x_3708_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_3709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3709_, 0, v___x_3708_);
return v___x_3709_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__2___boxed(lean_object* v___f_3710_, lean_object* v_e_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_){
_start:
{
lean_object* v_res_3717_; 
v_res_3717_ = l_Lean_Meta_zetaReduce___lam__2(v___f_3710_, v_e_3711_, v___y_3712_, v___y_3713_, v___y_3714_, v___y_3715_);
lean_dec(v___y_3715_);
lean_dec_ref(v___y_3714_);
lean_dec(v___y_3713_);
lean_dec_ref(v___y_3712_);
return v_res_3717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__4(lean_object* v___f_3718_, lean_object* v_e_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_){
_start:
{
lean_object* v___x_3725_; 
v___x_3725_ = l_Lean_Expr_getAppFn(v_e_3719_);
if (lean_obj_tag(v___x_3725_) == 1)
{
lean_object* v_fvarId_3726_; lean_object* v___x_3727_; 
v_fvarId_3726_ = lean_ctor_get(v___x_3725_, 0);
lean_inc(v_fvarId_3726_);
lean_dec_ref_known(v___x_3725_, 1);
lean_inc(v___y_3723_);
lean_inc_ref(v___y_3722_);
lean_inc(v___y_3721_);
lean_inc_ref(v___y_3720_);
v___x_3727_ = lean_apply_6(v___f_3718_, v_fvarId_3726_, v___y_3720_, v___y_3721_, v___y_3722_, v___y_3723_, lean_box(0));
if (lean_obj_tag(v___x_3727_) == 0)
{
lean_object* v_a_3728_; lean_object* v___x_3730_; uint8_t v_isShared_3731_; uint8_t v_isSharedCheck_3760_; 
v_a_3728_ = lean_ctor_get(v___x_3727_, 0);
v_isSharedCheck_3760_ = !lean_is_exclusive(v___x_3727_);
if (v_isSharedCheck_3760_ == 0)
{
v___x_3730_ = v___x_3727_;
v_isShared_3731_ = v_isSharedCheck_3760_;
goto v_resetjp_3729_;
}
else
{
lean_inc(v_a_3728_);
lean_dec(v___x_3727_);
v___x_3730_ = lean_box(0);
v_isShared_3731_ = v_isSharedCheck_3760_;
goto v_resetjp_3729_;
}
v_resetjp_3729_:
{
if (lean_obj_tag(v_a_3728_) == 1)
{
lean_object* v_val_3732_; lean_object* v___x_3734_; uint8_t v_isShared_3735_; uint8_t v_isSharedCheck_3755_; 
lean_del_object(v___x_3730_);
v_val_3732_ = lean_ctor_get(v_a_3728_, 0);
v_isSharedCheck_3755_ = !lean_is_exclusive(v_a_3728_);
if (v_isSharedCheck_3755_ == 0)
{
v___x_3734_ = v_a_3728_;
v_isShared_3735_ = v_isSharedCheck_3755_;
goto v_resetjp_3733_;
}
else
{
lean_inc(v_val_3732_);
lean_dec(v_a_3728_);
v___x_3734_ = lean_box(0);
v_isShared_3735_ = v_isSharedCheck_3755_;
goto v_resetjp_3733_;
}
v_resetjp_3733_:
{
lean_object* v___x_3736_; lean_object* v_a_3737_; lean_object* v___x_3739_; uint8_t v_isShared_3740_; uint8_t v_isSharedCheck_3754_; 
v___x_3736_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(v_val_3732_, v___y_3721_);
v_a_3737_ = lean_ctor_get(v___x_3736_, 0);
v_isSharedCheck_3754_ = !lean_is_exclusive(v___x_3736_);
if (v_isSharedCheck_3754_ == 0)
{
v___x_3739_ = v___x_3736_;
v_isShared_3740_ = v_isSharedCheck_3754_;
goto v_resetjp_3738_;
}
else
{
lean_inc(v_a_3737_);
lean_dec(v___x_3736_);
v___x_3739_ = lean_box(0);
v_isShared_3740_ = v_isSharedCheck_3754_;
goto v_resetjp_3738_;
}
v_resetjp_3738_:
{
lean_object* v_dummy_3741_; lean_object* v_nargs_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3749_; 
v_dummy_3741_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_3742_ = l_Lean_Expr_getAppNumArgs(v_e_3719_);
lean_inc(v_nargs_3742_);
v___x_3743_ = lean_mk_array(v_nargs_3742_, v_dummy_3741_);
v___x_3744_ = lean_unsigned_to_nat(1u);
v___x_3745_ = lean_nat_sub(v_nargs_3742_, v___x_3744_);
lean_dec(v_nargs_3742_);
v___x_3746_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3719_, v___x_3743_, v___x_3745_);
v___x_3747_ = l_Lean_Expr_beta(v_a_3737_, v___x_3746_);
if (v_isShared_3735_ == 0)
{
lean_ctor_set(v___x_3734_, 0, v___x_3747_);
v___x_3749_ = v___x_3734_;
goto v_reusejp_3748_;
}
else
{
lean_object* v_reuseFailAlloc_3753_; 
v_reuseFailAlloc_3753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3753_, 0, v___x_3747_);
v___x_3749_ = v_reuseFailAlloc_3753_;
goto v_reusejp_3748_;
}
v_reusejp_3748_:
{
lean_object* v___x_3751_; 
if (v_isShared_3740_ == 0)
{
lean_ctor_set(v___x_3739_, 0, v___x_3749_);
v___x_3751_ = v___x_3739_;
goto v_reusejp_3750_;
}
else
{
lean_object* v_reuseFailAlloc_3752_; 
v_reuseFailAlloc_3752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3752_, 0, v___x_3749_);
v___x_3751_ = v_reuseFailAlloc_3752_;
goto v_reusejp_3750_;
}
v_reusejp_3750_:
{
return v___x_3751_;
}
}
}
}
}
else
{
lean_object* v___x_3756_; lean_object* v___x_3758_; 
lean_dec(v_a_3728_);
lean_dec_ref(v_e_3719_);
v___x_3756_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
if (v_isShared_3731_ == 0)
{
lean_ctor_set(v___x_3730_, 0, v___x_3756_);
v___x_3758_ = v___x_3730_;
goto v_reusejp_3757_;
}
else
{
lean_object* v_reuseFailAlloc_3759_; 
v_reuseFailAlloc_3759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3759_, 0, v___x_3756_);
v___x_3758_ = v_reuseFailAlloc_3759_;
goto v_reusejp_3757_;
}
v_reusejp_3757_:
{
return v___x_3758_;
}
}
}
}
else
{
lean_object* v_a_3761_; lean_object* v___x_3763_; uint8_t v_isShared_3764_; uint8_t v_isSharedCheck_3768_; 
lean_dec_ref(v_e_3719_);
v_a_3761_ = lean_ctor_get(v___x_3727_, 0);
v_isSharedCheck_3768_ = !lean_is_exclusive(v___x_3727_);
if (v_isSharedCheck_3768_ == 0)
{
v___x_3763_ = v___x_3727_;
v_isShared_3764_ = v_isSharedCheck_3768_;
goto v_resetjp_3762_;
}
else
{
lean_inc(v_a_3761_);
lean_dec(v___x_3727_);
v___x_3763_ = lean_box(0);
v_isShared_3764_ = v_isSharedCheck_3768_;
goto v_resetjp_3762_;
}
v_resetjp_3762_:
{
lean_object* v___x_3766_; 
if (v_isShared_3764_ == 0)
{
v___x_3766_ = v___x_3763_;
goto v_reusejp_3765_;
}
else
{
lean_object* v_reuseFailAlloc_3767_; 
v_reuseFailAlloc_3767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3767_, 0, v_a_3761_);
v___x_3766_ = v_reuseFailAlloc_3767_;
goto v_reusejp_3765_;
}
v_reusejp_3765_:
{
return v___x_3766_;
}
}
}
}
else
{
lean_object* v___x_3769_; lean_object* v___x_3770_; 
lean_dec_ref(v___x_3725_);
lean_dec_ref(v_e_3719_);
lean_dec_ref(v___f_3718_);
v___x_3769_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_3770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3770_, 0, v___x_3769_);
return v___x_3770_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__4___boxed(lean_object* v___f_3771_, lean_object* v_e_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_){
_start:
{
lean_object* v_res_3778_; 
v_res_3778_ = l_Lean_Meta_zetaReduce___lam__4(v___f_3771_, v_e_3772_, v___y_3773_, v___y_3774_, v___y_3775_, v___y_3776_);
lean_dec(v___y_3776_);
lean_dec_ref(v___y_3775_);
lean_dec(v___y_3774_);
lean_dec_ref(v___y_3773_);
return v_res_3778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0(lean_object* v_00_u03b1_3779_, lean_object* v_x_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_){
_start:
{
lean_object* v___x_3786_; lean_object* v___x_3787_; 
v___x_3786_ = lean_apply_1(v_x_3780_, lean_box(0));
v___x_3787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3787_, 0, v___x_3786_);
return v___x_3787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0___boxed(lean_object* v_00_u03b1_3788_, lean_object* v_x_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_){
_start:
{
lean_object* v_res_3795_; 
v_res_3795_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0(v_00_u03b1_3788_, v_x_3789_, v___y_3790_, v___y_3791_, v___y_3792_, v___y_3793_);
lean_dec(v___y_3793_);
lean_dec_ref(v___y_3792_);
lean_dec(v___y_3791_);
lean_dec_ref(v___y_3790_);
return v_res_3795_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__2(lean_object* v___x_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_){
_start:
{
lean_object* v___x_3802_; 
v___x_3802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3802_, 0, v___x_3796_);
return v___x_3802_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__2___boxed(lean_object* v___x_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_){
_start:
{
lean_object* v_res_3809_; 
v_res_3809_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__2(v___x_3803_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_);
lean_dec(v___y_3807_);
lean_dec_ref(v___y_3806_);
lean_dec(v___y_3805_);
lean_dec_ref(v___y_3804_);
return v_res_3809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0(lean_object* v_k_3810_, lean_object* v___y_3811_, lean_object* v_b_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_){
_start:
{
lean_object* v___x_3818_; 
lean_inc(v___y_3816_);
lean_inc_ref(v___y_3815_);
lean_inc(v___y_3814_);
lean_inc_ref(v___y_3813_);
lean_inc(v___y_3811_);
v___x_3818_ = lean_apply_7(v_k_3810_, v_b_3812_, v___y_3811_, v___y_3813_, v___y_3814_, v___y_3815_, v___y_3816_, lean_box(0));
return v___x_3818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0___boxed(lean_object* v_k_3819_, lean_object* v___y_3820_, lean_object* v_b_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_){
_start:
{
lean_object* v_res_3827_; 
v_res_3827_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0(v_k_3819_, v___y_3820_, v_b_3821_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_);
lean_dec(v___y_3825_);
lean_dec_ref(v___y_3824_);
lean_dec(v___y_3823_);
lean_dec_ref(v___y_3822_);
lean_dec(v___y_3820_);
return v_res_3827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(lean_object* v_name_3828_, uint8_t v_bi_3829_, lean_object* v_type_3830_, lean_object* v_k_3831_, uint8_t v_kind_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_){
_start:
{
lean_object* v___f_3839_; lean_object* v___x_3840_; 
lean_inc(v___y_3833_);
v___f_3839_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3839_, 0, v_k_3831_);
lean_closure_set(v___f_3839_, 1, v___y_3833_);
v___x_3840_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3828_, v_bi_3829_, v_type_3830_, v___f_3839_, v_kind_3832_, v___y_3834_, v___y_3835_, v___y_3836_, v___y_3837_);
if (lean_obj_tag(v___x_3840_) == 0)
{
return v___x_3840_;
}
else
{
lean_object* v_a_3841_; lean_object* v___x_3843_; uint8_t v_isShared_3844_; uint8_t v_isSharedCheck_3848_; 
v_a_3841_ = lean_ctor_get(v___x_3840_, 0);
v_isSharedCheck_3848_ = !lean_is_exclusive(v___x_3840_);
if (v_isSharedCheck_3848_ == 0)
{
v___x_3843_ = v___x_3840_;
v_isShared_3844_ = v_isSharedCheck_3848_;
goto v_resetjp_3842_;
}
else
{
lean_inc(v_a_3841_);
lean_dec(v___x_3840_);
v___x_3843_ = lean_box(0);
v_isShared_3844_ = v_isSharedCheck_3848_;
goto v_resetjp_3842_;
}
v_resetjp_3842_:
{
lean_object* v___x_3846_; 
if (v_isShared_3844_ == 0)
{
v___x_3846_ = v___x_3843_;
goto v_reusejp_3845_;
}
else
{
lean_object* v_reuseFailAlloc_3847_; 
v_reuseFailAlloc_3847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3847_, 0, v_a_3841_);
v___x_3846_ = v_reuseFailAlloc_3847_;
goto v_reusejp_3845_;
}
v_reusejp_3845_:
{
return v___x_3846_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___boxed(lean_object* v_name_3849_, lean_object* v_bi_3850_, lean_object* v_type_3851_, lean_object* v_k_3852_, lean_object* v_kind_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_){
_start:
{
uint8_t v_bi_boxed_3860_; uint8_t v_kind_boxed_3861_; lean_object* v_res_3862_; 
v_bi_boxed_3860_ = lean_unbox(v_bi_3850_);
v_kind_boxed_3861_ = lean_unbox(v_kind_3853_);
v_res_3862_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_name_3849_, v_bi_boxed_3860_, v_type_3851_, v_k_3852_, v_kind_boxed_3861_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_);
lean_dec(v___y_3858_);
lean_dec_ref(v___y_3857_);
lean_dec(v___y_3856_);
lean_dec_ref(v___y_3855_);
lean_dec(v___y_3854_);
return v_res_3862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg(lean_object* v_name_3863_, lean_object* v_type_3864_, lean_object* v_val_3865_, lean_object* v_k_3866_, uint8_t v_nondep_3867_, uint8_t v_kind_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_){
_start:
{
lean_object* v___f_3875_; lean_object* v___x_3876_; 
lean_inc(v___y_3869_);
v___f_3875_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3875_, 0, v_k_3866_);
lean_closure_set(v___f_3875_, 1, v___y_3869_);
v___x_3876_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_3863_, v_type_3864_, v_val_3865_, v___f_3875_, v_nondep_3867_, v_kind_3868_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_);
if (lean_obj_tag(v___x_3876_) == 0)
{
return v___x_3876_;
}
else
{
lean_object* v_a_3877_; lean_object* v___x_3879_; uint8_t v_isShared_3880_; uint8_t v_isSharedCheck_3884_; 
v_a_3877_ = lean_ctor_get(v___x_3876_, 0);
v_isSharedCheck_3884_ = !lean_is_exclusive(v___x_3876_);
if (v_isSharedCheck_3884_ == 0)
{
v___x_3879_ = v___x_3876_;
v_isShared_3880_ = v_isSharedCheck_3884_;
goto v_resetjp_3878_;
}
else
{
lean_inc(v_a_3877_);
lean_dec(v___x_3876_);
v___x_3879_ = lean_box(0);
v_isShared_3880_ = v_isSharedCheck_3884_;
goto v_resetjp_3878_;
}
v_resetjp_3878_:
{
lean_object* v___x_3882_; 
if (v_isShared_3880_ == 0)
{
v___x_3882_ = v___x_3879_;
goto v_reusejp_3881_;
}
else
{
lean_object* v_reuseFailAlloc_3883_; 
v_reuseFailAlloc_3883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3883_, 0, v_a_3877_);
v___x_3882_ = v_reuseFailAlloc_3883_;
goto v_reusejp_3881_;
}
v_reusejp_3881_:
{
return v___x_3882_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg___boxed(lean_object* v_name_3885_, lean_object* v_type_3886_, lean_object* v_val_3887_, lean_object* v_k_3888_, lean_object* v_nondep_3889_, lean_object* v_kind_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_){
_start:
{
uint8_t v_nondep_boxed_3897_; uint8_t v_kind_boxed_3898_; lean_object* v_res_3899_; 
v_nondep_boxed_3897_ = lean_unbox(v_nondep_3889_);
v_kind_boxed_3898_ = lean_unbox(v_kind_3890_);
v_res_3899_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg(v_name_3885_, v_type_3886_, v_val_3887_, v_k_3888_, v_nondep_boxed_3897_, v_kind_boxed_3898_, v___y_3891_, v___y_3892_, v___y_3893_, v___y_3894_, v___y_3895_);
lean_dec(v___y_3895_);
lean_dec_ref(v___y_3894_);
lean_dec(v___y_3893_);
lean_dec_ref(v___y_3892_);
lean_dec(v___y_3891_);
return v_res_3899_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0(lean_object* v_00_u03b1_3900_, lean_object* v_x_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_){
_start:
{
lean_object* v___x_3907_; lean_object* v___x_3908_; 
v___x_3907_ = lean_apply_1(v_x_3901_, lean_box(0));
v___x_3908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3908_, 0, v___x_3907_);
return v___x_3908_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0___boxed(lean_object* v_00_u03b1_3909_, lean_object* v_x_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_){
_start:
{
lean_object* v_res_3916_; 
v_res_3916_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0(v_00_u03b1_3909_, v_x_3910_, v___y_3911_, v___y_3912_, v___y_3913_, v___y_3914_);
lean_dec(v___y_3914_);
lean_dec_ref(v___y_3913_);
lean_dec(v___y_3912_);
lean_dec_ref(v___y_3911_);
return v_res_3916_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg(lean_object* v_ref_3917_){
_start:
{
lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; 
v___x_3919_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5);
v___x_3920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3920_, 0, v_ref_3917_);
lean_ctor_set(v___x_3920_, 1, v___x_3919_);
v___x_3921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3921_, 0, v___x_3920_);
return v___x_3921_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg___boxed(lean_object* v_ref_3922_, lean_object* v___y_3923_){
_start:
{
lean_object* v_res_3924_; 
v_res_3924_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg(v_ref_3922_);
return v_res_3924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg(lean_object* v_x_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_){
_start:
{
lean_object* v___y_3933_; lean_object* v_fileName_3942_; lean_object* v_fileMap_3943_; lean_object* v_options_3944_; lean_object* v_currRecDepth_3945_; lean_object* v_maxRecDepth_3946_; lean_object* v_ref_3947_; lean_object* v_currNamespace_3948_; lean_object* v_openDecls_3949_; lean_object* v_initHeartbeats_3950_; lean_object* v_maxHeartbeats_3951_; lean_object* v_quotContext_3952_; lean_object* v_currMacroScope_3953_; uint8_t v_diag_3954_; lean_object* v_cancelTk_x3f_3955_; uint8_t v_suppressElabErrors_3956_; lean_object* v_inheritedTraceOptions_3957_; lean_object* v___x_3963_; uint8_t v___x_3964_; 
v_fileName_3942_ = lean_ctor_get(v___y_3929_, 0);
v_fileMap_3943_ = lean_ctor_get(v___y_3929_, 1);
v_options_3944_ = lean_ctor_get(v___y_3929_, 2);
v_currRecDepth_3945_ = lean_ctor_get(v___y_3929_, 3);
v_maxRecDepth_3946_ = lean_ctor_get(v___y_3929_, 4);
v_ref_3947_ = lean_ctor_get(v___y_3929_, 5);
v_currNamespace_3948_ = lean_ctor_get(v___y_3929_, 6);
v_openDecls_3949_ = lean_ctor_get(v___y_3929_, 7);
v_initHeartbeats_3950_ = lean_ctor_get(v___y_3929_, 8);
v_maxHeartbeats_3951_ = lean_ctor_get(v___y_3929_, 9);
v_quotContext_3952_ = lean_ctor_get(v___y_3929_, 10);
v_currMacroScope_3953_ = lean_ctor_get(v___y_3929_, 11);
v_diag_3954_ = lean_ctor_get_uint8(v___y_3929_, sizeof(void*)*14);
v_cancelTk_x3f_3955_ = lean_ctor_get(v___y_3929_, 12);
v_suppressElabErrors_3956_ = lean_ctor_get_uint8(v___y_3929_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3957_ = lean_ctor_get(v___y_3929_, 13);
v___x_3963_ = lean_unsigned_to_nat(0u);
v___x_3964_ = lean_nat_dec_eq(v_maxRecDepth_3946_, v___x_3963_);
if (v___x_3964_ == 0)
{
uint8_t v___x_3965_; 
v___x_3965_ = lean_nat_dec_eq(v_currRecDepth_3945_, v_maxRecDepth_3946_);
if (v___x_3965_ == 0)
{
goto v___jp_3958_;
}
else
{
lean_object* v___x_3966_; 
lean_dec_ref(v_x_3925_);
lean_inc(v_ref_3947_);
v___x_3966_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg(v_ref_3947_);
v___y_3933_ = v___x_3966_;
goto v___jp_3932_;
}
}
else
{
goto v___jp_3958_;
}
v___jp_3932_:
{
if (lean_obj_tag(v___y_3933_) == 0)
{
return v___y_3933_;
}
else
{
lean_object* v_a_3934_; lean_object* v___x_3936_; uint8_t v_isShared_3937_; uint8_t v_isSharedCheck_3941_; 
v_a_3934_ = lean_ctor_get(v___y_3933_, 0);
v_isSharedCheck_3941_ = !lean_is_exclusive(v___y_3933_);
if (v_isSharedCheck_3941_ == 0)
{
v___x_3936_ = v___y_3933_;
v_isShared_3937_ = v_isSharedCheck_3941_;
goto v_resetjp_3935_;
}
else
{
lean_inc(v_a_3934_);
lean_dec(v___y_3933_);
v___x_3936_ = lean_box(0);
v_isShared_3937_ = v_isSharedCheck_3941_;
goto v_resetjp_3935_;
}
v_resetjp_3935_:
{
lean_object* v___x_3939_; 
if (v_isShared_3937_ == 0)
{
v___x_3939_ = v___x_3936_;
goto v_reusejp_3938_;
}
else
{
lean_object* v_reuseFailAlloc_3940_; 
v_reuseFailAlloc_3940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3940_, 0, v_a_3934_);
v___x_3939_ = v_reuseFailAlloc_3940_;
goto v_reusejp_3938_;
}
v_reusejp_3938_:
{
return v___x_3939_;
}
}
}
}
v___jp_3958_:
{
lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; 
v___x_3959_ = lean_unsigned_to_nat(1u);
v___x_3960_ = lean_nat_add(v_currRecDepth_3945_, v___x_3959_);
lean_inc_ref(v_inheritedTraceOptions_3957_);
lean_inc(v_cancelTk_x3f_3955_);
lean_inc(v_currMacroScope_3953_);
lean_inc(v_quotContext_3952_);
lean_inc(v_maxHeartbeats_3951_);
lean_inc(v_initHeartbeats_3950_);
lean_inc(v_openDecls_3949_);
lean_inc(v_currNamespace_3948_);
lean_inc(v_ref_3947_);
lean_inc(v_maxRecDepth_3946_);
lean_inc_ref(v_options_3944_);
lean_inc_ref(v_fileMap_3943_);
lean_inc_ref(v_fileName_3942_);
v___x_3961_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3961_, 0, v_fileName_3942_);
lean_ctor_set(v___x_3961_, 1, v_fileMap_3943_);
lean_ctor_set(v___x_3961_, 2, v_options_3944_);
lean_ctor_set(v___x_3961_, 3, v___x_3960_);
lean_ctor_set(v___x_3961_, 4, v_maxRecDepth_3946_);
lean_ctor_set(v___x_3961_, 5, v_ref_3947_);
lean_ctor_set(v___x_3961_, 6, v_currNamespace_3948_);
lean_ctor_set(v___x_3961_, 7, v_openDecls_3949_);
lean_ctor_set(v___x_3961_, 8, v_initHeartbeats_3950_);
lean_ctor_set(v___x_3961_, 9, v_maxHeartbeats_3951_);
lean_ctor_set(v___x_3961_, 10, v_quotContext_3952_);
lean_ctor_set(v___x_3961_, 11, v_currMacroScope_3953_);
lean_ctor_set(v___x_3961_, 12, v_cancelTk_x3f_3955_);
lean_ctor_set(v___x_3961_, 13, v_inheritedTraceOptions_3957_);
lean_ctor_set_uint8(v___x_3961_, sizeof(void*)*14, v_diag_3954_);
lean_ctor_set_uint8(v___x_3961_, sizeof(void*)*14 + 1, v_suppressElabErrors_3956_);
lean_inc(v___y_3930_);
lean_inc(v___y_3928_);
lean_inc_ref(v___y_3927_);
lean_inc(v___y_3926_);
v___x_3962_ = lean_apply_6(v_x_3925_, v___y_3926_, v___y_3927_, v___y_3928_, v___x_3961_, v___y_3930_, lean_box(0));
v___y_3933_ = v___x_3962_;
goto v___jp_3932_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg___boxed(lean_object* v_x_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_){
_start:
{
lean_object* v_res_3974_; 
v_res_3974_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg(v_x_3967_, v___y_3968_, v___y_3969_, v___y_3970_, v___y_3971_, v___y_3972_);
lean_dec(v___y_3972_);
lean_dec_ref(v___y_3971_);
lean_dec(v___y_3970_);
lean_dec_ref(v___y_3969_);
lean_dec(v___y_3968_);
return v_res_3974_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___lam__0(lean_object* v_fvars_3975_, lean_object* v_pre_3976_, lean_object* v_post_3977_, uint8_t v_usedLetOnly_3978_, uint8_t v_skipConstInApp_3979_, uint8_t v_skipInstances_3980_, lean_object* v_body_3981_, lean_object* v_x_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_){
_start:
{
lean_object* v___x_3989_; lean_object* v___x_3990_; 
v___x_3989_ = lean_array_push(v_fvars_3975_, v_x_3982_);
v___x_3990_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6(v_pre_3976_, v_post_3977_, v_usedLetOnly_3978_, v_skipConstInApp_3979_, v_skipInstances_3980_, v___x_3989_, v_body_3981_, v___y_3983_, v___y_3984_, v___y_3985_, v___y_3986_, v___y_3987_);
return v___x_3990_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___lam__0___boxed(lean_object* v_fvars_3991_, lean_object* v_pre_3992_, lean_object* v_post_3993_, lean_object* v_usedLetOnly_3994_, lean_object* v_skipConstInApp_3995_, lean_object* v_skipInstances_3996_, lean_object* v_body_3997_, lean_object* v_x_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_){
_start:
{
uint8_t v_usedLetOnly_boxed_4005_; uint8_t v_skipConstInApp_boxed_4006_; uint8_t v_skipInstances_boxed_4007_; lean_object* v_res_4008_; 
v_usedLetOnly_boxed_4005_ = lean_unbox(v_usedLetOnly_3994_);
v_skipConstInApp_boxed_4006_ = lean_unbox(v_skipConstInApp_3995_);
v_skipInstances_boxed_4007_ = lean_unbox(v_skipInstances_3996_);
v_res_4008_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___lam__0(v_fvars_3991_, v_pre_3992_, v_post_3993_, v_usedLetOnly_boxed_4005_, v_skipConstInApp_boxed_4006_, v_skipInstances_boxed_4007_, v_body_3997_, v_x_3998_, v___y_3999_, v___y_4000_, v___y_4001_, v___y_4002_, v___y_4003_);
lean_dec(v___y_4003_);
lean_dec_ref(v___y_4002_);
lean_dec(v___y_4001_);
lean_dec_ref(v___y_4000_);
lean_dec(v___y_3999_);
return v_res_4008_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(lean_object* v_pre_4009_, lean_object* v_post_4010_, uint8_t v_usedLetOnly_4011_, uint8_t v_skipConstInApp_4012_, uint8_t v_skipInstances_4013_, lean_object* v_e_4014_, lean_object* v_a_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_){
_start:
{
lean_object* v___x_4021_; 
lean_inc_ref(v_post_4010_);
lean_inc(v___y_4019_);
lean_inc_ref(v___y_4018_);
lean_inc(v___y_4017_);
lean_inc_ref(v___y_4016_);
lean_inc_ref(v_e_4014_);
v___x_4021_ = lean_apply_6(v_post_4010_, v_e_4014_, v___y_4016_, v___y_4017_, v___y_4018_, v___y_4019_, lean_box(0));
if (lean_obj_tag(v___x_4021_) == 0)
{
lean_object* v_a_4022_; lean_object* v___x_4024_; uint8_t v_isShared_4025_; uint8_t v_isSharedCheck_4040_; 
v_a_4022_ = lean_ctor_get(v___x_4021_, 0);
v_isSharedCheck_4040_ = !lean_is_exclusive(v___x_4021_);
if (v_isSharedCheck_4040_ == 0)
{
v___x_4024_ = v___x_4021_;
v_isShared_4025_ = v_isSharedCheck_4040_;
goto v_resetjp_4023_;
}
else
{
lean_inc(v_a_4022_);
lean_dec(v___x_4021_);
v___x_4024_ = lean_box(0);
v_isShared_4025_ = v_isSharedCheck_4040_;
goto v_resetjp_4023_;
}
v_resetjp_4023_:
{
switch(lean_obj_tag(v_a_4022_))
{
case 0:
{
lean_object* v_e_4026_; lean_object* v___x_4028_; 
lean_dec_ref(v_e_4014_);
lean_dec_ref(v_post_4010_);
lean_dec_ref(v_pre_4009_);
v_e_4026_ = lean_ctor_get(v_a_4022_, 0);
lean_inc_ref(v_e_4026_);
lean_dec_ref_known(v_a_4022_, 1);
if (v_isShared_4025_ == 0)
{
lean_ctor_set(v___x_4024_, 0, v_e_4026_);
v___x_4028_ = v___x_4024_;
goto v_reusejp_4027_;
}
else
{
lean_object* v_reuseFailAlloc_4029_; 
v_reuseFailAlloc_4029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4029_, 0, v_e_4026_);
v___x_4028_ = v_reuseFailAlloc_4029_;
goto v_reusejp_4027_;
}
v_reusejp_4027_:
{
return v___x_4028_;
}
}
case 1:
{
lean_object* v_e_4030_; lean_object* v___x_4031_; 
lean_del_object(v___x_4024_);
lean_dec_ref(v_e_4014_);
v_e_4030_ = lean_ctor_get(v_a_4022_, 0);
lean_inc_ref(v_e_4030_);
lean_dec_ref_known(v_a_4022_, 1);
v___x_4031_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4009_, v_post_4010_, v_usedLetOnly_4011_, v_skipConstInApp_4012_, v_skipInstances_4013_, v_e_4030_, v_a_4015_, v___y_4016_, v___y_4017_, v___y_4018_, v___y_4019_);
return v___x_4031_;
}
default: 
{
lean_object* v_e_x3f_4032_; 
lean_dec_ref(v_post_4010_);
lean_dec_ref(v_pre_4009_);
v_e_x3f_4032_ = lean_ctor_get(v_a_4022_, 0);
lean_inc(v_e_x3f_4032_);
lean_dec_ref_known(v_a_4022_, 1);
if (lean_obj_tag(v_e_x3f_4032_) == 0)
{
lean_object* v___x_4034_; 
if (v_isShared_4025_ == 0)
{
lean_ctor_set(v___x_4024_, 0, v_e_4014_);
v___x_4034_ = v___x_4024_;
goto v_reusejp_4033_;
}
else
{
lean_object* v_reuseFailAlloc_4035_; 
v_reuseFailAlloc_4035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4035_, 0, v_e_4014_);
v___x_4034_ = v_reuseFailAlloc_4035_;
goto v_reusejp_4033_;
}
v_reusejp_4033_:
{
return v___x_4034_;
}
}
else
{
lean_object* v_val_4036_; lean_object* v___x_4038_; 
lean_dec_ref(v_e_4014_);
v_val_4036_ = lean_ctor_get(v_e_x3f_4032_, 0);
lean_inc(v_val_4036_);
lean_dec_ref_known(v_e_x3f_4032_, 1);
if (v_isShared_4025_ == 0)
{
lean_ctor_set(v___x_4024_, 0, v_val_4036_);
v___x_4038_ = v___x_4024_;
goto v_reusejp_4037_;
}
else
{
lean_object* v_reuseFailAlloc_4039_; 
v_reuseFailAlloc_4039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4039_, 0, v_val_4036_);
v___x_4038_ = v_reuseFailAlloc_4039_;
goto v_reusejp_4037_;
}
v_reusejp_4037_:
{
return v___x_4038_;
}
}
}
}
}
}
else
{
lean_object* v_a_4041_; lean_object* v___x_4043_; uint8_t v_isShared_4044_; uint8_t v_isSharedCheck_4048_; 
lean_dec_ref(v_e_4014_);
lean_dec_ref(v_post_4010_);
lean_dec_ref(v_pre_4009_);
v_a_4041_ = lean_ctor_get(v___x_4021_, 0);
v_isSharedCheck_4048_ = !lean_is_exclusive(v___x_4021_);
if (v_isSharedCheck_4048_ == 0)
{
v___x_4043_ = v___x_4021_;
v_isShared_4044_ = v_isSharedCheck_4048_;
goto v_resetjp_4042_;
}
else
{
lean_inc(v_a_4041_);
lean_dec(v___x_4021_);
v___x_4043_ = lean_box(0);
v_isShared_4044_ = v_isSharedCheck_4048_;
goto v_resetjp_4042_;
}
v_resetjp_4042_:
{
lean_object* v___x_4046_; 
if (v_isShared_4044_ == 0)
{
v___x_4046_ = v___x_4043_;
goto v_reusejp_4045_;
}
else
{
lean_object* v_reuseFailAlloc_4047_; 
v_reuseFailAlloc_4047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4047_, 0, v_a_4041_);
v___x_4046_ = v_reuseFailAlloc_4047_;
goto v_reusejp_4045_;
}
v_reusejp_4045_:
{
return v___x_4046_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6(lean_object* v_pre_4049_, lean_object* v_post_4050_, uint8_t v_usedLetOnly_4051_, uint8_t v_skipConstInApp_4052_, uint8_t v_skipInstances_4053_, lean_object* v_fvars_4054_, lean_object* v_e_4055_, lean_object* v_a_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_){
_start:
{
if (lean_obj_tag(v_e_4055_) == 6)
{
lean_object* v_binderName_4062_; lean_object* v_binderType_4063_; lean_object* v_body_4064_; uint8_t v_binderInfo_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; 
v_binderName_4062_ = lean_ctor_get(v_e_4055_, 0);
lean_inc(v_binderName_4062_);
v_binderType_4063_ = lean_ctor_get(v_e_4055_, 1);
lean_inc_ref(v_binderType_4063_);
v_body_4064_ = lean_ctor_get(v_e_4055_, 2);
lean_inc_ref(v_body_4064_);
v_binderInfo_4065_ = lean_ctor_get_uint8(v_e_4055_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_4055_, 3);
v___x_4066_ = lean_expr_instantiate_rev(v_binderType_4063_, v_fvars_4054_);
lean_dec_ref(v_binderType_4063_);
lean_inc_ref(v_post_4050_);
lean_inc_ref(v_pre_4049_);
v___x_4067_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4049_, v_post_4050_, v_usedLetOnly_4051_, v_skipConstInApp_4052_, v_skipInstances_4053_, v___x_4066_, v_a_4056_, v___y_4057_, v___y_4058_, v___y_4059_, v___y_4060_);
if (lean_obj_tag(v___x_4067_) == 0)
{
lean_object* v_a_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___f_4072_; uint8_t v___x_4073_; lean_object* v___x_4074_; 
v_a_4068_ = lean_ctor_get(v___x_4067_, 0);
lean_inc(v_a_4068_);
lean_dec_ref_known(v___x_4067_, 1);
v___x_4069_ = lean_box(v_usedLetOnly_4051_);
v___x_4070_ = lean_box(v_skipConstInApp_4052_);
v___x_4071_ = lean_box(v_skipInstances_4053_);
v___f_4072_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___lam__0___boxed), 14, 7);
lean_closure_set(v___f_4072_, 0, v_fvars_4054_);
lean_closure_set(v___f_4072_, 1, v_pre_4049_);
lean_closure_set(v___f_4072_, 2, v_post_4050_);
lean_closure_set(v___f_4072_, 3, v___x_4069_);
lean_closure_set(v___f_4072_, 4, v___x_4070_);
lean_closure_set(v___f_4072_, 5, v___x_4071_);
lean_closure_set(v___f_4072_, 6, v_body_4064_);
v___x_4073_ = 0;
v___x_4074_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_binderName_4062_, v_binderInfo_4065_, v_a_4068_, v___f_4072_, v___x_4073_, v_a_4056_, v___y_4057_, v___y_4058_, v___y_4059_, v___y_4060_);
return v___x_4074_;
}
else
{
lean_dec_ref(v_body_4064_);
lean_dec(v_binderName_4062_);
lean_dec_ref(v_fvars_4054_);
lean_dec_ref(v_post_4050_);
lean_dec_ref(v_pre_4049_);
return v___x_4067_;
}
}
else
{
lean_object* v___x_4075_; lean_object* v___x_4076_; 
v___x_4075_ = lean_expr_instantiate_rev(v_e_4055_, v_fvars_4054_);
lean_dec_ref(v_e_4055_);
lean_inc_ref(v_post_4050_);
lean_inc_ref(v_pre_4049_);
v___x_4076_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4049_, v_post_4050_, v_usedLetOnly_4051_, v_skipConstInApp_4052_, v_skipInstances_4053_, v___x_4075_, v_a_4056_, v___y_4057_, v___y_4058_, v___y_4059_, v___y_4060_);
if (lean_obj_tag(v___x_4076_) == 0)
{
lean_object* v_a_4077_; uint8_t v___x_4078_; uint8_t v___x_4079_; uint8_t v___x_4080_; lean_object* v___x_4081_; 
v_a_4077_ = lean_ctor_get(v___x_4076_, 0);
lean_inc(v_a_4077_);
lean_dec_ref_known(v___x_4076_, 1);
v___x_4078_ = 0;
v___x_4079_ = 1;
v___x_4080_ = 1;
v___x_4081_ = l_Lean_Meta_mkLambdaFVars(v_fvars_4054_, v_a_4077_, v___x_4078_, v_usedLetOnly_4051_, v___x_4078_, v___x_4079_, v___x_4080_, v___y_4057_, v___y_4058_, v___y_4059_, v___y_4060_);
lean_dec_ref(v_fvars_4054_);
if (lean_obj_tag(v___x_4081_) == 0)
{
lean_object* v_a_4082_; lean_object* v___x_4083_; 
v_a_4082_ = lean_ctor_get(v___x_4081_, 0);
lean_inc(v_a_4082_);
lean_dec_ref_known(v___x_4081_, 1);
v___x_4083_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4049_, v_post_4050_, v_usedLetOnly_4051_, v_skipConstInApp_4052_, v_skipInstances_4053_, v_a_4082_, v_a_4056_, v___y_4057_, v___y_4058_, v___y_4059_, v___y_4060_);
return v___x_4083_;
}
else
{
lean_dec_ref(v_post_4050_);
lean_dec_ref(v_pre_4049_);
return v___x_4081_;
}
}
else
{
lean_dec_ref(v_fvars_4054_);
lean_dec_ref(v_post_4050_);
lean_dec_ref(v_pre_4049_);
return v___x_4076_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___lam__0(lean_object* v_fvars_4084_, lean_object* v_pre_4085_, lean_object* v_post_4086_, uint8_t v_usedLetOnly_4087_, uint8_t v_skipConstInApp_4088_, uint8_t v_skipInstances_4089_, lean_object* v_body_4090_, lean_object* v_x_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_){
_start:
{
lean_object* v___x_4098_; lean_object* v___x_4099_; 
v___x_4098_ = lean_array_push(v_fvars_4084_, v_x_4091_);
v___x_4099_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7(v_pre_4085_, v_post_4086_, v_usedLetOnly_4087_, v_skipConstInApp_4088_, v_skipInstances_4089_, v___x_4098_, v_body_4090_, v___y_4092_, v___y_4093_, v___y_4094_, v___y_4095_, v___y_4096_);
return v___x_4099_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___lam__0___boxed(lean_object* v_fvars_4100_, lean_object* v_pre_4101_, lean_object* v_post_4102_, lean_object* v_usedLetOnly_4103_, lean_object* v_skipConstInApp_4104_, lean_object* v_skipInstances_4105_, lean_object* v_body_4106_, lean_object* v_x_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_){
_start:
{
uint8_t v_usedLetOnly_boxed_4114_; uint8_t v_skipConstInApp_boxed_4115_; uint8_t v_skipInstances_boxed_4116_; lean_object* v_res_4117_; 
v_usedLetOnly_boxed_4114_ = lean_unbox(v_usedLetOnly_4103_);
v_skipConstInApp_boxed_4115_ = lean_unbox(v_skipConstInApp_4104_);
v_skipInstances_boxed_4116_ = lean_unbox(v_skipInstances_4105_);
v_res_4117_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___lam__0(v_fvars_4100_, v_pre_4101_, v_post_4102_, v_usedLetOnly_boxed_4114_, v_skipConstInApp_boxed_4115_, v_skipInstances_boxed_4116_, v_body_4106_, v_x_4107_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_);
lean_dec(v___y_4112_);
lean_dec_ref(v___y_4111_);
lean_dec(v___y_4110_);
lean_dec_ref(v___y_4109_);
lean_dec(v___y_4108_);
return v_res_4117_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7(lean_object* v_pre_4118_, lean_object* v_post_4119_, uint8_t v_usedLetOnly_4120_, uint8_t v_skipConstInApp_4121_, uint8_t v_skipInstances_4122_, lean_object* v_fvars_4123_, lean_object* v_e_4124_, lean_object* v_a_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_){
_start:
{
if (lean_obj_tag(v_e_4124_) == 8)
{
lean_object* v_declName_4131_; lean_object* v_type_4132_; lean_object* v_value_4133_; lean_object* v_body_4134_; uint8_t v_nondep_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; 
v_declName_4131_ = lean_ctor_get(v_e_4124_, 0);
lean_inc(v_declName_4131_);
v_type_4132_ = lean_ctor_get(v_e_4124_, 1);
lean_inc_ref(v_type_4132_);
v_value_4133_ = lean_ctor_get(v_e_4124_, 2);
lean_inc_ref(v_value_4133_);
v_body_4134_ = lean_ctor_get(v_e_4124_, 3);
lean_inc_ref(v_body_4134_);
v_nondep_4135_ = lean_ctor_get_uint8(v_e_4124_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_4124_, 4);
v___x_4136_ = lean_expr_instantiate_rev(v_type_4132_, v_fvars_4123_);
lean_dec_ref(v_type_4132_);
lean_inc_ref(v_post_4119_);
lean_inc_ref(v_pre_4118_);
v___x_4137_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4118_, v_post_4119_, v_usedLetOnly_4120_, v_skipConstInApp_4121_, v_skipInstances_4122_, v___x_4136_, v_a_4125_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_);
if (lean_obj_tag(v___x_4137_) == 0)
{
lean_object* v_a_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; 
v_a_4138_ = lean_ctor_get(v___x_4137_, 0);
lean_inc(v_a_4138_);
lean_dec_ref_known(v___x_4137_, 1);
v___x_4139_ = lean_expr_instantiate_rev(v_value_4133_, v_fvars_4123_);
lean_dec_ref(v_value_4133_);
lean_inc_ref(v_post_4119_);
lean_inc_ref(v_pre_4118_);
v___x_4140_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4118_, v_post_4119_, v_usedLetOnly_4120_, v_skipConstInApp_4121_, v_skipInstances_4122_, v___x_4139_, v_a_4125_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_);
if (lean_obj_tag(v___x_4140_) == 0)
{
lean_object* v_a_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___f_4145_; uint8_t v___x_4146_; lean_object* v___x_4147_; 
v_a_4141_ = lean_ctor_get(v___x_4140_, 0);
lean_inc(v_a_4141_);
lean_dec_ref_known(v___x_4140_, 1);
v___x_4142_ = lean_box(v_usedLetOnly_4120_);
v___x_4143_ = lean_box(v_skipConstInApp_4121_);
v___x_4144_ = lean_box(v_skipInstances_4122_);
v___f_4145_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___lam__0___boxed), 14, 7);
lean_closure_set(v___f_4145_, 0, v_fvars_4123_);
lean_closure_set(v___f_4145_, 1, v_pre_4118_);
lean_closure_set(v___f_4145_, 2, v_post_4119_);
lean_closure_set(v___f_4145_, 3, v___x_4142_);
lean_closure_set(v___f_4145_, 4, v___x_4143_);
lean_closure_set(v___f_4145_, 5, v___x_4144_);
lean_closure_set(v___f_4145_, 6, v_body_4134_);
v___x_4146_ = 0;
v___x_4147_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg(v_declName_4131_, v_a_4138_, v_a_4141_, v___f_4145_, v_nondep_4135_, v___x_4146_, v_a_4125_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_);
return v___x_4147_;
}
else
{
lean_dec(v_a_4138_);
lean_dec_ref(v_body_4134_);
lean_dec(v_declName_4131_);
lean_dec_ref(v_fvars_4123_);
lean_dec_ref(v_post_4119_);
lean_dec_ref(v_pre_4118_);
return v___x_4140_;
}
}
else
{
lean_dec_ref(v_body_4134_);
lean_dec_ref(v_value_4133_);
lean_dec(v_declName_4131_);
lean_dec_ref(v_fvars_4123_);
lean_dec_ref(v_post_4119_);
lean_dec_ref(v_pre_4118_);
return v___x_4137_;
}
}
else
{
lean_object* v___x_4148_; lean_object* v___x_4149_; 
v___x_4148_ = lean_expr_instantiate_rev(v_e_4124_, v_fvars_4123_);
lean_dec_ref(v_e_4124_);
lean_inc_ref(v_post_4119_);
lean_inc_ref(v_pre_4118_);
v___x_4149_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4118_, v_post_4119_, v_usedLetOnly_4120_, v_skipConstInApp_4121_, v_skipInstances_4122_, v___x_4148_, v_a_4125_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_);
if (lean_obj_tag(v___x_4149_) == 0)
{
lean_object* v_a_4150_; uint8_t v___x_4151_; uint8_t v___x_4152_; lean_object* v___x_4153_; 
v_a_4150_ = lean_ctor_get(v___x_4149_, 0);
lean_inc(v_a_4150_);
lean_dec_ref_known(v___x_4149_, 1);
v___x_4151_ = 0;
v___x_4152_ = 1;
v___x_4153_ = l_Lean_Meta_mkLetFVars(v_fvars_4123_, v_a_4150_, v_usedLetOnly_4120_, v___x_4151_, v___x_4152_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_);
lean_dec_ref(v_fvars_4123_);
if (lean_obj_tag(v___x_4153_) == 0)
{
lean_object* v_a_4154_; lean_object* v___x_4155_; 
v_a_4154_ = lean_ctor_get(v___x_4153_, 0);
lean_inc(v_a_4154_);
lean_dec_ref_known(v___x_4153_, 1);
v___x_4155_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4118_, v_post_4119_, v_usedLetOnly_4120_, v_skipConstInApp_4121_, v_skipInstances_4122_, v_a_4154_, v_a_4125_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_);
return v___x_4155_;
}
else
{
lean_dec_ref(v_post_4119_);
lean_dec_ref(v_pre_4118_);
return v___x_4153_;
}
}
else
{
lean_dec_ref(v_fvars_4123_);
lean_dec_ref(v_post_4119_);
lean_dec_ref(v_pre_4118_);
return v___x_4149_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__2(lean_object* v_pre_4156_, lean_object* v_post_4157_, uint8_t v_usedLetOnly_4158_, uint8_t v_skipConstInApp_4159_, uint8_t v_skipInstances_4160_, size_t v_sz_4161_, size_t v_i_4162_, lean_object* v_bs_4163_, lean_object* v___y_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_){
_start:
{
uint8_t v___x_4170_; 
v___x_4170_ = lean_usize_dec_lt(v_i_4162_, v_sz_4161_);
if (v___x_4170_ == 0)
{
lean_object* v___x_4171_; 
lean_dec_ref(v_post_4157_);
lean_dec_ref(v_pre_4156_);
v___x_4171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4171_, 0, v_bs_4163_);
return v___x_4171_;
}
else
{
lean_object* v_v_4172_; lean_object* v___x_4173_; 
v_v_4172_ = lean_array_uget_borrowed(v_bs_4163_, v_i_4162_);
lean_inc(v_v_4172_);
lean_inc_ref(v_post_4157_);
lean_inc_ref(v_pre_4156_);
v___x_4173_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4156_, v_post_4157_, v_usedLetOnly_4158_, v_skipConstInApp_4159_, v_skipInstances_4160_, v_v_4172_, v___y_4164_, v___y_4165_, v___y_4166_, v___y_4167_, v___y_4168_);
if (lean_obj_tag(v___x_4173_) == 0)
{
lean_object* v_a_4174_; lean_object* v___x_4175_; lean_object* v_bs_x27_4176_; size_t v___x_4177_; size_t v___x_4178_; lean_object* v___x_4179_; 
v_a_4174_ = lean_ctor_get(v___x_4173_, 0);
lean_inc(v_a_4174_);
lean_dec_ref_known(v___x_4173_, 1);
v___x_4175_ = lean_unsigned_to_nat(0u);
v_bs_x27_4176_ = lean_array_uset(v_bs_4163_, v_i_4162_, v___x_4175_);
v___x_4177_ = ((size_t)1ULL);
v___x_4178_ = lean_usize_add(v_i_4162_, v___x_4177_);
v___x_4179_ = lean_array_uset(v_bs_x27_4176_, v_i_4162_, v_a_4174_);
v_i_4162_ = v___x_4178_;
v_bs_4163_ = v___x_4179_;
goto _start;
}
else
{
lean_object* v_a_4181_; lean_object* v___x_4183_; uint8_t v_isShared_4184_; uint8_t v_isSharedCheck_4188_; 
lean_dec_ref(v_bs_4163_);
lean_dec_ref(v_post_4157_);
lean_dec_ref(v_pre_4156_);
v_a_4181_ = lean_ctor_get(v___x_4173_, 0);
v_isSharedCheck_4188_ = !lean_is_exclusive(v___x_4173_);
if (v_isSharedCheck_4188_ == 0)
{
v___x_4183_ = v___x_4173_;
v_isShared_4184_ = v_isSharedCheck_4188_;
goto v_resetjp_4182_;
}
else
{
lean_inc(v_a_4181_);
lean_dec(v___x_4173_);
v___x_4183_ = lean_box(0);
v_isShared_4184_ = v_isSharedCheck_4188_;
goto v_resetjp_4182_;
}
v_resetjp_4182_:
{
lean_object* v___x_4186_; 
if (v_isShared_4184_ == 0)
{
v___x_4186_ = v___x_4183_;
goto v_reusejp_4185_;
}
else
{
lean_object* v_reuseFailAlloc_4187_; 
v_reuseFailAlloc_4187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4187_, 0, v_a_4181_);
v___x_4186_ = v_reuseFailAlloc_4187_;
goto v_reusejp_4185_;
}
v_reusejp_4185_:
{
return v___x_4186_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0(lean_object* v_pre_4189_, lean_object* v_post_4190_, uint8_t v_usedLetOnly_4191_, uint8_t v_skipConstInApp_4192_, uint8_t v_skipInstances_4193_, lean_object* v___x_4194_, lean_object* v___y_4195_, lean_object* v_b_4196_, lean_object* v_a_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_){
_start:
{
lean_object* v___x_4203_; 
v___x_4203_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4189_, v_post_4190_, v_usedLetOnly_4191_, v_skipConstInApp_4192_, v_skipInstances_4193_, v___x_4194_, v___y_4195_, v___y_4198_, v___y_4199_, v___y_4200_, v___y_4201_);
if (lean_obj_tag(v___x_4203_) == 0)
{
lean_object* v_a_4204_; lean_object* v___x_4206_; uint8_t v_isShared_4207_; uint8_t v_isSharedCheck_4213_; 
v_a_4204_ = lean_ctor_get(v___x_4203_, 0);
v_isSharedCheck_4213_ = !lean_is_exclusive(v___x_4203_);
if (v_isSharedCheck_4213_ == 0)
{
v___x_4206_ = v___x_4203_;
v_isShared_4207_ = v_isSharedCheck_4213_;
goto v_resetjp_4205_;
}
else
{
lean_inc(v_a_4204_);
lean_dec(v___x_4203_);
v___x_4206_ = lean_box(0);
v_isShared_4207_ = v_isSharedCheck_4213_;
goto v_resetjp_4205_;
}
v_resetjp_4205_:
{
lean_object* v___x_4208_; lean_object* v___x_4209_; lean_object* v___x_4211_; 
v___x_4208_ = lean_array_fset(v_b_4196_, v_a_4197_, v_a_4204_);
v___x_4209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4209_, 0, v___x_4208_);
if (v_isShared_4207_ == 0)
{
lean_ctor_set(v___x_4206_, 0, v___x_4209_);
v___x_4211_ = v___x_4206_;
goto v_reusejp_4210_;
}
else
{
lean_object* v_reuseFailAlloc_4212_; 
v_reuseFailAlloc_4212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4212_, 0, v___x_4209_);
v___x_4211_ = v_reuseFailAlloc_4212_;
goto v_reusejp_4210_;
}
v_reusejp_4210_:
{
return v___x_4211_;
}
}
}
else
{
lean_object* v_a_4214_; lean_object* v___x_4216_; uint8_t v_isShared_4217_; uint8_t v_isSharedCheck_4221_; 
lean_dec_ref(v_b_4196_);
v_a_4214_ = lean_ctor_get(v___x_4203_, 0);
v_isSharedCheck_4221_ = !lean_is_exclusive(v___x_4203_);
if (v_isSharedCheck_4221_ == 0)
{
v___x_4216_ = v___x_4203_;
v_isShared_4217_ = v_isSharedCheck_4221_;
goto v_resetjp_4215_;
}
else
{
lean_inc(v_a_4214_);
lean_dec(v___x_4203_);
v___x_4216_ = lean_box(0);
v_isShared_4217_ = v_isSharedCheck_4221_;
goto v_resetjp_4215_;
}
v_resetjp_4215_:
{
lean_object* v___x_4219_; 
if (v_isShared_4217_ == 0)
{
v___x_4219_ = v___x_4216_;
goto v_reusejp_4218_;
}
else
{
lean_object* v_reuseFailAlloc_4220_; 
v_reuseFailAlloc_4220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4220_, 0, v_a_4214_);
v___x_4219_ = v_reuseFailAlloc_4220_;
goto v_reusejp_4218_;
}
v_reusejp_4218_:
{
return v___x_4219_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed(lean_object* v_pre_4222_, lean_object* v_post_4223_, lean_object* v_usedLetOnly_4224_, lean_object* v_skipConstInApp_4225_, lean_object* v_skipInstances_4226_, lean_object* v___x_4227_, lean_object* v___y_4228_, lean_object* v_b_4229_, lean_object* v_a_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_, lean_object* v___y_4234_, lean_object* v___y_4235_){
_start:
{
uint8_t v_usedLetOnly_boxed_4236_; uint8_t v_skipConstInApp_boxed_4237_; uint8_t v_skipInstances_boxed_4238_; lean_object* v_res_4239_; 
v_usedLetOnly_boxed_4236_ = lean_unbox(v_usedLetOnly_4224_);
v_skipConstInApp_boxed_4237_ = lean_unbox(v_skipConstInApp_4225_);
v_skipInstances_boxed_4238_ = lean_unbox(v_skipInstances_4226_);
v_res_4239_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0(v_pre_4222_, v_post_4223_, v_usedLetOnly_boxed_4236_, v_skipConstInApp_boxed_4237_, v_skipInstances_boxed_4238_, v___x_4227_, v___y_4228_, v_b_4229_, v_a_4230_, v___y_4231_, v___y_4232_, v___y_4233_, v___y_4234_);
lean_dec(v___y_4234_);
lean_dec_ref(v___y_4233_);
lean_dec(v___y_4232_);
lean_dec_ref(v___y_4231_);
lean_dec(v_a_4230_);
lean_dec(v___y_4228_);
return v_res_4239_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg(lean_object* v_upperBound_4240_, lean_object* v___x_4241_, lean_object* v_pre_4242_, lean_object* v_post_4243_, uint8_t v_usedLetOnly_4244_, uint8_t v_skipConstInApp_4245_, uint8_t v_skipInstances_4246_, lean_object* v_a_4247_, lean_object* v_b_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_, lean_object* v___y_4252_, lean_object* v___y_4253_){
_start:
{
lean_object* v___y_4256_; uint8_t v___x_4279_; 
v___x_4279_ = lean_nat_dec_lt(v_a_4247_, v_upperBound_4240_);
if (v___x_4279_ == 0)
{
lean_object* v___x_4280_; 
lean_dec(v_a_4247_);
lean_dec_ref(v_post_4243_);
lean_dec_ref(v_pre_4242_);
v___x_4280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4280_, 0, v_b_4248_);
return v___x_4280_;
}
else
{
lean_object* v___x_4281_; lean_object* v___x_4282_; uint8_t v___x_4283_; 
v___x_4281_ = lean_array_fget_borrowed(v_b_4248_, v_a_4247_);
v___x_4282_ = lean_array_get_size(v___x_4241_);
v___x_4283_ = lean_nat_dec_lt(v_a_4247_, v___x_4282_);
if (v___x_4283_ == 0)
{
lean_object* v___x_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; lean_object* v___f_4287_; 
lean_inc(v___x_4281_);
v___x_4284_ = lean_box(v_usedLetOnly_4244_);
v___x_4285_ = lean_box(v_skipConstInApp_4245_);
v___x_4286_ = lean_box(v_skipInstances_4246_);
lean_inc(v_a_4247_);
lean_inc(v___y_4249_);
lean_inc_ref(v_post_4243_);
lean_inc_ref(v_pre_4242_);
v___f_4287_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_4287_, 0, v_pre_4242_);
lean_closure_set(v___f_4287_, 1, v_post_4243_);
lean_closure_set(v___f_4287_, 2, v___x_4284_);
lean_closure_set(v___f_4287_, 3, v___x_4285_);
lean_closure_set(v___f_4287_, 4, v___x_4286_);
lean_closure_set(v___f_4287_, 5, v___x_4281_);
lean_closure_set(v___f_4287_, 6, v___y_4249_);
lean_closure_set(v___f_4287_, 7, v_b_4248_);
lean_closure_set(v___f_4287_, 8, v_a_4247_);
v___y_4256_ = v___f_4287_;
goto v___jp_4255_;
}
else
{
lean_object* v___x_4288_; uint8_t v_isInstance_4289_; 
v___x_4288_ = lean_array_fget_borrowed(v___x_4241_, v_a_4247_);
v_isInstance_4289_ = lean_ctor_get_uint8(v___x_4288_, sizeof(void*)*1 + 4);
if (v_isInstance_4289_ == 0)
{
lean_object* v___x_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; lean_object* v___f_4293_; 
lean_inc(v___x_4281_);
v___x_4290_ = lean_box(v_usedLetOnly_4244_);
v___x_4291_ = lean_box(v_skipConstInApp_4245_);
v___x_4292_ = lean_box(v_skipInstances_4246_);
lean_inc(v_a_4247_);
lean_inc(v___y_4249_);
lean_inc_ref(v_post_4243_);
lean_inc_ref(v_pre_4242_);
v___f_4293_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_4293_, 0, v_pre_4242_);
lean_closure_set(v___f_4293_, 1, v_post_4243_);
lean_closure_set(v___f_4293_, 2, v___x_4290_);
lean_closure_set(v___f_4293_, 3, v___x_4291_);
lean_closure_set(v___f_4293_, 4, v___x_4292_);
lean_closure_set(v___f_4293_, 5, v___x_4281_);
lean_closure_set(v___f_4293_, 6, v___y_4249_);
lean_closure_set(v___f_4293_, 7, v_b_4248_);
lean_closure_set(v___f_4293_, 8, v_a_4247_);
v___y_4256_ = v___f_4293_;
goto v___jp_4255_;
}
else
{
lean_object* v___x_4294_; lean_object* v___f_4295_; 
v___x_4294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4294_, 0, v_b_4248_);
v___f_4295_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_4295_, 0, v___x_4294_);
v___y_4256_ = v___f_4295_;
goto v___jp_4255_;
}
}
}
v___jp_4255_:
{
lean_object* v___x_4257_; 
lean_inc(v___y_4253_);
lean_inc_ref(v___y_4252_);
lean_inc(v___y_4251_);
lean_inc_ref(v___y_4250_);
v___x_4257_ = lean_apply_5(v___y_4256_, v___y_4250_, v___y_4251_, v___y_4252_, v___y_4253_, lean_box(0));
if (lean_obj_tag(v___x_4257_) == 0)
{
lean_object* v_a_4258_; lean_object* v___x_4260_; uint8_t v_isShared_4261_; uint8_t v_isSharedCheck_4270_; 
v_a_4258_ = lean_ctor_get(v___x_4257_, 0);
v_isSharedCheck_4270_ = !lean_is_exclusive(v___x_4257_);
if (v_isSharedCheck_4270_ == 0)
{
v___x_4260_ = v___x_4257_;
v_isShared_4261_ = v_isSharedCheck_4270_;
goto v_resetjp_4259_;
}
else
{
lean_inc(v_a_4258_);
lean_dec(v___x_4257_);
v___x_4260_ = lean_box(0);
v_isShared_4261_ = v_isSharedCheck_4270_;
goto v_resetjp_4259_;
}
v_resetjp_4259_:
{
if (lean_obj_tag(v_a_4258_) == 0)
{
lean_object* v_a_4262_; lean_object* v___x_4264_; 
lean_dec(v_a_4247_);
lean_dec_ref(v_post_4243_);
lean_dec_ref(v_pre_4242_);
v_a_4262_ = lean_ctor_get(v_a_4258_, 0);
lean_inc(v_a_4262_);
lean_dec_ref_known(v_a_4258_, 1);
if (v_isShared_4261_ == 0)
{
lean_ctor_set(v___x_4260_, 0, v_a_4262_);
v___x_4264_ = v___x_4260_;
goto v_reusejp_4263_;
}
else
{
lean_object* v_reuseFailAlloc_4265_; 
v_reuseFailAlloc_4265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4265_, 0, v_a_4262_);
v___x_4264_ = v_reuseFailAlloc_4265_;
goto v_reusejp_4263_;
}
v_reusejp_4263_:
{
return v___x_4264_;
}
}
else
{
lean_object* v_a_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; 
lean_del_object(v___x_4260_);
v_a_4266_ = lean_ctor_get(v_a_4258_, 0);
lean_inc(v_a_4266_);
lean_dec_ref_known(v_a_4258_, 1);
v___x_4267_ = lean_unsigned_to_nat(1u);
v___x_4268_ = lean_nat_add(v_a_4247_, v___x_4267_);
lean_dec(v_a_4247_);
v_a_4247_ = v___x_4268_;
v_b_4248_ = v_a_4266_;
goto _start;
}
}
}
else
{
lean_object* v_a_4271_; lean_object* v___x_4273_; uint8_t v_isShared_4274_; uint8_t v_isSharedCheck_4278_; 
lean_dec(v_a_4247_);
lean_dec_ref(v_post_4243_);
lean_dec_ref(v_pre_4242_);
v_a_4271_ = lean_ctor_get(v___x_4257_, 0);
v_isSharedCheck_4278_ = !lean_is_exclusive(v___x_4257_);
if (v_isSharedCheck_4278_ == 0)
{
v___x_4273_ = v___x_4257_;
v_isShared_4274_ = v_isSharedCheck_4278_;
goto v_resetjp_4272_;
}
else
{
lean_inc(v_a_4271_);
lean_dec(v___x_4257_);
v___x_4273_ = lean_box(0);
v_isShared_4274_ = v_isSharedCheck_4278_;
goto v_resetjp_4272_;
}
v_resetjp_4272_:
{
lean_object* v___x_4276_; 
if (v_isShared_4274_ == 0)
{
v___x_4276_ = v___x_4273_;
goto v_reusejp_4275_;
}
else
{
lean_object* v_reuseFailAlloc_4277_; 
v_reuseFailAlloc_4277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4277_, 0, v_a_4271_);
v___x_4276_ = v_reuseFailAlloc_4277_;
goto v_reusejp_4275_;
}
v_reusejp_4275_:
{
return v___x_4276_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__8(uint8_t v_skipInstances_4296_, lean_object* v_pre_4297_, lean_object* v_post_4298_, uint8_t v_usedLetOnly_4299_, uint8_t v_skipConstInApp_4300_, lean_object* v_x_4301_, lean_object* v_x_4302_, lean_object* v_x_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_){
_start:
{
lean_object* v_f_4311_; lean_object* v___y_4312_; lean_object* v___y_4313_; lean_object* v___y_4314_; lean_object* v___y_4315_; lean_object* v___y_4316_; 
if (lean_obj_tag(v_x_4301_) == 5)
{
lean_object* v_fn_4359_; lean_object* v_arg_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; 
v_fn_4359_ = lean_ctor_get(v_x_4301_, 0);
lean_inc_ref(v_fn_4359_);
v_arg_4360_ = lean_ctor_get(v_x_4301_, 1);
lean_inc_ref(v_arg_4360_);
lean_dec_ref_known(v_x_4301_, 2);
v___x_4361_ = lean_array_set(v_x_4302_, v_x_4303_, v_arg_4360_);
v___x_4362_ = lean_unsigned_to_nat(1u);
v___x_4363_ = lean_nat_sub(v_x_4303_, v___x_4362_);
lean_dec(v_x_4303_);
v_x_4301_ = v_fn_4359_;
v_x_4302_ = v___x_4361_;
v_x_4303_ = v___x_4363_;
goto _start;
}
else
{
lean_dec(v_x_4303_);
if (v_skipConstInApp_4300_ == 0)
{
goto v___jp_4356_;
}
else
{
uint8_t v___x_4365_; 
v___x_4365_ = l_Lean_Expr_isConst(v_x_4301_);
if (v___x_4365_ == 0)
{
goto v___jp_4356_;
}
else
{
v_f_4311_ = v_x_4301_;
v___y_4312_ = v___y_4304_;
v___y_4313_ = v___y_4305_;
v___y_4314_ = v___y_4306_;
v___y_4315_ = v___y_4307_;
v___y_4316_ = v___y_4308_;
goto v___jp_4310_;
}
}
}
v___jp_4310_:
{
if (v_skipInstances_4296_ == 0)
{
size_t v_sz_4317_; size_t v___x_4318_; lean_object* v___x_4319_; 
v_sz_4317_ = lean_array_size(v_x_4302_);
v___x_4318_ = ((size_t)0ULL);
lean_inc_ref(v_post_4298_);
lean_inc_ref(v_pre_4297_);
v___x_4319_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__2(v_pre_4297_, v_post_4298_, v_usedLetOnly_4299_, v_skipConstInApp_4300_, v_skipInstances_4296_, v_sz_4317_, v___x_4318_, v_x_4302_, v___y_4312_, v___y_4313_, v___y_4314_, v___y_4315_, v___y_4316_);
if (lean_obj_tag(v___x_4319_) == 0)
{
lean_object* v_a_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; 
v_a_4320_ = lean_ctor_get(v___x_4319_, 0);
lean_inc(v_a_4320_);
lean_dec_ref_known(v___x_4319_, 1);
v___x_4321_ = l_Lean_mkAppN(v_f_4311_, v_a_4320_);
lean_dec(v_a_4320_);
v___x_4322_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4297_, v_post_4298_, v_usedLetOnly_4299_, v_skipConstInApp_4300_, v_skipInstances_4296_, v___x_4321_, v___y_4312_, v___y_4313_, v___y_4314_, v___y_4315_, v___y_4316_);
return v___x_4322_;
}
else
{
lean_object* v_a_4323_; lean_object* v___x_4325_; uint8_t v_isShared_4326_; uint8_t v_isSharedCheck_4330_; 
lean_dec_ref(v_f_4311_);
lean_dec_ref(v_post_4298_);
lean_dec_ref(v_pre_4297_);
v_a_4323_ = lean_ctor_get(v___x_4319_, 0);
v_isSharedCheck_4330_ = !lean_is_exclusive(v___x_4319_);
if (v_isSharedCheck_4330_ == 0)
{
v___x_4325_ = v___x_4319_;
v_isShared_4326_ = v_isSharedCheck_4330_;
goto v_resetjp_4324_;
}
else
{
lean_inc(v_a_4323_);
lean_dec(v___x_4319_);
v___x_4325_ = lean_box(0);
v_isShared_4326_ = v_isSharedCheck_4330_;
goto v_resetjp_4324_;
}
v_resetjp_4324_:
{
lean_object* v___x_4328_; 
if (v_isShared_4326_ == 0)
{
v___x_4328_ = v___x_4325_;
goto v_reusejp_4327_;
}
else
{
lean_object* v_reuseFailAlloc_4329_; 
v_reuseFailAlloc_4329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4329_, 0, v_a_4323_);
v___x_4328_ = v_reuseFailAlloc_4329_;
goto v_reusejp_4327_;
}
v_reusejp_4327_:
{
return v___x_4328_;
}
}
}
}
else
{
lean_object* v___x_4331_; lean_object* v___x_4332_; 
v___x_4331_ = lean_array_get_size(v_x_4302_);
lean_inc_ref(v_f_4311_);
v___x_4332_ = l_Lean_Meta_getFunInfoNArgs(v_f_4311_, v___x_4331_, v___y_4313_, v___y_4314_, v___y_4315_, v___y_4316_);
if (lean_obj_tag(v___x_4332_) == 0)
{
lean_object* v_a_4333_; lean_object* v_paramInfo_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; 
v_a_4333_ = lean_ctor_get(v___x_4332_, 0);
lean_inc(v_a_4333_);
lean_dec_ref_known(v___x_4332_, 1);
v_paramInfo_4334_ = lean_ctor_get(v_a_4333_, 0);
lean_inc_ref(v_paramInfo_4334_);
lean_dec(v_a_4333_);
v___x_4335_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_4298_);
lean_inc_ref(v_pre_4297_);
v___x_4336_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg(v___x_4331_, v_paramInfo_4334_, v_pre_4297_, v_post_4298_, v_usedLetOnly_4299_, v_skipConstInApp_4300_, v_skipInstances_4296_, v___x_4335_, v_x_4302_, v___y_4312_, v___y_4313_, v___y_4314_, v___y_4315_, v___y_4316_);
lean_dec_ref(v_paramInfo_4334_);
if (lean_obj_tag(v___x_4336_) == 0)
{
lean_object* v_a_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; 
v_a_4337_ = lean_ctor_get(v___x_4336_, 0);
lean_inc(v_a_4337_);
lean_dec_ref_known(v___x_4336_, 1);
v___x_4338_ = l_Lean_mkAppN(v_f_4311_, v_a_4337_);
lean_dec(v_a_4337_);
v___x_4339_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4297_, v_post_4298_, v_usedLetOnly_4299_, v_skipConstInApp_4300_, v_skipInstances_4296_, v___x_4338_, v___y_4312_, v___y_4313_, v___y_4314_, v___y_4315_, v___y_4316_);
return v___x_4339_;
}
else
{
lean_object* v_a_4340_; lean_object* v___x_4342_; uint8_t v_isShared_4343_; uint8_t v_isSharedCheck_4347_; 
lean_dec_ref(v_f_4311_);
lean_dec_ref(v_post_4298_);
lean_dec_ref(v_pre_4297_);
v_a_4340_ = lean_ctor_get(v___x_4336_, 0);
v_isSharedCheck_4347_ = !lean_is_exclusive(v___x_4336_);
if (v_isSharedCheck_4347_ == 0)
{
v___x_4342_ = v___x_4336_;
v_isShared_4343_ = v_isSharedCheck_4347_;
goto v_resetjp_4341_;
}
else
{
lean_inc(v_a_4340_);
lean_dec(v___x_4336_);
v___x_4342_ = lean_box(0);
v_isShared_4343_ = v_isSharedCheck_4347_;
goto v_resetjp_4341_;
}
v_resetjp_4341_:
{
lean_object* v___x_4345_; 
if (v_isShared_4343_ == 0)
{
v___x_4345_ = v___x_4342_;
goto v_reusejp_4344_;
}
else
{
lean_object* v_reuseFailAlloc_4346_; 
v_reuseFailAlloc_4346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4346_, 0, v_a_4340_);
v___x_4345_ = v_reuseFailAlloc_4346_;
goto v_reusejp_4344_;
}
v_reusejp_4344_:
{
return v___x_4345_;
}
}
}
}
else
{
lean_object* v_a_4348_; lean_object* v___x_4350_; uint8_t v_isShared_4351_; uint8_t v_isSharedCheck_4355_; 
lean_dec_ref(v_f_4311_);
lean_dec_ref(v_x_4302_);
lean_dec_ref(v_post_4298_);
lean_dec_ref(v_pre_4297_);
v_a_4348_ = lean_ctor_get(v___x_4332_, 0);
v_isSharedCheck_4355_ = !lean_is_exclusive(v___x_4332_);
if (v_isSharedCheck_4355_ == 0)
{
v___x_4350_ = v___x_4332_;
v_isShared_4351_ = v_isSharedCheck_4355_;
goto v_resetjp_4349_;
}
else
{
lean_inc(v_a_4348_);
lean_dec(v___x_4332_);
v___x_4350_ = lean_box(0);
v_isShared_4351_ = v_isSharedCheck_4355_;
goto v_resetjp_4349_;
}
v_resetjp_4349_:
{
lean_object* v___x_4353_; 
if (v_isShared_4351_ == 0)
{
v___x_4353_ = v___x_4350_;
goto v_reusejp_4352_;
}
else
{
lean_object* v_reuseFailAlloc_4354_; 
v_reuseFailAlloc_4354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4354_, 0, v_a_4348_);
v___x_4353_ = v_reuseFailAlloc_4354_;
goto v_reusejp_4352_;
}
v_reusejp_4352_:
{
return v___x_4353_;
}
}
}
}
}
v___jp_4356_:
{
lean_object* v___x_4357_; 
lean_inc_ref(v_post_4298_);
lean_inc_ref(v_pre_4297_);
v___x_4357_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4297_, v_post_4298_, v_usedLetOnly_4299_, v_skipConstInApp_4300_, v_skipInstances_4296_, v_x_4301_, v___y_4304_, v___y_4305_, v___y_4306_, v___y_4307_, v___y_4308_);
if (lean_obj_tag(v___x_4357_) == 0)
{
lean_object* v_a_4358_; 
v_a_4358_ = lean_ctor_get(v___x_4357_, 0);
lean_inc(v_a_4358_);
lean_dec_ref_known(v___x_4357_, 1);
v_f_4311_ = v_a_4358_;
v___y_4312_ = v___y_4304_;
v___y_4313_ = v___y_4305_;
v___y_4314_ = v___y_4306_;
v___y_4315_ = v___y_4307_;
v___y_4316_ = v___y_4308_;
goto v___jp_4310_;
}
else
{
lean_dec_ref(v_x_4302_);
lean_dec_ref(v_post_4298_);
lean_dec_ref(v_pre_4297_);
return v___x_4357_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1(lean_object* v___x_4366_, lean_object* v_pre_4367_, lean_object* v_e_4368_, lean_object* v_post_4369_, uint8_t v_usedLetOnly_4370_, uint8_t v_skipConstInApp_4371_, uint8_t v_skipInstances_4372_, lean_object* v___y_4373_, lean_object* v___y_4374_, lean_object* v___y_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_){
_start:
{
lean_object* v___x_4379_; 
v___x_4379_ = l_Lean_Core_checkSystem(v___x_4366_, v___y_4376_, v___y_4377_);
if (lean_obj_tag(v___x_4379_) == 0)
{
lean_object* v___x_4380_; 
lean_dec_ref_known(v___x_4379_, 1);
lean_inc_ref(v_pre_4367_);
lean_inc(v___y_4377_);
lean_inc_ref(v___y_4376_);
lean_inc(v___y_4375_);
lean_inc_ref(v___y_4374_);
lean_inc_ref(v_e_4368_);
v___x_4380_ = lean_apply_6(v_pre_4367_, v_e_4368_, v___y_4374_, v___y_4375_, v___y_4376_, v___y_4377_, lean_box(0));
if (lean_obj_tag(v___x_4380_) == 0)
{
lean_object* v_a_4381_; lean_object* v___x_4383_; uint8_t v_isShared_4384_; uint8_t v_isSharedCheck_4429_; 
v_a_4381_ = lean_ctor_get(v___x_4380_, 0);
v_isSharedCheck_4429_ = !lean_is_exclusive(v___x_4380_);
if (v_isSharedCheck_4429_ == 0)
{
v___x_4383_ = v___x_4380_;
v_isShared_4384_ = v_isSharedCheck_4429_;
goto v_resetjp_4382_;
}
else
{
lean_inc(v_a_4381_);
lean_dec(v___x_4380_);
v___x_4383_ = lean_box(0);
v_isShared_4384_ = v_isSharedCheck_4429_;
goto v_resetjp_4382_;
}
v_resetjp_4382_:
{
lean_object* v___y_4386_; 
switch(lean_obj_tag(v_a_4381_))
{
case 0:
{
lean_object* v_e_4421_; lean_object* v___x_4423_; 
lean_dec_ref(v_post_4369_);
lean_dec_ref(v_e_4368_);
lean_dec_ref(v_pre_4367_);
v_e_4421_ = lean_ctor_get(v_a_4381_, 0);
lean_inc_ref(v_e_4421_);
lean_dec_ref_known(v_a_4381_, 1);
if (v_isShared_4384_ == 0)
{
lean_ctor_set(v___x_4383_, 0, v_e_4421_);
v___x_4423_ = v___x_4383_;
goto v_reusejp_4422_;
}
else
{
lean_object* v_reuseFailAlloc_4424_; 
v_reuseFailAlloc_4424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4424_, 0, v_e_4421_);
v___x_4423_ = v_reuseFailAlloc_4424_;
goto v_reusejp_4422_;
}
v_reusejp_4422_:
{
return v___x_4423_;
}
}
case 1:
{
lean_object* v_e_4425_; lean_object* v___x_4426_; 
lean_del_object(v___x_4383_);
lean_dec_ref(v_e_4368_);
v_e_4425_ = lean_ctor_get(v_a_4381_, 0);
lean_inc_ref(v_e_4425_);
lean_dec_ref_known(v_a_4381_, 1);
v___x_4426_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4367_, v_post_4369_, v_usedLetOnly_4370_, v_skipConstInApp_4371_, v_skipInstances_4372_, v_e_4425_, v___y_4373_, v___y_4374_, v___y_4375_, v___y_4376_, v___y_4377_);
return v___x_4426_;
}
default: 
{
lean_object* v_e_x3f_4427_; 
lean_del_object(v___x_4383_);
v_e_x3f_4427_ = lean_ctor_get(v_a_4381_, 0);
lean_inc(v_e_x3f_4427_);
lean_dec_ref_known(v_a_4381_, 1);
if (lean_obj_tag(v_e_x3f_4427_) == 0)
{
v___y_4386_ = v_e_4368_;
goto v___jp_4385_;
}
else
{
lean_object* v_val_4428_; 
lean_dec_ref(v_e_4368_);
v_val_4428_ = lean_ctor_get(v_e_x3f_4427_, 0);
lean_inc(v_val_4428_);
lean_dec_ref_known(v_e_x3f_4427_, 1);
v___y_4386_ = v_val_4428_;
goto v___jp_4385_;
}
}
}
v___jp_4385_:
{
switch(lean_obj_tag(v___y_4386_))
{
case 7:
{
lean_object* v___x_4387_; lean_object* v___x_4388_; 
v___x_4387_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_4388_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5(v_pre_4367_, v_post_4369_, v_usedLetOnly_4370_, v_skipConstInApp_4371_, v_skipInstances_4372_, v___x_4387_, v___y_4386_, v___y_4373_, v___y_4374_, v___y_4375_, v___y_4376_, v___y_4377_);
return v___x_4388_;
}
case 6:
{
lean_object* v___x_4389_; lean_object* v___x_4390_; 
v___x_4389_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_4390_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6(v_pre_4367_, v_post_4369_, v_usedLetOnly_4370_, v_skipConstInApp_4371_, v_skipInstances_4372_, v___x_4389_, v___y_4386_, v___y_4373_, v___y_4374_, v___y_4375_, v___y_4376_, v___y_4377_);
return v___x_4390_;
}
case 8:
{
lean_object* v___x_4391_; lean_object* v___x_4392_; 
v___x_4391_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_4392_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7(v_pre_4367_, v_post_4369_, v_usedLetOnly_4370_, v_skipConstInApp_4371_, v_skipInstances_4372_, v___x_4391_, v___y_4386_, v___y_4373_, v___y_4374_, v___y_4375_, v___y_4376_, v___y_4377_);
return v___x_4392_;
}
case 5:
{
lean_object* v_dummy_4393_; lean_object* v_nargs_4394_; lean_object* v___x_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; 
v_dummy_4393_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_4394_ = l_Lean_Expr_getAppNumArgs(v___y_4386_);
lean_inc(v_nargs_4394_);
v___x_4395_ = lean_mk_array(v_nargs_4394_, v_dummy_4393_);
v___x_4396_ = lean_unsigned_to_nat(1u);
v___x_4397_ = lean_nat_sub(v_nargs_4394_, v___x_4396_);
lean_dec(v_nargs_4394_);
v___x_4398_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__8(v_skipInstances_4372_, v_pre_4367_, v_post_4369_, v_usedLetOnly_4370_, v_skipConstInApp_4371_, v___y_4386_, v___x_4395_, v___x_4397_, v___y_4373_, v___y_4374_, v___y_4375_, v___y_4376_, v___y_4377_);
return v___x_4398_;
}
case 10:
{
lean_object* v_data_4399_; lean_object* v_expr_4400_; lean_object* v___x_4401_; 
v_data_4399_ = lean_ctor_get(v___y_4386_, 0);
v_expr_4400_ = lean_ctor_get(v___y_4386_, 1);
lean_inc_ref(v_expr_4400_);
lean_inc_ref(v_post_4369_);
lean_inc_ref(v_pre_4367_);
v___x_4401_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4367_, v_post_4369_, v_usedLetOnly_4370_, v_skipConstInApp_4371_, v_skipInstances_4372_, v_expr_4400_, v___y_4373_, v___y_4374_, v___y_4375_, v___y_4376_, v___y_4377_);
if (lean_obj_tag(v___x_4401_) == 0)
{
lean_object* v_a_4402_; size_t v___x_4403_; size_t v___x_4404_; uint8_t v___x_4405_; 
v_a_4402_ = lean_ctor_get(v___x_4401_, 0);
lean_inc(v_a_4402_);
lean_dec_ref_known(v___x_4401_, 1);
v___x_4403_ = lean_ptr_addr(v_expr_4400_);
v___x_4404_ = lean_ptr_addr(v_a_4402_);
v___x_4405_ = lean_usize_dec_eq(v___x_4403_, v___x_4404_);
if (v___x_4405_ == 0)
{
lean_object* v___x_4406_; lean_object* v___x_4407_; 
lean_inc(v_data_4399_);
lean_dec_ref_known(v___y_4386_, 2);
v___x_4406_ = l_Lean_Expr_mdata___override(v_data_4399_, v_a_4402_);
v___x_4407_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4367_, v_post_4369_, v_usedLetOnly_4370_, v_skipConstInApp_4371_, v_skipInstances_4372_, v___x_4406_, v___y_4373_, v___y_4374_, v___y_4375_, v___y_4376_, v___y_4377_);
return v___x_4407_;
}
else
{
lean_object* v___x_4408_; 
lean_dec(v_a_4402_);
v___x_4408_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4367_, v_post_4369_, v_usedLetOnly_4370_, v_skipConstInApp_4371_, v_skipInstances_4372_, v___y_4386_, v___y_4373_, v___y_4374_, v___y_4375_, v___y_4376_, v___y_4377_);
return v___x_4408_;
}
}
else
{
lean_dec_ref_known(v___y_4386_, 2);
lean_dec_ref(v_post_4369_);
lean_dec_ref(v_pre_4367_);
return v___x_4401_;
}
}
case 11:
{
lean_object* v_typeName_4409_; lean_object* v_idx_4410_; lean_object* v_struct_4411_; lean_object* v___x_4412_; 
v_typeName_4409_ = lean_ctor_get(v___y_4386_, 0);
v_idx_4410_ = lean_ctor_get(v___y_4386_, 1);
v_struct_4411_ = lean_ctor_get(v___y_4386_, 2);
lean_inc_ref(v_struct_4411_);
lean_inc_ref(v_post_4369_);
lean_inc_ref(v_pre_4367_);
v___x_4412_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4367_, v_post_4369_, v_usedLetOnly_4370_, v_skipConstInApp_4371_, v_skipInstances_4372_, v_struct_4411_, v___y_4373_, v___y_4374_, v___y_4375_, v___y_4376_, v___y_4377_);
if (lean_obj_tag(v___x_4412_) == 0)
{
lean_object* v_a_4413_; size_t v___x_4414_; size_t v___x_4415_; uint8_t v___x_4416_; 
v_a_4413_ = lean_ctor_get(v___x_4412_, 0);
lean_inc(v_a_4413_);
lean_dec_ref_known(v___x_4412_, 1);
v___x_4414_ = lean_ptr_addr(v_struct_4411_);
v___x_4415_ = lean_ptr_addr(v_a_4413_);
v___x_4416_ = lean_usize_dec_eq(v___x_4414_, v___x_4415_);
if (v___x_4416_ == 0)
{
lean_object* v___x_4417_; lean_object* v___x_4418_; 
lean_inc(v_idx_4410_);
lean_inc(v_typeName_4409_);
lean_dec_ref_known(v___y_4386_, 3);
v___x_4417_ = l_Lean_Expr_proj___override(v_typeName_4409_, v_idx_4410_, v_a_4413_);
v___x_4418_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4367_, v_post_4369_, v_usedLetOnly_4370_, v_skipConstInApp_4371_, v_skipInstances_4372_, v___x_4417_, v___y_4373_, v___y_4374_, v___y_4375_, v___y_4376_, v___y_4377_);
return v___x_4418_;
}
else
{
lean_object* v___x_4419_; 
lean_dec(v_a_4413_);
v___x_4419_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4367_, v_post_4369_, v_usedLetOnly_4370_, v_skipConstInApp_4371_, v_skipInstances_4372_, v___y_4386_, v___y_4373_, v___y_4374_, v___y_4375_, v___y_4376_, v___y_4377_);
return v___x_4419_;
}
}
else
{
lean_dec_ref_known(v___y_4386_, 3);
lean_dec_ref(v_post_4369_);
lean_dec_ref(v_pre_4367_);
return v___x_4412_;
}
}
default: 
{
lean_object* v___x_4420_; 
v___x_4420_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4367_, v_post_4369_, v_usedLetOnly_4370_, v_skipConstInApp_4371_, v_skipInstances_4372_, v___y_4386_, v___y_4373_, v___y_4374_, v___y_4375_, v___y_4376_, v___y_4377_);
return v___x_4420_;
}
}
}
}
}
else
{
lean_object* v_a_4430_; lean_object* v___x_4432_; uint8_t v_isShared_4433_; uint8_t v_isSharedCheck_4437_; 
lean_dec_ref(v_post_4369_);
lean_dec_ref(v_e_4368_);
lean_dec_ref(v_pre_4367_);
v_a_4430_ = lean_ctor_get(v___x_4380_, 0);
v_isSharedCheck_4437_ = !lean_is_exclusive(v___x_4380_);
if (v_isSharedCheck_4437_ == 0)
{
v___x_4432_ = v___x_4380_;
v_isShared_4433_ = v_isSharedCheck_4437_;
goto v_resetjp_4431_;
}
else
{
lean_inc(v_a_4430_);
lean_dec(v___x_4380_);
v___x_4432_ = lean_box(0);
v_isShared_4433_ = v_isSharedCheck_4437_;
goto v_resetjp_4431_;
}
v_resetjp_4431_:
{
lean_object* v___x_4435_; 
if (v_isShared_4433_ == 0)
{
v___x_4435_ = v___x_4432_;
goto v_reusejp_4434_;
}
else
{
lean_object* v_reuseFailAlloc_4436_; 
v_reuseFailAlloc_4436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4436_, 0, v_a_4430_);
v___x_4435_ = v_reuseFailAlloc_4436_;
goto v_reusejp_4434_;
}
v_reusejp_4434_:
{
return v___x_4435_;
}
}
}
}
else
{
lean_object* v_a_4438_; lean_object* v___x_4440_; uint8_t v_isShared_4441_; uint8_t v_isSharedCheck_4445_; 
lean_dec_ref(v_post_4369_);
lean_dec_ref(v_e_4368_);
lean_dec_ref(v_pre_4367_);
v_a_4438_ = lean_ctor_get(v___x_4379_, 0);
v_isSharedCheck_4445_ = !lean_is_exclusive(v___x_4379_);
if (v_isSharedCheck_4445_ == 0)
{
v___x_4440_ = v___x_4379_;
v_isShared_4441_ = v_isSharedCheck_4445_;
goto v_resetjp_4439_;
}
else
{
lean_inc(v_a_4438_);
lean_dec(v___x_4379_);
v___x_4440_ = lean_box(0);
v_isShared_4441_ = v_isSharedCheck_4445_;
goto v_resetjp_4439_;
}
v_resetjp_4439_:
{
lean_object* v___x_4443_; 
if (v_isShared_4441_ == 0)
{
v___x_4443_ = v___x_4440_;
goto v_reusejp_4442_;
}
else
{
lean_object* v_reuseFailAlloc_4444_; 
v_reuseFailAlloc_4444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4444_, 0, v_a_4438_);
v___x_4443_ = v_reuseFailAlloc_4444_;
goto v_reusejp_4442_;
}
v_reusejp_4442_:
{
return v___x_4443_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1___boxed(lean_object* v___x_4446_, lean_object* v_pre_4447_, lean_object* v_e_4448_, lean_object* v_post_4449_, lean_object* v_usedLetOnly_4450_, lean_object* v_skipConstInApp_4451_, lean_object* v_skipInstances_4452_, lean_object* v___y_4453_, lean_object* v___y_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_){
_start:
{
uint8_t v_usedLetOnly_boxed_4459_; uint8_t v_skipConstInApp_boxed_4460_; uint8_t v_skipInstances_boxed_4461_; lean_object* v_res_4462_; 
v_usedLetOnly_boxed_4459_ = lean_unbox(v_usedLetOnly_4450_);
v_skipConstInApp_boxed_4460_ = lean_unbox(v_skipConstInApp_4451_);
v_skipInstances_boxed_4461_ = lean_unbox(v_skipInstances_4452_);
v_res_4462_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1(v___x_4446_, v_pre_4447_, v_e_4448_, v_post_4449_, v_usedLetOnly_boxed_4459_, v_skipConstInApp_boxed_4460_, v_skipInstances_boxed_4461_, v___y_4453_, v___y_4454_, v___y_4455_, v___y_4456_, v___y_4457_);
lean_dec(v___y_4457_);
lean_dec_ref(v___y_4456_);
lean_dec(v___y_4455_);
lean_dec_ref(v___y_4454_);
lean_dec(v___y_4453_);
return v_res_4462_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(lean_object* v_pre_4463_, lean_object* v_post_4464_, uint8_t v_usedLetOnly_4465_, uint8_t v_skipConstInApp_4466_, uint8_t v_skipInstances_4467_, lean_object* v_e_4468_, lean_object* v_a_4469_, lean_object* v___y_4470_, lean_object* v___y_4471_, lean_object* v___y_4472_, lean_object* v___y_4473_){
_start:
{
lean_object* v___x_4475_; lean_object* v___x_4476_; 
lean_inc(v_a_4469_);
v___x_4475_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_4475_, 0, lean_box(0));
lean_closure_set(v___x_4475_, 1, lean_box(0));
lean_closure_set(v___x_4475_, 2, v_a_4469_);
v___x_4476_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0(lean_box(0), v___x_4475_, v___y_4470_, v___y_4471_, v___y_4472_, v___y_4473_);
if (lean_obj_tag(v___x_4476_) == 0)
{
lean_object* v_a_4477_; lean_object* v___x_4479_; uint8_t v_isShared_4480_; uint8_t v_isSharedCheck_4511_; 
v_a_4477_ = lean_ctor_get(v___x_4476_, 0);
v_isSharedCheck_4511_ = !lean_is_exclusive(v___x_4476_);
if (v_isSharedCheck_4511_ == 0)
{
v___x_4479_ = v___x_4476_;
v_isShared_4480_ = v_isSharedCheck_4511_;
goto v_resetjp_4478_;
}
else
{
lean_inc(v_a_4477_);
lean_dec(v___x_4476_);
v___x_4479_ = lean_box(0);
v_isShared_4480_ = v_isSharedCheck_4511_;
goto v_resetjp_4478_;
}
v_resetjp_4478_:
{
lean_object* v___x_4481_; 
v___x_4481_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg(v_a_4477_, v_e_4468_);
lean_dec(v_a_4477_);
if (lean_obj_tag(v___x_4481_) == 0)
{
lean_object* v___x_4482_; lean_object* v___x_4483_; lean_object* v___x_4484_; lean_object* v___x_4485_; lean_object* v___f_4486_; lean_object* v___x_4487_; 
lean_del_object(v___x_4479_);
v___x_4482_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__19___closed__0));
v___x_4483_ = lean_box(v_usedLetOnly_4465_);
v___x_4484_ = lean_box(v_skipConstInApp_4466_);
v___x_4485_ = lean_box(v_skipInstances_4467_);
lean_inc_ref(v_e_4468_);
v___f_4486_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1___boxed), 13, 7);
lean_closure_set(v___f_4486_, 0, v___x_4482_);
lean_closure_set(v___f_4486_, 1, v_pre_4463_);
lean_closure_set(v___f_4486_, 2, v_e_4468_);
lean_closure_set(v___f_4486_, 3, v_post_4464_);
lean_closure_set(v___f_4486_, 4, v___x_4483_);
lean_closure_set(v___f_4486_, 5, v___x_4484_);
lean_closure_set(v___f_4486_, 6, v___x_4485_);
v___x_4487_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg(v___f_4486_, v_a_4469_, v___y_4470_, v___y_4471_, v___y_4472_, v___y_4473_);
if (lean_obj_tag(v___x_4487_) == 0)
{
lean_object* v_a_4488_; lean_object* v___f_4489_; lean_object* v___x_4490_; 
v_a_4488_ = lean_ctor_get(v___x_4487_, 0);
lean_inc_n(v_a_4488_, 2);
lean_dec_ref_known(v___x_4487_, 1);
lean_inc(v_a_4469_);
v___f_4489_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_4489_, 0, v_a_4469_);
lean_closure_set(v___f_4489_, 1, v_e_4468_);
lean_closure_set(v___f_4489_, 2, v_a_4488_);
v___x_4490_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0(lean_box(0), v___f_4489_, v___y_4470_, v___y_4471_, v___y_4472_, v___y_4473_);
if (lean_obj_tag(v___x_4490_) == 0)
{
lean_object* v___x_4492_; uint8_t v_isShared_4493_; uint8_t v_isSharedCheck_4497_; 
v_isSharedCheck_4497_ = !lean_is_exclusive(v___x_4490_);
if (v_isSharedCheck_4497_ == 0)
{
lean_object* v_unused_4498_; 
v_unused_4498_ = lean_ctor_get(v___x_4490_, 0);
lean_dec(v_unused_4498_);
v___x_4492_ = v___x_4490_;
v_isShared_4493_ = v_isSharedCheck_4497_;
goto v_resetjp_4491_;
}
else
{
lean_dec(v___x_4490_);
v___x_4492_ = lean_box(0);
v_isShared_4493_ = v_isSharedCheck_4497_;
goto v_resetjp_4491_;
}
v_resetjp_4491_:
{
lean_object* v___x_4495_; 
if (v_isShared_4493_ == 0)
{
lean_ctor_set(v___x_4492_, 0, v_a_4488_);
v___x_4495_ = v___x_4492_;
goto v_reusejp_4494_;
}
else
{
lean_object* v_reuseFailAlloc_4496_; 
v_reuseFailAlloc_4496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4496_, 0, v_a_4488_);
v___x_4495_ = v_reuseFailAlloc_4496_;
goto v_reusejp_4494_;
}
v_reusejp_4494_:
{
return v___x_4495_;
}
}
}
else
{
lean_object* v_a_4499_; lean_object* v___x_4501_; uint8_t v_isShared_4502_; uint8_t v_isSharedCheck_4506_; 
lean_dec(v_a_4488_);
v_a_4499_ = lean_ctor_get(v___x_4490_, 0);
v_isSharedCheck_4506_ = !lean_is_exclusive(v___x_4490_);
if (v_isSharedCheck_4506_ == 0)
{
v___x_4501_ = v___x_4490_;
v_isShared_4502_ = v_isSharedCheck_4506_;
goto v_resetjp_4500_;
}
else
{
lean_inc(v_a_4499_);
lean_dec(v___x_4490_);
v___x_4501_ = lean_box(0);
v_isShared_4502_ = v_isSharedCheck_4506_;
goto v_resetjp_4500_;
}
v_resetjp_4500_:
{
lean_object* v___x_4504_; 
if (v_isShared_4502_ == 0)
{
v___x_4504_ = v___x_4501_;
goto v_reusejp_4503_;
}
else
{
lean_object* v_reuseFailAlloc_4505_; 
v_reuseFailAlloc_4505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4505_, 0, v_a_4499_);
v___x_4504_ = v_reuseFailAlloc_4505_;
goto v_reusejp_4503_;
}
v_reusejp_4503_:
{
return v___x_4504_;
}
}
}
}
else
{
lean_dec_ref(v_e_4468_);
return v___x_4487_;
}
}
else
{
lean_object* v_val_4507_; lean_object* v___x_4509_; 
lean_dec_ref(v_e_4468_);
lean_dec_ref(v_post_4464_);
lean_dec_ref(v_pre_4463_);
v_val_4507_ = lean_ctor_get(v___x_4481_, 0);
lean_inc(v_val_4507_);
lean_dec_ref_known(v___x_4481_, 1);
if (v_isShared_4480_ == 0)
{
lean_ctor_set(v___x_4479_, 0, v_val_4507_);
v___x_4509_ = v___x_4479_;
goto v_reusejp_4508_;
}
else
{
lean_object* v_reuseFailAlloc_4510_; 
v_reuseFailAlloc_4510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4510_, 0, v_val_4507_);
v___x_4509_ = v_reuseFailAlloc_4510_;
goto v_reusejp_4508_;
}
v_reusejp_4508_:
{
return v___x_4509_;
}
}
}
}
else
{
lean_object* v_a_4512_; lean_object* v___x_4514_; uint8_t v_isShared_4515_; uint8_t v_isSharedCheck_4519_; 
lean_dec_ref(v_e_4468_);
lean_dec_ref(v_post_4464_);
lean_dec_ref(v_pre_4463_);
v_a_4512_ = lean_ctor_get(v___x_4476_, 0);
v_isSharedCheck_4519_ = !lean_is_exclusive(v___x_4476_);
if (v_isSharedCheck_4519_ == 0)
{
v___x_4514_ = v___x_4476_;
v_isShared_4515_ = v_isSharedCheck_4519_;
goto v_resetjp_4513_;
}
else
{
lean_inc(v_a_4512_);
lean_dec(v___x_4476_);
v___x_4514_ = lean_box(0);
v_isShared_4515_ = v_isSharedCheck_4519_;
goto v_resetjp_4513_;
}
v_resetjp_4513_:
{
lean_object* v___x_4517_; 
if (v_isShared_4515_ == 0)
{
v___x_4517_ = v___x_4514_;
goto v_reusejp_4516_;
}
else
{
lean_object* v_reuseFailAlloc_4518_; 
v_reuseFailAlloc_4518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4518_, 0, v_a_4512_);
v___x_4517_ = v_reuseFailAlloc_4518_;
goto v_reusejp_4516_;
}
v_reusejp_4516_:
{
return v___x_4517_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___lam__0___boxed(lean_object* v_fvars_4520_, lean_object* v_pre_4521_, lean_object* v_post_4522_, lean_object* v_usedLetOnly_4523_, lean_object* v_skipConstInApp_4524_, lean_object* v_skipInstances_4525_, lean_object* v_body_4526_, lean_object* v_x_4527_, lean_object* v___y_4528_, lean_object* v___y_4529_, lean_object* v___y_4530_, lean_object* v___y_4531_, lean_object* v___y_4532_, lean_object* v___y_4533_){
_start:
{
uint8_t v_usedLetOnly_boxed_4534_; uint8_t v_skipConstInApp_boxed_4535_; uint8_t v_skipInstances_boxed_4536_; lean_object* v_res_4537_; 
v_usedLetOnly_boxed_4534_ = lean_unbox(v_usedLetOnly_4523_);
v_skipConstInApp_boxed_4535_ = lean_unbox(v_skipConstInApp_4524_);
v_skipInstances_boxed_4536_ = lean_unbox(v_skipInstances_4525_);
v_res_4537_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___lam__0(v_fvars_4520_, v_pre_4521_, v_post_4522_, v_usedLetOnly_boxed_4534_, v_skipConstInApp_boxed_4535_, v_skipInstances_boxed_4536_, v_body_4526_, v_x_4527_, v___y_4528_, v___y_4529_, v___y_4530_, v___y_4531_, v___y_4532_);
lean_dec(v___y_4532_);
lean_dec_ref(v___y_4531_);
lean_dec(v___y_4530_);
lean_dec_ref(v___y_4529_);
lean_dec(v___y_4528_);
return v_res_4537_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5(lean_object* v_pre_4538_, lean_object* v_post_4539_, uint8_t v_usedLetOnly_4540_, uint8_t v_skipConstInApp_4541_, uint8_t v_skipInstances_4542_, lean_object* v_fvars_4543_, lean_object* v_e_4544_, lean_object* v_a_4545_, lean_object* v___y_4546_, lean_object* v___y_4547_, lean_object* v___y_4548_, lean_object* v___y_4549_){
_start:
{
if (lean_obj_tag(v_e_4544_) == 7)
{
lean_object* v_binderName_4551_; lean_object* v_binderType_4552_; lean_object* v_body_4553_; uint8_t v_binderInfo_4554_; lean_object* v___x_4555_; lean_object* v___x_4556_; 
v_binderName_4551_ = lean_ctor_get(v_e_4544_, 0);
lean_inc(v_binderName_4551_);
v_binderType_4552_ = lean_ctor_get(v_e_4544_, 1);
lean_inc_ref(v_binderType_4552_);
v_body_4553_ = lean_ctor_get(v_e_4544_, 2);
lean_inc_ref(v_body_4553_);
v_binderInfo_4554_ = lean_ctor_get_uint8(v_e_4544_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_4544_, 3);
v___x_4555_ = lean_expr_instantiate_rev(v_binderType_4552_, v_fvars_4543_);
lean_dec_ref(v_binderType_4552_);
lean_inc_ref(v_post_4539_);
lean_inc_ref(v_pre_4538_);
v___x_4556_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4538_, v_post_4539_, v_usedLetOnly_4540_, v_skipConstInApp_4541_, v_skipInstances_4542_, v___x_4555_, v_a_4545_, v___y_4546_, v___y_4547_, v___y_4548_, v___y_4549_);
if (lean_obj_tag(v___x_4556_) == 0)
{
lean_object* v_a_4557_; lean_object* v___x_4558_; lean_object* v___x_4559_; lean_object* v___x_4560_; lean_object* v___f_4561_; uint8_t v___x_4562_; lean_object* v___x_4563_; 
v_a_4557_ = lean_ctor_get(v___x_4556_, 0);
lean_inc(v_a_4557_);
lean_dec_ref_known(v___x_4556_, 1);
v___x_4558_ = lean_box(v_usedLetOnly_4540_);
v___x_4559_ = lean_box(v_skipConstInApp_4541_);
v___x_4560_ = lean_box(v_skipInstances_4542_);
v___f_4561_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___lam__0___boxed), 14, 7);
lean_closure_set(v___f_4561_, 0, v_fvars_4543_);
lean_closure_set(v___f_4561_, 1, v_pre_4538_);
lean_closure_set(v___f_4561_, 2, v_post_4539_);
lean_closure_set(v___f_4561_, 3, v___x_4558_);
lean_closure_set(v___f_4561_, 4, v___x_4559_);
lean_closure_set(v___f_4561_, 5, v___x_4560_);
lean_closure_set(v___f_4561_, 6, v_body_4553_);
v___x_4562_ = 0;
v___x_4563_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_binderName_4551_, v_binderInfo_4554_, v_a_4557_, v___f_4561_, v___x_4562_, v_a_4545_, v___y_4546_, v___y_4547_, v___y_4548_, v___y_4549_);
return v___x_4563_;
}
else
{
lean_dec_ref(v_body_4553_);
lean_dec(v_binderName_4551_);
lean_dec_ref(v_fvars_4543_);
lean_dec_ref(v_post_4539_);
lean_dec_ref(v_pre_4538_);
return v___x_4556_;
}
}
else
{
lean_object* v___x_4564_; lean_object* v___x_4565_; 
v___x_4564_ = lean_expr_instantiate_rev(v_e_4544_, v_fvars_4543_);
lean_dec_ref(v_e_4544_);
lean_inc_ref(v_post_4539_);
lean_inc_ref(v_pre_4538_);
v___x_4565_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4538_, v_post_4539_, v_usedLetOnly_4540_, v_skipConstInApp_4541_, v_skipInstances_4542_, v___x_4564_, v_a_4545_, v___y_4546_, v___y_4547_, v___y_4548_, v___y_4549_);
if (lean_obj_tag(v___x_4565_) == 0)
{
lean_object* v_a_4566_; uint8_t v___x_4567_; uint8_t v___x_4568_; uint8_t v___x_4569_; lean_object* v___x_4570_; 
v_a_4566_ = lean_ctor_get(v___x_4565_, 0);
lean_inc(v_a_4566_);
lean_dec_ref_known(v___x_4565_, 1);
v___x_4567_ = 0;
v___x_4568_ = 1;
v___x_4569_ = 1;
v___x_4570_ = l_Lean_Meta_mkForallFVars(v_fvars_4543_, v_a_4566_, v___x_4567_, v_usedLetOnly_4540_, v___x_4568_, v___x_4569_, v___y_4546_, v___y_4547_, v___y_4548_, v___y_4549_);
lean_dec_ref(v_fvars_4543_);
if (lean_obj_tag(v___x_4570_) == 0)
{
lean_object* v_a_4571_; lean_object* v___x_4572_; 
v_a_4571_ = lean_ctor_get(v___x_4570_, 0);
lean_inc(v_a_4571_);
lean_dec_ref_known(v___x_4570_, 1);
v___x_4572_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4538_, v_post_4539_, v_usedLetOnly_4540_, v_skipConstInApp_4541_, v_skipInstances_4542_, v_a_4571_, v_a_4545_, v___y_4546_, v___y_4547_, v___y_4548_, v___y_4549_);
return v___x_4572_;
}
else
{
lean_dec_ref(v_post_4539_);
lean_dec_ref(v_pre_4538_);
return v___x_4570_;
}
}
else
{
lean_dec_ref(v_fvars_4543_);
lean_dec_ref(v_post_4539_);
lean_dec_ref(v_pre_4538_);
return v___x_4565_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___lam__0(lean_object* v_fvars_4573_, lean_object* v_pre_4574_, lean_object* v_post_4575_, uint8_t v_usedLetOnly_4576_, uint8_t v_skipConstInApp_4577_, uint8_t v_skipInstances_4578_, lean_object* v_body_4579_, lean_object* v_x_4580_, lean_object* v___y_4581_, lean_object* v___y_4582_, lean_object* v___y_4583_, lean_object* v___y_4584_, lean_object* v___y_4585_){
_start:
{
lean_object* v___x_4587_; lean_object* v___x_4588_; 
v___x_4587_ = lean_array_push(v_fvars_4573_, v_x_4580_);
v___x_4588_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5(v_pre_4574_, v_post_4575_, v_usedLetOnly_4576_, v_skipConstInApp_4577_, v_skipInstances_4578_, v___x_4587_, v_body_4579_, v___y_4581_, v___y_4582_, v___y_4583_, v___y_4584_, v___y_4585_);
return v___x_4588_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3___boxed(lean_object* v_pre_4589_, lean_object* v_post_4590_, lean_object* v_usedLetOnly_4591_, lean_object* v_skipConstInApp_4592_, lean_object* v_skipInstances_4593_, lean_object* v_e_4594_, lean_object* v_a_4595_, lean_object* v___y_4596_, lean_object* v___y_4597_, lean_object* v___y_4598_, lean_object* v___y_4599_, lean_object* v___y_4600_){
_start:
{
uint8_t v_usedLetOnly_boxed_4601_; uint8_t v_skipConstInApp_boxed_4602_; uint8_t v_skipInstances_boxed_4603_; lean_object* v_res_4604_; 
v_usedLetOnly_boxed_4601_ = lean_unbox(v_usedLetOnly_4591_);
v_skipConstInApp_boxed_4602_ = lean_unbox(v_skipConstInApp_4592_);
v_skipInstances_boxed_4603_ = lean_unbox(v_skipInstances_4593_);
v_res_4604_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4589_, v_post_4590_, v_usedLetOnly_boxed_4601_, v_skipConstInApp_boxed_4602_, v_skipInstances_boxed_4603_, v_e_4594_, v_a_4595_, v___y_4596_, v___y_4597_, v___y_4598_, v___y_4599_);
lean_dec(v___y_4599_);
lean_dec_ref(v___y_4598_);
lean_dec(v___y_4597_);
lean_dec_ref(v___y_4596_);
lean_dec(v_a_4595_);
return v_res_4604_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__2___boxed(lean_object* v_pre_4605_, lean_object* v_post_4606_, lean_object* v_usedLetOnly_4607_, lean_object* v_skipConstInApp_4608_, lean_object* v_skipInstances_4609_, lean_object* v_sz_4610_, lean_object* v_i_4611_, lean_object* v_bs_4612_, lean_object* v___y_4613_, lean_object* v___y_4614_, lean_object* v___y_4615_, lean_object* v___y_4616_, lean_object* v___y_4617_, lean_object* v___y_4618_){
_start:
{
uint8_t v_usedLetOnly_boxed_4619_; uint8_t v_skipConstInApp_boxed_4620_; uint8_t v_skipInstances_boxed_4621_; size_t v_sz_boxed_4622_; size_t v_i_boxed_4623_; lean_object* v_res_4624_; 
v_usedLetOnly_boxed_4619_ = lean_unbox(v_usedLetOnly_4607_);
v_skipConstInApp_boxed_4620_ = lean_unbox(v_skipConstInApp_4608_);
v_skipInstances_boxed_4621_ = lean_unbox(v_skipInstances_4609_);
v_sz_boxed_4622_ = lean_unbox_usize(v_sz_4610_);
lean_dec(v_sz_4610_);
v_i_boxed_4623_ = lean_unbox_usize(v_i_4611_);
lean_dec(v_i_4611_);
v_res_4624_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__2(v_pre_4605_, v_post_4606_, v_usedLetOnly_boxed_4619_, v_skipConstInApp_boxed_4620_, v_skipInstances_boxed_4621_, v_sz_boxed_4622_, v_i_boxed_4623_, v_bs_4612_, v___y_4613_, v___y_4614_, v___y_4615_, v___y_4616_, v___y_4617_);
lean_dec(v___y_4617_);
lean_dec_ref(v___y_4616_);
lean_dec(v___y_4615_);
lean_dec_ref(v___y_4614_);
lean_dec(v___y_4613_);
return v_res_4624_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___boxed(lean_object* v_pre_4625_, lean_object* v_post_4626_, lean_object* v_usedLetOnly_4627_, lean_object* v_skipConstInApp_4628_, lean_object* v_skipInstances_4629_, lean_object* v_e_4630_, lean_object* v_a_4631_, lean_object* v___y_4632_, lean_object* v___y_4633_, lean_object* v___y_4634_, lean_object* v___y_4635_, lean_object* v___y_4636_){
_start:
{
uint8_t v_usedLetOnly_boxed_4637_; uint8_t v_skipConstInApp_boxed_4638_; uint8_t v_skipInstances_boxed_4639_; lean_object* v_res_4640_; 
v_usedLetOnly_boxed_4637_ = lean_unbox(v_usedLetOnly_4627_);
v_skipConstInApp_boxed_4638_ = lean_unbox(v_skipConstInApp_4628_);
v_skipInstances_boxed_4639_ = lean_unbox(v_skipInstances_4629_);
v_res_4640_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4625_, v_post_4626_, v_usedLetOnly_boxed_4637_, v_skipConstInApp_boxed_4638_, v_skipInstances_boxed_4639_, v_e_4630_, v_a_4631_, v___y_4632_, v___y_4633_, v___y_4634_, v___y_4635_);
lean_dec(v___y_4635_);
lean_dec_ref(v___y_4634_);
lean_dec(v___y_4633_);
lean_dec_ref(v___y_4632_);
lean_dec(v_a_4631_);
return v_res_4640_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___boxed(lean_object* v_pre_4641_, lean_object* v_post_4642_, lean_object* v_usedLetOnly_4643_, lean_object* v_skipConstInApp_4644_, lean_object* v_skipInstances_4645_, lean_object* v_fvars_4646_, lean_object* v_e_4647_, lean_object* v_a_4648_, lean_object* v___y_4649_, lean_object* v___y_4650_, lean_object* v___y_4651_, lean_object* v___y_4652_, lean_object* v___y_4653_){
_start:
{
uint8_t v_usedLetOnly_boxed_4654_; uint8_t v_skipConstInApp_boxed_4655_; uint8_t v_skipInstances_boxed_4656_; lean_object* v_res_4657_; 
v_usedLetOnly_boxed_4654_ = lean_unbox(v_usedLetOnly_4643_);
v_skipConstInApp_boxed_4655_ = lean_unbox(v_skipConstInApp_4644_);
v_skipInstances_boxed_4656_ = lean_unbox(v_skipInstances_4645_);
v_res_4657_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5(v_pre_4641_, v_post_4642_, v_usedLetOnly_boxed_4654_, v_skipConstInApp_boxed_4655_, v_skipInstances_boxed_4656_, v_fvars_4646_, v_e_4647_, v_a_4648_, v___y_4649_, v___y_4650_, v___y_4651_, v___y_4652_);
lean_dec(v___y_4652_);
lean_dec_ref(v___y_4651_);
lean_dec(v___y_4650_);
lean_dec_ref(v___y_4649_);
lean_dec(v_a_4648_);
return v_res_4657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___boxed(lean_object* v_pre_4658_, lean_object* v_post_4659_, lean_object* v_usedLetOnly_4660_, lean_object* v_skipConstInApp_4661_, lean_object* v_skipInstances_4662_, lean_object* v_fvars_4663_, lean_object* v_e_4664_, lean_object* v_a_4665_, lean_object* v___y_4666_, lean_object* v___y_4667_, lean_object* v___y_4668_, lean_object* v___y_4669_, lean_object* v___y_4670_){
_start:
{
uint8_t v_usedLetOnly_boxed_4671_; uint8_t v_skipConstInApp_boxed_4672_; uint8_t v_skipInstances_boxed_4673_; lean_object* v_res_4674_; 
v_usedLetOnly_boxed_4671_ = lean_unbox(v_usedLetOnly_4660_);
v_skipConstInApp_boxed_4672_ = lean_unbox(v_skipConstInApp_4661_);
v_skipInstances_boxed_4673_ = lean_unbox(v_skipInstances_4662_);
v_res_4674_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6(v_pre_4658_, v_post_4659_, v_usedLetOnly_boxed_4671_, v_skipConstInApp_boxed_4672_, v_skipInstances_boxed_4673_, v_fvars_4663_, v_e_4664_, v_a_4665_, v___y_4666_, v___y_4667_, v___y_4668_, v___y_4669_);
lean_dec(v___y_4669_);
lean_dec_ref(v___y_4668_);
lean_dec(v___y_4667_);
lean_dec_ref(v___y_4666_);
lean_dec(v_a_4665_);
return v_res_4674_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___boxed(lean_object* v_pre_4675_, lean_object* v_post_4676_, lean_object* v_usedLetOnly_4677_, lean_object* v_skipConstInApp_4678_, lean_object* v_skipInstances_4679_, lean_object* v_fvars_4680_, lean_object* v_e_4681_, lean_object* v_a_4682_, lean_object* v___y_4683_, lean_object* v___y_4684_, lean_object* v___y_4685_, lean_object* v___y_4686_, lean_object* v___y_4687_){
_start:
{
uint8_t v_usedLetOnly_boxed_4688_; uint8_t v_skipConstInApp_boxed_4689_; uint8_t v_skipInstances_boxed_4690_; lean_object* v_res_4691_; 
v_usedLetOnly_boxed_4688_ = lean_unbox(v_usedLetOnly_4677_);
v_skipConstInApp_boxed_4689_ = lean_unbox(v_skipConstInApp_4678_);
v_skipInstances_boxed_4690_ = lean_unbox(v_skipInstances_4679_);
v_res_4691_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7(v_pre_4675_, v_post_4676_, v_usedLetOnly_boxed_4688_, v_skipConstInApp_boxed_4689_, v_skipInstances_boxed_4690_, v_fvars_4680_, v_e_4681_, v_a_4682_, v___y_4683_, v___y_4684_, v___y_4685_, v___y_4686_);
lean_dec(v___y_4686_);
lean_dec_ref(v___y_4685_);
lean_dec(v___y_4684_);
lean_dec_ref(v___y_4683_);
lean_dec(v_a_4682_);
return v_res_4691_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_upperBound_4692_, lean_object* v___x_4693_, lean_object* v_pre_4694_, lean_object* v_post_4695_, lean_object* v_usedLetOnly_4696_, lean_object* v_skipConstInApp_4697_, lean_object* v_skipInstances_4698_, lean_object* v_a_4699_, lean_object* v_b_4700_, lean_object* v___y_4701_, lean_object* v___y_4702_, lean_object* v___y_4703_, lean_object* v___y_4704_, lean_object* v___y_4705_, lean_object* v___y_4706_){
_start:
{
uint8_t v_usedLetOnly_boxed_4707_; uint8_t v_skipConstInApp_boxed_4708_; uint8_t v_skipInstances_boxed_4709_; lean_object* v_res_4710_; 
v_usedLetOnly_boxed_4707_ = lean_unbox(v_usedLetOnly_4696_);
v_skipConstInApp_boxed_4708_ = lean_unbox(v_skipConstInApp_4697_);
v_skipInstances_boxed_4709_ = lean_unbox(v_skipInstances_4698_);
v_res_4710_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg(v_upperBound_4692_, v___x_4693_, v_pre_4694_, v_post_4695_, v_usedLetOnly_boxed_4707_, v_skipConstInApp_boxed_4708_, v_skipInstances_boxed_4709_, v_a_4699_, v_b_4700_, v___y_4701_, v___y_4702_, v___y_4703_, v___y_4704_, v___y_4705_);
lean_dec(v___y_4705_);
lean_dec_ref(v___y_4704_);
lean_dec(v___y_4703_);
lean_dec_ref(v___y_4702_);
lean_dec(v___y_4701_);
lean_dec_ref(v___x_4693_);
lean_dec(v_upperBound_4692_);
return v_res_4710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__8___boxed(lean_object* v_skipInstances_4711_, lean_object* v_pre_4712_, lean_object* v_post_4713_, lean_object* v_usedLetOnly_4714_, lean_object* v_skipConstInApp_4715_, lean_object* v_x_4716_, lean_object* v_x_4717_, lean_object* v_x_4718_, lean_object* v___y_4719_, lean_object* v___y_4720_, lean_object* v___y_4721_, lean_object* v___y_4722_, lean_object* v___y_4723_, lean_object* v___y_4724_){
_start:
{
uint8_t v_skipInstances_boxed_4725_; uint8_t v_usedLetOnly_boxed_4726_; uint8_t v_skipConstInApp_boxed_4727_; lean_object* v_res_4728_; 
v_skipInstances_boxed_4725_ = lean_unbox(v_skipInstances_4711_);
v_usedLetOnly_boxed_4726_ = lean_unbox(v_usedLetOnly_4714_);
v_skipConstInApp_boxed_4727_ = lean_unbox(v_skipConstInApp_4715_);
v_res_4728_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__8(v_skipInstances_boxed_4725_, v_pre_4712_, v_post_4713_, v_usedLetOnly_boxed_4726_, v_skipConstInApp_boxed_4727_, v_x_4716_, v_x_4717_, v_x_4718_, v___y_4719_, v___y_4720_, v___y_4721_, v___y_4722_, v___y_4723_);
lean_dec(v___y_4723_);
lean_dec_ref(v___y_4722_);
lean_dec(v___y_4721_);
lean_dec_ref(v___y_4720_);
lean_dec(v___y_4719_);
return v_res_4728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(lean_object* v_input_4729_, lean_object* v_pre_4730_, lean_object* v_post_4731_, uint8_t v_usedLetOnly_4732_, uint8_t v_skipConstInApp_4733_, lean_object* v___y_4734_, lean_object* v___y_4735_, lean_object* v___y_4736_, lean_object* v___y_4737_){
_start:
{
lean_object* v___x_4739_; lean_object* v___x_4740_; lean_object* v_a_4741_; uint8_t v___x_4742_; lean_object* v___x_4743_; 
v___x_4739_ = lean_obj_once(&l_Lean_Core_transform___redArg___closed__3, &l_Lean_Core_transform___redArg___closed__3_once, _init_l_Lean_Core_transform___redArg___closed__3);
v___x_4740_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0(lean_box(0), v___x_4739_, v___y_4734_, v___y_4735_, v___y_4736_, v___y_4737_);
v_a_4741_ = lean_ctor_get(v___x_4740_, 0);
lean_inc(v_a_4741_);
lean_dec_ref(v___x_4740_);
v___x_4742_ = 0;
v___x_4743_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4730_, v_post_4731_, v_usedLetOnly_4732_, v_skipConstInApp_4733_, v___x_4742_, v_input_4729_, v_a_4741_, v___y_4734_, v___y_4735_, v___y_4736_, v___y_4737_);
if (lean_obj_tag(v___x_4743_) == 0)
{
lean_object* v_a_4744_; lean_object* v___x_4745_; lean_object* v___x_4746_; lean_object* v___x_4748_; uint8_t v_isShared_4749_; uint8_t v_isSharedCheck_4753_; 
v_a_4744_ = lean_ctor_get(v___x_4743_, 0);
lean_inc(v_a_4744_);
lean_dec_ref_known(v___x_4743_, 1);
v___x_4745_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_4745_, 0, lean_box(0));
lean_closure_set(v___x_4745_, 1, lean_box(0));
lean_closure_set(v___x_4745_, 2, v_a_4741_);
v___x_4746_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0(lean_box(0), v___x_4745_, v___y_4734_, v___y_4735_, v___y_4736_, v___y_4737_);
v_isSharedCheck_4753_ = !lean_is_exclusive(v___x_4746_);
if (v_isSharedCheck_4753_ == 0)
{
lean_object* v_unused_4754_; 
v_unused_4754_ = lean_ctor_get(v___x_4746_, 0);
lean_dec(v_unused_4754_);
v___x_4748_ = v___x_4746_;
v_isShared_4749_ = v_isSharedCheck_4753_;
goto v_resetjp_4747_;
}
else
{
lean_dec(v___x_4746_);
v___x_4748_ = lean_box(0);
v_isShared_4749_ = v_isSharedCheck_4753_;
goto v_resetjp_4747_;
}
v_resetjp_4747_:
{
lean_object* v___x_4751_; 
if (v_isShared_4749_ == 0)
{
lean_ctor_set(v___x_4748_, 0, v_a_4744_);
v___x_4751_ = v___x_4748_;
goto v_reusejp_4750_;
}
else
{
lean_object* v_reuseFailAlloc_4752_; 
v_reuseFailAlloc_4752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4752_, 0, v_a_4744_);
v___x_4751_ = v_reuseFailAlloc_4752_;
goto v_reusejp_4750_;
}
v_reusejp_4750_:
{
return v___x_4751_;
}
}
}
else
{
lean_dec(v_a_4741_);
return v___x_4743_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___boxed(lean_object* v_input_4755_, lean_object* v_pre_4756_, lean_object* v_post_4757_, lean_object* v_usedLetOnly_4758_, lean_object* v_skipConstInApp_4759_, lean_object* v___y_4760_, lean_object* v___y_4761_, lean_object* v___y_4762_, lean_object* v___y_4763_, lean_object* v___y_4764_){
_start:
{
uint8_t v_usedLetOnly_boxed_4765_; uint8_t v_skipConstInApp_boxed_4766_; lean_object* v_res_4767_; 
v_usedLetOnly_boxed_4765_ = lean_unbox(v_usedLetOnly_4758_);
v_skipConstInApp_boxed_4766_ = lean_unbox(v_skipConstInApp_4759_);
v_res_4767_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(v_input_4755_, v_pre_4756_, v_post_4757_, v_usedLetOnly_boxed_4765_, v_skipConstInApp_boxed_4766_, v___y_4760_, v___y_4761_, v___y_4762_, v___y_4763_);
lean_dec(v___y_4763_);
lean_dec_ref(v___y_4762_);
lean_dec(v___y_4761_);
lean_dec_ref(v___y_4760_);
return v_res_4767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce(lean_object* v_e_4769_, uint8_t v_zetaDelta_4770_, uint8_t v_zetaHave_4771_, uint8_t v_beta_4772_, lean_object* v_a_4773_, lean_object* v_a_4774_, lean_object* v_a_4775_, lean_object* v_a_4776_){
_start:
{
lean_object* v_lctx_4778_; lean_object* v___x_4779_; lean_object* v___x_4780_; lean_object* v___x_4781_; lean_object* v___f_4782_; uint8_t v___x_4783_; 
v_lctx_4778_ = lean_ctor_get(v_a_4773_, 2);
lean_inc_ref(v_lctx_4778_);
v___x_4779_ = lean_local_ctx_num_indices(v_lctx_4778_);
v___x_4780_ = lean_box(v_zetaHave_4771_);
v___x_4781_ = lean_box(v_zetaDelta_4770_);
v___f_4782_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaReduce___lam__0___boxed), 9, 3);
lean_closure_set(v___f_4782_, 0, v___x_4780_);
lean_closure_set(v___f_4782_, 1, v___x_4779_);
lean_closure_set(v___f_4782_, 2, v___x_4781_);
v___x_4783_ = 1;
if (v_beta_4772_ == 0)
{
lean_object* v___f_4784_; lean_object* v___f_4785_; lean_object* v___x_4786_; 
v___f_4784_ = ((lean_object*)(l_Lean_Meta_zetaReduce___closed__0));
v___f_4785_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaReduce___lam__2___boxed), 7, 1);
lean_closure_set(v___f_4785_, 0, v___f_4782_);
v___x_4786_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(v_e_4769_, v___f_4785_, v___f_4784_, v___x_4783_, v_beta_4772_, v_a_4773_, v_a_4774_, v_a_4775_, v_a_4776_);
return v___x_4786_;
}
else
{
lean_object* v___f_4787_; lean_object* v___f_4788_; uint8_t v___x_4789_; lean_object* v___x_4790_; 
v___f_4787_ = ((lean_object*)(l_Lean_Meta_zetaReduce___closed__0));
v___f_4788_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaReduce___lam__4___boxed), 7, 1);
lean_closure_set(v___f_4788_, 0, v___f_4782_);
v___x_4789_ = 0;
v___x_4790_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(v_e_4769_, v___f_4788_, v___f_4787_, v___x_4783_, v___x_4789_, v_a_4773_, v_a_4774_, v_a_4775_, v_a_4776_);
return v___x_4790_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___boxed(lean_object* v_e_4791_, lean_object* v_zetaDelta_4792_, lean_object* v_zetaHave_4793_, lean_object* v_beta_4794_, lean_object* v_a_4795_, lean_object* v_a_4796_, lean_object* v_a_4797_, lean_object* v_a_4798_, lean_object* v_a_4799_){
_start:
{
uint8_t v_zetaDelta_boxed_4800_; uint8_t v_zetaHave_boxed_4801_; uint8_t v_beta_boxed_4802_; lean_object* v_res_4803_; 
v_zetaDelta_boxed_4800_ = lean_unbox(v_zetaDelta_4792_);
v_zetaHave_boxed_4801_ = lean_unbox(v_zetaHave_4793_);
v_beta_boxed_4802_ = lean_unbox(v_beta_4794_);
v_res_4803_ = l_Lean_Meta_zetaReduce(v_e_4791_, v_zetaDelta_boxed_4800_, v_zetaHave_boxed_4801_, v_beta_boxed_4802_, v_a_4795_, v_a_4796_, v_a_4797_, v_a_4798_);
lean_dec(v_a_4798_);
lean_dec_ref(v_a_4797_);
lean_dec(v_a_4796_);
lean_dec_ref(v_a_4795_);
return v_res_4803_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4(lean_object* v_upperBound_4804_, lean_object* v___x_4805_, lean_object* v_pre_4806_, lean_object* v_post_4807_, uint8_t v_usedLetOnly_4808_, uint8_t v_skipConstInApp_4809_, uint8_t v_skipInstances_4810_, lean_object* v___x_4811_, lean_object* v_inst_4812_, lean_object* v_R_4813_, lean_object* v_a_4814_, lean_object* v_b_4815_, lean_object* v_c_4816_, lean_object* v___y_4817_, lean_object* v___y_4818_, lean_object* v___y_4819_, lean_object* v___y_4820_, lean_object* v___y_4821_){
_start:
{
lean_object* v___x_4823_; 
v___x_4823_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg(v_upperBound_4804_, v___x_4805_, v_pre_4806_, v_post_4807_, v_usedLetOnly_4808_, v_skipConstInApp_4809_, v_skipInstances_4810_, v_a_4814_, v_b_4815_, v___y_4817_, v___y_4818_, v___y_4819_, v___y_4820_, v___y_4821_);
return v___x_4823_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___boxed(lean_object** _args){
lean_object* v_upperBound_4824_ = _args[0];
lean_object* v___x_4825_ = _args[1];
lean_object* v_pre_4826_ = _args[2];
lean_object* v_post_4827_ = _args[3];
lean_object* v_usedLetOnly_4828_ = _args[4];
lean_object* v_skipConstInApp_4829_ = _args[5];
lean_object* v_skipInstances_4830_ = _args[6];
lean_object* v___x_4831_ = _args[7];
lean_object* v_inst_4832_ = _args[8];
lean_object* v_R_4833_ = _args[9];
lean_object* v_a_4834_ = _args[10];
lean_object* v_b_4835_ = _args[11];
lean_object* v_c_4836_ = _args[12];
lean_object* v___y_4837_ = _args[13];
lean_object* v___y_4838_ = _args[14];
lean_object* v___y_4839_ = _args[15];
lean_object* v___y_4840_ = _args[16];
lean_object* v___y_4841_ = _args[17];
lean_object* v___y_4842_ = _args[18];
_start:
{
uint8_t v_usedLetOnly_boxed_4843_; uint8_t v_skipConstInApp_boxed_4844_; uint8_t v_skipInstances_boxed_4845_; lean_object* v_res_4846_; 
v_usedLetOnly_boxed_4843_ = lean_unbox(v_usedLetOnly_4828_);
v_skipConstInApp_boxed_4844_ = lean_unbox(v_skipConstInApp_4829_);
v_skipInstances_boxed_4845_ = lean_unbox(v_skipInstances_4830_);
v_res_4846_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4(v_upperBound_4824_, v___x_4825_, v_pre_4826_, v_post_4827_, v_usedLetOnly_boxed_4843_, v_skipConstInApp_boxed_4844_, v_skipInstances_boxed_4845_, v___x_4831_, v_inst_4832_, v_R_4833_, v_a_4834_, v_b_4835_, v_c_4836_, v___y_4837_, v___y_4838_, v___y_4839_, v___y_4840_, v___y_4841_);
lean_dec(v___y_4841_);
lean_dec_ref(v___y_4840_);
lean_dec(v___y_4839_);
lean_dec_ref(v___y_4838_);
lean_dec(v___y_4837_);
lean_dec(v___x_4831_);
lean_dec_ref(v___x_4825_);
lean_dec(v_upperBound_4824_);
return v_res_4846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6(lean_object* v_00_u03b1_4847_, lean_object* v_name_4848_, uint8_t v_bi_4849_, lean_object* v_type_4850_, lean_object* v_k_4851_, uint8_t v_kind_4852_, lean_object* v___y_4853_, lean_object* v___y_4854_, lean_object* v___y_4855_, lean_object* v___y_4856_, lean_object* v___y_4857_){
_start:
{
lean_object* v___x_4859_; 
v___x_4859_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_name_4848_, v_bi_4849_, v_type_4850_, v_k_4851_, v_kind_4852_, v___y_4853_, v___y_4854_, v___y_4855_, v___y_4856_, v___y_4857_);
return v___x_4859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___boxed(lean_object* v_00_u03b1_4860_, lean_object* v_name_4861_, lean_object* v_bi_4862_, lean_object* v_type_4863_, lean_object* v_k_4864_, lean_object* v_kind_4865_, lean_object* v___y_4866_, lean_object* v___y_4867_, lean_object* v___y_4868_, lean_object* v___y_4869_, lean_object* v___y_4870_, lean_object* v___y_4871_){
_start:
{
uint8_t v_bi_boxed_4872_; uint8_t v_kind_boxed_4873_; lean_object* v_res_4874_; 
v_bi_boxed_4872_ = lean_unbox(v_bi_4862_);
v_kind_boxed_4873_ = lean_unbox(v_kind_4865_);
v_res_4874_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6(v_00_u03b1_4860_, v_name_4861_, v_bi_boxed_4872_, v_type_4863_, v_k_4864_, v_kind_boxed_4873_, v___y_4866_, v___y_4867_, v___y_4868_, v___y_4869_, v___y_4870_);
lean_dec(v___y_4870_);
lean_dec_ref(v___y_4869_);
lean_dec(v___y_4868_);
lean_dec_ref(v___y_4867_);
lean_dec(v___y_4866_);
return v_res_4874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9(lean_object* v_00_u03b1_4875_, lean_object* v_name_4876_, lean_object* v_type_4877_, lean_object* v_val_4878_, lean_object* v_k_4879_, uint8_t v_nondep_4880_, uint8_t v_kind_4881_, lean_object* v___y_4882_, lean_object* v___y_4883_, lean_object* v___y_4884_, lean_object* v___y_4885_, lean_object* v___y_4886_){
_start:
{
lean_object* v___x_4888_; 
v___x_4888_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg(v_name_4876_, v_type_4877_, v_val_4878_, v_k_4879_, v_nondep_4880_, v_kind_4881_, v___y_4882_, v___y_4883_, v___y_4884_, v___y_4885_, v___y_4886_);
return v___x_4888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___boxed(lean_object* v_00_u03b1_4889_, lean_object* v_name_4890_, lean_object* v_type_4891_, lean_object* v_val_4892_, lean_object* v_k_4893_, lean_object* v_nondep_4894_, lean_object* v_kind_4895_, lean_object* v___y_4896_, lean_object* v___y_4897_, lean_object* v___y_4898_, lean_object* v___y_4899_, lean_object* v___y_4900_, lean_object* v___y_4901_){
_start:
{
uint8_t v_nondep_boxed_4902_; uint8_t v_kind_boxed_4903_; lean_object* v_res_4904_; 
v_nondep_boxed_4902_ = lean_unbox(v_nondep_4894_);
v_kind_boxed_4903_ = lean_unbox(v_kind_4895_);
v_res_4904_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9(v_00_u03b1_4889_, v_name_4890_, v_type_4891_, v_val_4892_, v_k_4893_, v_nondep_boxed_4902_, v_kind_boxed_4903_, v___y_4896_, v___y_4897_, v___y_4898_, v___y_4899_, v___y_4900_);
lean_dec(v___y_4900_);
lean_dec_ref(v___y_4899_);
lean_dec(v___y_4898_);
lean_dec_ref(v___y_4897_);
lean_dec(v___y_4896_);
return v_res_4904_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12(lean_object* v_00_u03b1_4905_, lean_object* v_ref_4906_, lean_object* v___y_4907_, lean_object* v___y_4908_, lean_object* v___y_4909_, lean_object* v___y_4910_){
_start:
{
lean_object* v___x_4912_; 
v___x_4912_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg(v_ref_4906_);
return v___x_4912_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___boxed(lean_object* v_00_u03b1_4913_, lean_object* v_ref_4914_, lean_object* v___y_4915_, lean_object* v___y_4916_, lean_object* v___y_4917_, lean_object* v___y_4918_, lean_object* v___y_4919_){
_start:
{
lean_object* v_res_4920_; 
v_res_4920_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12(v_00_u03b1_4913_, v_ref_4914_, v___y_4915_, v___y_4916_, v___y_4917_, v___y_4918_);
lean_dec(v___y_4918_);
lean_dec_ref(v___y_4917_);
lean_dec(v___y_4916_);
lean_dec_ref(v___y_4915_);
return v_res_4920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9(lean_object* v_00_u03b1_4921_, lean_object* v_x_4922_, lean_object* v___y_4923_, lean_object* v___y_4924_, lean_object* v___y_4925_, lean_object* v___y_4926_, lean_object* v___y_4927_){
_start:
{
lean_object* v___x_4929_; 
v___x_4929_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg(v_x_4922_, v___y_4923_, v___y_4924_, v___y_4925_, v___y_4926_, v___y_4927_);
return v___x_4929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___boxed(lean_object* v_00_u03b1_4930_, lean_object* v_x_4931_, lean_object* v___y_4932_, lean_object* v___y_4933_, lean_object* v___y_4934_, lean_object* v___y_4935_, lean_object* v___y_4936_, lean_object* v___y_4937_){
_start:
{
lean_object* v_res_4938_; 
v_res_4938_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9(v_00_u03b1_4930_, v_x_4931_, v___y_4932_, v___y_4933_, v___y_4934_, v___y_4935_, v___y_4936_);
lean_dec(v___y_4936_);
lean_dec_ref(v___y_4935_);
lean_dec(v___y_4934_);
lean_dec_ref(v___y_4933_);
lean_dec(v___y_4932_);
return v_res_4938_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0_spec__0(lean_object* v_a_4939_, lean_object* v_as_4940_, size_t v_i_4941_, size_t v_stop_4942_){
_start:
{
uint8_t v___x_4943_; 
v___x_4943_ = lean_usize_dec_eq(v_i_4941_, v_stop_4942_);
if (v___x_4943_ == 0)
{
lean_object* v___x_4944_; uint8_t v___x_4945_; 
v___x_4944_ = lean_array_uget_borrowed(v_as_4940_, v_i_4941_);
v___x_4945_ = l_Lean_instBEqFVarId_beq(v_a_4939_, v___x_4944_);
if (v___x_4945_ == 0)
{
size_t v___x_4946_; size_t v___x_4947_; 
v___x_4946_ = ((size_t)1ULL);
v___x_4947_ = lean_usize_add(v_i_4941_, v___x_4946_);
v_i_4941_ = v___x_4947_;
goto _start;
}
else
{
return v___x_4945_;
}
}
else
{
uint8_t v___x_4949_; 
v___x_4949_ = 0;
return v___x_4949_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0_spec__0___boxed(lean_object* v_a_4950_, lean_object* v_as_4951_, lean_object* v_i_4952_, lean_object* v_stop_4953_){
_start:
{
size_t v_i_boxed_4954_; size_t v_stop_boxed_4955_; uint8_t v_res_4956_; lean_object* v_r_4957_; 
v_i_boxed_4954_ = lean_unbox_usize(v_i_4952_);
lean_dec(v_i_4952_);
v_stop_boxed_4955_ = lean_unbox_usize(v_stop_4953_);
lean_dec(v_stop_4953_);
v_res_4956_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0_spec__0(v_a_4950_, v_as_4951_, v_i_boxed_4954_, v_stop_boxed_4955_);
lean_dec_ref(v_as_4951_);
lean_dec(v_a_4950_);
v_r_4957_ = lean_box(v_res_4956_);
return v_r_4957_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0(lean_object* v_as_4958_, lean_object* v_a_4959_){
_start:
{
lean_object* v___x_4960_; lean_object* v___x_4961_; uint8_t v___x_4962_; 
v___x_4960_ = lean_unsigned_to_nat(0u);
v___x_4961_ = lean_array_get_size(v_as_4958_);
v___x_4962_ = lean_nat_dec_lt(v___x_4960_, v___x_4961_);
if (v___x_4962_ == 0)
{
return v___x_4962_;
}
else
{
if (v___x_4962_ == 0)
{
return v___x_4962_;
}
else
{
size_t v___x_4963_; size_t v___x_4964_; uint8_t v___x_4965_; 
v___x_4963_ = ((size_t)0ULL);
v___x_4964_ = lean_usize_of_nat(v___x_4961_);
v___x_4965_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0_spec__0(v_a_4959_, v_as_4958_, v___x_4963_, v___x_4964_);
return v___x_4965_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0___boxed(lean_object* v_as_4966_, lean_object* v_a_4967_){
_start:
{
uint8_t v_res_4968_; lean_object* v_r_4969_; 
v_res_4968_ = l_Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0(v_as_4966_, v_a_4967_);
lean_dec(v_a_4967_);
lean_dec_ref(v_as_4966_);
v_r_4969_ = lean_box(v_res_4968_);
return v_r_4969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaFVars___lam__1(lean_object* v_fvars_4970_, lean_object* v_e_4971_, lean_object* v___y_4972_, lean_object* v___y_4973_, lean_object* v___y_4974_, lean_object* v___y_4975_){
_start:
{
lean_object* v___x_4980_; 
v___x_4980_ = l_Lean_Expr_getAppFn(v_e_4971_);
if (lean_obj_tag(v___x_4980_) == 1)
{
lean_object* v_fvarId_4981_; uint8_t v___x_4982_; 
v_fvarId_4981_ = lean_ctor_get(v___x_4980_, 0);
lean_inc(v_fvarId_4981_);
lean_dec_ref_known(v___x_4980_, 1);
v___x_4982_ = l_Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0(v_fvars_4970_, v_fvarId_4981_);
if (v___x_4982_ == 0)
{
lean_dec(v_fvarId_4981_);
lean_dec_ref(v_e_4971_);
goto v___jp_4977_;
}
else
{
uint8_t v___x_4983_; lean_object* v___x_4984_; 
v___x_4983_ = 0;
v___x_4984_ = l_Lean_FVarId_getValue_x3f___redArg(v_fvarId_4981_, v___x_4983_, v___y_4972_, v___y_4974_, v___y_4975_);
if (lean_obj_tag(v___x_4984_) == 0)
{
lean_object* v_a_4985_; 
v_a_4985_ = lean_ctor_get(v___x_4984_, 0);
lean_inc(v_a_4985_);
lean_dec_ref_known(v___x_4984_, 1);
if (lean_obj_tag(v_a_4985_) == 1)
{
lean_object* v_val_4986_; lean_object* v___x_4988_; uint8_t v_isShared_4989_; uint8_t v_isSharedCheck_5009_; 
v_val_4986_ = lean_ctor_get(v_a_4985_, 0);
v_isSharedCheck_5009_ = !lean_is_exclusive(v_a_4985_);
if (v_isSharedCheck_5009_ == 0)
{
v___x_4988_ = v_a_4985_;
v_isShared_4989_ = v_isSharedCheck_5009_;
goto v_resetjp_4987_;
}
else
{
lean_inc(v_val_4986_);
lean_dec(v_a_4985_);
v___x_4988_ = lean_box(0);
v_isShared_4989_ = v_isSharedCheck_5009_;
goto v_resetjp_4987_;
}
v_resetjp_4987_:
{
lean_object* v___x_4990_; lean_object* v_a_4991_; lean_object* v___x_4993_; uint8_t v_isShared_4994_; uint8_t v_isSharedCheck_5008_; 
v___x_4990_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(v_val_4986_, v___y_4973_);
v_a_4991_ = lean_ctor_get(v___x_4990_, 0);
v_isSharedCheck_5008_ = !lean_is_exclusive(v___x_4990_);
if (v_isSharedCheck_5008_ == 0)
{
v___x_4993_ = v___x_4990_;
v_isShared_4994_ = v_isSharedCheck_5008_;
goto v_resetjp_4992_;
}
else
{
lean_inc(v_a_4991_);
lean_dec(v___x_4990_);
v___x_4993_ = lean_box(0);
v_isShared_4994_ = v_isSharedCheck_5008_;
goto v_resetjp_4992_;
}
v_resetjp_4992_:
{
lean_object* v_dummy_4995_; lean_object* v_nargs_4996_; lean_object* v___x_4997_; lean_object* v___x_4998_; lean_object* v___x_4999_; lean_object* v___x_5000_; lean_object* v___x_5001_; lean_object* v___x_5003_; 
v_dummy_4995_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_4996_ = l_Lean_Expr_getAppNumArgs(v_e_4971_);
lean_inc(v_nargs_4996_);
v___x_4997_ = lean_mk_array(v_nargs_4996_, v_dummy_4995_);
v___x_4998_ = lean_unsigned_to_nat(1u);
v___x_4999_ = lean_nat_sub(v_nargs_4996_, v___x_4998_);
lean_dec(v_nargs_4996_);
v___x_5000_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_4971_, v___x_4997_, v___x_4999_);
v___x_5001_ = l_Lean_Expr_beta(v_a_4991_, v___x_5000_);
if (v_isShared_4989_ == 0)
{
lean_ctor_set(v___x_4988_, 0, v___x_5001_);
v___x_5003_ = v___x_4988_;
goto v_reusejp_5002_;
}
else
{
lean_object* v_reuseFailAlloc_5007_; 
v_reuseFailAlloc_5007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5007_, 0, v___x_5001_);
v___x_5003_ = v_reuseFailAlloc_5007_;
goto v_reusejp_5002_;
}
v_reusejp_5002_:
{
lean_object* v___x_5005_; 
if (v_isShared_4994_ == 0)
{
lean_ctor_set(v___x_4993_, 0, v___x_5003_);
v___x_5005_ = v___x_4993_;
goto v_reusejp_5004_;
}
else
{
lean_object* v_reuseFailAlloc_5006_; 
v_reuseFailAlloc_5006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5006_, 0, v___x_5003_);
v___x_5005_ = v_reuseFailAlloc_5006_;
goto v_reusejp_5004_;
}
v_reusejp_5004_:
{
return v___x_5005_;
}
}
}
}
}
else
{
lean_dec(v_a_4985_);
lean_dec_ref(v_e_4971_);
goto v___jp_4977_;
}
}
else
{
lean_object* v_a_5010_; lean_object* v___x_5012_; uint8_t v_isShared_5013_; uint8_t v_isSharedCheck_5017_; 
lean_dec_ref(v_e_4971_);
v_a_5010_ = lean_ctor_get(v___x_4984_, 0);
v_isSharedCheck_5017_ = !lean_is_exclusive(v___x_4984_);
if (v_isSharedCheck_5017_ == 0)
{
v___x_5012_ = v___x_4984_;
v_isShared_5013_ = v_isSharedCheck_5017_;
goto v_resetjp_5011_;
}
else
{
lean_inc(v_a_5010_);
lean_dec(v___x_4984_);
v___x_5012_ = lean_box(0);
v_isShared_5013_ = v_isSharedCheck_5017_;
goto v_resetjp_5011_;
}
v_resetjp_5011_:
{
lean_object* v___x_5015_; 
if (v_isShared_5013_ == 0)
{
v___x_5015_ = v___x_5012_;
goto v_reusejp_5014_;
}
else
{
lean_object* v_reuseFailAlloc_5016_; 
v_reuseFailAlloc_5016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5016_, 0, v_a_5010_);
v___x_5015_ = v_reuseFailAlloc_5016_;
goto v_reusejp_5014_;
}
v_reusejp_5014_:
{
return v___x_5015_;
}
}
}
}
}
else
{
lean_object* v___x_5018_; lean_object* v___x_5019_; 
lean_dec_ref(v___x_4980_);
lean_dec_ref(v_e_4971_);
v___x_5018_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_5019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5019_, 0, v___x_5018_);
return v___x_5019_;
}
v___jp_4977_:
{
lean_object* v___x_4978_; lean_object* v___x_4979_; 
v___x_4978_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_4979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4979_, 0, v___x_4978_);
return v___x_4979_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaFVars___lam__1___boxed(lean_object* v_fvars_5020_, lean_object* v_e_5021_, lean_object* v___y_5022_, lean_object* v___y_5023_, lean_object* v___y_5024_, lean_object* v___y_5025_, lean_object* v___y_5026_){
_start:
{
lean_object* v_res_5027_; 
v_res_5027_ = l_Lean_Meta_zetaDeltaFVars___lam__1(v_fvars_5020_, v_e_5021_, v___y_5022_, v___y_5023_, v___y_5024_, v___y_5025_);
lean_dec(v___y_5025_);
lean_dec_ref(v___y_5024_);
lean_dec(v___y_5023_);
lean_dec_ref(v___y_5022_);
lean_dec_ref(v_fvars_5020_);
return v_res_5027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaFVars(lean_object* v_e_5028_, lean_object* v_fvars_5029_, lean_object* v_a_5030_, lean_object* v_a_5031_, lean_object* v_a_5032_, lean_object* v_a_5033_){
_start:
{
lean_object* v___f_5035_; lean_object* v_pre_5036_; uint8_t v___x_5037_; lean_object* v___x_5038_; 
v___f_5035_ = ((lean_object*)(l_Lean_Meta_zetaReduce___closed__0));
v_pre_5036_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaDeltaFVars___lam__1___boxed), 7, 1);
lean_closure_set(v_pre_5036_, 0, v_fvars_5029_);
v___x_5037_ = 0;
v___x_5038_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(v_e_5028_, v_pre_5036_, v___f_5035_, v___x_5037_, v___x_5037_, v_a_5030_, v_a_5031_, v_a_5032_, v_a_5033_);
return v___x_5038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaFVars___boxed(lean_object* v_e_5039_, lean_object* v_fvars_5040_, lean_object* v_a_5041_, lean_object* v_a_5042_, lean_object* v_a_5043_, lean_object* v_a_5044_, lean_object* v_a_5045_){
_start:
{
lean_object* v_res_5046_; 
v_res_5046_ = l_Lean_Meta_zetaDeltaFVars(v_e_5039_, v_fvars_5040_, v_a_5041_, v_a_5042_, v_a_5043_, v_a_5044_);
lean_dec(v_a_5044_);
lean_dec_ref(v_a_5043_);
lean_dec(v_a_5042_);
lean_dec_ref(v_a_5041_);
return v_res_5046_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_5047_; 
v___x_5047_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_5047_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_5048_; lean_object* v___x_5049_; 
v___x_5048_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__0, &l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__0);
v___x_5049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5049_, 0, v___x_5048_);
return v___x_5049_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_5050_; lean_object* v___x_5051_; 
v___x_5050_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__1, &l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__1);
v___x_5051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5051_, 0, v___x_5050_);
lean_ctor_set(v___x_5051_, 1, v___x_5050_);
return v___x_5051_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(lean_object* v_env_5052_, lean_object* v___y_5053_){
_start:
{
lean_object* v___x_5055_; lean_object* v_nextMacroScope_5056_; lean_object* v_ngen_5057_; lean_object* v_auxDeclNGen_5058_; lean_object* v_traceState_5059_; lean_object* v_messages_5060_; lean_object* v_infoState_5061_; lean_object* v_snapshotTasks_5062_; lean_object* v___x_5064_; uint8_t v_isShared_5065_; uint8_t v_isSharedCheck_5073_; 
v___x_5055_ = lean_st_ref_take(v___y_5053_);
v_nextMacroScope_5056_ = lean_ctor_get(v___x_5055_, 1);
v_ngen_5057_ = lean_ctor_get(v___x_5055_, 2);
v_auxDeclNGen_5058_ = lean_ctor_get(v___x_5055_, 3);
v_traceState_5059_ = lean_ctor_get(v___x_5055_, 4);
v_messages_5060_ = lean_ctor_get(v___x_5055_, 6);
v_infoState_5061_ = lean_ctor_get(v___x_5055_, 7);
v_snapshotTasks_5062_ = lean_ctor_get(v___x_5055_, 8);
v_isSharedCheck_5073_ = !lean_is_exclusive(v___x_5055_);
if (v_isSharedCheck_5073_ == 0)
{
lean_object* v_unused_5074_; lean_object* v_unused_5075_; 
v_unused_5074_ = lean_ctor_get(v___x_5055_, 5);
lean_dec(v_unused_5074_);
v_unused_5075_ = lean_ctor_get(v___x_5055_, 0);
lean_dec(v_unused_5075_);
v___x_5064_ = v___x_5055_;
v_isShared_5065_ = v_isSharedCheck_5073_;
goto v_resetjp_5063_;
}
else
{
lean_inc(v_snapshotTasks_5062_);
lean_inc(v_infoState_5061_);
lean_inc(v_messages_5060_);
lean_inc(v_traceState_5059_);
lean_inc(v_auxDeclNGen_5058_);
lean_inc(v_ngen_5057_);
lean_inc(v_nextMacroScope_5056_);
lean_dec(v___x_5055_);
v___x_5064_ = lean_box(0);
v_isShared_5065_ = v_isSharedCheck_5073_;
goto v_resetjp_5063_;
}
v_resetjp_5063_:
{
lean_object* v___x_5066_; lean_object* v___x_5068_; 
v___x_5066_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2, &l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2);
if (v_isShared_5065_ == 0)
{
lean_ctor_set(v___x_5064_, 5, v___x_5066_);
lean_ctor_set(v___x_5064_, 0, v_env_5052_);
v___x_5068_ = v___x_5064_;
goto v_reusejp_5067_;
}
else
{
lean_object* v_reuseFailAlloc_5072_; 
v_reuseFailAlloc_5072_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5072_, 0, v_env_5052_);
lean_ctor_set(v_reuseFailAlloc_5072_, 1, v_nextMacroScope_5056_);
lean_ctor_set(v_reuseFailAlloc_5072_, 2, v_ngen_5057_);
lean_ctor_set(v_reuseFailAlloc_5072_, 3, v_auxDeclNGen_5058_);
lean_ctor_set(v_reuseFailAlloc_5072_, 4, v_traceState_5059_);
lean_ctor_set(v_reuseFailAlloc_5072_, 5, v___x_5066_);
lean_ctor_set(v_reuseFailAlloc_5072_, 6, v_messages_5060_);
lean_ctor_set(v_reuseFailAlloc_5072_, 7, v_infoState_5061_);
lean_ctor_set(v_reuseFailAlloc_5072_, 8, v_snapshotTasks_5062_);
v___x_5068_ = v_reuseFailAlloc_5072_;
goto v_reusejp_5067_;
}
v_reusejp_5067_:
{
lean_object* v___x_5069_; lean_object* v___x_5070_; lean_object* v___x_5071_; 
v___x_5069_ = lean_st_ref_put(v___y_5053_, v___x_5068_);
v___x_5070_ = lean_box(0);
v___x_5071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5071_, 0, v___x_5070_);
return v___x_5071_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___boxed(lean_object* v_env_5076_, lean_object* v___y_5077_, lean_object* v___y_5078_){
_start:
{
lean_object* v_res_5079_; 
v_res_5079_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_5076_, v___y_5077_);
lean_dec(v___y_5077_);
return v_res_5079_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0(lean_object* v_env_5080_, lean_object* v___y_5081_, lean_object* v___y_5082_){
_start:
{
lean_object* v___x_5084_; 
v___x_5084_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_5080_, v___y_5082_);
return v___x_5084_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___boxed(lean_object* v_env_5085_, lean_object* v___y_5086_, lean_object* v___y_5087_, lean_object* v___y_5088_){
_start:
{
lean_object* v_res_5089_; 
v_res_5089_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0(v_env_5085_, v___y_5086_, v___y_5087_);
lean_dec(v___y_5087_);
lean_dec_ref(v___y_5086_);
return v_res_5089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___lam__1(lean_object* v_env_5090_, lean_object* v___x_5091_, uint8_t v___x_5092_, lean_object* v_e_5093_, lean_object* v___y_5094_, lean_object* v___y_5095_){
_start:
{
if (lean_obj_tag(v_e_5093_) == 4)
{
lean_object* v_declName_5097_; lean_object* v_us_5098_; uint8_t v___x_5099_; uint8_t v___x_5100_; 
v_declName_5097_ = lean_ctor_get(v_e_5093_, 0);
v_us_5098_ = lean_ctor_get(v_e_5093_, 1);
v___x_5099_ = 1;
lean_inc(v_declName_5097_);
v___x_5100_ = l_Lean_Environment_contains(v_env_5090_, v_declName_5097_, v___x_5099_);
if (v___x_5100_ == 0)
{
lean_object* v___x_5101_; 
lean_inc(v_declName_5097_);
v___x_5101_ = l_Lean_Environment_find_x3f(v___x_5091_, v_declName_5097_, v___x_5092_);
if (lean_obj_tag(v___x_5101_) == 1)
{
lean_object* v_val_5102_; lean_object* v___x_5104_; uint8_t v_isShared_5105_; uint8_t v_isSharedCheck_5131_; 
v_val_5102_ = lean_ctor_get(v___x_5101_, 0);
v_isSharedCheck_5131_ = !lean_is_exclusive(v___x_5101_);
if (v_isSharedCheck_5131_ == 0)
{
v___x_5104_ = v___x_5101_;
v_isShared_5105_ = v_isSharedCheck_5131_;
goto v_resetjp_5103_;
}
else
{
lean_inc(v_val_5102_);
lean_dec(v___x_5101_);
v___x_5104_ = lean_box(0);
v_isShared_5105_ = v_isSharedCheck_5131_;
goto v_resetjp_5103_;
}
v_resetjp_5103_:
{
uint8_t v___x_5106_; 
v___x_5106_ = l_Lean_ConstantInfo_hasValue(v_val_5102_, v___x_5099_);
if (v___x_5106_ == 0)
{
lean_object* v___x_5108_; 
lean_dec(v_val_5102_);
if (v_isShared_5105_ == 0)
{
lean_ctor_set_tag(v___x_5104_, 0);
lean_ctor_set(v___x_5104_, 0, v_e_5093_);
v___x_5108_ = v___x_5104_;
goto v_reusejp_5107_;
}
else
{
lean_object* v_reuseFailAlloc_5110_; 
v_reuseFailAlloc_5110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5110_, 0, v_e_5093_);
v___x_5108_ = v_reuseFailAlloc_5110_;
goto v_reusejp_5107_;
}
v_reusejp_5107_:
{
lean_object* v___x_5109_; 
v___x_5109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5109_, 0, v___x_5108_);
return v___x_5109_;
}
}
else
{
lean_object* v___x_5111_; 
lean_inc(v_us_5098_);
lean_dec_ref_known(v_e_5093_, 2);
v___x_5111_ = l_Lean_Core_instantiateValueLevelParams(v_val_5102_, v_us_5098_, v___x_5099_, v___y_5094_, v___y_5095_);
lean_dec(v_val_5102_);
if (lean_obj_tag(v___x_5111_) == 0)
{
lean_object* v_a_5112_; lean_object* v___x_5114_; uint8_t v_isShared_5115_; uint8_t v_isSharedCheck_5122_; 
v_a_5112_ = lean_ctor_get(v___x_5111_, 0);
v_isSharedCheck_5122_ = !lean_is_exclusive(v___x_5111_);
if (v_isSharedCheck_5122_ == 0)
{
v___x_5114_ = v___x_5111_;
v_isShared_5115_ = v_isSharedCheck_5122_;
goto v_resetjp_5113_;
}
else
{
lean_inc(v_a_5112_);
lean_dec(v___x_5111_);
v___x_5114_ = lean_box(0);
v_isShared_5115_ = v_isSharedCheck_5122_;
goto v_resetjp_5113_;
}
v_resetjp_5113_:
{
lean_object* v___x_5117_; 
if (v_isShared_5105_ == 0)
{
lean_ctor_set(v___x_5104_, 0, v_a_5112_);
v___x_5117_ = v___x_5104_;
goto v_reusejp_5116_;
}
else
{
lean_object* v_reuseFailAlloc_5121_; 
v_reuseFailAlloc_5121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5121_, 0, v_a_5112_);
v___x_5117_ = v_reuseFailAlloc_5121_;
goto v_reusejp_5116_;
}
v_reusejp_5116_:
{
lean_object* v___x_5119_; 
if (v_isShared_5115_ == 0)
{
lean_ctor_set(v___x_5114_, 0, v___x_5117_);
v___x_5119_ = v___x_5114_;
goto v_reusejp_5118_;
}
else
{
lean_object* v_reuseFailAlloc_5120_; 
v_reuseFailAlloc_5120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5120_, 0, v___x_5117_);
v___x_5119_ = v_reuseFailAlloc_5120_;
goto v_reusejp_5118_;
}
v_reusejp_5118_:
{
return v___x_5119_;
}
}
}
}
else
{
lean_object* v_a_5123_; lean_object* v___x_5125_; uint8_t v_isShared_5126_; uint8_t v_isSharedCheck_5130_; 
lean_del_object(v___x_5104_);
v_a_5123_ = lean_ctor_get(v___x_5111_, 0);
v_isSharedCheck_5130_ = !lean_is_exclusive(v___x_5111_);
if (v_isSharedCheck_5130_ == 0)
{
v___x_5125_ = v___x_5111_;
v_isShared_5126_ = v_isSharedCheck_5130_;
goto v_resetjp_5124_;
}
else
{
lean_inc(v_a_5123_);
lean_dec(v___x_5111_);
v___x_5125_ = lean_box(0);
v_isShared_5126_ = v_isSharedCheck_5130_;
goto v_resetjp_5124_;
}
v_resetjp_5124_:
{
lean_object* v___x_5128_; 
if (v_isShared_5126_ == 0)
{
v___x_5128_ = v___x_5125_;
goto v_reusejp_5127_;
}
else
{
lean_object* v_reuseFailAlloc_5129_; 
v_reuseFailAlloc_5129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5129_, 0, v_a_5123_);
v___x_5128_ = v_reuseFailAlloc_5129_;
goto v_reusejp_5127_;
}
v_reusejp_5127_:
{
return v___x_5128_;
}
}
}
}
}
}
else
{
lean_object* v___x_5132_; lean_object* v___x_5133_; 
lean_dec(v___x_5101_);
v___x_5132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5132_, 0, v_e_5093_);
v___x_5133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5133_, 0, v___x_5132_);
return v___x_5133_;
}
}
else
{
lean_object* v___x_5134_; lean_object* v___x_5135_; 
lean_dec_ref(v___x_5091_);
v___x_5134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5134_, 0, v_e_5093_);
v___x_5135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5135_, 0, v___x_5134_);
return v___x_5135_;
}
}
else
{
lean_object* v___x_5136_; lean_object* v___x_5137_; 
lean_dec_ref(v_e_5093_);
lean_dec_ref(v___x_5091_);
lean_dec_ref(v_env_5090_);
v___x_5136_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_5137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5137_, 0, v___x_5136_);
return v___x_5137_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___lam__1___boxed(lean_object* v_env_5138_, lean_object* v___x_5139_, lean_object* v___x_5140_, lean_object* v_e_5141_, lean_object* v___y_5142_, lean_object* v___y_5143_, lean_object* v___y_5144_){
_start:
{
uint8_t v___x_2152__boxed_5145_; lean_object* v_res_5146_; 
v___x_2152__boxed_5145_ = lean_unbox(v___x_5140_);
v_res_5146_ = l_Lean_Meta_unfoldDeclsFrom___lam__1(v_env_5138_, v___x_5139_, v___x_2152__boxed_5145_, v_e_5141_, v___y_5142_, v___y_5143_);
lean_dec(v___y_5143_);
lean_dec_ref(v___y_5142_);
return v_res_5146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___lam__0(lean_object* v_biggerEnv_5147_, lean_object* v_e_5148_, lean_object* v___f_5149_, lean_object* v___y_5150_, lean_object* v___y_5151_){
_start:
{
lean_object* v___x_5153_; uint8_t v___x_5154_; lean_object* v___x_5155_; lean_object* v___x_5156_; lean_object* v_env_5157_; lean_object* v___x_5158_; lean_object* v___f_5159_; lean_object* v___x_5160_; 
v___x_5153_ = lean_st_ref_get(v___y_5151_);
v___x_5154_ = 0;
v___x_5155_ = l_Lean_Environment_setExporting(v_biggerEnv_5147_, v___x_5154_);
lean_inc_ref(v___x_5155_);
v___x_5156_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v___x_5155_, v___y_5151_);
lean_dec_ref(v___x_5156_);
v_env_5157_ = lean_ctor_get(v___x_5153_, 0);
lean_inc_ref(v_env_5157_);
lean_dec(v___x_5153_);
v___x_5158_ = lean_box(v___x_5154_);
v___f_5159_ = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDeclsFrom___lam__1___boxed), 7, 3);
lean_closure_set(v___f_5159_, 0, v_env_5157_);
lean_closure_set(v___f_5159_, 1, v___x_5155_);
lean_closure_set(v___f_5159_, 2, v___x_5158_);
v___x_5160_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_5148_, v___f_5159_, v___f_5149_, v___y_5150_, v___y_5151_);
return v___x_5160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___lam__0___boxed(lean_object* v_biggerEnv_5161_, lean_object* v_e_5162_, lean_object* v___f_5163_, lean_object* v___y_5164_, lean_object* v___y_5165_, lean_object* v___y_5166_){
_start:
{
lean_object* v_res_5167_; 
v_res_5167_ = l_Lean_Meta_unfoldDeclsFrom___lam__0(v_biggerEnv_5161_, v_e_5162_, v___f_5163_, v___y_5164_, v___y_5165_);
lean_dec(v___y_5165_);
lean_dec_ref(v___y_5164_);
return v_res_5167_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg(lean_object* v_env_5168_, lean_object* v_x_5169_, lean_object* v___y_5170_, lean_object* v___y_5171_){
_start:
{
lean_object* v___x_5173_; lean_object* v_env_5174_; lean_object* v_a_5176_; lean_object* v___x_5186_; lean_object* v___x_5187_; 
v___x_5173_ = lean_st_ref_get(v___y_5171_);
v_env_5174_ = lean_ctor_get(v___x_5173_, 0);
lean_inc_ref(v_env_5174_);
lean_dec(v___x_5173_);
v___x_5186_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_5168_, v___y_5171_);
lean_dec_ref(v___x_5186_);
lean_inc(v___y_5171_);
lean_inc_ref(v___y_5170_);
v___x_5187_ = lean_apply_3(v_x_5169_, v___y_5170_, v___y_5171_, lean_box(0));
if (lean_obj_tag(v___x_5187_) == 0)
{
lean_object* v_a_5188_; lean_object* v___x_5189_; lean_object* v___x_5191_; uint8_t v_isShared_5192_; uint8_t v_isSharedCheck_5196_; 
v_a_5188_ = lean_ctor_get(v___x_5187_, 0);
lean_inc(v_a_5188_);
lean_dec_ref_known(v___x_5187_, 1);
v___x_5189_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_5174_, v___y_5171_);
v_isSharedCheck_5196_ = !lean_is_exclusive(v___x_5189_);
if (v_isSharedCheck_5196_ == 0)
{
lean_object* v_unused_5197_; 
v_unused_5197_ = lean_ctor_get(v___x_5189_, 0);
lean_dec(v_unused_5197_);
v___x_5191_ = v___x_5189_;
v_isShared_5192_ = v_isSharedCheck_5196_;
goto v_resetjp_5190_;
}
else
{
lean_dec(v___x_5189_);
v___x_5191_ = lean_box(0);
v_isShared_5192_ = v_isSharedCheck_5196_;
goto v_resetjp_5190_;
}
v_resetjp_5190_:
{
lean_object* v___x_5194_; 
if (v_isShared_5192_ == 0)
{
lean_ctor_set(v___x_5191_, 0, v_a_5188_);
v___x_5194_ = v___x_5191_;
goto v_reusejp_5193_;
}
else
{
lean_object* v_reuseFailAlloc_5195_; 
v_reuseFailAlloc_5195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5195_, 0, v_a_5188_);
v___x_5194_ = v_reuseFailAlloc_5195_;
goto v_reusejp_5193_;
}
v_reusejp_5193_:
{
return v___x_5194_;
}
}
}
else
{
lean_object* v_a_5198_; 
v_a_5198_ = lean_ctor_get(v___x_5187_, 0);
lean_inc(v_a_5198_);
lean_dec_ref_known(v___x_5187_, 1);
v_a_5176_ = v_a_5198_;
goto v___jp_5175_;
}
v___jp_5175_:
{
lean_object* v___x_5177_; lean_object* v___x_5179_; uint8_t v_isShared_5180_; uint8_t v_isSharedCheck_5184_; 
v___x_5177_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_5174_, v___y_5171_);
v_isSharedCheck_5184_ = !lean_is_exclusive(v___x_5177_);
if (v_isSharedCheck_5184_ == 0)
{
lean_object* v_unused_5185_; 
v_unused_5185_ = lean_ctor_get(v___x_5177_, 0);
lean_dec(v_unused_5185_);
v___x_5179_ = v___x_5177_;
v_isShared_5180_ = v_isSharedCheck_5184_;
goto v_resetjp_5178_;
}
else
{
lean_dec(v___x_5177_);
v___x_5179_ = lean_box(0);
v_isShared_5180_ = v_isSharedCheck_5184_;
goto v_resetjp_5178_;
}
v_resetjp_5178_:
{
lean_object* v___x_5182_; 
if (v_isShared_5180_ == 0)
{
lean_ctor_set_tag(v___x_5179_, 1);
lean_ctor_set(v___x_5179_, 0, v_a_5176_);
v___x_5182_ = v___x_5179_;
goto v_reusejp_5181_;
}
else
{
lean_object* v_reuseFailAlloc_5183_; 
v_reuseFailAlloc_5183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5183_, 0, v_a_5176_);
v___x_5182_ = v_reuseFailAlloc_5183_;
goto v_reusejp_5181_;
}
v_reusejp_5181_:
{
return v___x_5182_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg___boxed(lean_object* v_env_5199_, lean_object* v_x_5200_, lean_object* v___y_5201_, lean_object* v___y_5202_, lean_object* v___y_5203_){
_start:
{
lean_object* v_res_5204_; 
v_res_5204_ = l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg(v_env_5199_, v_x_5200_, v___y_5201_, v___y_5202_);
lean_dec(v___y_5202_);
lean_dec_ref(v___y_5201_);
return v_res_5204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom(lean_object* v_biggerEnv_5205_, lean_object* v_e_5206_, lean_object* v_a_5207_, lean_object* v_a_5208_){
_start:
{
lean_object* v___x_5210_; lean_object* v_env_5211_; lean_object* v___f_5212_; lean_object* v___f_5213_; lean_object* v___x_5214_; lean_object* v___x_5215_; 
v___x_5210_ = lean_st_ref_get(v_a_5208_);
v_env_5211_ = lean_ctor_get(v___x_5210_, 0);
lean_inc_ref(v_env_5211_);
lean_dec(v___x_5210_);
v___f_5212_ = ((lean_object*)(l_Lean_Core_betaReduce___closed__1));
v___f_5213_ = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDeclsFrom___lam__0___boxed), 6, 3);
lean_closure_set(v___f_5213_, 0, v_biggerEnv_5205_);
lean_closure_set(v___f_5213_, 1, v_e_5206_);
lean_closure_set(v___f_5213_, 2, v___f_5212_);
v___x_5214_ = l_Lean_Environment_unlockAsync(v_env_5211_);
v___x_5215_ = l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg(v___x_5214_, v___f_5213_, v_a_5207_, v_a_5208_);
return v___x_5215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___boxed(lean_object* v_biggerEnv_5216_, lean_object* v_e_5217_, lean_object* v_a_5218_, lean_object* v_a_5219_, lean_object* v_a_5220_){
_start:
{
lean_object* v_res_5221_; 
v_res_5221_ = l_Lean_Meta_unfoldDeclsFrom(v_biggerEnv_5216_, v_e_5217_, v_a_5218_, v_a_5219_);
lean_dec(v_a_5219_);
lean_dec_ref(v_a_5218_);
return v_res_5221_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1(lean_object* v_00_u03b1_5222_, lean_object* v_env_5223_, lean_object* v_x_5224_, lean_object* v___y_5225_, lean_object* v___y_5226_){
_start:
{
lean_object* v___x_5228_; 
v___x_5228_ = l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg(v_env_5223_, v_x_5224_, v___y_5225_, v___y_5226_);
return v___x_5228_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___boxed(lean_object* v_00_u03b1_5229_, lean_object* v_env_5230_, lean_object* v_x_5231_, lean_object* v___y_5232_, lean_object* v___y_5233_, lean_object* v___y_5234_){
_start:
{
lean_object* v_res_5235_; 
v_res_5235_ = l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1(v_00_u03b1_5229_, v_env_5230_, v_x_5231_, v___y_5232_, v___y_5233_);
lean_dec(v___y_5233_);
lean_dec_ref(v___y_5232_);
return v_res_5235_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0(lean_object* v_af_5236_, lean_object* v_axs_5237_, lean_object* v_numSectionVars_5238_, lean_object* v_as_5239_, size_t v_i_5240_, size_t v_stop_5241_){
_start:
{
uint8_t v___x_5242_; 
v___x_5242_ = lean_usize_dec_eq(v_i_5240_, v_stop_5241_);
if (v___x_5242_ == 0)
{
uint8_t v___x_5243_; uint8_t v___y_5245_; lean_object* v___x_5249_; lean_object* v___x_5250_; uint8_t v___x_5251_; 
v___x_5243_ = 1;
v___x_5249_ = lean_array_uget_borrowed(v_as_5239_, v_i_5240_);
v___x_5250_ = l_Lean_Expr_constName_x21(v_af_5236_);
v___x_5251_ = lean_name_eq(v___x_5250_, v___x_5249_);
lean_dec(v___x_5250_);
if (v___x_5251_ == 0)
{
v___y_5245_ = v___x_5251_;
goto v___jp_5244_;
}
else
{
lean_object* v___x_5252_; uint8_t v___x_5253_; 
v___x_5252_ = lean_array_get_size(v_axs_5237_);
v___x_5253_ = lean_nat_dec_le(v___x_5252_, v_numSectionVars_5238_);
v___y_5245_ = v___x_5253_;
goto v___jp_5244_;
}
v___jp_5244_:
{
if (v___y_5245_ == 0)
{
size_t v___x_5246_; size_t v___x_5247_; 
v___x_5246_ = ((size_t)1ULL);
v___x_5247_ = lean_usize_add(v_i_5240_, v___x_5246_);
v_i_5240_ = v___x_5247_;
goto _start;
}
else
{
return v___x_5243_;
}
}
}
else
{
uint8_t v___x_5254_; 
v___x_5254_ = 0;
return v___x_5254_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0___boxed(lean_object* v_af_5255_, lean_object* v_axs_5256_, lean_object* v_numSectionVars_5257_, lean_object* v_as_5258_, lean_object* v_i_5259_, lean_object* v_stop_5260_){
_start:
{
size_t v_i_boxed_5261_; size_t v_stop_boxed_5262_; uint8_t v_res_5263_; lean_object* v_r_5264_; 
v_i_boxed_5261_ = lean_unbox_usize(v_i_5259_);
lean_dec(v_i_5259_);
v_stop_boxed_5262_ = lean_unbox_usize(v_stop_5260_);
lean_dec(v_stop_5260_);
v_res_5263_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0(v_af_5255_, v_axs_5256_, v_numSectionVars_5257_, v_as_5258_, v_i_boxed_5261_, v_stop_boxed_5262_);
lean_dec_ref(v_as_5258_);
lean_dec(v_numSectionVars_5257_);
lean_dec_ref(v_axs_5256_);
lean_dec_ref(v_af_5255_);
v_r_5264_ = lean_box(v_res_5263_);
return v_r_5264_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1_spec__1(lean_object* v_fnNames_5265_, lean_object* v_numSectionVars_5266_, lean_object* v_x_5267_, lean_object* v_x_5268_, lean_object* v_x_5269_){
_start:
{
if (lean_obj_tag(v_x_5267_) == 5)
{
lean_object* v_fn_5270_; lean_object* v_arg_5271_; lean_object* v___x_5272_; lean_object* v___x_5273_; lean_object* v___x_5274_; 
v_fn_5270_ = lean_ctor_get(v_x_5267_, 0);
lean_inc_ref(v_fn_5270_);
v_arg_5271_ = lean_ctor_get(v_x_5267_, 1);
lean_inc_ref(v_arg_5271_);
lean_dec_ref_known(v_x_5267_, 2);
v___x_5272_ = lean_array_set(v_x_5268_, v_x_5269_, v_arg_5271_);
v___x_5273_ = lean_unsigned_to_nat(1u);
v___x_5274_ = lean_nat_sub(v_x_5269_, v___x_5273_);
lean_dec(v_x_5269_);
v_x_5267_ = v_fn_5270_;
v_x_5268_ = v___x_5272_;
v_x_5269_ = v___x_5274_;
goto _start;
}
else
{
uint8_t v___x_5276_; 
lean_dec(v_x_5269_);
v___x_5276_ = l_Lean_Expr_isConst(v_x_5267_);
if (v___x_5276_ == 0)
{
lean_dec_ref(v_x_5268_);
lean_dec_ref(v_x_5267_);
return v___x_5276_;
}
else
{
lean_object* v___x_5277_; lean_object* v___x_5278_; uint8_t v___x_5279_; 
v___x_5277_ = lean_unsigned_to_nat(0u);
v___x_5278_ = lean_array_get_size(v_fnNames_5265_);
v___x_5279_ = lean_nat_dec_lt(v___x_5277_, v___x_5278_);
if (v___x_5279_ == 0)
{
lean_dec_ref(v_x_5268_);
lean_dec_ref(v_x_5267_);
return v___x_5279_;
}
else
{
if (v___x_5279_ == 0)
{
lean_dec_ref(v_x_5268_);
lean_dec_ref(v_x_5267_);
return v___x_5279_;
}
else
{
size_t v___x_5280_; size_t v___x_5281_; uint8_t v___x_5282_; 
v___x_5280_ = ((size_t)0ULL);
v___x_5281_ = lean_usize_of_nat(v___x_5278_);
v___x_5282_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0(v_x_5267_, v_x_5268_, v_numSectionVars_5266_, v_fnNames_5265_, v___x_5280_, v___x_5281_);
lean_dec_ref(v_x_5268_);
lean_dec_ref(v_x_5267_);
return v___x_5282_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1_spec__1___boxed(lean_object* v_fnNames_5283_, lean_object* v_numSectionVars_5284_, lean_object* v_x_5285_, lean_object* v_x_5286_, lean_object* v_x_5287_){
_start:
{
uint8_t v_res_5288_; lean_object* v_r_5289_; 
v_res_5288_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1_spec__1(v_fnNames_5283_, v_numSectionVars_5284_, v_x_5285_, v_x_5286_, v_x_5287_);
lean_dec(v_numSectionVars_5284_);
lean_dec_ref(v_fnNames_5283_);
v_r_5289_ = lean_box(v_res_5288_);
return v_r_5289_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1(lean_object* v_numSectionVars_5290_, lean_object* v_fnNames_5291_, lean_object* v_x_5292_, lean_object* v_x_5293_, lean_object* v_x_5294_){
_start:
{
if (lean_obj_tag(v_x_5292_) == 5)
{
lean_object* v_fn_5295_; lean_object* v_arg_5296_; lean_object* v___x_5297_; lean_object* v___x_5298_; lean_object* v___x_5299_; uint8_t v___x_5300_; 
v_fn_5295_ = lean_ctor_get(v_x_5292_, 0);
lean_inc_ref(v_fn_5295_);
v_arg_5296_ = lean_ctor_get(v_x_5292_, 1);
lean_inc_ref(v_arg_5296_);
lean_dec_ref_known(v_x_5292_, 2);
v___x_5297_ = lean_array_set(v_x_5293_, v_x_5294_, v_arg_5296_);
v___x_5298_ = lean_unsigned_to_nat(1u);
v___x_5299_ = lean_nat_sub(v_x_5294_, v___x_5298_);
v___x_5300_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1_spec__1(v_fnNames_5291_, v_numSectionVars_5290_, v_fn_5295_, v___x_5297_, v___x_5299_);
return v___x_5300_;
}
else
{
uint8_t v___x_5301_; 
v___x_5301_ = l_Lean_Expr_isConst(v_x_5292_);
if (v___x_5301_ == 0)
{
lean_dec_ref(v_x_5293_);
lean_dec_ref(v_x_5292_);
return v___x_5301_;
}
else
{
lean_object* v___x_5302_; lean_object* v___x_5303_; uint8_t v___x_5304_; 
v___x_5302_ = lean_unsigned_to_nat(0u);
v___x_5303_ = lean_array_get_size(v_fnNames_5291_);
v___x_5304_ = lean_nat_dec_lt(v___x_5302_, v___x_5303_);
if (v___x_5304_ == 0)
{
lean_dec_ref(v_x_5293_);
lean_dec_ref(v_x_5292_);
return v___x_5304_;
}
else
{
if (v___x_5304_ == 0)
{
lean_dec_ref(v_x_5293_);
lean_dec_ref(v_x_5292_);
return v___x_5304_;
}
else
{
size_t v___x_5305_; size_t v___x_5306_; uint8_t v___x_5307_; 
v___x_5305_ = ((size_t)0ULL);
v___x_5306_ = lean_usize_of_nat(v___x_5303_);
v___x_5307_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0(v_x_5292_, v_x_5293_, v_numSectionVars_5290_, v_fnNames_5291_, v___x_5305_, v___x_5306_);
lean_dec_ref(v_x_5293_);
lean_dec_ref(v_x_5292_);
return v___x_5307_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1___boxed(lean_object* v_numSectionVars_5308_, lean_object* v_fnNames_5309_, lean_object* v_x_5310_, lean_object* v_x_5311_, lean_object* v_x_5312_){
_start:
{
uint8_t v_res_5313_; lean_object* v_r_5314_; 
v_res_5313_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1(v_numSectionVars_5308_, v_fnNames_5309_, v_x_5310_, v_x_5311_, v_x_5312_);
lean_dec(v_x_5312_);
lean_dec_ref(v_fnNames_5309_);
lean_dec(v_numSectionVars_5308_);
v_r_5314_ = lean_box(v_res_5313_);
return v_r_5314_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg(lean_object* v_fnNames_5315_, lean_object* v_numSectionVars_5316_, lean_object* v_a_5317_){
_start:
{
lean_object* v_dummy_5318_; lean_object* v_nargs_5319_; lean_object* v___x_5320_; lean_object* v___x_5321_; lean_object* v___x_5322_; uint8_t v___x_5323_; 
v_dummy_5318_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_5319_ = l_Lean_Expr_getAppNumArgs(v_a_5317_);
lean_inc(v_nargs_5319_);
v___x_5320_ = lean_mk_array(v_nargs_5319_, v_dummy_5318_);
v___x_5321_ = lean_unsigned_to_nat(1u);
v___x_5322_ = lean_nat_sub(v_nargs_5319_, v___x_5321_);
lean_dec(v_nargs_5319_);
v___x_5323_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1(v_numSectionVars_5316_, v_fnNames_5315_, v_a_5317_, v___x_5320_, v___x_5322_);
lean_dec(v___x_5322_);
return v___x_5323_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg___boxed(lean_object* v_fnNames_5324_, lean_object* v_numSectionVars_5325_, lean_object* v_a_5326_){
_start:
{
uint8_t v_res_5327_; lean_object* v_r_5328_; 
v_res_5327_ = l___private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg(v_fnNames_5324_, v_numSectionVars_5325_, v_a_5326_);
lean_dec(v_numSectionVars_5325_);
lean_dec_ref(v_fnNames_5324_);
v_r_5328_ = lean_box(v_res_5327_);
return v_r_5328_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__0(lean_object* v_fnNames_5329_, lean_object* v_numSectionVars_5330_, lean_object* v_as_5331_, size_t v_i_5332_, size_t v_stop_5333_){
_start:
{
uint8_t v___x_5334_; 
v___x_5334_ = lean_usize_dec_eq(v_i_5332_, v_stop_5333_);
if (v___x_5334_ == 0)
{
lean_object* v___x_5335_; uint8_t v___x_5336_; 
v___x_5335_ = lean_array_uget_borrowed(v_as_5331_, v_i_5332_);
lean_inc(v___x_5335_);
v___x_5336_ = l___private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg(v_fnNames_5329_, v_numSectionVars_5330_, v___x_5335_);
if (v___x_5336_ == 0)
{
size_t v___x_5337_; size_t v___x_5338_; 
v___x_5337_ = ((size_t)1ULL);
v___x_5338_ = lean_usize_add(v_i_5332_, v___x_5337_);
v_i_5332_ = v___x_5338_;
goto _start;
}
else
{
return v___x_5336_;
}
}
else
{
uint8_t v___x_5340_; 
v___x_5340_ = 0;
return v___x_5340_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__0___boxed(lean_object* v_fnNames_5341_, lean_object* v_numSectionVars_5342_, lean_object* v_as_5343_, lean_object* v_i_5344_, lean_object* v_stop_5345_){
_start:
{
size_t v_i_boxed_5346_; size_t v_stop_boxed_5347_; uint8_t v_res_5348_; lean_object* v_r_5349_; 
v_i_boxed_5346_ = lean_unbox_usize(v_i_5344_);
lean_dec(v_i_5344_);
v_stop_boxed_5347_ = lean_unbox_usize(v_stop_5345_);
lean_dec(v_stop_5345_);
v_res_5348_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__0(v_fnNames_5341_, v_numSectionVars_5342_, v_as_5343_, v_i_boxed_5346_, v_stop_boxed_5347_);
lean_dec_ref(v_as_5343_);
lean_dec(v_numSectionVars_5342_);
lean_dec_ref(v_fnNames_5341_);
v_r_5349_ = lean_box(v_res_5348_);
return v_r_5349_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__1(lean_object* v_fnNames_5350_, lean_object* v_numSectionVars_5351_, lean_object* v___x_5352_, lean_object* v_x_5353_, lean_object* v_x_5354_, lean_object* v___y_5355_, lean_object* v___y_5356_){
_start:
{
if (lean_obj_tag(v_x_5353_) == 5)
{
lean_object* v_fn_5361_; lean_object* v_arg_5362_; lean_object* v___x_5363_; 
v_fn_5361_ = lean_ctor_get(v_x_5353_, 0);
lean_inc_ref(v_fn_5361_);
v_arg_5362_ = lean_ctor_get(v_x_5353_, 1);
lean_inc_ref(v_arg_5362_);
lean_dec_ref_known(v_x_5353_, 2);
v___x_5363_ = lean_array_push(v_x_5354_, v_arg_5362_);
v_x_5353_ = v_fn_5361_;
v_x_5354_ = v___x_5363_;
goto _start;
}
else
{
uint8_t v___x_5365_; 
v___x_5365_ = l_Lean_Expr_isConst(v_x_5353_);
if (v___x_5365_ == 0)
{
lean_dec_ref(v_x_5354_);
lean_dec_ref(v_x_5353_);
lean_dec_ref(v___x_5352_);
goto v___jp_5358_;
}
else
{
lean_object* v___x_5366_; lean_object* v___x_5367_; uint8_t v___x_5368_; 
v___x_5366_ = lean_unsigned_to_nat(0u);
v___x_5367_ = lean_array_get_size(v_x_5354_);
v___x_5368_ = lean_nat_dec_lt(v___x_5366_, v___x_5367_);
if (v___x_5368_ == 0)
{
lean_dec_ref(v_x_5354_);
lean_dec_ref(v_x_5353_);
lean_dec_ref(v___x_5352_);
goto v___jp_5358_;
}
else
{
if (v___x_5368_ == 0)
{
lean_dec_ref(v_x_5354_);
lean_dec_ref(v_x_5353_);
lean_dec_ref(v___x_5352_);
goto v___jp_5358_;
}
else
{
size_t v___x_5369_; size_t v___x_5370_; uint8_t v___x_5371_; 
v___x_5369_ = ((size_t)0ULL);
v___x_5370_ = lean_usize_of_nat(v___x_5367_);
v___x_5371_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__0(v_fnNames_5350_, v_numSectionVars_5351_, v_x_5354_, v___x_5369_, v___x_5370_);
if (v___x_5371_ == 0)
{
lean_dec_ref(v_x_5354_);
lean_dec_ref(v_x_5353_);
lean_dec_ref(v___x_5352_);
goto v___jp_5358_;
}
else
{
lean_object* v___x_5372_; uint8_t v___x_5373_; lean_object* v___x_5374_; 
v___x_5372_ = l_Lean_Expr_constName_x21(v_x_5353_);
v___x_5373_ = 0;
v___x_5374_ = l_Lean_Environment_find_x3f(v___x_5352_, v___x_5372_, v___x_5373_);
if (lean_obj_tag(v___x_5374_) == 1)
{
lean_object* v_val_5375_; 
v_val_5375_ = lean_ctor_get(v___x_5374_, 0);
lean_inc(v_val_5375_);
lean_dec_ref_known(v___x_5374_, 1);
if (lean_obj_tag(v_val_5375_) == 2)
{
lean_object* v___x_5376_; lean_object* v___x_5377_; lean_object* v___x_5379_; uint8_t v_isShared_5380_; uint8_t v_isSharedCheck_5401_; 
v___x_5376_ = l_Lean_Expr_constLevels_x21(v_x_5353_);
lean_dec_ref(v_x_5353_);
v___x_5377_ = l_Lean_Core_instantiateValueLevelParams(v_val_5375_, v___x_5376_, v___x_5365_, v___y_5355_, v___y_5356_);
v_isSharedCheck_5401_ = !lean_is_exclusive(v_val_5375_);
if (v_isSharedCheck_5401_ == 0)
{
lean_object* v_unused_5402_; 
v_unused_5402_ = lean_ctor_get(v_val_5375_, 0);
lean_dec(v_unused_5402_);
v___x_5379_ = v_val_5375_;
v_isShared_5380_ = v_isSharedCheck_5401_;
goto v_resetjp_5378_;
}
else
{
lean_dec(v_val_5375_);
v___x_5379_ = lean_box(0);
v_isShared_5380_ = v_isSharedCheck_5401_;
goto v_resetjp_5378_;
}
v_resetjp_5378_:
{
if (lean_obj_tag(v___x_5377_) == 0)
{
lean_object* v_a_5381_; lean_object* v___x_5383_; uint8_t v_isShared_5384_; uint8_t v_isSharedCheck_5392_; 
v_a_5381_ = lean_ctor_get(v___x_5377_, 0);
v_isSharedCheck_5392_ = !lean_is_exclusive(v___x_5377_);
if (v_isSharedCheck_5392_ == 0)
{
v___x_5383_ = v___x_5377_;
v_isShared_5384_ = v_isSharedCheck_5392_;
goto v_resetjp_5382_;
}
else
{
lean_inc(v_a_5381_);
lean_dec(v___x_5377_);
v___x_5383_ = lean_box(0);
v_isShared_5384_ = v_isSharedCheck_5392_;
goto v_resetjp_5382_;
}
v_resetjp_5382_:
{
lean_object* v___x_5385_; lean_object* v___x_5387_; 
v___x_5385_ = l_Lean_Expr_betaRev(v_a_5381_, v_x_5354_, v___x_5373_, v___x_5373_);
lean_dec_ref(v_x_5354_);
if (v_isShared_5380_ == 0)
{
lean_ctor_set_tag(v___x_5379_, 1);
lean_ctor_set(v___x_5379_, 0, v___x_5385_);
v___x_5387_ = v___x_5379_;
goto v_reusejp_5386_;
}
else
{
lean_object* v_reuseFailAlloc_5391_; 
v_reuseFailAlloc_5391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5391_, 0, v___x_5385_);
v___x_5387_ = v_reuseFailAlloc_5391_;
goto v_reusejp_5386_;
}
v_reusejp_5386_:
{
lean_object* v___x_5389_; 
if (v_isShared_5384_ == 0)
{
lean_ctor_set(v___x_5383_, 0, v___x_5387_);
v___x_5389_ = v___x_5383_;
goto v_reusejp_5388_;
}
else
{
lean_object* v_reuseFailAlloc_5390_; 
v_reuseFailAlloc_5390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5390_, 0, v___x_5387_);
v___x_5389_ = v_reuseFailAlloc_5390_;
goto v_reusejp_5388_;
}
v_reusejp_5388_:
{
return v___x_5389_;
}
}
}
}
else
{
lean_object* v_a_5393_; lean_object* v___x_5395_; uint8_t v_isShared_5396_; uint8_t v_isSharedCheck_5400_; 
lean_del_object(v___x_5379_);
lean_dec_ref(v_x_5354_);
v_a_5393_ = lean_ctor_get(v___x_5377_, 0);
v_isSharedCheck_5400_ = !lean_is_exclusive(v___x_5377_);
if (v_isSharedCheck_5400_ == 0)
{
v___x_5395_ = v___x_5377_;
v_isShared_5396_ = v_isSharedCheck_5400_;
goto v_resetjp_5394_;
}
else
{
lean_inc(v_a_5393_);
lean_dec(v___x_5377_);
v___x_5395_ = lean_box(0);
v_isShared_5396_ = v_isSharedCheck_5400_;
goto v_resetjp_5394_;
}
v_resetjp_5394_:
{
lean_object* v___x_5398_; 
if (v_isShared_5396_ == 0)
{
v___x_5398_ = v___x_5395_;
goto v_reusejp_5397_;
}
else
{
lean_object* v_reuseFailAlloc_5399_; 
v_reuseFailAlloc_5399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5399_, 0, v_a_5393_);
v___x_5398_ = v_reuseFailAlloc_5399_;
goto v_reusejp_5397_;
}
v_reusejp_5397_:
{
return v___x_5398_;
}
}
}
}
}
else
{
lean_dec(v_val_5375_);
lean_dec_ref(v_x_5354_);
lean_dec_ref(v_x_5353_);
goto v___jp_5358_;
}
}
else
{
lean_dec(v___x_5374_);
lean_dec_ref(v_x_5354_);
lean_dec_ref(v_x_5353_);
goto v___jp_5358_;
}
}
}
}
}
}
v___jp_5358_:
{
lean_object* v___x_5359_; lean_object* v___x_5360_; 
v___x_5359_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_5360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5360_, 0, v___x_5359_);
return v___x_5360_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__1___boxed(lean_object* v_fnNames_5403_, lean_object* v_numSectionVars_5404_, lean_object* v___x_5405_, lean_object* v_x_5406_, lean_object* v_x_5407_, lean_object* v___y_5408_, lean_object* v___y_5409_, lean_object* v___y_5410_){
_start:
{
lean_object* v_res_5411_; 
v_res_5411_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__1(v_fnNames_5403_, v_numSectionVars_5404_, v___x_5405_, v_x_5406_, v_x_5407_, v___y_5408_, v___y_5409_);
lean_dec(v___y_5409_);
lean_dec_ref(v___y_5408_);
lean_dec(v_numSectionVars_5404_);
lean_dec_ref(v_fnNames_5403_);
return v_res_5411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___lam__1(lean_object* v_fnNames_5412_, lean_object* v_numSectionVars_5413_, lean_object* v_env_5414_, lean_object* v_e_5415_, lean_object* v___y_5416_, lean_object* v___y_5417_){
_start:
{
lean_object* v___x_5419_; lean_object* v___x_5420_; lean_object* v___x_5421_; 
v___x_5419_ = l_Lean_Expr_getAppNumArgs(v_e_5415_);
v___x_5420_ = lean_mk_empty_array_with_capacity(v___x_5419_);
lean_dec(v___x_5419_);
v___x_5421_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__1(v_fnNames_5412_, v_numSectionVars_5413_, v_env_5414_, v_e_5415_, v___x_5420_, v___y_5416_, v___y_5417_);
return v___x_5421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___lam__1___boxed(lean_object* v_fnNames_5422_, lean_object* v_numSectionVars_5423_, lean_object* v_env_5424_, lean_object* v_e_5425_, lean_object* v___y_5426_, lean_object* v___y_5427_, lean_object* v___y_5428_){
_start:
{
lean_object* v_res_5429_; 
v_res_5429_ = l_Lean_Meta_unfoldIfArgIsAppOf___lam__1(v_fnNames_5422_, v_numSectionVars_5423_, v_env_5424_, v_e_5425_, v___y_5426_, v___y_5427_);
lean_dec(v___y_5427_);
lean_dec_ref(v___y_5426_);
lean_dec(v_numSectionVars_5423_);
lean_dec_ref(v_fnNames_5422_);
return v_res_5429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___lam__0(lean_object* v_fnNames_5430_, lean_object* v_numSectionVars_5431_, lean_object* v_e_5432_, lean_object* v___f_5433_, lean_object* v___y_5434_, lean_object* v___y_5435_){
_start:
{
lean_object* v___x_5437_; lean_object* v_env_5438_; lean_object* v___f_5439_; lean_object* v___x_5440_; 
v___x_5437_ = lean_st_ref_get(v___y_5435_);
v_env_5438_ = lean_ctor_get(v___x_5437_, 0);
lean_inc_ref(v_env_5438_);
lean_dec(v___x_5437_);
v___f_5439_ = lean_alloc_closure((void*)(l_Lean_Meta_unfoldIfArgIsAppOf___lam__1___boxed), 7, 3);
lean_closure_set(v___f_5439_, 0, v_fnNames_5430_);
lean_closure_set(v___f_5439_, 1, v_numSectionVars_5431_);
lean_closure_set(v___f_5439_, 2, v_env_5438_);
v___x_5440_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_5432_, v___f_5439_, v___f_5433_, v___y_5434_, v___y_5435_);
return v___x_5440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___lam__0___boxed(lean_object* v_fnNames_5441_, lean_object* v_numSectionVars_5442_, lean_object* v_e_5443_, lean_object* v___f_5444_, lean_object* v___y_5445_, lean_object* v___y_5446_, lean_object* v___y_5447_){
_start:
{
lean_object* v_res_5448_; 
v_res_5448_ = l_Lean_Meta_unfoldIfArgIsAppOf___lam__0(v_fnNames_5441_, v_numSectionVars_5442_, v_e_5443_, v___f_5444_, v___y_5445_, v___y_5446_);
lean_dec(v___y_5446_);
lean_dec_ref(v___y_5445_);
return v_res_5448_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0(lean_object* v___y_5449_, uint8_t v_isExporting_5450_, lean_object* v___x_5451_, lean_object* v_a_x3f_5452_){
_start:
{
lean_object* v___x_5454_; lean_object* v_env_5455_; lean_object* v_nextMacroScope_5456_; lean_object* v_ngen_5457_; lean_object* v_auxDeclNGen_5458_; lean_object* v_traceState_5459_; lean_object* v_messages_5460_; lean_object* v_infoState_5461_; lean_object* v_snapshotTasks_5462_; lean_object* v___x_5464_; uint8_t v_isShared_5465_; uint8_t v_isSharedCheck_5473_; 
v___x_5454_ = lean_st_ref_take(v___y_5449_);
v_env_5455_ = lean_ctor_get(v___x_5454_, 0);
v_nextMacroScope_5456_ = lean_ctor_get(v___x_5454_, 1);
v_ngen_5457_ = lean_ctor_get(v___x_5454_, 2);
v_auxDeclNGen_5458_ = lean_ctor_get(v___x_5454_, 3);
v_traceState_5459_ = lean_ctor_get(v___x_5454_, 4);
v_messages_5460_ = lean_ctor_get(v___x_5454_, 6);
v_infoState_5461_ = lean_ctor_get(v___x_5454_, 7);
v_snapshotTasks_5462_ = lean_ctor_get(v___x_5454_, 8);
v_isSharedCheck_5473_ = !lean_is_exclusive(v___x_5454_);
if (v_isSharedCheck_5473_ == 0)
{
lean_object* v_unused_5474_; 
v_unused_5474_ = lean_ctor_get(v___x_5454_, 5);
lean_dec(v_unused_5474_);
v___x_5464_ = v___x_5454_;
v_isShared_5465_ = v_isSharedCheck_5473_;
goto v_resetjp_5463_;
}
else
{
lean_inc(v_snapshotTasks_5462_);
lean_inc(v_infoState_5461_);
lean_inc(v_messages_5460_);
lean_inc(v_traceState_5459_);
lean_inc(v_auxDeclNGen_5458_);
lean_inc(v_ngen_5457_);
lean_inc(v_nextMacroScope_5456_);
lean_inc(v_env_5455_);
lean_dec(v___x_5454_);
v___x_5464_ = lean_box(0);
v_isShared_5465_ = v_isSharedCheck_5473_;
goto v_resetjp_5463_;
}
v_resetjp_5463_:
{
lean_object* v___x_5466_; lean_object* v___x_5468_; 
v___x_5466_ = l_Lean_Environment_setExporting(v_env_5455_, v_isExporting_5450_);
if (v_isShared_5465_ == 0)
{
lean_ctor_set(v___x_5464_, 5, v___x_5451_);
lean_ctor_set(v___x_5464_, 0, v___x_5466_);
v___x_5468_ = v___x_5464_;
goto v_reusejp_5467_;
}
else
{
lean_object* v_reuseFailAlloc_5472_; 
v_reuseFailAlloc_5472_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5472_, 0, v___x_5466_);
lean_ctor_set(v_reuseFailAlloc_5472_, 1, v_nextMacroScope_5456_);
lean_ctor_set(v_reuseFailAlloc_5472_, 2, v_ngen_5457_);
lean_ctor_set(v_reuseFailAlloc_5472_, 3, v_auxDeclNGen_5458_);
lean_ctor_set(v_reuseFailAlloc_5472_, 4, v_traceState_5459_);
lean_ctor_set(v_reuseFailAlloc_5472_, 5, v___x_5451_);
lean_ctor_set(v_reuseFailAlloc_5472_, 6, v_messages_5460_);
lean_ctor_set(v_reuseFailAlloc_5472_, 7, v_infoState_5461_);
lean_ctor_set(v_reuseFailAlloc_5472_, 8, v_snapshotTasks_5462_);
v___x_5468_ = v_reuseFailAlloc_5472_;
goto v_reusejp_5467_;
}
v_reusejp_5467_:
{
lean_object* v___x_5469_; lean_object* v___x_5470_; lean_object* v___x_5471_; 
v___x_5469_ = lean_st_ref_put(v___y_5449_, v___x_5468_);
v___x_5470_ = lean_box(0);
v___x_5471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5471_, 0, v___x_5470_);
return v___x_5471_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0___boxed(lean_object* v___y_5475_, lean_object* v_isExporting_5476_, lean_object* v___x_5477_, lean_object* v_a_x3f_5478_, lean_object* v___y_5479_){
_start:
{
uint8_t v_isExporting_boxed_5480_; lean_object* v_res_5481_; 
v_isExporting_boxed_5480_ = lean_unbox(v_isExporting_5476_);
v_res_5481_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0(v___y_5475_, v_isExporting_boxed_5480_, v___x_5477_, v_a_x3f_5478_);
lean_dec(v_a_x3f_5478_);
lean_dec(v___y_5475_);
return v_res_5481_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg(lean_object* v_x_5482_, uint8_t v_isExporting_5483_, lean_object* v___y_5484_, lean_object* v___y_5485_){
_start:
{
lean_object* v___x_5487_; lean_object* v_env_5488_; uint8_t v_isExporting_5489_; lean_object* v___x_5540_; uint8_t v_isModule_5541_; 
v___x_5487_ = lean_st_ref_get(v___y_5485_);
v_env_5488_ = lean_ctor_get(v___x_5487_, 0);
lean_inc_ref(v_env_5488_);
lean_dec(v___x_5487_);
v_isExporting_5489_ = lean_ctor_get_uint8(v_env_5488_, sizeof(void*)*8);
v___x_5540_ = l_Lean_Environment_header(v_env_5488_);
lean_dec_ref(v_env_5488_);
v_isModule_5541_ = lean_ctor_get_uint8(v___x_5540_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_5540_);
if (v_isModule_5541_ == 0)
{
lean_object* v___x_5542_; 
lean_inc(v___y_5485_);
lean_inc_ref(v___y_5484_);
v___x_5542_ = lean_apply_3(v_x_5482_, v___y_5484_, v___y_5485_, lean_box(0));
return v___x_5542_;
}
else
{
if (v_isExporting_5489_ == 0)
{
if (v_isExporting_5483_ == 0)
{
lean_object* v___x_5543_; 
lean_inc(v___y_5485_);
lean_inc_ref(v___y_5484_);
v___x_5543_ = lean_apply_3(v_x_5482_, v___y_5484_, v___y_5485_, lean_box(0));
return v___x_5543_;
}
else
{
goto v___jp_5490_;
}
}
else
{
if (v_isExporting_5483_ == 0)
{
goto v___jp_5490_;
}
else
{
lean_object* v___x_5544_; 
lean_inc(v___y_5485_);
lean_inc_ref(v___y_5484_);
v___x_5544_ = lean_apply_3(v_x_5482_, v___y_5484_, v___y_5485_, lean_box(0));
return v___x_5544_;
}
}
}
v___jp_5490_:
{
lean_object* v___x_5491_; lean_object* v_env_5492_; lean_object* v_nextMacroScope_5493_; lean_object* v_ngen_5494_; lean_object* v_auxDeclNGen_5495_; lean_object* v_traceState_5496_; lean_object* v_messages_5497_; lean_object* v_infoState_5498_; lean_object* v_snapshotTasks_5499_; lean_object* v___x_5501_; uint8_t v_isShared_5502_; uint8_t v_isSharedCheck_5538_; 
v___x_5491_ = lean_st_ref_take(v___y_5485_);
v_env_5492_ = lean_ctor_get(v___x_5491_, 0);
v_nextMacroScope_5493_ = lean_ctor_get(v___x_5491_, 1);
v_ngen_5494_ = lean_ctor_get(v___x_5491_, 2);
v_auxDeclNGen_5495_ = lean_ctor_get(v___x_5491_, 3);
v_traceState_5496_ = lean_ctor_get(v___x_5491_, 4);
v_messages_5497_ = lean_ctor_get(v___x_5491_, 6);
v_infoState_5498_ = lean_ctor_get(v___x_5491_, 7);
v_snapshotTasks_5499_ = lean_ctor_get(v___x_5491_, 8);
v_isSharedCheck_5538_ = !lean_is_exclusive(v___x_5491_);
if (v_isSharedCheck_5538_ == 0)
{
lean_object* v_unused_5539_; 
v_unused_5539_ = lean_ctor_get(v___x_5491_, 5);
lean_dec(v_unused_5539_);
v___x_5501_ = v___x_5491_;
v_isShared_5502_ = v_isSharedCheck_5538_;
goto v_resetjp_5500_;
}
else
{
lean_inc(v_snapshotTasks_5499_);
lean_inc(v_infoState_5498_);
lean_inc(v_messages_5497_);
lean_inc(v_traceState_5496_);
lean_inc(v_auxDeclNGen_5495_);
lean_inc(v_ngen_5494_);
lean_inc(v_nextMacroScope_5493_);
lean_inc(v_env_5492_);
lean_dec(v___x_5491_);
v___x_5501_ = lean_box(0);
v_isShared_5502_ = v_isSharedCheck_5538_;
goto v_resetjp_5500_;
}
v_resetjp_5500_:
{
lean_object* v___x_5503_; lean_object* v___x_5504_; lean_object* v___x_5506_; 
v___x_5503_ = l_Lean_Environment_setExporting(v_env_5492_, v_isExporting_5483_);
v___x_5504_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2, &l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2);
if (v_isShared_5502_ == 0)
{
lean_ctor_set(v___x_5501_, 5, v___x_5504_);
lean_ctor_set(v___x_5501_, 0, v___x_5503_);
v___x_5506_ = v___x_5501_;
goto v_reusejp_5505_;
}
else
{
lean_object* v_reuseFailAlloc_5537_; 
v_reuseFailAlloc_5537_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5537_, 0, v___x_5503_);
lean_ctor_set(v_reuseFailAlloc_5537_, 1, v_nextMacroScope_5493_);
lean_ctor_set(v_reuseFailAlloc_5537_, 2, v_ngen_5494_);
lean_ctor_set(v_reuseFailAlloc_5537_, 3, v_auxDeclNGen_5495_);
lean_ctor_set(v_reuseFailAlloc_5537_, 4, v_traceState_5496_);
lean_ctor_set(v_reuseFailAlloc_5537_, 5, v___x_5504_);
lean_ctor_set(v_reuseFailAlloc_5537_, 6, v_messages_5497_);
lean_ctor_set(v_reuseFailAlloc_5537_, 7, v_infoState_5498_);
lean_ctor_set(v_reuseFailAlloc_5537_, 8, v_snapshotTasks_5499_);
v___x_5506_ = v_reuseFailAlloc_5537_;
goto v_reusejp_5505_;
}
v_reusejp_5505_:
{
lean_object* v___x_5507_; lean_object* v_r_5508_; 
v___x_5507_ = lean_st_ref_put(v___y_5485_, v___x_5506_);
lean_inc(v___y_5485_);
lean_inc_ref(v___y_5484_);
v_r_5508_ = lean_apply_3(v_x_5482_, v___y_5484_, v___y_5485_, lean_box(0));
if (lean_obj_tag(v_r_5508_) == 0)
{
lean_object* v_a_5509_; lean_object* v___x_5511_; uint8_t v_isShared_5512_; uint8_t v_isSharedCheck_5525_; 
v_a_5509_ = lean_ctor_get(v_r_5508_, 0);
v_isSharedCheck_5525_ = !lean_is_exclusive(v_r_5508_);
if (v_isSharedCheck_5525_ == 0)
{
v___x_5511_ = v_r_5508_;
v_isShared_5512_ = v_isSharedCheck_5525_;
goto v_resetjp_5510_;
}
else
{
lean_inc(v_a_5509_);
lean_dec(v_r_5508_);
v___x_5511_ = lean_box(0);
v_isShared_5512_ = v_isSharedCheck_5525_;
goto v_resetjp_5510_;
}
v_resetjp_5510_:
{
lean_object* v___x_5514_; 
lean_inc(v_a_5509_);
if (v_isShared_5512_ == 0)
{
lean_ctor_set_tag(v___x_5511_, 1);
v___x_5514_ = v___x_5511_;
goto v_reusejp_5513_;
}
else
{
lean_object* v_reuseFailAlloc_5524_; 
v_reuseFailAlloc_5524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5524_, 0, v_a_5509_);
v___x_5514_ = v_reuseFailAlloc_5524_;
goto v_reusejp_5513_;
}
v_reusejp_5513_:
{
lean_object* v___x_5515_; lean_object* v___x_5517_; uint8_t v_isShared_5518_; uint8_t v_isSharedCheck_5522_; 
v___x_5515_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0(v___y_5485_, v_isExporting_5489_, v___x_5504_, v___x_5514_);
lean_dec_ref(v___x_5514_);
v_isSharedCheck_5522_ = !lean_is_exclusive(v___x_5515_);
if (v_isSharedCheck_5522_ == 0)
{
lean_object* v_unused_5523_; 
v_unused_5523_ = lean_ctor_get(v___x_5515_, 0);
lean_dec(v_unused_5523_);
v___x_5517_ = v___x_5515_;
v_isShared_5518_ = v_isSharedCheck_5522_;
goto v_resetjp_5516_;
}
else
{
lean_dec(v___x_5515_);
v___x_5517_ = lean_box(0);
v_isShared_5518_ = v_isSharedCheck_5522_;
goto v_resetjp_5516_;
}
v_resetjp_5516_:
{
lean_object* v___x_5520_; 
if (v_isShared_5518_ == 0)
{
lean_ctor_set(v___x_5517_, 0, v_a_5509_);
v___x_5520_ = v___x_5517_;
goto v_reusejp_5519_;
}
else
{
lean_object* v_reuseFailAlloc_5521_; 
v_reuseFailAlloc_5521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5521_, 0, v_a_5509_);
v___x_5520_ = v_reuseFailAlloc_5521_;
goto v_reusejp_5519_;
}
v_reusejp_5519_:
{
return v___x_5520_;
}
}
}
}
}
else
{
lean_object* v_a_5526_; lean_object* v___x_5527_; lean_object* v___x_5528_; lean_object* v___x_5530_; uint8_t v_isShared_5531_; uint8_t v_isSharedCheck_5535_; 
v_a_5526_ = lean_ctor_get(v_r_5508_, 0);
lean_inc(v_a_5526_);
lean_dec_ref_known(v_r_5508_, 1);
v___x_5527_ = lean_box(0);
v___x_5528_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0(v___y_5485_, v_isExporting_5489_, v___x_5504_, v___x_5527_);
v_isSharedCheck_5535_ = !lean_is_exclusive(v___x_5528_);
if (v_isSharedCheck_5535_ == 0)
{
lean_object* v_unused_5536_; 
v_unused_5536_ = lean_ctor_get(v___x_5528_, 0);
lean_dec(v_unused_5536_);
v___x_5530_ = v___x_5528_;
v_isShared_5531_ = v_isSharedCheck_5535_;
goto v_resetjp_5529_;
}
else
{
lean_dec(v___x_5528_);
v___x_5530_ = lean_box(0);
v_isShared_5531_ = v_isSharedCheck_5535_;
goto v_resetjp_5529_;
}
v_resetjp_5529_:
{
lean_object* v___x_5533_; 
if (v_isShared_5531_ == 0)
{
lean_ctor_set_tag(v___x_5530_, 1);
lean_ctor_set(v___x_5530_, 0, v_a_5526_);
v___x_5533_ = v___x_5530_;
goto v_reusejp_5532_;
}
else
{
lean_object* v_reuseFailAlloc_5534_; 
v_reuseFailAlloc_5534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5534_, 0, v_a_5526_);
v___x_5533_ = v_reuseFailAlloc_5534_;
goto v_reusejp_5532_;
}
v_reusejp_5532_:
{
return v___x_5533_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___boxed(lean_object* v_x_5545_, lean_object* v_isExporting_5546_, lean_object* v___y_5547_, lean_object* v___y_5548_, lean_object* v___y_5549_){
_start:
{
uint8_t v_isExporting_boxed_5550_; lean_object* v_res_5551_; 
v_isExporting_boxed_5550_ = lean_unbox(v_isExporting_5546_);
v_res_5551_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg(v_x_5545_, v_isExporting_boxed_5550_, v___y_5547_, v___y_5548_);
lean_dec(v___y_5548_);
lean_dec_ref(v___y_5547_);
return v_res_5551_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg(lean_object* v_x_5552_, uint8_t v_when_5553_, lean_object* v___y_5554_, lean_object* v___y_5555_){
_start:
{
if (v_when_5553_ == 0)
{
lean_object* v___x_5557_; 
lean_inc(v___y_5555_);
lean_inc_ref(v___y_5554_);
v___x_5557_ = lean_apply_3(v_x_5552_, v___y_5554_, v___y_5555_, lean_box(0));
return v___x_5557_;
}
else
{
uint8_t v___x_5558_; lean_object* v___x_5559_; 
v___x_5558_ = 0;
v___x_5559_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg(v_x_5552_, v___x_5558_, v___y_5554_, v___y_5555_);
return v___x_5559_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg___boxed(lean_object* v_x_5560_, lean_object* v_when_5561_, lean_object* v___y_5562_, lean_object* v___y_5563_, lean_object* v___y_5564_){
_start:
{
uint8_t v_when_boxed_5565_; lean_object* v_res_5566_; 
v_when_boxed_5565_ = lean_unbox(v_when_5561_);
v_res_5566_ = l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg(v_x_5560_, v_when_boxed_5565_, v___y_5562_, v___y_5563_);
lean_dec(v___y_5563_);
lean_dec_ref(v___y_5562_);
return v_res_5566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf(lean_object* v_fnNames_5567_, lean_object* v_numSectionVars_5568_, lean_object* v_e_5569_, lean_object* v_a_5570_, lean_object* v_a_5571_){
_start:
{
lean_object* v___f_5573_; lean_object* v___f_5574_; uint8_t v___x_5575_; lean_object* v___x_5576_; 
v___f_5573_ = ((lean_object*)(l_Lean_Core_betaReduce___closed__1));
v___f_5574_ = lean_alloc_closure((void*)(l_Lean_Meta_unfoldIfArgIsAppOf___lam__0___boxed), 7, 4);
lean_closure_set(v___f_5574_, 0, v_fnNames_5567_);
lean_closure_set(v___f_5574_, 1, v_numSectionVars_5568_);
lean_closure_set(v___f_5574_, 2, v_e_5569_);
lean_closure_set(v___f_5574_, 3, v___f_5573_);
v___x_5575_ = 1;
v___x_5576_ = l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg(v___f_5574_, v___x_5575_, v_a_5570_, v_a_5571_);
return v___x_5576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___boxed(lean_object* v_fnNames_5577_, lean_object* v_numSectionVars_5578_, lean_object* v_e_5579_, lean_object* v_a_5580_, lean_object* v_a_5581_, lean_object* v_a_5582_){
_start:
{
lean_object* v_res_5583_; 
v_res_5583_ = l_Lean_Meta_unfoldIfArgIsAppOf(v_fnNames_5577_, v_numSectionVars_5578_, v_e_5579_, v_a_5580_, v_a_5581_);
lean_dec(v_a_5581_);
lean_dec_ref(v_a_5580_);
return v_res_5583_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2(lean_object* v_00_u03b1_5584_, lean_object* v_x_5585_, uint8_t v_isExporting_5586_, lean_object* v___y_5587_, lean_object* v___y_5588_){
_start:
{
lean_object* v___x_5590_; 
v___x_5590_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg(v_x_5585_, v_isExporting_5586_, v___y_5587_, v___y_5588_);
return v___x_5590_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___boxed(lean_object* v_00_u03b1_5591_, lean_object* v_x_5592_, lean_object* v_isExporting_5593_, lean_object* v___y_5594_, lean_object* v___y_5595_, lean_object* v___y_5596_){
_start:
{
uint8_t v_isExporting_boxed_5597_; lean_object* v_res_5598_; 
v_isExporting_boxed_5597_ = lean_unbox(v_isExporting_5593_);
v_res_5598_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2(v_00_u03b1_5591_, v_x_5592_, v_isExporting_boxed_5597_, v___y_5594_, v___y_5595_);
lean_dec(v___y_5595_);
lean_dec_ref(v___y_5594_);
return v_res_5598_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2(lean_object* v_00_u03b1_5599_, lean_object* v_x_5600_, uint8_t v_when_5601_, lean_object* v___y_5602_, lean_object* v___y_5603_){
_start:
{
lean_object* v___x_5605_; 
v___x_5605_ = l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg(v_x_5600_, v_when_5601_, v___y_5602_, v___y_5603_);
return v___x_5605_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___boxed(lean_object* v_00_u03b1_5606_, lean_object* v_x_5607_, lean_object* v_when_5608_, lean_object* v___y_5609_, lean_object* v___y_5610_, lean_object* v___y_5611_){
_start:
{
uint8_t v_when_boxed_5612_; lean_object* v_res_5613_; 
v_when_boxed_5612_ = lean_unbox(v_when_5608_);
v_res_5613_ = l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2(v_00_u03b1_5606_, v_x_5607_, v_when_boxed_5612_, v___y_5609_, v___y_5610_);
lean_dec(v___y_5610_);
lean_dec_ref(v___y_5609_);
return v_res_5613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___lam__0(lean_object* v_x_5614_, lean_object* v___y_5615_, lean_object* v___y_5616_){
_start:
{
lean_object* v___x_5618_; lean_object* v___x_5619_; 
v___x_5618_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_5619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5619_, 0, v___x_5618_);
return v___x_5619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___lam__0___boxed(lean_object* v_x_5620_, lean_object* v___y_5621_, lean_object* v___y_5622_, lean_object* v___y_5623_){
_start:
{
lean_object* v_res_5624_; 
v_res_5624_ = l_Lean_Meta_eraseInaccessibleAnnotations___lam__0(v_x_5620_, v___y_5621_, v___y_5622_);
lean_dec(v___y_5622_);
lean_dec_ref(v___y_5621_);
lean_dec_ref(v_x_5620_);
return v_res_5624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___lam__1(lean_object* v_e_5625_, lean_object* v___y_5626_, lean_object* v___y_5627_){
_start:
{
lean_object* v___y_5630_; lean_object* v___x_5633_; 
v___x_5633_ = l_Lean_inaccessible_x3f(v_e_5625_);
if (lean_obj_tag(v___x_5633_) == 1)
{
lean_object* v_val_5634_; 
lean_dec_ref(v_e_5625_);
v_val_5634_ = lean_ctor_get(v___x_5633_, 0);
lean_inc(v_val_5634_);
lean_dec_ref_known(v___x_5633_, 1);
v___y_5630_ = v_val_5634_;
goto v___jp_5629_;
}
else
{
lean_dec(v___x_5633_);
v___y_5630_ = v_e_5625_;
goto v___jp_5629_;
}
v___jp_5629_:
{
lean_object* v___x_5631_; lean_object* v___x_5632_; 
v___x_5631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5631_, 0, v___y_5630_);
v___x_5632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5632_, 0, v___x_5631_);
return v___x_5632_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___lam__1___boxed(lean_object* v_e_5635_, lean_object* v___y_5636_, lean_object* v___y_5637_, lean_object* v___y_5638_){
_start:
{
lean_object* v_res_5639_; 
v_res_5639_ = l_Lean_Meta_eraseInaccessibleAnnotations___lam__1(v_e_5635_, v___y_5636_, v___y_5637_);
lean_dec(v___y_5637_);
lean_dec_ref(v___y_5636_);
return v_res_5639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations(lean_object* v_e_5642_, lean_object* v_a_5643_, lean_object* v_a_5644_){
_start:
{
lean_object* v___f_5646_; lean_object* v___f_5647_; lean_object* v___x_5648_; 
v___f_5646_ = ((lean_object*)(l_Lean_Meta_eraseInaccessibleAnnotations___closed__0));
v___f_5647_ = ((lean_object*)(l_Lean_Meta_eraseInaccessibleAnnotations___closed__1));
v___x_5648_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_5642_, v___f_5646_, v___f_5647_, v_a_5643_, v_a_5644_);
return v___x_5648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___boxed(lean_object* v_e_5649_, lean_object* v_a_5650_, lean_object* v_a_5651_, lean_object* v_a_5652_){
_start:
{
lean_object* v_res_5653_; 
v_res_5653_ = l_Lean_Meta_eraseInaccessibleAnnotations(v_e_5649_, v_a_5650_, v_a_5651_);
lean_dec(v_a_5651_);
lean_dec_ref(v_a_5650_);
return v_res_5653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_erasePatternRefAnnotations___lam__1(lean_object* v_e_5654_, lean_object* v___y_5655_, lean_object* v___y_5656_){
_start:
{
lean_object* v___y_5659_; lean_object* v___x_5662_; 
v___x_5662_ = l_Lean_patternWithRef_x3f(v_e_5654_);
if (lean_obj_tag(v___x_5662_) == 1)
{
lean_object* v_val_5663_; lean_object* v_snd_5664_; 
lean_dec_ref(v_e_5654_);
v_val_5663_ = lean_ctor_get(v___x_5662_, 0);
lean_inc(v_val_5663_);
lean_dec_ref_known(v___x_5662_, 1);
v_snd_5664_ = lean_ctor_get(v_val_5663_, 1);
lean_inc(v_snd_5664_);
lean_dec(v_val_5663_);
v___y_5659_ = v_snd_5664_;
goto v___jp_5658_;
}
else
{
lean_dec(v___x_5662_);
v___y_5659_ = v_e_5654_;
goto v___jp_5658_;
}
v___jp_5658_:
{
lean_object* v___x_5660_; lean_object* v___x_5661_; 
v___x_5660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5660_, 0, v___y_5659_);
v___x_5661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5661_, 0, v___x_5660_);
return v___x_5661_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_erasePatternRefAnnotations___lam__1___boxed(lean_object* v_e_5665_, lean_object* v___y_5666_, lean_object* v___y_5667_, lean_object* v___y_5668_){
_start:
{
lean_object* v_res_5669_; 
v_res_5669_ = l_Lean_Meta_erasePatternRefAnnotations___lam__1(v_e_5665_, v___y_5666_, v___y_5667_);
lean_dec(v___y_5667_);
lean_dec_ref(v___y_5666_);
return v_res_5669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_erasePatternRefAnnotations(lean_object* v_e_5671_, lean_object* v_a_5672_, lean_object* v_a_5673_){
_start:
{
lean_object* v___f_5675_; lean_object* v___f_5676_; lean_object* v___x_5677_; 
v___f_5675_ = ((lean_object*)(l_Lean_Meta_eraseInaccessibleAnnotations___closed__0));
v___f_5676_ = ((lean_object*)(l_Lean_Meta_erasePatternRefAnnotations___closed__0));
v___x_5677_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_5671_, v___f_5675_, v___f_5676_, v_a_5672_, v_a_5673_);
return v___x_5677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_erasePatternRefAnnotations___boxed(lean_object* v_e_5678_, lean_object* v_a_5679_, lean_object* v_a_5680_, lean_object* v_a_5681_){
_start:
{
lean_object* v_res_5682_; 
v_res_5682_ = l_Lean_Meta_erasePatternRefAnnotations(v_e_5678_, v_a_5679_, v_a_5680_);
lean_dec(v_a_5680_);
lean_dec_ref(v_a_5679_);
return v_res_5682_;
}
}
lean_object* runtime_initialize_Lean_Meta_FunInfo(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Transform(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
