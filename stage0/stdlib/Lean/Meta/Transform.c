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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
lean_object* l_Lean_Environment_header(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__8(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__9(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__10(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__11(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__12___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__13(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__13___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__14(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_2523__overap_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
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
v___x_2523__overap_220_ = l_Lean_Core_withIncRecDepth___redArg(v___x_209_, v___x_210_, v___x_219_);
lean_inc(v_a_211_);
v___x_221_ = lean_apply_1(v___x_2523__overap_220_, v_a_211_);
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
lean_dec_ref_known(v_a_215_, 1);
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
lean_object* v___f_287_; lean_object* v___x_288_; size_t v_sz_289_; size_t v___x_290_; lean_object* v___x_2253__overap_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
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
v___x_2253__overap_291_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_284_, v___x_288_, v_sz_289_, v___x_290_, v_args_283_);
v___x_292_ = lean_apply_1(v___x_2253__overap_291_, v___y_282_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__8(lean_object* v_binderType_345_, lean_object* v_a_346_, lean_object* v_binderName_347_, uint8_t v_binderInfo_348_, lean_object* v_inst_349_, lean_object* v_inst_350_, lean_object* v_inst_351_, lean_object* v_pre_352_, lean_object* v_post_353_, lean_object* v_x_354_, lean_object* v_x_355_, lean_object* v___y_356_, lean_object* v_body_357_, lean_object* v___y_358_, lean_object* v_a_359_){
_start:
{
size_t v___x_360_; size_t v___x_361_; uint8_t v___x_362_; 
v___x_360_ = lean_ptr_addr(v_binderType_345_);
v___x_361_ = lean_ptr_addr(v_a_346_);
v___x_362_ = lean_usize_dec_eq(v___x_360_, v___x_361_);
if (v___x_362_ == 0)
{
lean_object* v___x_363_; lean_object* v___x_364_; 
lean_dec_ref(v___y_358_);
v___x_363_ = l_Lean_Expr_forallE___override(v_binderName_347_, v_a_346_, v_a_359_, v_binderInfo_348_);
v___x_364_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_349_, v_inst_350_, v_inst_351_, v_pre_352_, v_post_353_, v_x_354_, v_x_355_, v___x_363_, v___y_356_);
return v___x_364_;
}
else
{
size_t v___x_365_; size_t v___x_366_; uint8_t v___x_367_; 
v___x_365_ = lean_ptr_addr(v_body_357_);
v___x_366_ = lean_ptr_addr(v_a_359_);
v___x_367_ = lean_usize_dec_eq(v___x_365_, v___x_366_);
if (v___x_367_ == 0)
{
lean_object* v___x_368_; lean_object* v___x_369_; 
lean_dec_ref(v___y_358_);
v___x_368_ = l_Lean_Expr_forallE___override(v_binderName_347_, v_a_346_, v_a_359_, v_binderInfo_348_);
v___x_369_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_349_, v_inst_350_, v_inst_351_, v_pre_352_, v_post_353_, v_x_354_, v_x_355_, v___x_368_, v___y_356_);
return v___x_369_;
}
else
{
uint8_t v___x_370_; 
v___x_370_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_348_, v_binderInfo_348_);
if (v___x_370_ == 0)
{
lean_object* v___x_371_; lean_object* v___x_372_; 
lean_dec_ref(v___y_358_);
v___x_371_ = l_Lean_Expr_forallE___override(v_binderName_347_, v_a_346_, v_a_359_, v_binderInfo_348_);
v___x_372_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_349_, v_inst_350_, v_inst_351_, v_pre_352_, v_post_353_, v_x_354_, v_x_355_, v___x_371_, v___y_356_);
return v___x_372_;
}
else
{
lean_object* v___x_373_; 
lean_dec_ref(v_a_359_);
lean_dec(v_binderName_347_);
lean_dec_ref(v_a_346_);
v___x_373_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_349_, v_inst_350_, v_inst_351_, v_pre_352_, v_post_353_, v_x_354_, v_x_355_, v___y_358_, v___y_356_);
return v___x_373_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__8___boxed(lean_object* v_binderType_374_, lean_object* v_a_375_, lean_object* v_binderName_376_, lean_object* v_binderInfo_377_, lean_object* v_inst_378_, lean_object* v_inst_379_, lean_object* v_inst_380_, lean_object* v_pre_381_, lean_object* v_post_382_, lean_object* v_x_383_, lean_object* v_x_384_, lean_object* v___y_385_, lean_object* v_body_386_, lean_object* v___y_387_, lean_object* v_a_388_){
_start:
{
uint8_t v_binderInfo_2847__boxed_389_; lean_object* v_res_390_; 
v_binderInfo_2847__boxed_389_ = lean_unbox(v_binderInfo_377_);
v_res_390_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__8(v_binderType_374_, v_a_375_, v_binderName_376_, v_binderInfo_2847__boxed_389_, v_inst_378_, v_inst_379_, v_inst_380_, v_pre_381_, v_post_382_, v_x_383_, v_x_384_, v___y_385_, v_body_386_, v___y_387_, v_a_388_);
lean_dec_ref(v_body_386_);
lean_dec(v___y_385_);
lean_dec_ref(v_binderType_374_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__9(lean_object* v_binderType_391_, lean_object* v_binderName_392_, uint8_t v_binderInfo_393_, lean_object* v_inst_394_, lean_object* v_inst_395_, lean_object* v_inst_396_, lean_object* v_pre_397_, lean_object* v_post_398_, lean_object* v_x_399_, lean_object* v_x_400_, lean_object* v___y_401_, lean_object* v_body_402_, lean_object* v___y_403_, lean_object* v_toBind_404_, lean_object* v_a_405_){
_start:
{
lean_object* v___x_406_; lean_object* v___f_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_406_ = lean_box(v_binderInfo_393_);
lean_inc_ref(v_body_402_);
lean_inc(v___y_401_);
lean_inc(v_x_400_);
lean_inc(v_post_398_);
lean_inc(v_pre_397_);
lean_inc_ref(v_inst_396_);
lean_inc(v_inst_395_);
lean_inc_ref(v_inst_394_);
v___f_407_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__8___boxed), 15, 14);
lean_closure_set(v___f_407_, 0, v_binderType_391_);
lean_closure_set(v___f_407_, 1, v_a_405_);
lean_closure_set(v___f_407_, 2, v_binderName_392_);
lean_closure_set(v___f_407_, 3, v___x_406_);
lean_closure_set(v___f_407_, 4, v_inst_394_);
lean_closure_set(v___f_407_, 5, v_inst_395_);
lean_closure_set(v___f_407_, 6, v_inst_396_);
lean_closure_set(v___f_407_, 7, v_pre_397_);
lean_closure_set(v___f_407_, 8, v_post_398_);
lean_closure_set(v___f_407_, 9, v_x_399_);
lean_closure_set(v___f_407_, 10, v_x_400_);
lean_closure_set(v___f_407_, 11, v___y_401_);
lean_closure_set(v___f_407_, 12, v_body_402_);
lean_closure_set(v___f_407_, 13, v___y_403_);
v___x_408_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_394_, v_inst_395_, v_inst_396_, v_pre_397_, v_post_398_, v_x_399_, v_x_400_, v_body_402_, v___y_401_);
v___x_409_ = lean_apply_4(v_toBind_404_, lean_box(0), lean_box(0), v___x_408_, v___f_407_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__9___boxed(lean_object* v_binderType_410_, lean_object* v_binderName_411_, lean_object* v_binderInfo_412_, lean_object* v_inst_413_, lean_object* v_inst_414_, lean_object* v_inst_415_, lean_object* v_pre_416_, lean_object* v_post_417_, lean_object* v_x_418_, lean_object* v_x_419_, lean_object* v___y_420_, lean_object* v_body_421_, lean_object* v___y_422_, lean_object* v_toBind_423_, lean_object* v_a_424_){
_start:
{
uint8_t v_binderInfo_2708__boxed_425_; lean_object* v_res_426_; 
v_binderInfo_2708__boxed_425_ = lean_unbox(v_binderInfo_412_);
v_res_426_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__9(v_binderType_410_, v_binderName_411_, v_binderInfo_2708__boxed_425_, v_inst_413_, v_inst_414_, v_inst_415_, v_pre_416_, v_post_417_, v_x_418_, v_x_419_, v___y_420_, v_body_421_, v___y_422_, v_toBind_423_, v_a_424_);
lean_dec(v___y_420_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__10(lean_object* v_binderType_427_, lean_object* v_a_428_, lean_object* v_binderName_429_, uint8_t v_binderInfo_430_, lean_object* v_inst_431_, lean_object* v_inst_432_, lean_object* v_inst_433_, lean_object* v_pre_434_, lean_object* v_post_435_, lean_object* v_x_436_, lean_object* v_x_437_, lean_object* v___y_438_, lean_object* v_body_439_, lean_object* v___y_440_, lean_object* v_a_441_){
_start:
{
size_t v___x_442_; size_t v___x_443_; uint8_t v___x_444_; 
v___x_442_ = lean_ptr_addr(v_binderType_427_);
v___x_443_ = lean_ptr_addr(v_a_428_);
v___x_444_ = lean_usize_dec_eq(v___x_442_, v___x_443_);
if (v___x_444_ == 0)
{
lean_object* v___x_445_; lean_object* v___x_446_; 
lean_dec_ref(v___y_440_);
v___x_445_ = l_Lean_Expr_lam___override(v_binderName_429_, v_a_428_, v_a_441_, v_binderInfo_430_);
v___x_446_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_431_, v_inst_432_, v_inst_433_, v_pre_434_, v_post_435_, v_x_436_, v_x_437_, v___x_445_, v___y_438_);
return v___x_446_;
}
else
{
size_t v___x_447_; size_t v___x_448_; uint8_t v___x_449_; 
v___x_447_ = lean_ptr_addr(v_body_439_);
v___x_448_ = lean_ptr_addr(v_a_441_);
v___x_449_ = lean_usize_dec_eq(v___x_447_, v___x_448_);
if (v___x_449_ == 0)
{
lean_object* v___x_450_; lean_object* v___x_451_; 
lean_dec_ref(v___y_440_);
v___x_450_ = l_Lean_Expr_lam___override(v_binderName_429_, v_a_428_, v_a_441_, v_binderInfo_430_);
v___x_451_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_431_, v_inst_432_, v_inst_433_, v_pre_434_, v_post_435_, v_x_436_, v_x_437_, v___x_450_, v___y_438_);
return v___x_451_;
}
else
{
uint8_t v___x_452_; 
v___x_452_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_430_, v_binderInfo_430_);
if (v___x_452_ == 0)
{
lean_object* v___x_453_; lean_object* v___x_454_; 
lean_dec_ref(v___y_440_);
v___x_453_ = l_Lean_Expr_lam___override(v_binderName_429_, v_a_428_, v_a_441_, v_binderInfo_430_);
v___x_454_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_431_, v_inst_432_, v_inst_433_, v_pre_434_, v_post_435_, v_x_436_, v_x_437_, v___x_453_, v___y_438_);
return v___x_454_;
}
else
{
lean_object* v___x_455_; 
lean_dec_ref(v_a_441_);
lean_dec(v_binderName_429_);
lean_dec_ref(v_a_428_);
v___x_455_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_431_, v_inst_432_, v_inst_433_, v_pre_434_, v_post_435_, v_x_436_, v_x_437_, v___y_440_, v___y_438_);
return v___x_455_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__10___boxed(lean_object* v_binderType_456_, lean_object* v_a_457_, lean_object* v_binderName_458_, lean_object* v_binderInfo_459_, lean_object* v_inst_460_, lean_object* v_inst_461_, lean_object* v_inst_462_, lean_object* v_pre_463_, lean_object* v_post_464_, lean_object* v_x_465_, lean_object* v_x_466_, lean_object* v___y_467_, lean_object* v_body_468_, lean_object* v___y_469_, lean_object* v_a_470_){
_start:
{
uint8_t v_binderInfo_2822__boxed_471_; lean_object* v_res_472_; 
v_binderInfo_2822__boxed_471_ = lean_unbox(v_binderInfo_459_);
v_res_472_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__10(v_binderType_456_, v_a_457_, v_binderName_458_, v_binderInfo_2822__boxed_471_, v_inst_460_, v_inst_461_, v_inst_462_, v_pre_463_, v_post_464_, v_x_465_, v_x_466_, v___y_467_, v_body_468_, v___y_469_, v_a_470_);
lean_dec_ref(v_body_468_);
lean_dec(v___y_467_);
lean_dec_ref(v_binderType_456_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__11(lean_object* v_binderType_473_, lean_object* v_binderName_474_, uint8_t v_binderInfo_475_, lean_object* v_inst_476_, lean_object* v_inst_477_, lean_object* v_inst_478_, lean_object* v_pre_479_, lean_object* v_post_480_, lean_object* v_x_481_, lean_object* v_x_482_, lean_object* v___y_483_, lean_object* v_body_484_, lean_object* v___y_485_, lean_object* v_toBind_486_, lean_object* v_a_487_){
_start:
{
lean_object* v___x_488_; lean_object* v___f_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_488_ = lean_box(v_binderInfo_475_);
lean_inc_ref(v_body_484_);
lean_inc(v___y_483_);
lean_inc(v_x_482_);
lean_inc(v_post_480_);
lean_inc(v_pre_479_);
lean_inc_ref(v_inst_478_);
lean_inc(v_inst_477_);
lean_inc_ref(v_inst_476_);
v___f_489_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__10___boxed), 15, 14);
lean_closure_set(v___f_489_, 0, v_binderType_473_);
lean_closure_set(v___f_489_, 1, v_a_487_);
lean_closure_set(v___f_489_, 2, v_binderName_474_);
lean_closure_set(v___f_489_, 3, v___x_488_);
lean_closure_set(v___f_489_, 4, v_inst_476_);
lean_closure_set(v___f_489_, 5, v_inst_477_);
lean_closure_set(v___f_489_, 6, v_inst_478_);
lean_closure_set(v___f_489_, 7, v_pre_479_);
lean_closure_set(v___f_489_, 8, v_post_480_);
lean_closure_set(v___f_489_, 9, v_x_481_);
lean_closure_set(v___f_489_, 10, v_x_482_);
lean_closure_set(v___f_489_, 11, v___y_483_);
lean_closure_set(v___f_489_, 12, v_body_484_);
lean_closure_set(v___f_489_, 13, v___y_485_);
v___x_490_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_476_, v_inst_477_, v_inst_478_, v_pre_479_, v_post_480_, v_x_481_, v_x_482_, v_body_484_, v___y_483_);
v___x_491_ = lean_apply_4(v_toBind_486_, lean_box(0), lean_box(0), v___x_490_, v___f_489_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__11___boxed(lean_object* v_binderType_492_, lean_object* v_binderName_493_, lean_object* v_binderInfo_494_, lean_object* v_inst_495_, lean_object* v_inst_496_, lean_object* v_inst_497_, lean_object* v_pre_498_, lean_object* v_post_499_, lean_object* v_x_500_, lean_object* v_x_501_, lean_object* v___y_502_, lean_object* v_body_503_, lean_object* v___y_504_, lean_object* v_toBind_505_, lean_object* v_a_506_){
_start:
{
uint8_t v_binderInfo_2654__boxed_507_; lean_object* v_res_508_; 
v_binderInfo_2654__boxed_507_ = lean_unbox(v_binderInfo_494_);
v_res_508_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__11(v_binderType_492_, v_binderName_493_, v_binderInfo_2654__boxed_507_, v_inst_495_, v_inst_496_, v_inst_497_, v_pre_498_, v_post_499_, v_x_500_, v_x_501_, v___y_502_, v_body_503_, v___y_504_, v_toBind_505_, v_a_506_);
lean_dec(v___y_502_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__12(lean_object* v_type_509_, lean_object* v_a_510_, lean_object* v_declName_511_, lean_object* v_a_512_, uint8_t v_nondep_513_, lean_object* v_inst_514_, lean_object* v_inst_515_, lean_object* v_inst_516_, lean_object* v_pre_517_, lean_object* v_post_518_, lean_object* v_x_519_, lean_object* v_x_520_, lean_object* v___y_521_, lean_object* v_value_522_, lean_object* v_body_523_, lean_object* v___y_524_, lean_object* v_a_525_){
_start:
{
size_t v___x_526_; size_t v___x_527_; uint8_t v___x_528_; 
v___x_526_ = lean_ptr_addr(v_type_509_);
v___x_527_ = lean_ptr_addr(v_a_510_);
v___x_528_ = lean_usize_dec_eq(v___x_526_, v___x_527_);
if (v___x_528_ == 0)
{
lean_object* v___x_529_; lean_object* v___x_530_; 
lean_dec_ref(v___y_524_);
v___x_529_ = l_Lean_Expr_letE___override(v_declName_511_, v_a_510_, v_a_512_, v_a_525_, v_nondep_513_);
v___x_530_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_514_, v_inst_515_, v_inst_516_, v_pre_517_, v_post_518_, v_x_519_, v_x_520_, v___x_529_, v___y_521_);
return v___x_530_;
}
else
{
size_t v___x_531_; size_t v___x_532_; uint8_t v___x_533_; 
v___x_531_ = lean_ptr_addr(v_value_522_);
v___x_532_ = lean_ptr_addr(v_a_512_);
v___x_533_ = lean_usize_dec_eq(v___x_531_, v___x_532_);
if (v___x_533_ == 0)
{
lean_object* v___x_534_; lean_object* v___x_535_; 
lean_dec_ref(v___y_524_);
v___x_534_ = l_Lean_Expr_letE___override(v_declName_511_, v_a_510_, v_a_512_, v_a_525_, v_nondep_513_);
v___x_535_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_514_, v_inst_515_, v_inst_516_, v_pre_517_, v_post_518_, v_x_519_, v_x_520_, v___x_534_, v___y_521_);
return v___x_535_;
}
else
{
size_t v___x_536_; size_t v___x_537_; uint8_t v___x_538_; 
v___x_536_ = lean_ptr_addr(v_body_523_);
v___x_537_ = lean_ptr_addr(v_a_525_);
v___x_538_ = lean_usize_dec_eq(v___x_536_, v___x_537_);
if (v___x_538_ == 0)
{
lean_object* v___x_539_; lean_object* v___x_540_; 
lean_dec_ref(v___y_524_);
v___x_539_ = l_Lean_Expr_letE___override(v_declName_511_, v_a_510_, v_a_512_, v_a_525_, v_nondep_513_);
v___x_540_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_514_, v_inst_515_, v_inst_516_, v_pre_517_, v_post_518_, v_x_519_, v_x_520_, v___x_539_, v___y_521_);
return v___x_540_;
}
else
{
lean_object* v___x_541_; 
lean_dec_ref(v_a_525_);
lean_dec_ref(v_a_512_);
lean_dec(v_declName_511_);
lean_dec_ref(v_a_510_);
v___x_541_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_514_, v_inst_515_, v_inst_516_, v_pre_517_, v_post_518_, v_x_519_, v_x_520_, v___y_524_, v___y_521_);
return v___x_541_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__12___boxed(lean_object** _args){
lean_object* v_type_542_ = _args[0];
lean_object* v_a_543_ = _args[1];
lean_object* v_declName_544_ = _args[2];
lean_object* v_a_545_ = _args[3];
lean_object* v_nondep_546_ = _args[4];
lean_object* v_inst_547_ = _args[5];
lean_object* v_inst_548_ = _args[6];
lean_object* v_inst_549_ = _args[7];
lean_object* v_pre_550_ = _args[8];
lean_object* v_post_551_ = _args[9];
lean_object* v_x_552_ = _args[10];
lean_object* v_x_553_ = _args[11];
lean_object* v___y_554_ = _args[12];
lean_object* v_value_555_ = _args[13];
lean_object* v_body_556_ = _args[14];
lean_object* v___y_557_ = _args[15];
lean_object* v_a_558_ = _args[16];
_start:
{
uint8_t v_nondep_2872__boxed_559_; lean_object* v_res_560_; 
v_nondep_2872__boxed_559_ = lean_unbox(v_nondep_546_);
v_res_560_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__12(v_type_542_, v_a_543_, v_declName_544_, v_a_545_, v_nondep_2872__boxed_559_, v_inst_547_, v_inst_548_, v_inst_549_, v_pre_550_, v_post_551_, v_x_552_, v_x_553_, v___y_554_, v_value_555_, v_body_556_, v___y_557_, v_a_558_);
lean_dec_ref(v_body_556_);
lean_dec_ref(v_value_555_);
lean_dec(v___y_554_);
lean_dec_ref(v_type_542_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__13(lean_object* v_type_561_, lean_object* v_a_562_, lean_object* v_declName_563_, uint8_t v_nondep_564_, lean_object* v_inst_565_, lean_object* v_inst_566_, lean_object* v_inst_567_, lean_object* v_pre_568_, lean_object* v_post_569_, lean_object* v_x_570_, lean_object* v_x_571_, lean_object* v___y_572_, lean_object* v_value_573_, lean_object* v_body_574_, lean_object* v___y_575_, lean_object* v_toBind_576_, lean_object* v_a_577_){
_start:
{
lean_object* v___x_578_; lean_object* v___f_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_578_ = lean_box(v_nondep_564_);
lean_inc_ref(v_body_574_);
lean_inc(v___y_572_);
lean_inc(v_x_571_);
lean_inc(v_post_569_);
lean_inc(v_pre_568_);
lean_inc_ref(v_inst_567_);
lean_inc(v_inst_566_);
lean_inc_ref(v_inst_565_);
v___f_579_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__12___boxed), 17, 16);
lean_closure_set(v___f_579_, 0, v_type_561_);
lean_closure_set(v___f_579_, 1, v_a_562_);
lean_closure_set(v___f_579_, 2, v_declName_563_);
lean_closure_set(v___f_579_, 3, v_a_577_);
lean_closure_set(v___f_579_, 4, v___x_578_);
lean_closure_set(v___f_579_, 5, v_inst_565_);
lean_closure_set(v___f_579_, 6, v_inst_566_);
lean_closure_set(v___f_579_, 7, v_inst_567_);
lean_closure_set(v___f_579_, 8, v_pre_568_);
lean_closure_set(v___f_579_, 9, v_post_569_);
lean_closure_set(v___f_579_, 10, v_x_570_);
lean_closure_set(v___f_579_, 11, v_x_571_);
lean_closure_set(v___f_579_, 12, v___y_572_);
lean_closure_set(v___f_579_, 13, v_value_573_);
lean_closure_set(v___f_579_, 14, v_body_574_);
lean_closure_set(v___f_579_, 15, v___y_575_);
v___x_580_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_565_, v_inst_566_, v_inst_567_, v_pre_568_, v_post_569_, v_x_570_, v_x_571_, v_body_574_, v___y_572_);
v___x_581_ = lean_apply_4(v_toBind_576_, lean_box(0), lean_box(0), v___x_580_, v___f_579_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__13___boxed(lean_object** _args){
lean_object* v_type_582_ = _args[0];
lean_object* v_a_583_ = _args[1];
lean_object* v_declName_584_ = _args[2];
lean_object* v_nondep_585_ = _args[3];
lean_object* v_inst_586_ = _args[4];
lean_object* v_inst_587_ = _args[5];
lean_object* v_inst_588_ = _args[6];
lean_object* v_pre_589_ = _args[7];
lean_object* v_post_590_ = _args[8];
lean_object* v_x_591_ = _args[9];
lean_object* v_x_592_ = _args[10];
lean_object* v___y_593_ = _args[11];
lean_object* v_value_594_ = _args[12];
lean_object* v_body_595_ = _args[13];
lean_object* v___y_596_ = _args[14];
lean_object* v_toBind_597_ = _args[15];
lean_object* v_a_598_ = _args[16];
_start:
{
uint8_t v_nondep_2668__boxed_599_; lean_object* v_res_600_; 
v_nondep_2668__boxed_599_ = lean_unbox(v_nondep_585_);
v_res_600_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__13(v_type_582_, v_a_583_, v_declName_584_, v_nondep_2668__boxed_599_, v_inst_586_, v_inst_587_, v_inst_588_, v_pre_589_, v_post_590_, v_x_591_, v_x_592_, v___y_593_, v_value_594_, v_body_595_, v___y_596_, v_toBind_597_, v_a_598_);
lean_dec(v___y_593_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__14(lean_object* v_type_601_, lean_object* v_declName_602_, uint8_t v_nondep_603_, lean_object* v_inst_604_, lean_object* v_inst_605_, lean_object* v_inst_606_, lean_object* v_pre_607_, lean_object* v_post_608_, lean_object* v_x_609_, lean_object* v_x_610_, lean_object* v___y_611_, lean_object* v_value_612_, lean_object* v_body_613_, lean_object* v___y_614_, lean_object* v_toBind_615_, lean_object* v_a_616_){
_start:
{
lean_object* v___x_617_; lean_object* v___f_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_617_ = lean_box(v_nondep_603_);
lean_inc(v_toBind_615_);
lean_inc_ref(v_value_612_);
lean_inc(v___y_611_);
lean_inc(v_x_610_);
lean_inc(v_post_608_);
lean_inc(v_pre_607_);
lean_inc_ref(v_inst_606_);
lean_inc(v_inst_605_);
lean_inc_ref(v_inst_604_);
v___f_618_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__13___boxed), 17, 16);
lean_closure_set(v___f_618_, 0, v_type_601_);
lean_closure_set(v___f_618_, 1, v_a_616_);
lean_closure_set(v___f_618_, 2, v_declName_602_);
lean_closure_set(v___f_618_, 3, v___x_617_);
lean_closure_set(v___f_618_, 4, v_inst_604_);
lean_closure_set(v___f_618_, 5, v_inst_605_);
lean_closure_set(v___f_618_, 6, v_inst_606_);
lean_closure_set(v___f_618_, 7, v_pre_607_);
lean_closure_set(v___f_618_, 8, v_post_608_);
lean_closure_set(v___f_618_, 9, v_x_609_);
lean_closure_set(v___f_618_, 10, v_x_610_);
lean_closure_set(v___f_618_, 11, v___y_611_);
lean_closure_set(v___f_618_, 12, v_value_612_);
lean_closure_set(v___f_618_, 13, v_body_613_);
lean_closure_set(v___f_618_, 14, v___y_614_);
lean_closure_set(v___f_618_, 15, v_toBind_615_);
v___x_619_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_604_, v_inst_605_, v_inst_606_, v_pre_607_, v_post_608_, v_x_609_, v_x_610_, v_value_612_, v___y_611_);
v___x_620_ = lean_apply_4(v_toBind_615_, lean_box(0), lean_box(0), v___x_619_, v___f_618_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__14___boxed(lean_object* v_type_621_, lean_object* v_declName_622_, lean_object* v_nondep_623_, lean_object* v_inst_624_, lean_object* v_inst_625_, lean_object* v_inst_626_, lean_object* v_pre_627_, lean_object* v_post_628_, lean_object* v_x_629_, lean_object* v_x_630_, lean_object* v___y_631_, lean_object* v_value_632_, lean_object* v_body_633_, lean_object* v___y_634_, lean_object* v_toBind_635_, lean_object* v_a_636_){
_start:
{
uint8_t v_nondep_2683__boxed_637_; lean_object* v_res_638_; 
v_nondep_2683__boxed_637_ = lean_unbox(v_nondep_623_);
v_res_638_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__14(v_type_621_, v_declName_622_, v_nondep_2683__boxed_637_, v_inst_624_, v_inst_625_, v_inst_626_, v_pre_627_, v_post_628_, v_x_629_, v_x_630_, v___y_631_, v_value_632_, v_body_633_, v___y_634_, v_toBind_635_, v_a_636_);
lean_dec(v___y_631_);
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
lean_dec_ref_known(v_a_718_, 1);
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
lean_dec_ref_known(v_a_718_, 1);
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
lean_dec_ref_known(v_a_718_, 1);
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
lean_dec_ref_known(v_e_x3f_771_, 1);
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
lean_closure_set(v___f_726_, 0, v_binderType_722_);
lean_closure_set(v___f_726_, 1, v_binderName_721_);
lean_closure_set(v___f_726_, 2, v___x_725_);
lean_closure_set(v___f_726_, 3, v_inst_706_);
lean_closure_set(v___f_726_, 4, v_inst_707_);
lean_closure_set(v___f_726_, 5, v_inst_708_);
lean_closure_set(v___f_726_, 6, v_pre_709_);
lean_closure_set(v___f_726_, 7, v_post_710_);
lean_closure_set(v___f_726_, 8, v_x_711_);
lean_closure_set(v___f_726_, 9, v_x_712_);
lean_closure_set(v___f_726_, 10, v___y_713_);
lean_closure_set(v___f_726_, 11, v_body_723_);
lean_closure_set(v___f_726_, 12, v___y_720_);
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
lean_closure_set(v___f_734_, 0, v_binderType_730_);
lean_closure_set(v___f_734_, 1, v_binderName_729_);
lean_closure_set(v___f_734_, 2, v___x_733_);
lean_closure_set(v___f_734_, 3, v_inst_706_);
lean_closure_set(v___f_734_, 4, v_inst_707_);
lean_closure_set(v___f_734_, 5, v_inst_708_);
lean_closure_set(v___f_734_, 6, v_pre_709_);
lean_closure_set(v___f_734_, 7, v_post_710_);
lean_closure_set(v___f_734_, 8, v_x_711_);
lean_closure_set(v___f_734_, 9, v_x_712_);
lean_closure_set(v___f_734_, 10, v___y_713_);
lean_closure_set(v___f_734_, 11, v_body_731_);
lean_closure_set(v___f_734_, 12, v___y_720_);
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
lean_closure_set(v___f_743_, 0, v_type_738_);
lean_closure_set(v___f_743_, 1, v_declName_737_);
lean_closure_set(v___f_743_, 2, v___x_742_);
lean_closure_set(v___f_743_, 3, v_inst_706_);
lean_closure_set(v___f_743_, 4, v_inst_707_);
lean_closure_set(v___f_743_, 5, v_inst_708_);
lean_closure_set(v___f_743_, 6, v_pre_709_);
lean_closure_set(v___f_743_, 7, v_post_710_);
lean_closure_set(v___f_743_, 8, v_x_711_);
lean_closure_set(v___f_743_, 9, v_x_712_);
lean_closure_set(v___f_743_, 10, v___y_713_);
lean_closure_set(v___f_743_, 11, v_value_739_);
lean_closure_set(v___f_743_, 12, v_body_740_);
lean_closure_set(v___f_743_, 13, v___y_720_);
lean_closure_set(v___f_743_, 14, v_toBind_714_);
v___x_744_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_706_, v_inst_707_, v_inst_708_, v_pre_709_, v_post_710_, v_x_711_, v_x_712_, v_type_738_, v___y_713_);
v___x_745_ = lean_apply_4(v_toBind_714_, lean_box(0), lean_box(0), v___x_744_, v___f_743_);
return v___x_745_;
}
case 5:
{
lean_object* v_dummy_746_; lean_object* v_nargs_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_2483__overap_751_; lean_object* v___x_752_; 
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
v___x_2483__overap_751_ = l_Lean_Expr_withAppAux___redArg(v___f_716_, v___y_720_, v___x_748_, v___x_750_);
lean_inc(v___y_713_);
v___x_752_ = lean_apply_1(v___x_2483__overap_751_, v___y_713_);
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
lean_dec_ref_known(v_a_856_, 1);
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
lean_dec_ref_known(v_a_856_, 1);
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
lean_dec_ref_known(v_a_856_, 1);
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
lean_dec_ref_known(v_e_x3f_866_, 1);
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
lean_object* v___y_1099_; lean_object* v___y_1109_; uint8_t v___y_1110_; lean_object* v___y_1111_; uint8_t v___y_1112_; lean_object* v___y_1113_; lean_object* v_toCold_1118_; lean_object* v_currRecDepth_1119_; lean_object* v_ref_1120_; uint8_t v_diag_1121_; uint8_t v_suppressElabErrors_1122_; lean_object* v_maxRecDepth_1123_; lean_object* v_cancelTk_x3f_1124_; 
v_toCold_1118_ = lean_ctor_get(v___y_1095_, 0);
v_currRecDepth_1119_ = lean_ctor_get(v___y_1095_, 1);
v_ref_1120_ = lean_ctor_get(v___y_1095_, 2);
v_diag_1121_ = lean_ctor_get_uint8(v___y_1095_, sizeof(void*)*3);
v_suppressElabErrors_1122_ = lean_ctor_get_uint8(v___y_1095_, sizeof(void*)*3 + 1);
v_maxRecDepth_1123_ = lean_ctor_get(v_toCold_1118_, 3);
v_cancelTk_x3f_1124_ = lean_ctor_get(v_toCold_1118_, 10);
if (lean_obj_tag(v_cancelTk_x3f_1124_) == 1)
{
lean_object* v_val_1130_; uint8_t v___x_1131_; 
v_val_1130_ = lean_ctor_get(v_cancelTk_x3f_1124_, 0);
v___x_1131_ = l_IO_CancelToken_isSet(v_val_1130_);
if (v___x_1131_ == 0)
{
goto v___jp_1125_;
}
else
{
lean_object* v___x_1132_; lean_object* v_a_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1140_; 
lean_dec_ref(v_x_1093_);
v___x_1132_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___redArg();
v_a_1133_ = lean_ctor_get(v___x_1132_, 0);
v_isSharedCheck_1140_ = !lean_is_exclusive(v___x_1132_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1135_ = v___x_1132_;
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_a_1133_);
lean_dec(v___x_1132_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1138_; 
if (v_isShared_1136_ == 0)
{
v___x_1138_ = v___x_1135_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v_a_1133_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
return v___x_1138_;
}
}
}
}
else
{
goto v___jp_1125_;
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
lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1114_ = lean_unsigned_to_nat(1u);
v___x_1115_ = lean_nat_add(v___y_1109_, v___x_1114_);
lean_inc_ref(v___y_1111_);
v___x_1116_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1116_, 0, v___y_1111_);
lean_ctor_set(v___x_1116_, 1, v___x_1115_);
lean_ctor_set(v___x_1116_, 2, v___y_1113_);
lean_ctor_set_uint8(v___x_1116_, sizeof(void*)*3, v___y_1112_);
lean_ctor_set_uint8(v___x_1116_, sizeof(void*)*3 + 1, v___y_1110_);
lean_inc(v___y_1096_);
lean_inc(v___y_1094_);
v___x_1117_ = lean_apply_4(v_x_1093_, v___y_1094_, v___x_1116_, v___y_1096_, lean_box(0));
v___y_1099_ = v___x_1117_;
goto v___jp_1098_;
}
v___jp_1125_:
{
lean_object* v___x_1126_; uint8_t v___x_1127_; 
v___x_1126_ = lean_unsigned_to_nat(0u);
v___x_1127_ = lean_nat_dec_eq(v_maxRecDepth_1123_, v___x_1126_);
if (v___x_1127_ == 0)
{
uint8_t v___x_1128_; 
v___x_1128_ = lean_nat_dec_eq(v_currRecDepth_1119_, v_maxRecDepth_1123_);
if (v___x_1128_ == 0)
{
lean_inc(v_ref_1120_);
v___y_1109_ = v_currRecDepth_1119_;
v___y_1110_ = v_suppressElabErrors_1122_;
v___y_1111_ = v_toCold_1118_;
v___y_1112_ = v_diag_1121_;
v___y_1113_ = v_ref_1120_;
goto v___jp_1108_;
}
else
{
lean_object* v___x_1129_; 
lean_dec_ref(v_x_1093_);
lean_inc(v_ref_1120_);
v___x_1129_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_1120_);
v___y_1099_ = v___x_1129_;
goto v___jp_1098_;
}
}
else
{
lean_inc(v_ref_1120_);
v___y_1109_ = v_currRecDepth_1119_;
v___y_1110_ = v_suppressElabErrors_1122_;
v___y_1111_ = v_toCold_1118_;
v___y_1112_ = v_diag_1121_;
v___y_1113_ = v_ref_1120_;
goto v___jp_1108_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___redArg___boxed(lean_object* v_x_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_){
_start:
{
lean_object* v_res_1146_; 
v_res_1146_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___redArg(v_x_1141_, v___y_1142_, v___y_1143_, v___y_1144_);
lean_dec(v___y_1144_);
lean_dec_ref(v___y_1143_);
lean_dec(v___y_1142_);
return v_res_1146_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_1147_, lean_object* v_x_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_){
_start:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___x_1152_ = lean_apply_1(v_x_1148_, lean_box(0));
v___x_1153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1153_, 0, v___x_1152_);
return v___x_1153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_1154_, lean_object* v_x_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_){
_start:
{
lean_object* v_res_1159_; 
v_res_1159_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__0(v_00_u03b1_1154_, v_x_1155_, v___y_1156_, v___y_1157_);
lean_dec(v___y_1157_);
lean_dec_ref(v___y_1156_);
return v_res_1159_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___redArg(lean_object* v_a_1160_, lean_object* v_x_1161_){
_start:
{
if (lean_obj_tag(v_x_1161_) == 0)
{
uint8_t v___x_1162_; 
v___x_1162_ = 0;
return v___x_1162_;
}
else
{
lean_object* v_key_1163_; lean_object* v_tail_1164_; uint8_t v___x_1165_; 
v_key_1163_ = lean_ctor_get(v_x_1161_, 0);
v_tail_1164_ = lean_ctor_get(v_x_1161_, 2);
v___x_1165_ = l_Lean_ExprStructEq_beq(v_key_1163_, v_a_1160_);
if (v___x_1165_ == 0)
{
v_x_1161_ = v_tail_1164_;
goto _start;
}
else
{
return v___x_1165_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___redArg___boxed(lean_object* v_a_1167_, lean_object* v_x_1168_){
_start:
{
uint8_t v_res_1169_; lean_object* v_r_1170_; 
v_res_1169_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___redArg(v_a_1167_, v_x_1168_);
lean_dec(v_x_1168_);
lean_dec_ref(v_a_1167_);
v_r_1170_ = lean_box(v_res_1169_);
return v_r_1170_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(lean_object* v_x_1171_, lean_object* v_x_1172_){
_start:
{
if (lean_obj_tag(v_x_1172_) == 0)
{
return v_x_1171_;
}
else
{
lean_object* v_key_1173_; lean_object* v_value_1174_; lean_object* v_tail_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1198_; 
v_key_1173_ = lean_ctor_get(v_x_1172_, 0);
v_value_1174_ = lean_ctor_get(v_x_1172_, 1);
v_tail_1175_ = lean_ctor_get(v_x_1172_, 2);
v_isSharedCheck_1198_ = !lean_is_exclusive(v_x_1172_);
if (v_isSharedCheck_1198_ == 0)
{
v___x_1177_ = v_x_1172_;
v_isShared_1178_ = v_isSharedCheck_1198_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_tail_1175_);
lean_inc(v_value_1174_);
lean_inc(v_key_1173_);
lean_dec(v_x_1172_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1198_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v___x_1179_; uint64_t v___x_1180_; uint64_t v___x_1181_; uint64_t v___x_1182_; uint64_t v_fold_1183_; uint64_t v___x_1184_; uint64_t v___x_1185_; uint64_t v___x_1186_; size_t v___x_1187_; size_t v___x_1188_; size_t v___x_1189_; size_t v___x_1190_; size_t v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1194_; 
v___x_1179_ = lean_array_get_size(v_x_1171_);
v___x_1180_ = l_Lean_ExprStructEq_hash(v_key_1173_);
v___x_1181_ = 32ULL;
v___x_1182_ = lean_uint64_shift_right(v___x_1180_, v___x_1181_);
v_fold_1183_ = lean_uint64_xor(v___x_1180_, v___x_1182_);
v___x_1184_ = 16ULL;
v___x_1185_ = lean_uint64_shift_right(v_fold_1183_, v___x_1184_);
v___x_1186_ = lean_uint64_xor(v_fold_1183_, v___x_1185_);
v___x_1187_ = lean_uint64_to_usize(v___x_1186_);
v___x_1188_ = lean_usize_of_nat(v___x_1179_);
v___x_1189_ = ((size_t)1ULL);
v___x_1190_ = lean_usize_sub(v___x_1188_, v___x_1189_);
v___x_1191_ = lean_usize_land(v___x_1187_, v___x_1190_);
v___x_1192_ = lean_array_uget_borrowed(v_x_1171_, v___x_1191_);
lean_inc(v___x_1192_);
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 2, v___x_1192_);
v___x_1194_ = v___x_1177_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v_key_1173_);
lean_ctor_set(v_reuseFailAlloc_1197_, 1, v_value_1174_);
lean_ctor_set(v_reuseFailAlloc_1197_, 2, v___x_1192_);
v___x_1194_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
lean_object* v___x_1195_; 
v___x_1195_ = lean_array_uset(v_x_1171_, v___x_1191_, v___x_1194_);
v_x_1171_ = v___x_1195_;
v_x_1172_ = v_tail_1175_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(lean_object* v_i_1199_, lean_object* v_source_1200_, lean_object* v_target_1201_){
_start:
{
lean_object* v___x_1202_; uint8_t v___x_1203_; 
v___x_1202_ = lean_array_get_size(v_source_1200_);
v___x_1203_ = lean_nat_dec_lt(v_i_1199_, v___x_1202_);
if (v___x_1203_ == 0)
{
lean_dec_ref(v_source_1200_);
lean_dec(v_i_1199_);
return v_target_1201_;
}
else
{
lean_object* v_es_1204_; lean_object* v___x_1205_; lean_object* v_source_1206_; lean_object* v_target_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; 
v_es_1204_ = lean_array_fget(v_source_1200_, v_i_1199_);
v___x_1205_ = lean_box(0);
v_source_1206_ = lean_array_fset(v_source_1200_, v_i_1199_, v___x_1205_);
v_target_1207_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_target_1201_, v_es_1204_);
v___x_1208_ = lean_unsigned_to_nat(1u);
v___x_1209_ = lean_nat_add(v_i_1199_, v___x_1208_);
lean_dec(v_i_1199_);
v_i_1199_ = v___x_1209_;
v_source_1200_ = v_source_1206_;
v_target_1201_ = v_target_1207_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11___redArg(lean_object* v_data_1211_){
_start:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v_nbuckets_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1212_ = lean_array_get_size(v_data_1211_);
v___x_1213_ = lean_unsigned_to_nat(2u);
v_nbuckets_1214_ = lean_nat_mul(v___x_1212_, v___x_1213_);
v___x_1215_ = lean_unsigned_to_nat(0u);
v___x_1216_ = lean_box(0);
v___x_1217_ = lean_mk_array(v_nbuckets_1214_, v___x_1216_);
v___x_1218_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v___x_1215_, v_data_1211_, v___x_1217_);
return v___x_1218_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__12___redArg(lean_object* v_a_1219_, lean_object* v_b_1220_, lean_object* v_x_1221_){
_start:
{
if (lean_obj_tag(v_x_1221_) == 0)
{
lean_dec(v_b_1220_);
lean_dec_ref(v_a_1219_);
return v_x_1221_;
}
else
{
lean_object* v_key_1222_; lean_object* v_value_1223_; lean_object* v_tail_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1236_; 
v_key_1222_ = lean_ctor_get(v_x_1221_, 0);
v_value_1223_ = lean_ctor_get(v_x_1221_, 1);
v_tail_1224_ = lean_ctor_get(v_x_1221_, 2);
v_isSharedCheck_1236_ = !lean_is_exclusive(v_x_1221_);
if (v_isSharedCheck_1236_ == 0)
{
v___x_1226_ = v_x_1221_;
v_isShared_1227_ = v_isSharedCheck_1236_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_tail_1224_);
lean_inc(v_value_1223_);
lean_inc(v_key_1222_);
lean_dec(v_x_1221_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1236_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
uint8_t v___x_1228_; 
v___x_1228_ = l_Lean_ExprStructEq_beq(v_key_1222_, v_a_1219_);
if (v___x_1228_ == 0)
{
lean_object* v___x_1229_; lean_object* v___x_1231_; 
v___x_1229_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__12___redArg(v_a_1219_, v_b_1220_, v_tail_1224_);
if (v_isShared_1227_ == 0)
{
lean_ctor_set(v___x_1226_, 2, v___x_1229_);
v___x_1231_ = v___x_1226_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v_key_1222_);
lean_ctor_set(v_reuseFailAlloc_1232_, 1, v_value_1223_);
lean_ctor_set(v_reuseFailAlloc_1232_, 2, v___x_1229_);
v___x_1231_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
return v___x_1231_;
}
}
else
{
lean_object* v___x_1234_; 
lean_dec(v_value_1223_);
lean_dec(v_key_1222_);
if (v_isShared_1227_ == 0)
{
lean_ctor_set(v___x_1226_, 1, v_b_1220_);
lean_ctor_set(v___x_1226_, 0, v_a_1219_);
v___x_1234_ = v___x_1226_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v_a_1219_);
lean_ctor_set(v_reuseFailAlloc_1235_, 1, v_b_1220_);
lean_ctor_set(v_reuseFailAlloc_1235_, 2, v_tail_1224_);
v___x_1234_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
return v___x_1234_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6___redArg(lean_object* v_m_1237_, lean_object* v_a_1238_, lean_object* v_b_1239_){
_start:
{
lean_object* v_size_1240_; lean_object* v_buckets_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1284_; 
v_size_1240_ = lean_ctor_get(v_m_1237_, 0);
v_buckets_1241_ = lean_ctor_get(v_m_1237_, 1);
v_isSharedCheck_1284_ = !lean_is_exclusive(v_m_1237_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1243_ = v_m_1237_;
v_isShared_1244_ = v_isSharedCheck_1284_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_buckets_1241_);
lean_inc(v_size_1240_);
lean_dec(v_m_1237_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1284_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v___x_1245_; uint64_t v___x_1246_; uint64_t v___x_1247_; uint64_t v___x_1248_; uint64_t v_fold_1249_; uint64_t v___x_1250_; uint64_t v___x_1251_; uint64_t v___x_1252_; size_t v___x_1253_; size_t v___x_1254_; size_t v___x_1255_; size_t v___x_1256_; size_t v___x_1257_; lean_object* v_bkt_1258_; uint8_t v___x_1259_; 
v___x_1245_ = lean_array_get_size(v_buckets_1241_);
v___x_1246_ = l_Lean_ExprStructEq_hash(v_a_1238_);
v___x_1247_ = 32ULL;
v___x_1248_ = lean_uint64_shift_right(v___x_1246_, v___x_1247_);
v_fold_1249_ = lean_uint64_xor(v___x_1246_, v___x_1248_);
v___x_1250_ = 16ULL;
v___x_1251_ = lean_uint64_shift_right(v_fold_1249_, v___x_1250_);
v___x_1252_ = lean_uint64_xor(v_fold_1249_, v___x_1251_);
v___x_1253_ = lean_uint64_to_usize(v___x_1252_);
v___x_1254_ = lean_usize_of_nat(v___x_1245_);
v___x_1255_ = ((size_t)1ULL);
v___x_1256_ = lean_usize_sub(v___x_1254_, v___x_1255_);
v___x_1257_ = lean_usize_land(v___x_1253_, v___x_1256_);
v_bkt_1258_ = lean_array_uget_borrowed(v_buckets_1241_, v___x_1257_);
v___x_1259_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___redArg(v_a_1238_, v_bkt_1258_);
if (v___x_1259_ == 0)
{
lean_object* v___x_1260_; lean_object* v_size_x27_1261_; lean_object* v___x_1262_; lean_object* v_buckets_x27_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; uint8_t v___x_1269_; 
v___x_1260_ = lean_unsigned_to_nat(1u);
v_size_x27_1261_ = lean_nat_add(v_size_1240_, v___x_1260_);
lean_dec(v_size_1240_);
lean_inc(v_bkt_1258_);
v___x_1262_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1262_, 0, v_a_1238_);
lean_ctor_set(v___x_1262_, 1, v_b_1239_);
lean_ctor_set(v___x_1262_, 2, v_bkt_1258_);
v_buckets_x27_1263_ = lean_array_uset(v_buckets_1241_, v___x_1257_, v___x_1262_);
v___x_1264_ = lean_unsigned_to_nat(4u);
v___x_1265_ = lean_nat_mul(v_size_x27_1261_, v___x_1264_);
v___x_1266_ = lean_unsigned_to_nat(3u);
v___x_1267_ = lean_nat_div(v___x_1265_, v___x_1266_);
lean_dec(v___x_1265_);
v___x_1268_ = lean_array_get_size(v_buckets_x27_1263_);
v___x_1269_ = lean_nat_dec_le(v___x_1267_, v___x_1268_);
lean_dec(v___x_1267_);
if (v___x_1269_ == 0)
{
lean_object* v_val_1270_; lean_object* v___x_1272_; 
v_val_1270_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11___redArg(v_buckets_x27_1263_);
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 1, v_val_1270_);
lean_ctor_set(v___x_1243_, 0, v_size_x27_1261_);
v___x_1272_ = v___x_1243_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_size_x27_1261_);
lean_ctor_set(v_reuseFailAlloc_1273_, 1, v_val_1270_);
v___x_1272_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
return v___x_1272_;
}
}
else
{
lean_object* v___x_1275_; 
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 1, v_buckets_x27_1263_);
lean_ctor_set(v___x_1243_, 0, v_size_x27_1261_);
v___x_1275_ = v___x_1243_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v_size_x27_1261_);
lean_ctor_set(v_reuseFailAlloc_1276_, 1, v_buckets_x27_1263_);
v___x_1275_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
return v___x_1275_;
}
}
}
else
{
lean_object* v___x_1277_; lean_object* v_buckets_x27_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1282_; 
lean_inc(v_bkt_1258_);
v___x_1277_ = lean_box(0);
v_buckets_x27_1278_ = lean_array_uset(v_buckets_1241_, v___x_1257_, v___x_1277_);
v___x_1279_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__12___redArg(v_a_1238_, v_b_1239_, v_bkt_1258_);
v___x_1280_ = lean_array_uset(v_buckets_x27_1278_, v___x_1257_, v___x_1279_);
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 1, v___x_1280_);
v___x_1282_ = v___x_1243_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v_size_1240_);
lean_ctor_set(v_reuseFailAlloc_1283_, 1, v___x_1280_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__2(lean_object* v_a_1285_, lean_object* v_e_1286_, lean_object* v_a_1287_){
_start:
{
lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1289_ = lean_st_ref_take(v_a_1285_);
v___x_1290_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6___redArg(v___x_1289_, v_e_1286_, v_a_1287_);
v___x_1291_ = lean_st_ref_put(v_a_1285_, v___x_1290_);
v___x_1292_ = lean_box(0);
return v___x_1292_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__2___boxed(lean_object* v_a_1293_, lean_object* v_e_1294_, lean_object* v_a_1295_, lean_object* v___y_1296_){
_start:
{
lean_object* v_res_1297_; 
v_res_1297_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__2(v_a_1293_, v_e_1294_, v_a_1295_);
lean_dec(v_a_1293_);
return v_res_1297_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___redArg(lean_object* v_a_1298_, lean_object* v_x_1299_){
_start:
{
if (lean_obj_tag(v_x_1299_) == 0)
{
lean_object* v___x_1300_; 
v___x_1300_ = lean_box(0);
return v___x_1300_;
}
else
{
lean_object* v_key_1301_; lean_object* v_value_1302_; lean_object* v_tail_1303_; uint8_t v___x_1304_; 
v_key_1301_ = lean_ctor_get(v_x_1299_, 0);
v_value_1302_ = lean_ctor_get(v_x_1299_, 1);
v_tail_1303_ = lean_ctor_get(v_x_1299_, 2);
v___x_1304_ = l_Lean_ExprStructEq_beq(v_key_1301_, v_a_1298_);
if (v___x_1304_ == 0)
{
v_x_1299_ = v_tail_1303_;
goto _start;
}
else
{
lean_object* v___x_1306_; 
lean_inc(v_value_1302_);
v___x_1306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1306_, 0, v_value_1302_);
return v___x_1306_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___redArg___boxed(lean_object* v_a_1307_, lean_object* v_x_1308_){
_start:
{
lean_object* v_res_1309_; 
v_res_1309_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___redArg(v_a_1307_, v_x_1308_);
lean_dec(v_x_1308_);
lean_dec_ref(v_a_1307_);
return v_res_1309_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg(lean_object* v_m_1310_, lean_object* v_a_1311_){
_start:
{
lean_object* v_buckets_1312_; lean_object* v___x_1313_; uint64_t v___x_1314_; uint64_t v___x_1315_; uint64_t v___x_1316_; uint64_t v_fold_1317_; uint64_t v___x_1318_; uint64_t v___x_1319_; uint64_t v___x_1320_; size_t v___x_1321_; size_t v___x_1322_; size_t v___x_1323_; size_t v___x_1324_; size_t v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; 
v_buckets_1312_ = lean_ctor_get(v_m_1310_, 1);
v___x_1313_ = lean_array_get_size(v_buckets_1312_);
v___x_1314_ = l_Lean_ExprStructEq_hash(v_a_1311_);
v___x_1315_ = 32ULL;
v___x_1316_ = lean_uint64_shift_right(v___x_1314_, v___x_1315_);
v_fold_1317_ = lean_uint64_xor(v___x_1314_, v___x_1316_);
v___x_1318_ = 16ULL;
v___x_1319_ = lean_uint64_shift_right(v_fold_1317_, v___x_1318_);
v___x_1320_ = lean_uint64_xor(v_fold_1317_, v___x_1319_);
v___x_1321_ = lean_uint64_to_usize(v___x_1320_);
v___x_1322_ = lean_usize_of_nat(v___x_1313_);
v___x_1323_ = ((size_t)1ULL);
v___x_1324_ = lean_usize_sub(v___x_1322_, v___x_1323_);
v___x_1325_ = lean_usize_land(v___x_1321_, v___x_1324_);
v___x_1326_ = lean_array_uget_borrowed(v_buckets_1312_, v___x_1325_);
v___x_1327_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___redArg(v_a_1311_, v___x_1326_);
return v___x_1327_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_m_1328_, lean_object* v_a_1329_){
_start:
{
lean_object* v_res_1330_; 
v_res_1330_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg(v_m_1328_, v_a_1329_);
lean_dec_ref(v_a_1329_);
lean_dec_ref(v_m_1328_);
return v_res_1330_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1(lean_object* v_pre_1331_, lean_object* v_post_1332_, size_t v_sz_1333_, size_t v_i_1334_, lean_object* v_bs_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_){
_start:
{
uint8_t v___x_1340_; 
v___x_1340_ = lean_usize_dec_lt(v_i_1334_, v_sz_1333_);
if (v___x_1340_ == 0)
{
lean_object* v___x_1341_; 
lean_dec_ref(v_post_1332_);
lean_dec_ref(v_pre_1331_);
v___x_1341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1341_, 0, v_bs_1335_);
return v___x_1341_;
}
else
{
lean_object* v_v_1342_; lean_object* v___x_1343_; 
v_v_1342_ = lean_array_uget_borrowed(v_bs_1335_, v_i_1334_);
lean_inc(v_v_1342_);
lean_inc_ref(v_post_1332_);
lean_inc_ref(v_pre_1331_);
v___x_1343_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1331_, v_post_1332_, v_v_1342_, v___y_1336_, v___y_1337_, v___y_1338_);
if (lean_obj_tag(v___x_1343_) == 0)
{
lean_object* v_a_1344_; lean_object* v___x_1345_; lean_object* v_bs_x27_1346_; size_t v___x_1347_; size_t v___x_1348_; lean_object* v___x_1349_; 
v_a_1344_ = lean_ctor_get(v___x_1343_, 0);
lean_inc(v_a_1344_);
lean_dec_ref_known(v___x_1343_, 1);
v___x_1345_ = lean_unsigned_to_nat(0u);
v_bs_x27_1346_ = lean_array_uset(v_bs_1335_, v_i_1334_, v___x_1345_);
v___x_1347_ = ((size_t)1ULL);
v___x_1348_ = lean_usize_add(v_i_1334_, v___x_1347_);
v___x_1349_ = lean_array_uset(v_bs_x27_1346_, v_i_1334_, v_a_1344_);
v_i_1334_ = v___x_1348_;
v_bs_1335_ = v___x_1349_;
goto _start;
}
else
{
lean_object* v_a_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1358_; 
lean_dec_ref(v_bs_1335_);
lean_dec_ref(v_post_1332_);
lean_dec_ref(v_pre_1331_);
v_a_1351_ = lean_ctor_get(v___x_1343_, 0);
v_isSharedCheck_1358_ = !lean_is_exclusive(v___x_1343_);
if (v_isSharedCheck_1358_ == 0)
{
v___x_1353_ = v___x_1343_;
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_a_1351_);
lean_dec(v___x_1343_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v___x_1356_; 
if (v_isShared_1354_ == 0)
{
v___x_1356_ = v___x_1353_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_a_1351_);
v___x_1356_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
return v___x_1356_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__4(lean_object* v_pre_1359_, lean_object* v_post_1360_, lean_object* v_x_1361_, lean_object* v_x_1362_, lean_object* v_x_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_){
_start:
{
if (lean_obj_tag(v_x_1361_) == 5)
{
lean_object* v_fn_1368_; lean_object* v_arg_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; 
v_fn_1368_ = lean_ctor_get(v_x_1361_, 0);
lean_inc_ref(v_fn_1368_);
v_arg_1369_ = lean_ctor_get(v_x_1361_, 1);
lean_inc_ref(v_arg_1369_);
lean_dec_ref_known(v_x_1361_, 2);
v___x_1370_ = lean_array_set(v_x_1362_, v_x_1363_, v_arg_1369_);
v___x_1371_ = lean_unsigned_to_nat(1u);
v___x_1372_ = lean_nat_sub(v_x_1363_, v___x_1371_);
lean_dec(v_x_1363_);
v_x_1361_ = v_fn_1368_;
v_x_1362_ = v___x_1370_;
v_x_1363_ = v___x_1372_;
goto _start;
}
else
{
lean_object* v___x_1374_; 
lean_dec(v_x_1363_);
lean_inc_ref(v_post_1360_);
lean_inc_ref(v_pre_1359_);
v___x_1374_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1359_, v_post_1360_, v_x_1361_, v___y_1364_, v___y_1365_, v___y_1366_);
if (lean_obj_tag(v___x_1374_) == 0)
{
lean_object* v_a_1375_; size_t v_sz_1376_; size_t v___x_1377_; lean_object* v___x_1378_; 
v_a_1375_ = lean_ctor_get(v___x_1374_, 0);
lean_inc(v_a_1375_);
lean_dec_ref_known(v___x_1374_, 1);
v_sz_1376_ = lean_array_size(v_x_1362_);
v___x_1377_ = ((size_t)0ULL);
lean_inc_ref(v_post_1360_);
lean_inc_ref(v_pre_1359_);
v___x_1378_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1(v_pre_1359_, v_post_1360_, v_sz_1376_, v___x_1377_, v_x_1362_, v___y_1364_, v___y_1365_, v___y_1366_);
if (lean_obj_tag(v___x_1378_) == 0)
{
lean_object* v_a_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; 
v_a_1379_ = lean_ctor_get(v___x_1378_, 0);
lean_inc(v_a_1379_);
lean_dec_ref_known(v___x_1378_, 1);
v___x_1380_ = l_Lean_mkAppN(v_a_1375_, v_a_1379_);
lean_dec(v_a_1379_);
v___x_1381_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1359_, v_post_1360_, v___x_1380_, v___y_1364_, v___y_1365_, v___y_1366_);
return v___x_1381_;
}
else
{
lean_object* v_a_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1389_; 
lean_dec(v_a_1375_);
lean_dec_ref(v_post_1360_);
lean_dec_ref(v_pre_1359_);
v_a_1382_ = lean_ctor_get(v___x_1378_, 0);
v_isSharedCheck_1389_ = !lean_is_exclusive(v___x_1378_);
if (v_isSharedCheck_1389_ == 0)
{
v___x_1384_ = v___x_1378_;
v_isShared_1385_ = v_isSharedCheck_1389_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_a_1382_);
lean_dec(v___x_1378_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1389_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v___x_1387_; 
if (v_isShared_1385_ == 0)
{
v___x_1387_ = v___x_1384_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v_a_1382_);
v___x_1387_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
return v___x_1387_;
}
}
}
}
else
{
lean_dec_ref(v_x_1362_);
lean_dec_ref(v_post_1360_);
lean_dec_ref(v_pre_1359_);
return v___x_1374_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__1(lean_object* v___x_1390_, lean_object* v_pre_1391_, lean_object* v_e_1392_, lean_object* v_post_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_){
_start:
{
lean_object* v___x_1398_; 
v___x_1398_ = l_Lean_Core_checkSystem(v___x_1390_, v___y_1395_, v___y_1396_);
if (lean_obj_tag(v___x_1398_) == 0)
{
lean_object* v___x_1399_; 
lean_dec_ref_known(v___x_1398_, 1);
lean_inc_ref(v_pre_1391_);
lean_inc(v___y_1396_);
lean_inc_ref(v___y_1395_);
lean_inc_ref(v_e_1392_);
v___x_1399_ = lean_apply_4(v_pre_1391_, v_e_1392_, v___y_1395_, v___y_1396_, lean_box(0));
if (lean_obj_tag(v___x_1399_) == 0)
{
lean_object* v_a_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1515_; 
v_a_1400_ = lean_ctor_get(v___x_1399_, 0);
v_isSharedCheck_1515_ = !lean_is_exclusive(v___x_1399_);
if (v_isSharedCheck_1515_ == 0)
{
v___x_1402_ = v___x_1399_;
v_isShared_1403_ = v_isSharedCheck_1515_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_a_1400_);
lean_dec(v___x_1399_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1515_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v___y_1405_; 
switch(lean_obj_tag(v_a_1400_))
{
case 0:
{
lean_object* v_e_1505_; lean_object* v___x_1507_; 
lean_dec_ref(v_post_1393_);
lean_dec_ref(v_e_1392_);
lean_dec_ref(v_pre_1391_);
v_e_1505_ = lean_ctor_get(v_a_1400_, 0);
lean_inc_ref(v_e_1505_);
lean_dec_ref_known(v_a_1400_, 1);
if (v_isShared_1403_ == 0)
{
lean_ctor_set(v___x_1402_, 0, v_e_1505_);
v___x_1507_ = v___x_1402_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v_e_1505_);
v___x_1507_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
return v___x_1507_;
}
}
case 1:
{
lean_object* v_e_1509_; lean_object* v___x_1510_; 
lean_del_object(v___x_1402_);
lean_dec_ref(v_e_1392_);
v_e_1509_ = lean_ctor_get(v_a_1400_, 0);
lean_inc_ref(v_e_1509_);
lean_dec_ref_known(v_a_1400_, 1);
lean_inc_ref(v_post_1393_);
lean_inc_ref(v_pre_1391_);
v___x_1510_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1391_, v_post_1393_, v_e_1509_, v___y_1394_, v___y_1395_, v___y_1396_);
if (lean_obj_tag(v___x_1510_) == 0)
{
lean_object* v_a_1511_; lean_object* v___x_1512_; 
v_a_1511_ = lean_ctor_get(v___x_1510_, 0);
lean_inc(v_a_1511_);
lean_dec_ref_known(v___x_1510_, 1);
v___x_1512_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1391_, v_post_1393_, v_a_1511_, v___y_1394_, v___y_1395_, v___y_1396_);
return v___x_1512_;
}
else
{
lean_dec_ref(v_post_1393_);
lean_dec_ref(v_pre_1391_);
return v___x_1510_;
}
}
default: 
{
lean_object* v_e_x3f_1513_; 
lean_del_object(v___x_1402_);
v_e_x3f_1513_ = lean_ctor_get(v_a_1400_, 0);
lean_inc(v_e_x3f_1513_);
lean_dec_ref_known(v_a_1400_, 1);
if (lean_obj_tag(v_e_x3f_1513_) == 0)
{
v___y_1405_ = v_e_1392_;
goto v___jp_1404_;
}
else
{
lean_object* v_val_1514_; 
lean_dec_ref(v_e_1392_);
v_val_1514_ = lean_ctor_get(v_e_x3f_1513_, 0);
lean_inc(v_val_1514_);
lean_dec_ref_known(v_e_x3f_1513_, 1);
v___y_1405_ = v_val_1514_;
goto v___jp_1404_;
}
}
}
v___jp_1404_:
{
switch(lean_obj_tag(v___y_1405_))
{
case 7:
{
lean_object* v_binderName_1406_; lean_object* v_binderType_1407_; lean_object* v_body_1408_; uint8_t v_binderInfo_1409_; lean_object* v___x_1410_; 
v_binderName_1406_ = lean_ctor_get(v___y_1405_, 0);
v_binderType_1407_ = lean_ctor_get(v___y_1405_, 1);
v_body_1408_ = lean_ctor_get(v___y_1405_, 2);
v_binderInfo_1409_ = lean_ctor_get_uint8(v___y_1405_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1407_);
lean_inc_ref(v_post_1393_);
lean_inc_ref(v_pre_1391_);
v___x_1410_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1391_, v_post_1393_, v_binderType_1407_, v___y_1394_, v___y_1395_, v___y_1396_);
if (lean_obj_tag(v___x_1410_) == 0)
{
lean_object* v_a_1411_; lean_object* v___x_1412_; 
v_a_1411_ = lean_ctor_get(v___x_1410_, 0);
lean_inc(v_a_1411_);
lean_dec_ref_known(v___x_1410_, 1);
lean_inc_ref(v_body_1408_);
lean_inc_ref(v_post_1393_);
lean_inc_ref(v_pre_1391_);
v___x_1412_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1391_, v_post_1393_, v_body_1408_, v___y_1394_, v___y_1395_, v___y_1396_);
if (lean_obj_tag(v___x_1412_) == 0)
{
lean_object* v_a_1413_; size_t v___x_1414_; size_t v___x_1415_; uint8_t v___x_1416_; 
v_a_1413_ = lean_ctor_get(v___x_1412_, 0);
lean_inc(v_a_1413_);
lean_dec_ref_known(v___x_1412_, 1);
v___x_1414_ = lean_ptr_addr(v_binderType_1407_);
v___x_1415_ = lean_ptr_addr(v_a_1411_);
v___x_1416_ = lean_usize_dec_eq(v___x_1414_, v___x_1415_);
if (v___x_1416_ == 0)
{
lean_object* v___x_1417_; lean_object* v___x_1418_; 
lean_inc(v_binderName_1406_);
lean_dec_ref_known(v___y_1405_, 3);
v___x_1417_ = l_Lean_Expr_forallE___override(v_binderName_1406_, v_a_1411_, v_a_1413_, v_binderInfo_1409_);
v___x_1418_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1391_, v_post_1393_, v___x_1417_, v___y_1394_, v___y_1395_, v___y_1396_);
return v___x_1418_;
}
else
{
size_t v___x_1419_; size_t v___x_1420_; uint8_t v___x_1421_; 
v___x_1419_ = lean_ptr_addr(v_body_1408_);
v___x_1420_ = lean_ptr_addr(v_a_1413_);
v___x_1421_ = lean_usize_dec_eq(v___x_1419_, v___x_1420_);
if (v___x_1421_ == 0)
{
lean_object* v___x_1422_; lean_object* v___x_1423_; 
lean_inc(v_binderName_1406_);
lean_dec_ref_known(v___y_1405_, 3);
v___x_1422_ = l_Lean_Expr_forallE___override(v_binderName_1406_, v_a_1411_, v_a_1413_, v_binderInfo_1409_);
v___x_1423_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1391_, v_post_1393_, v___x_1422_, v___y_1394_, v___y_1395_, v___y_1396_);
return v___x_1423_;
}
else
{
uint8_t v___x_1424_; 
v___x_1424_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1409_, v_binderInfo_1409_);
if (v___x_1424_ == 0)
{
lean_object* v___x_1425_; lean_object* v___x_1426_; 
lean_inc(v_binderName_1406_);
lean_dec_ref_known(v___y_1405_, 3);
v___x_1425_ = l_Lean_Expr_forallE___override(v_binderName_1406_, v_a_1411_, v_a_1413_, v_binderInfo_1409_);
v___x_1426_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1391_, v_post_1393_, v___x_1425_, v___y_1394_, v___y_1395_, v___y_1396_);
return v___x_1426_;
}
else
{
lean_object* v___x_1427_; 
lean_dec(v_a_1413_);
lean_dec(v_a_1411_);
v___x_1427_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1391_, v_post_1393_, v___y_1405_, v___y_1394_, v___y_1395_, v___y_1396_);
return v___x_1427_;
}
}
}
}
else
{
lean_dec(v_a_1411_);
lean_dec_ref_known(v___y_1405_, 3);
lean_dec_ref(v_post_1393_);
lean_dec_ref(v_pre_1391_);
return v___x_1412_;
}
}
else
{
lean_dec_ref_known(v___y_1405_, 3);
lean_dec_ref(v_post_1393_);
lean_dec_ref(v_pre_1391_);
return v___x_1410_;
}
}
case 6:
{
lean_object* v_binderName_1428_; lean_object* v_binderType_1429_; lean_object* v_body_1430_; uint8_t v_binderInfo_1431_; lean_object* v___x_1432_; 
v_binderName_1428_ = lean_ctor_get(v___y_1405_, 0);
v_binderType_1429_ = lean_ctor_get(v___y_1405_, 1);
v_body_1430_ = lean_ctor_get(v___y_1405_, 2);
v_binderInfo_1431_ = lean_ctor_get_uint8(v___y_1405_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1429_);
lean_inc_ref(v_post_1393_);
lean_inc_ref(v_pre_1391_);
v___x_1432_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1391_, v_post_1393_, v_binderType_1429_, v___y_1394_, v___y_1395_, v___y_1396_);
if (lean_obj_tag(v___x_1432_) == 0)
{
lean_object* v_a_1433_; lean_object* v___x_1434_; 
v_a_1433_ = lean_ctor_get(v___x_1432_, 0);
lean_inc(v_a_1433_);
lean_dec_ref_known(v___x_1432_, 1);
lean_inc_ref(v_body_1430_);
lean_inc_ref(v_post_1393_);
lean_inc_ref(v_pre_1391_);
v___x_1434_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1391_, v_post_1393_, v_body_1430_, v___y_1394_, v___y_1395_, v___y_1396_);
if (lean_obj_tag(v___x_1434_) == 0)
{
lean_object* v_a_1435_; size_t v___x_1436_; size_t v___x_1437_; uint8_t v___x_1438_; 
v_a_1435_ = lean_ctor_get(v___x_1434_, 0);
lean_inc(v_a_1435_);
lean_dec_ref_known(v___x_1434_, 1);
v___x_1436_ = lean_ptr_addr(v_binderType_1429_);
v___x_1437_ = lean_ptr_addr(v_a_1433_);
v___x_1438_ = lean_usize_dec_eq(v___x_1436_, v___x_1437_);
if (v___x_1438_ == 0)
{
lean_object* v___x_1439_; lean_object* v___x_1440_; 
lean_inc(v_binderName_1428_);
lean_dec_ref_known(v___y_1405_, 3);
v___x_1439_ = l_Lean_Expr_lam___override(v_binderName_1428_, v_a_1433_, v_a_1435_, v_binderInfo_1431_);
v___x_1440_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1391_, v_post_1393_, v___x_1439_, v___y_1394_, v___y_1395_, v___y_1396_);
return v___x_1440_;
}
else
{
size_t v___x_1441_; size_t v___x_1442_; uint8_t v___x_1443_; 
v___x_1441_ = lean_ptr_addr(v_body_1430_);
v___x_1442_ = lean_ptr_addr(v_a_1435_);
v___x_1443_ = lean_usize_dec_eq(v___x_1441_, v___x_1442_);
if (v___x_1443_ == 0)
{
lean_object* v___x_1444_; lean_object* v___x_1445_; 
lean_inc(v_binderName_1428_);
lean_dec_ref_known(v___y_1405_, 3);
v___x_1444_ = l_Lean_Expr_lam___override(v_binderName_1428_, v_a_1433_, v_a_1435_, v_binderInfo_1431_);
v___x_1445_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1391_, v_post_1393_, v___x_1444_, v___y_1394_, v___y_1395_, v___y_1396_);
return v___x_1445_;
}
else
{
uint8_t v___x_1446_; 
v___x_1446_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1431_, v_binderInfo_1431_);
if (v___x_1446_ == 0)
{
lean_object* v___x_1447_; lean_object* v___x_1448_; 
lean_inc(v_binderName_1428_);
lean_dec_ref_known(v___y_1405_, 3);
v___x_1447_ = l_Lean_Expr_lam___override(v_binderName_1428_, v_a_1433_, v_a_1435_, v_binderInfo_1431_);
v___x_1448_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1391_, v_post_1393_, v___x_1447_, v___y_1394_, v___y_1395_, v___y_1396_);
return v___x_1448_;
}
else
{
lean_object* v___x_1449_; 
lean_dec(v_a_1435_);
lean_dec(v_a_1433_);
v___x_1449_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1391_, v_post_1393_, v___y_1405_, v___y_1394_, v___y_1395_, v___y_1396_);
return v___x_1449_;
}
}
}
}
else
{
lean_dec(v_a_1433_);
lean_dec_ref_known(v___y_1405_, 3);
lean_dec_ref(v_post_1393_);
lean_dec_ref(v_pre_1391_);
return v___x_1434_;
}
}
else
{
lean_dec_ref_known(v___y_1405_, 3);
lean_dec_ref(v_post_1393_);
lean_dec_ref(v_pre_1391_);
return v___x_1432_;
}
}
case 8:
{
lean_object* v_declName_1450_; lean_object* v_type_1451_; lean_object* v_value_1452_; lean_object* v_body_1453_; uint8_t v_nondep_1454_; lean_object* v___x_1455_; 
v_declName_1450_ = lean_ctor_get(v___y_1405_, 0);
v_type_1451_ = lean_ctor_get(v___y_1405_, 1);
v_value_1452_ = lean_ctor_get(v___y_1405_, 2);
v_body_1453_ = lean_ctor_get(v___y_1405_, 3);
v_nondep_1454_ = lean_ctor_get_uint8(v___y_1405_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_1451_);
lean_inc_ref(v_post_1393_);
lean_inc_ref(v_pre_1391_);
v___x_1455_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1391_, v_post_1393_, v_type_1451_, v___y_1394_, v___y_1395_, v___y_1396_);
if (lean_obj_tag(v___x_1455_) == 0)
{
lean_object* v_a_1456_; lean_object* v___x_1457_; 
v_a_1456_ = lean_ctor_get(v___x_1455_, 0);
lean_inc(v_a_1456_);
lean_dec_ref_known(v___x_1455_, 1);
lean_inc_ref(v_value_1452_);
lean_inc_ref(v_post_1393_);
lean_inc_ref(v_pre_1391_);
v___x_1457_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1391_, v_post_1393_, v_value_1452_, v___y_1394_, v___y_1395_, v___y_1396_);
if (lean_obj_tag(v___x_1457_) == 0)
{
lean_object* v_a_1458_; lean_object* v___x_1459_; 
v_a_1458_ = lean_ctor_get(v___x_1457_, 0);
lean_inc(v_a_1458_);
lean_dec_ref_known(v___x_1457_, 1);
lean_inc_ref(v_body_1453_);
lean_inc_ref(v_post_1393_);
lean_inc_ref(v_pre_1391_);
v___x_1459_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1391_, v_post_1393_, v_body_1453_, v___y_1394_, v___y_1395_, v___y_1396_);
if (lean_obj_tag(v___x_1459_) == 0)
{
lean_object* v_a_1460_; size_t v___x_1461_; size_t v___x_1462_; uint8_t v___x_1463_; 
v_a_1460_ = lean_ctor_get(v___x_1459_, 0);
lean_inc(v_a_1460_);
lean_dec_ref_known(v___x_1459_, 1);
v___x_1461_ = lean_ptr_addr(v_type_1451_);
v___x_1462_ = lean_ptr_addr(v_a_1456_);
v___x_1463_ = lean_usize_dec_eq(v___x_1461_, v___x_1462_);
if (v___x_1463_ == 0)
{
lean_object* v___x_1464_; lean_object* v___x_1465_; 
lean_inc(v_declName_1450_);
lean_dec_ref_known(v___y_1405_, 4);
v___x_1464_ = l_Lean_Expr_letE___override(v_declName_1450_, v_a_1456_, v_a_1458_, v_a_1460_, v_nondep_1454_);
v___x_1465_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1391_, v_post_1393_, v___x_1464_, v___y_1394_, v___y_1395_, v___y_1396_);
return v___x_1465_;
}
else
{
size_t v___x_1466_; size_t v___x_1467_; uint8_t v___x_1468_; 
v___x_1466_ = lean_ptr_addr(v_value_1452_);
v___x_1467_ = lean_ptr_addr(v_a_1458_);
v___x_1468_ = lean_usize_dec_eq(v___x_1466_, v___x_1467_);
if (v___x_1468_ == 0)
{
lean_object* v___x_1469_; lean_object* v___x_1470_; 
lean_inc(v_declName_1450_);
lean_dec_ref_known(v___y_1405_, 4);
v___x_1469_ = l_Lean_Expr_letE___override(v_declName_1450_, v_a_1456_, v_a_1458_, v_a_1460_, v_nondep_1454_);
v___x_1470_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1391_, v_post_1393_, v___x_1469_, v___y_1394_, v___y_1395_, v___y_1396_);
return v___x_1470_;
}
else
{
size_t v___x_1471_; size_t v___x_1472_; uint8_t v___x_1473_; 
v___x_1471_ = lean_ptr_addr(v_body_1453_);
v___x_1472_ = lean_ptr_addr(v_a_1460_);
v___x_1473_ = lean_usize_dec_eq(v___x_1471_, v___x_1472_);
if (v___x_1473_ == 0)
{
lean_object* v___x_1474_; lean_object* v___x_1475_; 
lean_inc(v_declName_1450_);
lean_dec_ref_known(v___y_1405_, 4);
v___x_1474_ = l_Lean_Expr_letE___override(v_declName_1450_, v_a_1456_, v_a_1458_, v_a_1460_, v_nondep_1454_);
v___x_1475_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1391_, v_post_1393_, v___x_1474_, v___y_1394_, v___y_1395_, v___y_1396_);
return v___x_1475_;
}
else
{
lean_object* v___x_1476_; 
lean_dec(v_a_1460_);
lean_dec(v_a_1458_);
lean_dec(v_a_1456_);
v___x_1476_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1391_, v_post_1393_, v___y_1405_, v___y_1394_, v___y_1395_, v___y_1396_);
return v___x_1476_;
}
}
}
}
else
{
lean_dec(v_a_1458_);
lean_dec(v_a_1456_);
lean_dec_ref_known(v___y_1405_, 4);
lean_dec_ref(v_post_1393_);
lean_dec_ref(v_pre_1391_);
return v___x_1459_;
}
}
else
{
lean_dec(v_a_1456_);
lean_dec_ref_known(v___y_1405_, 4);
lean_dec_ref(v_post_1393_);
lean_dec_ref(v_pre_1391_);
return v___x_1457_;
}
}
else
{
lean_dec_ref_known(v___y_1405_, 4);
lean_dec_ref(v_post_1393_);
lean_dec_ref(v_pre_1391_);
return v___x_1455_;
}
}
case 5:
{
lean_object* v_dummy_1477_; lean_object* v_nargs_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; 
v_dummy_1477_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_1478_ = l_Lean_Expr_getAppNumArgs(v___y_1405_);
lean_inc(v_nargs_1478_);
v___x_1479_ = lean_mk_array(v_nargs_1478_, v_dummy_1477_);
v___x_1480_ = lean_unsigned_to_nat(1u);
v___x_1481_ = lean_nat_sub(v_nargs_1478_, v___x_1480_);
lean_dec(v_nargs_1478_);
v___x_1482_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__4(v_pre_1391_, v_post_1393_, v___y_1405_, v___x_1479_, v___x_1481_, v___y_1394_, v___y_1395_, v___y_1396_);
return v___x_1482_;
}
case 10:
{
lean_object* v_data_1483_; lean_object* v_expr_1484_; lean_object* v___x_1485_; 
v_data_1483_ = lean_ctor_get(v___y_1405_, 0);
v_expr_1484_ = lean_ctor_get(v___y_1405_, 1);
lean_inc_ref(v_expr_1484_);
lean_inc_ref(v_post_1393_);
lean_inc_ref(v_pre_1391_);
v___x_1485_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1391_, v_post_1393_, v_expr_1484_, v___y_1394_, v___y_1395_, v___y_1396_);
if (lean_obj_tag(v___x_1485_) == 0)
{
lean_object* v_a_1486_; size_t v___x_1487_; size_t v___x_1488_; uint8_t v___x_1489_; 
v_a_1486_ = lean_ctor_get(v___x_1485_, 0);
lean_inc(v_a_1486_);
lean_dec_ref_known(v___x_1485_, 1);
v___x_1487_ = lean_ptr_addr(v_expr_1484_);
v___x_1488_ = lean_ptr_addr(v_a_1486_);
v___x_1489_ = lean_usize_dec_eq(v___x_1487_, v___x_1488_);
if (v___x_1489_ == 0)
{
lean_object* v___x_1490_; lean_object* v___x_1491_; 
lean_inc(v_data_1483_);
lean_dec_ref_known(v___y_1405_, 2);
v___x_1490_ = l_Lean_Expr_mdata___override(v_data_1483_, v_a_1486_);
v___x_1491_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1391_, v_post_1393_, v___x_1490_, v___y_1394_, v___y_1395_, v___y_1396_);
return v___x_1491_;
}
else
{
lean_object* v___x_1492_; 
lean_dec(v_a_1486_);
v___x_1492_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1391_, v_post_1393_, v___y_1405_, v___y_1394_, v___y_1395_, v___y_1396_);
return v___x_1492_;
}
}
else
{
lean_dec_ref_known(v___y_1405_, 2);
lean_dec_ref(v_post_1393_);
lean_dec_ref(v_pre_1391_);
return v___x_1485_;
}
}
case 11:
{
lean_object* v_typeName_1493_; lean_object* v_idx_1494_; lean_object* v_struct_1495_; lean_object* v___x_1496_; 
v_typeName_1493_ = lean_ctor_get(v___y_1405_, 0);
v_idx_1494_ = lean_ctor_get(v___y_1405_, 1);
v_struct_1495_ = lean_ctor_get(v___y_1405_, 2);
lean_inc_ref(v_struct_1495_);
lean_inc_ref(v_post_1393_);
lean_inc_ref(v_pre_1391_);
v___x_1496_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1391_, v_post_1393_, v_struct_1495_, v___y_1394_, v___y_1395_, v___y_1396_);
if (lean_obj_tag(v___x_1496_) == 0)
{
lean_object* v_a_1497_; size_t v___x_1498_; size_t v___x_1499_; uint8_t v___x_1500_; 
v_a_1497_ = lean_ctor_get(v___x_1496_, 0);
lean_inc(v_a_1497_);
lean_dec_ref_known(v___x_1496_, 1);
v___x_1498_ = lean_ptr_addr(v_struct_1495_);
v___x_1499_ = lean_ptr_addr(v_a_1497_);
v___x_1500_ = lean_usize_dec_eq(v___x_1498_, v___x_1499_);
if (v___x_1500_ == 0)
{
lean_object* v___x_1501_; lean_object* v___x_1502_; 
lean_inc(v_idx_1494_);
lean_inc(v_typeName_1493_);
lean_dec_ref_known(v___y_1405_, 3);
v___x_1501_ = l_Lean_Expr_proj___override(v_typeName_1493_, v_idx_1494_, v_a_1497_);
v___x_1502_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1391_, v_post_1393_, v___x_1501_, v___y_1394_, v___y_1395_, v___y_1396_);
return v___x_1502_;
}
else
{
lean_object* v___x_1503_; 
lean_dec(v_a_1497_);
v___x_1503_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1391_, v_post_1393_, v___y_1405_, v___y_1394_, v___y_1395_, v___y_1396_);
return v___x_1503_;
}
}
else
{
lean_dec_ref_known(v___y_1405_, 3);
lean_dec_ref(v_post_1393_);
lean_dec_ref(v_pre_1391_);
return v___x_1496_;
}
}
default: 
{
lean_object* v___x_1504_; 
v___x_1504_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1391_, v_post_1393_, v___y_1405_, v___y_1394_, v___y_1395_, v___y_1396_);
return v___x_1504_;
}
}
}
}
}
else
{
lean_object* v_a_1516_; lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1523_; 
lean_dec_ref(v_post_1393_);
lean_dec_ref(v_e_1392_);
lean_dec_ref(v_pre_1391_);
v_a_1516_ = lean_ctor_get(v___x_1399_, 0);
v_isSharedCheck_1523_ = !lean_is_exclusive(v___x_1399_);
if (v_isSharedCheck_1523_ == 0)
{
v___x_1518_ = v___x_1399_;
v_isShared_1519_ = v_isSharedCheck_1523_;
goto v_resetjp_1517_;
}
else
{
lean_inc(v_a_1516_);
lean_dec(v___x_1399_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1523_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
lean_object* v___x_1521_; 
if (v_isShared_1519_ == 0)
{
v___x_1521_ = v___x_1518_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v_a_1516_);
v___x_1521_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
return v___x_1521_;
}
}
}
}
else
{
lean_object* v_a_1524_; lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1531_; 
lean_dec_ref(v_post_1393_);
lean_dec_ref(v_e_1392_);
lean_dec_ref(v_pre_1391_);
v_a_1524_ = lean_ctor_get(v___x_1398_, 0);
v_isSharedCheck_1531_ = !lean_is_exclusive(v___x_1398_);
if (v_isSharedCheck_1531_ == 0)
{
v___x_1526_ = v___x_1398_;
v_isShared_1527_ = v_isSharedCheck_1531_;
goto v_resetjp_1525_;
}
else
{
lean_inc(v_a_1524_);
lean_dec(v___x_1398_);
v___x_1526_ = lean_box(0);
v_isShared_1527_ = v_isSharedCheck_1531_;
goto v_resetjp_1525_;
}
v_resetjp_1525_:
{
lean_object* v___x_1529_; 
if (v_isShared_1527_ == 0)
{
v___x_1529_ = v___x_1526_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v_a_1524_);
v___x_1529_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
return v___x_1529_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__1___boxed(lean_object* v___x_1532_, lean_object* v_pre_1533_, lean_object* v_e_1534_, lean_object* v_post_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_){
_start:
{
lean_object* v_res_1540_; 
v_res_1540_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__1(v___x_1532_, v_pre_1533_, v_e_1534_, v_post_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
lean_dec(v___y_1538_);
lean_dec_ref(v___y_1537_);
lean_dec(v___y_1536_);
return v_res_1540_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(lean_object* v_pre_1541_, lean_object* v_post_1542_, lean_object* v_e_1543_, lean_object* v_a_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_){
_start:
{
lean_object* v___x_1548_; lean_object* v___x_1549_; 
lean_inc(v_a_1544_);
v___x_1548_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1548_, 0, lean_box(0));
lean_closure_set(v___x_1548_, 1, lean_box(0));
lean_closure_set(v___x_1548_, 2, v_a_1544_);
v___x_1549_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__0(lean_box(0), v___x_1548_, v___y_1545_, v___y_1546_);
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_object* v_a_1550_; lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1581_; 
v_a_1550_ = lean_ctor_get(v___x_1549_, 0);
v_isSharedCheck_1581_ = !lean_is_exclusive(v___x_1549_);
if (v_isSharedCheck_1581_ == 0)
{
v___x_1552_ = v___x_1549_;
v_isShared_1553_ = v_isSharedCheck_1581_;
goto v_resetjp_1551_;
}
else
{
lean_inc(v_a_1550_);
lean_dec(v___x_1549_);
v___x_1552_ = lean_box(0);
v_isShared_1553_ = v_isSharedCheck_1581_;
goto v_resetjp_1551_;
}
v_resetjp_1551_:
{
lean_object* v___x_1554_; 
v___x_1554_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg(v_a_1550_, v_e_1543_);
lean_dec(v_a_1550_);
if (lean_obj_tag(v___x_1554_) == 0)
{
lean_object* v___x_1555_; lean_object* v___f_1556_; lean_object* v___x_1557_; 
lean_del_object(v___x_1552_);
v___x_1555_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__19___closed__0));
lean_inc_ref(v_e_1543_);
v___f_1556_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__1___boxed), 8, 4);
lean_closure_set(v___f_1556_, 0, v___x_1555_);
lean_closure_set(v___f_1556_, 1, v_pre_1541_);
lean_closure_set(v___f_1556_, 2, v_e_1543_);
lean_closure_set(v___f_1556_, 3, v_post_1542_);
v___x_1557_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___redArg(v___f_1556_, v_a_1544_, v___y_1545_, v___y_1546_);
if (lean_obj_tag(v___x_1557_) == 0)
{
lean_object* v_a_1558_; lean_object* v___f_1559_; lean_object* v___x_1560_; 
v_a_1558_ = lean_ctor_get(v___x_1557_, 0);
lean_inc_n(v_a_1558_, 2);
lean_dec_ref_known(v___x_1557_, 1);
lean_inc(v_a_1544_);
v___f_1559_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1559_, 0, v_a_1544_);
lean_closure_set(v___f_1559_, 1, v_e_1543_);
lean_closure_set(v___f_1559_, 2, v_a_1558_);
v___x_1560_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__0(lean_box(0), v___f_1559_, v___y_1545_, v___y_1546_);
if (lean_obj_tag(v___x_1560_) == 0)
{
lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1567_; 
v_isSharedCheck_1567_ = !lean_is_exclusive(v___x_1560_);
if (v_isSharedCheck_1567_ == 0)
{
lean_object* v_unused_1568_; 
v_unused_1568_ = lean_ctor_get(v___x_1560_, 0);
lean_dec(v_unused_1568_);
v___x_1562_ = v___x_1560_;
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
else
{
lean_dec(v___x_1560_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___x_1565_; 
if (v_isShared_1563_ == 0)
{
lean_ctor_set(v___x_1562_, 0, v_a_1558_);
v___x_1565_ = v___x_1562_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v_a_1558_);
v___x_1565_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
return v___x_1565_;
}
}
}
else
{
lean_object* v_a_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1576_; 
lean_dec(v_a_1558_);
v_a_1569_ = lean_ctor_get(v___x_1560_, 0);
v_isSharedCheck_1576_ = !lean_is_exclusive(v___x_1560_);
if (v_isSharedCheck_1576_ == 0)
{
v___x_1571_ = v___x_1560_;
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_a_1569_);
lean_dec(v___x_1560_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v___x_1574_; 
if (v_isShared_1572_ == 0)
{
v___x_1574_ = v___x_1571_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v_a_1569_);
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
else
{
lean_dec_ref(v_e_1543_);
return v___x_1557_;
}
}
else
{
lean_object* v_val_1577_; lean_object* v___x_1579_; 
lean_dec_ref(v_e_1543_);
lean_dec_ref(v_post_1542_);
lean_dec_ref(v_pre_1541_);
v_val_1577_ = lean_ctor_get(v___x_1554_, 0);
lean_inc(v_val_1577_);
lean_dec_ref_known(v___x_1554_, 1);
if (v_isShared_1553_ == 0)
{
lean_ctor_set(v___x_1552_, 0, v_val_1577_);
v___x_1579_ = v___x_1552_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v_val_1577_);
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
else
{
lean_object* v_a_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1589_; 
lean_dec_ref(v_e_1543_);
lean_dec_ref(v_post_1542_);
lean_dec_ref(v_pre_1541_);
v_a_1582_ = lean_ctor_get(v___x_1549_, 0);
v_isSharedCheck_1589_ = !lean_is_exclusive(v___x_1549_);
if (v_isSharedCheck_1589_ == 0)
{
v___x_1584_ = v___x_1549_;
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_a_1582_);
lean_dec(v___x_1549_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v___x_1587_; 
if (v_isShared_1585_ == 0)
{
v___x_1587_ = v___x_1584_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v_a_1582_);
v___x_1587_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
return v___x_1587_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(lean_object* v_pre_1590_, lean_object* v_post_1591_, lean_object* v_e_1592_, lean_object* v_a_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_){
_start:
{
lean_object* v___x_1597_; 
lean_inc_ref(v_post_1591_);
lean_inc(v___y_1595_);
lean_inc_ref(v___y_1594_);
lean_inc_ref(v_e_1592_);
v___x_1597_ = lean_apply_4(v_post_1591_, v_e_1592_, v___y_1594_, v___y_1595_, lean_box(0));
if (lean_obj_tag(v___x_1597_) == 0)
{
lean_object* v_a_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1616_; 
v_a_1598_ = lean_ctor_get(v___x_1597_, 0);
v_isSharedCheck_1616_ = !lean_is_exclusive(v___x_1597_);
if (v_isSharedCheck_1616_ == 0)
{
v___x_1600_ = v___x_1597_;
v_isShared_1601_ = v_isSharedCheck_1616_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_a_1598_);
lean_dec(v___x_1597_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1616_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
switch(lean_obj_tag(v_a_1598_))
{
case 0:
{
lean_object* v_e_1602_; lean_object* v___x_1604_; 
lean_dec_ref(v_e_1592_);
lean_dec_ref(v_post_1591_);
lean_dec_ref(v_pre_1590_);
v_e_1602_ = lean_ctor_get(v_a_1598_, 0);
lean_inc_ref(v_e_1602_);
lean_dec_ref_known(v_a_1598_, 1);
if (v_isShared_1601_ == 0)
{
lean_ctor_set(v___x_1600_, 0, v_e_1602_);
v___x_1604_ = v___x_1600_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_e_1602_);
v___x_1604_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
return v___x_1604_;
}
}
case 1:
{
lean_object* v_e_1606_; lean_object* v___x_1607_; 
lean_del_object(v___x_1600_);
lean_dec_ref(v_e_1592_);
v_e_1606_ = lean_ctor_get(v_a_1598_, 0);
lean_inc_ref(v_e_1606_);
lean_dec_ref_known(v_a_1598_, 1);
v___x_1607_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1590_, v_post_1591_, v_e_1606_, v_a_1593_, v___y_1594_, v___y_1595_);
return v___x_1607_;
}
default: 
{
lean_object* v_e_x3f_1608_; 
lean_dec_ref(v_post_1591_);
lean_dec_ref(v_pre_1590_);
v_e_x3f_1608_ = lean_ctor_get(v_a_1598_, 0);
lean_inc(v_e_x3f_1608_);
lean_dec_ref_known(v_a_1598_, 1);
if (lean_obj_tag(v_e_x3f_1608_) == 0)
{
lean_object* v___x_1610_; 
if (v_isShared_1601_ == 0)
{
lean_ctor_set(v___x_1600_, 0, v_e_1592_);
v___x_1610_ = v___x_1600_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v_e_1592_);
v___x_1610_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
return v___x_1610_;
}
}
else
{
lean_object* v_val_1612_; lean_object* v___x_1614_; 
lean_dec_ref(v_e_1592_);
v_val_1612_ = lean_ctor_get(v_e_x3f_1608_, 0);
lean_inc(v_val_1612_);
lean_dec_ref_known(v_e_x3f_1608_, 1);
if (v_isShared_1601_ == 0)
{
lean_ctor_set(v___x_1600_, 0, v_val_1612_);
v___x_1614_ = v___x_1600_;
goto v_reusejp_1613_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v_val_1612_);
v___x_1614_ = v_reuseFailAlloc_1615_;
goto v_reusejp_1613_;
}
v_reusejp_1613_:
{
return v___x_1614_;
}
}
}
}
}
}
else
{
lean_object* v_a_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1624_; 
lean_dec_ref(v_e_1592_);
lean_dec_ref(v_post_1591_);
lean_dec_ref(v_pre_1590_);
v_a_1617_ = lean_ctor_get(v___x_1597_, 0);
v_isSharedCheck_1624_ = !lean_is_exclusive(v___x_1597_);
if (v_isSharedCheck_1624_ == 0)
{
v___x_1619_ = v___x_1597_;
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_a_1617_);
lean_dec(v___x_1597_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v___x_1622_; 
if (v_isShared_1620_ == 0)
{
v___x_1622_ = v___x_1619_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v_a_1617_);
v___x_1622_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
return v___x_1622_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_1625_, lean_object* v_post_1626_, lean_object* v_e_1627_, lean_object* v_a_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_){
_start:
{
lean_object* v_res_1632_; 
v_res_1632_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1625_, v_post_1626_, v_e_1627_, v_a_1628_, v___y_1629_, v___y_1630_);
lean_dec(v___y_1630_);
lean_dec_ref(v___y_1629_);
lean_dec(v_a_1628_);
return v_res_1632_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_1633_, lean_object* v_post_1634_, lean_object* v_sz_1635_, lean_object* v_i_1636_, lean_object* v_bs_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_){
_start:
{
size_t v_sz_boxed_1642_; size_t v_i_boxed_1643_; lean_object* v_res_1644_; 
v_sz_boxed_1642_ = lean_unbox_usize(v_sz_1635_);
lean_dec(v_sz_1635_);
v_i_boxed_1643_ = lean_unbox_usize(v_i_1636_);
lean_dec(v_i_1636_);
v_res_1644_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1(v_pre_1633_, v_post_1634_, v_sz_boxed_1642_, v_i_boxed_1643_, v_bs_1637_, v___y_1638_, v___y_1639_, v___y_1640_);
lean_dec(v___y_1640_);
lean_dec_ref(v___y_1639_);
lean_dec(v___y_1638_);
return v_res_1644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__4___boxed(lean_object* v_pre_1645_, lean_object* v_post_1646_, lean_object* v_x_1647_, lean_object* v_x_1648_, lean_object* v_x_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_){
_start:
{
lean_object* v_res_1654_; 
v_res_1654_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__4(v_pre_1645_, v_post_1646_, v_x_1647_, v_x_1648_, v_x_1649_, v___y_1650_, v___y_1651_, v___y_1652_);
lean_dec(v___y_1652_);
lean_dec_ref(v___y_1651_);
lean_dec(v___y_1650_);
return v_res_1654_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___boxed(lean_object* v_pre_1655_, lean_object* v_post_1656_, lean_object* v_e_1657_, lean_object* v_a_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_){
_start:
{
lean_object* v_res_1662_; 
v_res_1662_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1655_, v_post_1656_, v_e_1657_, v_a_1658_, v___y_1659_, v___y_1660_);
lean_dec(v___y_1660_);
lean_dec_ref(v___y_1659_);
lean_dec(v_a_1658_);
return v_res_1662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___lam__0(lean_object* v_00_u03b1_1663_, lean_object* v_x_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_){
_start:
{
lean_object* v___x_1668_; lean_object* v___x_1669_; 
v___x_1668_ = lean_apply_1(v_x_1664_, lean_box(0));
v___x_1669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1669_, 0, v___x_1668_);
return v___x_1669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___lam__0___boxed(lean_object* v_00_u03b1_1670_, lean_object* v_x_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_){
_start:
{
lean_object* v_res_1675_; 
v_res_1675_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___lam__0(v_00_u03b1_1670_, v_x_1671_, v___y_1672_, v___y_1673_);
lean_dec(v___y_1673_);
lean_dec_ref(v___y_1672_);
return v_res_1675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(lean_object* v_input_1676_, lean_object* v_pre_1677_, lean_object* v_post_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_){
_start:
{
lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v_a_1684_; lean_object* v___x_1685_; 
v___x_1682_ = lean_obj_once(&l_Lean_Core_transform___redArg___closed__2, &l_Lean_Core_transform___redArg___closed__2_once, _init_l_Lean_Core_transform___redArg___closed__2);
v___x_1683_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___lam__0(lean_box(0), v___x_1682_, v___y_1679_, v___y_1680_);
v_a_1684_ = lean_ctor_get(v___x_1683_, 0);
lean_inc(v_a_1684_);
lean_dec_ref(v___x_1683_);
v___x_1685_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1677_, v_post_1678_, v_input_1676_, v_a_1684_, v___y_1679_, v___y_1680_);
if (lean_obj_tag(v___x_1685_) == 0)
{
lean_object* v_a_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1695_; 
v_a_1686_ = lean_ctor_get(v___x_1685_, 0);
lean_inc(v_a_1686_);
lean_dec_ref_known(v___x_1685_, 1);
v___x_1687_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1687_, 0, lean_box(0));
lean_closure_set(v___x_1687_, 1, lean_box(0));
lean_closure_set(v___x_1687_, 2, v_a_1684_);
v___x_1688_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___lam__0(lean_box(0), v___x_1687_, v___y_1679_, v___y_1680_);
v_isSharedCheck_1695_ = !lean_is_exclusive(v___x_1688_);
if (v_isSharedCheck_1695_ == 0)
{
lean_object* v_unused_1696_; 
v_unused_1696_ = lean_ctor_get(v___x_1688_, 0);
lean_dec(v_unused_1696_);
v___x_1690_ = v___x_1688_;
v_isShared_1691_ = v_isSharedCheck_1695_;
goto v_resetjp_1689_;
}
else
{
lean_dec(v___x_1688_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1695_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
lean_object* v___x_1693_; 
if (v_isShared_1691_ == 0)
{
lean_ctor_set(v___x_1690_, 0, v_a_1686_);
v___x_1693_ = v___x_1690_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v_a_1686_);
v___x_1693_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
return v___x_1693_;
}
}
}
else
{
lean_dec(v_a_1684_);
return v___x_1685_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___boxed(lean_object* v_input_1697_, lean_object* v_pre_1698_, lean_object* v_post_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_){
_start:
{
lean_object* v_res_1703_; 
v_res_1703_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_input_1697_, v_pre_1698_, v_post_1699_, v___y_1700_, v___y_1701_);
lean_dec(v___y_1701_);
lean_dec_ref(v___y_1700_);
return v_res_1703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_betaReduce(lean_object* v_e_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_){
_start:
{
lean_object* v___f_1710_; lean_object* v___f_1711_; lean_object* v___x_1712_; 
v___f_1710_ = ((lean_object*)(l_Lean_Core_betaReduce___closed__0));
v___f_1711_ = ((lean_object*)(l_Lean_Core_betaReduce___closed__1));
v___x_1712_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_1706_, v___f_1710_, v___f_1711_, v_a_1707_, v_a_1708_);
return v___x_1712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_betaReduce___boxed(lean_object* v_e_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_){
_start:
{
lean_object* v_res_1717_; 
v_res_1717_ = l_Lean_Core_betaReduce(v_e_1713_, v_a_1714_, v_a_1715_);
lean_dec(v_a_1715_);
lean_dec_ref(v_a_1714_);
return v_res_1717_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_1718_, lean_object* v_m_1719_, lean_object* v_a_1720_){
_start:
{
lean_object* v___x_1721_; 
v___x_1721_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg(v_m_1719_, v_a_1720_);
return v___x_1721_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_1722_, lean_object* v_m_1723_, lean_object* v_a_1724_){
_start:
{
lean_object* v_res_1725_; 
v_res_1725_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3(v_00_u03b2_1722_, v_m_1723_, v_a_1724_);
lean_dec_ref(v_a_1724_);
lean_dec_ref(v_m_1723_);
return v_res_1725_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_1726_, lean_object* v_ref_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_){
_start:
{
lean_object* v___x_1731_; 
v___x_1731_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_1727_);
return v___x_1731_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1732_, lean_object* v_ref_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_){
_start:
{
lean_object* v_res_1737_; 
v_res_1737_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_1732_, v_ref_1733_, v___y_1734_, v___y_1735_);
lean_dec(v___y_1735_);
lean_dec_ref(v___y_1734_);
return v_res_1737_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8(lean_object* v_00_u03b1_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_){
_start:
{
lean_object* v___x_1742_; 
v___x_1742_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___redArg();
return v___x_1742_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___boxed(lean_object* v_00_u03b1_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_){
_start:
{
lean_object* v_res_1747_; 
v_res_1747_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8(v_00_u03b1_1743_, v___y_1744_, v___y_1745_);
lean_dec(v___y_1745_);
lean_dec_ref(v___y_1744_);
return v_res_1747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5(lean_object* v_00_u03b1_1748_, lean_object* v_x_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_){
_start:
{
lean_object* v___x_1754_; 
v___x_1754_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___redArg(v_x_1749_, v___y_1750_, v___y_1751_, v___y_1752_);
return v___x_1754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b1_1755_, lean_object* v_x_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_){
_start:
{
lean_object* v_res_1761_; 
v_res_1761_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5(v_00_u03b1_1755_, v_x_1756_, v___y_1757_, v___y_1758_, v___y_1759_);
lean_dec(v___y_1759_);
lean_dec_ref(v___y_1758_);
lean_dec(v___y_1757_);
return v_res_1761_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6(lean_object* v_00_u03b2_1762_, lean_object* v_m_1763_, lean_object* v_a_1764_, lean_object* v_b_1765_){
_start:
{
lean_object* v___x_1766_; 
v___x_1766_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6___redArg(v_m_1763_, v_a_1764_, v_b_1765_);
return v___x_1766_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4(lean_object* v_00_u03b2_1767_, lean_object* v_a_1768_, lean_object* v_x_1769_){
_start:
{
lean_object* v___x_1770_; 
v___x_1770_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___redArg(v_a_1768_, v_x_1769_);
return v___x_1770_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___boxed(lean_object* v_00_u03b2_1771_, lean_object* v_a_1772_, lean_object* v_x_1773_){
_start:
{
lean_object* v_res_1774_; 
v_res_1774_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4(v_00_u03b2_1771_, v_a_1772_, v_x_1773_);
lean_dec(v_x_1773_);
lean_dec_ref(v_a_1772_);
return v_res_1774_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10(lean_object* v_00_u03b2_1775_, lean_object* v_a_1776_, lean_object* v_x_1777_){
_start:
{
uint8_t v___x_1778_; 
v___x_1778_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___redArg(v_a_1776_, v_x_1777_);
return v___x_1778_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___boxed(lean_object* v_00_u03b2_1779_, lean_object* v_a_1780_, lean_object* v_x_1781_){
_start:
{
uint8_t v_res_1782_; lean_object* v_r_1783_; 
v_res_1782_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10(v_00_u03b2_1779_, v_a_1780_, v_x_1781_);
lean_dec(v_x_1781_);
lean_dec_ref(v_a_1780_);
v_r_1783_ = lean_box(v_res_1782_);
return v_r_1783_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11(lean_object* v_00_u03b2_1784_, lean_object* v_data_1785_){
_start:
{
lean_object* v___x_1786_; 
v___x_1786_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11___redArg(v_data_1785_);
return v___x_1786_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__12(lean_object* v_00_u03b2_1787_, lean_object* v_a_1788_, lean_object* v_b_1789_, lean_object* v_x_1790_){
_start:
{
lean_object* v___x_1791_; 
v___x_1791_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__12___redArg(v_a_1788_, v_b_1789_, v_x_1790_);
return v___x_1791_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12(lean_object* v_00_u03b2_1792_, lean_object* v_i_1793_, lean_object* v_source_1794_, lean_object* v_target_1795_){
_start:
{
lean_object* v___x_1796_; 
v___x_1796_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v_i_1793_, v_source_1794_, v_target_1795_);
return v___x_1796_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13(lean_object* v_00_u03b2_1797_, lean_object* v_x_1798_, lean_object* v_x_1799_){
_start:
{
lean_object* v___x_1800_; 
v___x_1800_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_x_1798_, v_x_1799_);
return v___x_1800_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__0(lean_object* v_toApplicative_1801_, lean_object* v_a_1802_){
_start:
{
lean_object* v_toPure_1803_; lean_object* v___x_1804_; 
v_toPure_1803_ = lean_ctor_get(v_toApplicative_1801_, 1);
lean_inc(v_toPure_1803_);
lean_dec_ref(v_toApplicative_1801_);
v___x_1804_ = lean_apply_2(v_toPure_1803_, lean_box(0), v_a_1802_);
return v___x_1804_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__13(lean_object* v___x_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_){
_start:
{
lean_object* v___x_1811_; 
v___x_1811_ = l_Lean_Core_checkSystem(v___x_1805_, v___y_1808_, v___y_1809_);
return v___x_1811_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__13___boxed(lean_object* v___x_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_){
_start:
{
lean_object* v_res_1818_; 
v_res_1818_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__13(v___x_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_);
lean_dec(v___y_1816_);
lean_dec_ref(v___y_1815_);
lean_dec(v___y_1814_);
lean_dec_ref(v___y_1813_);
return v_res_1818_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14(lean_object* v_inst_1821_, lean_object* v_x_1822_, lean_object* v___x_1823_, lean_object* v___x_1824_, lean_object* v_inst_1825_, lean_object* v___f_1826_, lean_object* v___x_1827_, lean_object* v___x_1828_, lean_object* v_a_1829_, lean_object* v_toBind_1830_, lean_object* v___f_1831_, lean_object* v_toApplicative_1832_, lean_object* v_a_1833_){
_start:
{
if (lean_obj_tag(v_a_1833_) == 0)
{
lean_object* v___f_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_3407__overap_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; 
lean_dec_ref(v_toApplicative_1832_);
v___f_1834_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14___closed__0));
v___x_1835_ = lean_apply_2(v_inst_1821_, lean_box(0), v___f_1834_);
lean_inc_ref(v___x_1824_);
lean_inc_ref(v___x_1823_);
v___x_1836_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonadLift___aux__1___boxed), 10, 9);
lean_closure_set(v___x_1836_, 0, lean_box(0));
lean_closure_set(v___x_1836_, 1, lean_box(0));
lean_closure_set(v___x_1836_, 2, lean_box(0));
lean_closure_set(v___x_1836_, 3, lean_box(0));
lean_closure_set(v___x_1836_, 4, v_x_1822_);
lean_closure_set(v___x_1836_, 5, v___x_1823_);
lean_closure_set(v___x_1836_, 6, v___x_1824_);
lean_closure_set(v___x_1836_, 7, lean_box(0));
lean_closure_set(v___x_1836_, 8, v___x_1835_);
v___x_1837_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonad___aux__13___boxed), 13, 12);
lean_closure_set(v___x_1837_, 0, lean_box(0));
lean_closure_set(v___x_1837_, 1, lean_box(0));
lean_closure_set(v___x_1837_, 2, lean_box(0));
lean_closure_set(v___x_1837_, 3, lean_box(0));
lean_closure_set(v___x_1837_, 4, v_x_1822_);
lean_closure_set(v___x_1837_, 5, v___x_1823_);
lean_closure_set(v___x_1837_, 6, v___x_1824_);
lean_closure_set(v___x_1837_, 7, v_inst_1825_);
lean_closure_set(v___x_1837_, 8, lean_box(0));
lean_closure_set(v___x_1837_, 9, lean_box(0));
lean_closure_set(v___x_1837_, 10, v___x_1836_);
lean_closure_set(v___x_1837_, 11, v___f_1826_);
v___x_3407__overap_1838_ = l_Lean_Meta_withIncRecDepth___redArg(v___x_1827_, v___x_1828_, v___x_1837_);
lean_inc(v_a_1829_);
v___x_1839_ = lean_apply_1(v___x_3407__overap_1838_, v_a_1829_);
v___x_1840_ = lean_apply_4(v_toBind_1830_, lean_box(0), lean_box(0), v___x_1839_, v___f_1831_);
return v___x_1840_;
}
else
{
lean_object* v_val_1841_; lean_object* v_toPure_1842_; lean_object* v___x_1843_; 
lean_dec(v___f_1831_);
lean_dec(v_toBind_1830_);
lean_dec_ref(v___x_1828_);
lean_dec_ref(v___x_1827_);
lean_dec(v___f_1826_);
lean_dec_ref(v_inst_1825_);
lean_dec_ref(v___x_1824_);
lean_dec_ref(v___x_1823_);
lean_dec(v_inst_1821_);
v_val_1841_ = lean_ctor_get(v_a_1833_, 0);
lean_inc(v_val_1841_);
lean_dec_ref_known(v_a_1833_, 1);
v_toPure_1842_ = lean_ctor_get(v_toApplicative_1832_, 1);
lean_inc(v_toPure_1842_);
lean_dec_ref(v_toApplicative_1832_);
v___x_1843_ = lean_apply_2(v_toPure_1842_, lean_box(0), v_val_1841_);
return v___x_1843_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14___boxed(lean_object* v_inst_1844_, lean_object* v_x_1845_, lean_object* v___x_1846_, lean_object* v___x_1847_, lean_object* v_inst_1848_, lean_object* v___f_1849_, lean_object* v___x_1850_, lean_object* v___x_1851_, lean_object* v_a_1852_, lean_object* v_toBind_1853_, lean_object* v___f_1854_, lean_object* v_toApplicative_1855_, lean_object* v_a_1856_){
_start:
{
lean_object* v_res_1857_; 
v_res_1857_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14(v_inst_1844_, v_x_1845_, v___x_1846_, v___x_1847_, v_inst_1848_, v___f_1849_, v___x_1850_, v___x_1851_, v_a_1852_, v_toBind_1853_, v___f_1854_, v_toApplicative_1855_, v_a_1856_);
lean_dec(v_a_1852_);
return v_res_1857_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__1(lean_object* v___x_1858_, lean_object* v___x_1859_, lean_object* v_declName_1860_, lean_object* v_a_1861_, lean_object* v___f_1862_, uint8_t v_nondep_1863_, lean_object* v_a_1864_, lean_object* v_a_1865_){
_start:
{
uint8_t v___x_1866_; lean_object* v___x_3426__overap_1867_; lean_object* v___x_1868_; 
v___x_1866_ = 0;
v___x_3426__overap_1867_ = l_Lean_Meta_withLetDecl___redArg(v___x_1858_, v___x_1859_, v_declName_1860_, v_a_1861_, v_a_1865_, v___f_1862_, v_nondep_1863_, v___x_1866_);
lean_inc(v_a_1864_);
v___x_1868_ = lean_apply_1(v___x_3426__overap_1867_, v_a_1864_);
return v___x_1868_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__1___boxed(lean_object* v___x_1869_, lean_object* v___x_1870_, lean_object* v_declName_1871_, lean_object* v_a_1872_, lean_object* v___f_1873_, lean_object* v_nondep_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_){
_start:
{
uint8_t v_nondep_3605__boxed_1877_; lean_object* v_res_1878_; 
v_nondep_3605__boxed_1877_ = lean_unbox(v_nondep_1874_);
v_res_1878_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__1(v___x_1869_, v___x_1870_, v_declName_1871_, v_a_1872_, v___f_1873_, v_nondep_3605__boxed_1877_, v_a_1875_, v_a_1876_);
lean_dec(v_a_1875_);
return v_res_1878_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__4(lean_object* v_fvars_1879_, uint8_t v_usedLetOnly_1880_, lean_object* v_inst_1881_, lean_object* v_toBind_1882_, lean_object* v___f_1883_, lean_object* v_a_1884_){
_start:
{
uint8_t v___x_1885_; uint8_t v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; 
v___x_1885_ = 0;
v___x_1886_ = 1;
v___x_1887_ = lean_box(v_usedLetOnly_1880_);
v___x_1888_ = lean_box(v___x_1885_);
v___x_1889_ = lean_box(v___x_1886_);
v___x_1890_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLetFVars___boxed), 10, 5);
lean_closure_set(v___x_1890_, 0, v_fvars_1879_);
lean_closure_set(v___x_1890_, 1, v_a_1884_);
lean_closure_set(v___x_1890_, 2, v___x_1887_);
lean_closure_set(v___x_1890_, 3, v___x_1888_);
lean_closure_set(v___x_1890_, 4, v___x_1889_);
v___x_1891_ = lean_apply_2(v_inst_1881_, lean_box(0), v___x_1890_);
v___x_1892_ = lean_apply_4(v_toBind_1882_, lean_box(0), lean_box(0), v___x_1891_, v___f_1883_);
return v___x_1892_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__4___boxed(lean_object* v_fvars_1893_, lean_object* v_usedLetOnly_1894_, lean_object* v_inst_1895_, lean_object* v_toBind_1896_, lean_object* v___f_1897_, lean_object* v_a_1898_){
_start:
{
uint8_t v_usedLetOnly_boxed_1899_; lean_object* v_res_1900_; 
v_usedLetOnly_boxed_1899_ = lean_unbox(v_usedLetOnly_1894_);
v_res_1900_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__4(v_fvars_1893_, v_usedLetOnly_boxed_1899_, v_inst_1895_, v_toBind_1896_, v___f_1897_, v_a_1898_);
return v_res_1900_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__3(lean_object* v_fvars_1901_, uint8_t v_usedLetOnly_1902_, lean_object* v_inst_1903_, lean_object* v_toBind_1904_, lean_object* v___f_1905_, lean_object* v_a_1906_){
_start:
{
uint8_t v___x_1907_; uint8_t v___x_1908_; uint8_t v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; 
v___x_1907_ = 0;
v___x_1908_ = 1;
v___x_1909_ = 1;
v___x_1910_ = lean_box(v___x_1907_);
v___x_1911_ = lean_box(v_usedLetOnly_1902_);
v___x_1912_ = lean_box(v___x_1907_);
v___x_1913_ = lean_box(v___x_1908_);
v___x_1914_ = lean_box(v___x_1909_);
v___x_1915_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(v___x_1915_, 0, v_fvars_1901_);
lean_closure_set(v___x_1915_, 1, v_a_1906_);
lean_closure_set(v___x_1915_, 2, v___x_1910_);
lean_closure_set(v___x_1915_, 3, v___x_1911_);
lean_closure_set(v___x_1915_, 4, v___x_1912_);
lean_closure_set(v___x_1915_, 5, v___x_1913_);
lean_closure_set(v___x_1915_, 6, v___x_1914_);
v___x_1916_ = lean_apply_2(v_inst_1903_, lean_box(0), v___x_1915_);
v___x_1917_ = lean_apply_4(v_toBind_1904_, lean_box(0), lean_box(0), v___x_1916_, v___f_1905_);
return v___x_1917_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__3___boxed(lean_object* v_fvars_1918_, lean_object* v_usedLetOnly_1919_, lean_object* v_inst_1920_, lean_object* v_toBind_1921_, lean_object* v___f_1922_, lean_object* v_a_1923_){
_start:
{
uint8_t v_usedLetOnly_boxed_1924_; lean_object* v_res_1925_; 
v_usedLetOnly_boxed_1924_ = lean_unbox(v_usedLetOnly_1919_);
v_res_1925_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__3(v_fvars_1918_, v_usedLetOnly_boxed_1924_, v_inst_1920_, v_toBind_1921_, v___f_1922_, v_a_1923_);
return v_res_1925_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1(lean_object* v___x_1926_, lean_object* v___x_1927_, lean_object* v_binderName_1928_, uint8_t v_binderInfo_1929_, lean_object* v___f_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_){
_start:
{
uint8_t v___x_1933_; lean_object* v___x_3484__overap_1934_; lean_object* v___x_1935_; 
v___x_1933_ = 0;
v___x_3484__overap_1934_ = l_Lean_Meta_withLocalDecl___redArg(v___x_1926_, v___x_1927_, v_binderName_1928_, v_binderInfo_1929_, v_a_1932_, v___f_1930_, v___x_1933_);
lean_inc(v_a_1931_);
v___x_1935_ = lean_apply_1(v___x_3484__overap_1934_, v_a_1931_);
return v___x_1935_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1___boxed(lean_object* v___x_1936_, lean_object* v___x_1937_, lean_object* v_binderName_1938_, lean_object* v_binderInfo_1939_, lean_object* v___f_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_){
_start:
{
uint8_t v_binderInfo_3673__boxed_1943_; lean_object* v_res_1944_; 
v_binderInfo_3673__boxed_1943_ = lean_unbox(v_binderInfo_1939_);
v_res_1944_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1(v___x_1936_, v___x_1937_, v_binderName_1938_, v_binderInfo_3673__boxed_1943_, v___f_1940_, v_a_1941_, v_a_1942_);
lean_dec(v_a_1941_);
return v_res_1944_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__3(lean_object* v_fvars_1945_, uint8_t v_usedLetOnly_1946_, lean_object* v_inst_1947_, lean_object* v_toBind_1948_, lean_object* v___f_1949_, lean_object* v_a_1950_){
_start:
{
uint8_t v___x_1951_; uint8_t v___x_1952_; uint8_t v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; 
v___x_1951_ = 0;
v___x_1952_ = 1;
v___x_1953_ = 1;
v___x_1954_ = lean_box(v___x_1951_);
v___x_1955_ = lean_box(v_usedLetOnly_1946_);
v___x_1956_ = lean_box(v___x_1952_);
v___x_1957_ = lean_box(v___x_1953_);
v___x_1958_ = lean_alloc_closure((void*)(l_Lean_Meta_mkForallFVars___boxed), 11, 6);
lean_closure_set(v___x_1958_, 0, v_fvars_1945_);
lean_closure_set(v___x_1958_, 1, v_a_1950_);
lean_closure_set(v___x_1958_, 2, v___x_1954_);
lean_closure_set(v___x_1958_, 3, v___x_1955_);
lean_closure_set(v___x_1958_, 4, v___x_1956_);
lean_closure_set(v___x_1958_, 5, v___x_1957_);
v___x_1959_ = lean_apply_2(v_inst_1947_, lean_box(0), v___x_1958_);
v___x_1960_ = lean_apply_4(v_toBind_1948_, lean_box(0), lean_box(0), v___x_1959_, v___f_1949_);
return v___x_1960_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__3___boxed(lean_object* v_fvars_1961_, lean_object* v_usedLetOnly_1962_, lean_object* v_inst_1963_, lean_object* v_toBind_1964_, lean_object* v___f_1965_, lean_object* v_a_1966_){
_start:
{
uint8_t v_usedLetOnly_boxed_1967_; lean_object* v_res_1968_; 
v_usedLetOnly_boxed_1967_ = lean_unbox(v_usedLetOnly_1962_);
v_res_1968_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__3(v_fvars_1961_, v_usedLetOnly_boxed_1967_, v_inst_1963_, v_toBind_1964_, v___f_1965_, v_a_1966_);
return v_res_1968_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__7(lean_object* v___f_1969_, lean_object* v___y_1970_, lean_object* v_a_1971_){
_start:
{
lean_object* v___x_1972_; 
lean_inc(v___y_1970_);
v___x_1972_ = lean_apply_2(v___f_1969_, v_a_1971_, v___y_1970_);
return v___x_1972_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__7___boxed(lean_object* v___f_1973_, lean_object* v___y_1974_, lean_object* v_a_1975_){
_start:
{
lean_object* v_res_1976_; 
v_res_1976_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__7(v___f_1973_, v___y_1974_, v_a_1975_);
lean_dec(v___y_1974_);
return v_res_1976_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1(lean_object* v_toApplicative_1977_, lean_object* v_acc_1978_, lean_object* v_next_1979_, lean_object* v_a_1980_){
_start:
{
lean_object* v_toPure_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; 
v_toPure_1981_ = lean_ctor_get(v_toApplicative_1977_, 1);
lean_inc(v_toPure_1981_);
lean_dec_ref(v_toApplicative_1977_);
v___x_1982_ = lean_array_fset(v_acc_1978_, v_next_1979_, v_a_1980_);
v___x_1983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1983_, 0, v___x_1982_);
v___x_1984_ = lean_apply_2(v_toPure_1981_, lean_box(0), v___x_1983_);
return v___x_1984_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1___boxed(lean_object* v_toApplicative_1985_, lean_object* v_acc_1986_, lean_object* v_next_1987_, lean_object* v_a_1988_){
_start:
{
lean_object* v_res_1989_; 
v_res_1989_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1(v_toApplicative_1985_, v_acc_1986_, v_next_1987_, v_a_1988_);
lean_dec(v_next_1987_);
return v_res_1989_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__2(lean_object* v_toApplicative_1990_, lean_object* v_next_1991_, lean_object* v_G_1992_, lean_object* v___y_1993_, lean_object* v_a_1994_){
_start:
{
if (lean_obj_tag(v_a_1994_) == 0)
{
lean_object* v_a_1995_; lean_object* v_toPure_1996_; lean_object* v___x_1997_; 
lean_dec(v_G_1992_);
v_a_1995_ = lean_ctor_get(v_a_1994_, 0);
lean_inc(v_a_1995_);
lean_dec_ref_known(v_a_1994_, 1);
v_toPure_1996_ = lean_ctor_get(v_toApplicative_1990_, 1);
lean_inc(v_toPure_1996_);
lean_dec_ref(v_toApplicative_1990_);
v___x_1997_ = lean_apply_2(v_toPure_1996_, lean_box(0), v_a_1995_);
return v___x_1997_;
}
else
{
lean_object* v_a_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; 
lean_dec_ref(v_toApplicative_1990_);
v_a_1998_ = lean_ctor_get(v_a_1994_, 0);
lean_inc(v_a_1998_);
lean_dec_ref_known(v_a_1994_, 1);
v___x_1999_ = lean_unsigned_to_nat(1u);
v___x_2000_ = lean_nat_add(v_next_1991_, v___x_1999_);
lean_inc(v___y_1993_);
v___x_2001_ = lean_apply_5(v_G_1992_, v___x_2000_, v_a_1998_, lean_box(0), lean_box(0), v___y_1993_);
return v___x_2001_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__2___boxed(lean_object* v_toApplicative_2002_, lean_object* v_next_2003_, lean_object* v_G_2004_, lean_object* v___y_2005_, lean_object* v_a_2006_){
_start:
{
lean_object* v_res_2007_; 
v_res_2007_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__2(v_toApplicative_2002_, v_next_2003_, v_G_2004_, v___y_2005_, v_a_2006_);
lean_dec(v___y_2005_);
lean_dec(v_next_2003_);
return v_res_2007_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5(lean_object* v_f_2008_, lean_object* v_inst_2009_, lean_object* v_inst_2010_, lean_object* v_inst_2011_, lean_object* v_pre_2012_, lean_object* v_post_2013_, uint8_t v_usedLetOnly_2014_, uint8_t v_skipConstInApp_2015_, uint8_t v_skipInstances_2016_, lean_object* v_x_2017_, lean_object* v_x_2018_, lean_object* v___y_2019_, lean_object* v_a_2020_){
_start:
{
lean_object* v___x_2021_; lean_object* v___x_2022_; 
v___x_2021_ = l_Lean_mkAppN(v_f_2008_, v_a_2020_);
v___x_2022_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2009_, v_inst_2010_, v_inst_2011_, v_pre_2012_, v_post_2013_, v_usedLetOnly_2014_, v_skipConstInApp_2015_, v_skipInstances_2016_, v_x_2017_, v_x_2018_, v___x_2021_, v___y_2019_);
return v___x_2022_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5___boxed(lean_object* v_f_2023_, lean_object* v_inst_2024_, lean_object* v_inst_2025_, lean_object* v_inst_2026_, lean_object* v_pre_2027_, lean_object* v_post_2028_, lean_object* v_usedLetOnly_2029_, lean_object* v_skipConstInApp_2030_, lean_object* v_skipInstances_2031_, lean_object* v_x_2032_, lean_object* v_x_2033_, lean_object* v___y_2034_, lean_object* v_a_2035_){
_start:
{
uint8_t v_usedLetOnly_boxed_2036_; uint8_t v_skipConstInApp_boxed_2037_; uint8_t v_skipInstances_boxed_2038_; lean_object* v_res_2039_; 
v_usedLetOnly_boxed_2036_ = lean_unbox(v_usedLetOnly_2029_);
v_skipConstInApp_boxed_2037_ = lean_unbox(v_skipConstInApp_2030_);
v_skipInstances_boxed_2038_ = lean_unbox(v_skipInstances_2031_);
v_res_2039_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5(v_f_2023_, v_inst_2024_, v_inst_2025_, v_inst_2026_, v_pre_2027_, v_post_2028_, v_usedLetOnly_boxed_2036_, v_skipConstInApp_boxed_2037_, v_skipInstances_boxed_2038_, v_x_2032_, v_x_2033_, v___y_2034_, v_a_2035_);
lean_dec_ref(v_a_2035_);
lean_dec(v___y_2034_);
return v_res_2039_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___boxed(lean_object* v_inst_2040_, lean_object* v_inst_2041_, lean_object* v_inst_2042_, lean_object* v_pre_2043_, lean_object* v_post_2044_, lean_object* v_usedLetOnly_2045_, lean_object* v_skipConstInApp_2046_, lean_object* v_skipInstances_2047_, lean_object* v_x_2048_, lean_object* v_x_2049_, lean_object* v_e_2050_, lean_object* v_a_2051_){
_start:
{
uint8_t v_usedLetOnly_boxed_2052_; uint8_t v_skipConstInApp_boxed_2053_; uint8_t v_skipInstances_boxed_2054_; lean_object* v_res_2055_; 
v_usedLetOnly_boxed_2052_ = lean_unbox(v_usedLetOnly_2045_);
v_skipConstInApp_boxed_2053_ = lean_unbox(v_skipConstInApp_2046_);
v_skipInstances_boxed_2054_ = lean_unbox(v_skipInstances_2047_);
v_res_2055_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2040_, v_inst_2041_, v_inst_2042_, v_pre_2043_, v_post_2044_, v_usedLetOnly_boxed_2052_, v_skipConstInApp_boxed_2053_, v_skipInstances_boxed_2054_, v_x_2048_, v_x_2049_, v_e_2050_, v_a_2051_);
lean_dec(v_a_2051_);
return v_res_2055_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__4(lean_object* v___x_2056_, lean_object* v_toApplicative_2057_, lean_object* v_toBind_2058_, lean_object* v___f_2059_, lean_object* v_paramInfo_2060_, lean_object* v_inst_2061_, lean_object* v_inst_2062_, lean_object* v_inst_2063_, lean_object* v_pre_2064_, lean_object* v_post_2065_, uint8_t v_usedLetOnly_2066_, uint8_t v_skipConstInApp_2067_, uint8_t v_skipInstances_2068_, lean_object* v_x_2069_, lean_object* v_x_2070_, lean_object* v_next_2071_, lean_object* v_acc_2072_, lean_object* v_h_2073_, lean_object* v_G_2074_, lean_object* v___y_2075_){
_start:
{
uint8_t v___x_2076_; 
v___x_2076_ = lean_nat_dec_lt(v_next_2071_, v___x_2056_);
if (v___x_2076_ == 0)
{
lean_object* v_toPure_2077_; lean_object* v___x_2078_; 
lean_dec(v_G_2074_);
lean_dec(v_next_2071_);
lean_dec(v_x_2070_);
lean_dec(v_post_2065_);
lean_dec(v_pre_2064_);
lean_dec_ref(v_inst_2063_);
lean_dec(v_inst_2062_);
lean_dec_ref(v_inst_2061_);
lean_dec(v___f_2059_);
lean_dec(v_toBind_2058_);
v_toPure_2077_ = lean_ctor_get(v_toApplicative_2057_, 1);
lean_inc(v_toPure_2077_);
lean_dec_ref(v_toApplicative_2057_);
v___x_2078_ = lean_apply_2(v_toPure_2077_, lean_box(0), v_acc_2072_);
return v___x_2078_;
}
else
{
lean_object* v___f_2079_; lean_object* v___y_2081_; lean_object* v___x_2084_; lean_object* v___x_2085_; uint8_t v___x_2086_; 
lean_inc(v___y_2075_);
lean_inc(v_next_2071_);
lean_inc_ref(v_toApplicative_2057_);
v___f_2079_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__2___boxed), 5, 4);
lean_closure_set(v___f_2079_, 0, v_toApplicative_2057_);
lean_closure_set(v___f_2079_, 1, v_next_2071_);
lean_closure_set(v___f_2079_, 2, v_G_2074_);
lean_closure_set(v___f_2079_, 3, v___y_2075_);
v___x_2084_ = lean_array_fget_borrowed(v_acc_2072_, v_next_2071_);
v___x_2085_ = lean_array_get_size(v_paramInfo_2060_);
v___x_2086_ = lean_nat_dec_lt(v_next_2071_, v___x_2085_);
if (v___x_2086_ == 0)
{
lean_object* v___f_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; 
lean_inc(v___x_2084_);
v___f_2087_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2087_, 0, v_toApplicative_2057_);
lean_closure_set(v___f_2087_, 1, v_acc_2072_);
lean_closure_set(v___f_2087_, 2, v_next_2071_);
v___x_2088_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2061_, v_inst_2062_, v_inst_2063_, v_pre_2064_, v_post_2065_, v_usedLetOnly_2066_, v_skipConstInApp_2067_, v_skipInstances_2068_, v_x_2069_, v_x_2070_, v___x_2084_, v___y_2075_);
lean_inc(v_toBind_2058_);
v___x_2089_ = lean_apply_4(v_toBind_2058_, lean_box(0), lean_box(0), v___x_2088_, v___f_2087_);
v___y_2081_ = v___x_2089_;
goto v___jp_2080_;
}
else
{
lean_object* v___x_2090_; uint8_t v_isInstance_2091_; 
v___x_2090_ = lean_array_fget_borrowed(v_paramInfo_2060_, v_next_2071_);
v_isInstance_2091_ = lean_ctor_get_uint8(v___x_2090_, sizeof(void*)*1 + 4);
if (v_isInstance_2091_ == 0)
{
lean_object* v___f_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; 
lean_inc(v___x_2084_);
v___f_2092_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2092_, 0, v_toApplicative_2057_);
lean_closure_set(v___f_2092_, 1, v_acc_2072_);
lean_closure_set(v___f_2092_, 2, v_next_2071_);
v___x_2093_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2061_, v_inst_2062_, v_inst_2063_, v_pre_2064_, v_post_2065_, v_usedLetOnly_2066_, v_skipConstInApp_2067_, v_skipInstances_2068_, v_x_2069_, v_x_2070_, v___x_2084_, v___y_2075_);
lean_inc(v_toBind_2058_);
v___x_2094_ = lean_apply_4(v_toBind_2058_, lean_box(0), lean_box(0), v___x_2093_, v___f_2092_);
v___y_2081_ = v___x_2094_;
goto v___jp_2080_;
}
else
{
lean_object* v_toPure_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; 
lean_dec(v_next_2071_);
lean_dec(v_x_2070_);
lean_dec(v_post_2065_);
lean_dec(v_pre_2064_);
lean_dec_ref(v_inst_2063_);
lean_dec(v_inst_2062_);
lean_dec_ref(v_inst_2061_);
v_toPure_2095_ = lean_ctor_get(v_toApplicative_2057_, 1);
lean_inc(v_toPure_2095_);
lean_dec_ref(v_toApplicative_2057_);
v___x_2096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2096_, 0, v_acc_2072_);
v___x_2097_ = lean_apply_2(v_toPure_2095_, lean_box(0), v___x_2096_);
v___y_2081_ = v___x_2097_;
goto v___jp_2080_;
}
}
v___jp_2080_:
{
lean_object* v___x_2082_; lean_object* v___x_2083_; 
lean_inc(v_toBind_2058_);
v___x_2082_ = lean_apply_4(v_toBind_2058_, lean_box(0), lean_box(0), v___y_2081_, v___f_2059_);
v___x_2083_ = lean_apply_4(v_toBind_2058_, lean_box(0), lean_box(0), v___x_2082_, v___f_2079_);
return v___x_2083_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__4___boxed(lean_object** _args){
lean_object* v___x_2098_ = _args[0];
lean_object* v_toApplicative_2099_ = _args[1];
lean_object* v_toBind_2100_ = _args[2];
lean_object* v___f_2101_ = _args[3];
lean_object* v_paramInfo_2102_ = _args[4];
lean_object* v_inst_2103_ = _args[5];
lean_object* v_inst_2104_ = _args[6];
lean_object* v_inst_2105_ = _args[7];
lean_object* v_pre_2106_ = _args[8];
lean_object* v_post_2107_ = _args[9];
lean_object* v_usedLetOnly_2108_ = _args[10];
lean_object* v_skipConstInApp_2109_ = _args[11];
lean_object* v_skipInstances_2110_ = _args[12];
lean_object* v_x_2111_ = _args[13];
lean_object* v_x_2112_ = _args[14];
lean_object* v_next_2113_ = _args[15];
lean_object* v_acc_2114_ = _args[16];
lean_object* v_h_2115_ = _args[17];
lean_object* v_G_2116_ = _args[18];
lean_object* v___y_2117_ = _args[19];
_start:
{
uint8_t v_usedLetOnly_boxed_2118_; uint8_t v_skipConstInApp_boxed_2119_; uint8_t v_skipInstances_boxed_2120_; lean_object* v_res_2121_; 
v_usedLetOnly_boxed_2118_ = lean_unbox(v_usedLetOnly_2108_);
v_skipConstInApp_boxed_2119_ = lean_unbox(v_skipConstInApp_2109_);
v_skipInstances_boxed_2120_ = lean_unbox(v_skipInstances_2110_);
v_res_2121_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__4(v___x_2098_, v_toApplicative_2099_, v_toBind_2100_, v___f_2101_, v_paramInfo_2102_, v_inst_2103_, v_inst_2104_, v_inst_2105_, v_pre_2106_, v_post_2107_, v_usedLetOnly_boxed_2118_, v_skipConstInApp_boxed_2119_, v_skipInstances_boxed_2120_, v_x_2111_, v_x_2112_, v_next_2113_, v_acc_2114_, v_h_2115_, v_G_2116_, v___y_2117_);
lean_dec(v___y_2117_);
lean_dec_ref(v_paramInfo_2102_);
lean_dec(v___x_2098_);
return v_res_2121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__3(lean_object* v___x_2122_, lean_object* v_toApplicative_2123_, lean_object* v_toBind_2124_, lean_object* v___f_2125_, lean_object* v_inst_2126_, lean_object* v_inst_2127_, lean_object* v_inst_2128_, lean_object* v_pre_2129_, lean_object* v_post_2130_, uint8_t v_usedLetOnly_2131_, uint8_t v_skipConstInApp_2132_, uint8_t v_skipInstances_2133_, lean_object* v_x_2134_, lean_object* v_x_2135_, lean_object* v_args_2136_, lean_object* v___y_2137_, lean_object* v___f_2138_, lean_object* v_a_2139_){
_start:
{
lean_object* v_paramInfo_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___f_2145_; lean_object* v___x_3244__overap_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; 
v_paramInfo_2140_ = lean_ctor_get(v_a_2139_, 0);
lean_inc_ref(v_paramInfo_2140_);
lean_dec_ref(v_a_2139_);
v___x_2141_ = lean_unsigned_to_nat(0u);
v___x_2142_ = lean_box(v_usedLetOnly_2131_);
v___x_2143_ = lean_box(v_skipConstInApp_2132_);
v___x_2144_ = lean_box(v_skipInstances_2133_);
lean_inc(v_toBind_2124_);
v___f_2145_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__4___boxed), 20, 15);
lean_closure_set(v___f_2145_, 0, v___x_2122_);
lean_closure_set(v___f_2145_, 1, v_toApplicative_2123_);
lean_closure_set(v___f_2145_, 2, v_toBind_2124_);
lean_closure_set(v___f_2145_, 3, v___f_2125_);
lean_closure_set(v___f_2145_, 4, v_paramInfo_2140_);
lean_closure_set(v___f_2145_, 5, v_inst_2126_);
lean_closure_set(v___f_2145_, 6, v_inst_2127_);
lean_closure_set(v___f_2145_, 7, v_inst_2128_);
lean_closure_set(v___f_2145_, 8, v_pre_2129_);
lean_closure_set(v___f_2145_, 9, v_post_2130_);
lean_closure_set(v___f_2145_, 10, v___x_2142_);
lean_closure_set(v___f_2145_, 11, v___x_2143_);
lean_closure_set(v___f_2145_, 12, v___x_2144_);
lean_closure_set(v___f_2145_, 13, v_x_2134_);
lean_closure_set(v___f_2145_, 14, v_x_2135_);
v___x_3244__overap_2146_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_2145_, v___x_2141_, v_args_2136_, lean_box(0));
lean_inc(v___y_2137_);
v___x_2147_ = lean_apply_1(v___x_3244__overap_2146_, v___y_2137_);
v___x_2148_ = lean_apply_4(v_toBind_2124_, lean_box(0), lean_box(0), v___x_2147_, v___f_2138_);
return v___x_2148_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__3___boxed(lean_object** _args){
lean_object* v___x_2149_ = _args[0];
lean_object* v_toApplicative_2150_ = _args[1];
lean_object* v_toBind_2151_ = _args[2];
lean_object* v___f_2152_ = _args[3];
lean_object* v_inst_2153_ = _args[4];
lean_object* v_inst_2154_ = _args[5];
lean_object* v_inst_2155_ = _args[6];
lean_object* v_pre_2156_ = _args[7];
lean_object* v_post_2157_ = _args[8];
lean_object* v_usedLetOnly_2158_ = _args[9];
lean_object* v_skipConstInApp_2159_ = _args[10];
lean_object* v_skipInstances_2160_ = _args[11];
lean_object* v_x_2161_ = _args[12];
lean_object* v_x_2162_ = _args[13];
lean_object* v_args_2163_ = _args[14];
lean_object* v___y_2164_ = _args[15];
lean_object* v___f_2165_ = _args[16];
lean_object* v_a_2166_ = _args[17];
_start:
{
uint8_t v_usedLetOnly_boxed_2167_; uint8_t v_skipConstInApp_boxed_2168_; uint8_t v_skipInstances_boxed_2169_; lean_object* v_res_2170_; 
v_usedLetOnly_boxed_2167_ = lean_unbox(v_usedLetOnly_2158_);
v_skipConstInApp_boxed_2168_ = lean_unbox(v_skipConstInApp_2159_);
v_skipInstances_boxed_2169_ = lean_unbox(v_skipInstances_2160_);
v_res_2170_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__3(v___x_2149_, v_toApplicative_2150_, v_toBind_2151_, v___f_2152_, v_inst_2153_, v_inst_2154_, v_inst_2155_, v_pre_2156_, v_post_2157_, v_usedLetOnly_boxed_2167_, v_skipConstInApp_boxed_2168_, v_skipInstances_boxed_2169_, v_x_2161_, v_x_2162_, v_args_2163_, v___y_2164_, v___f_2165_, v_a_2166_);
lean_dec(v___y_2164_);
return v_res_2170_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__6(uint8_t v_skipInstances_2171_, lean_object* v_inst_2172_, lean_object* v_inst_2173_, lean_object* v_inst_2174_, lean_object* v_pre_2175_, lean_object* v_post_2176_, uint8_t v_usedLetOnly_2177_, uint8_t v_skipConstInApp_2178_, lean_object* v_x_2179_, lean_object* v_x_2180_, lean_object* v_args_2181_, lean_object* v___x_2182_, lean_object* v_toBind_2183_, lean_object* v_toApplicative_2184_, lean_object* v___f_2185_, lean_object* v_f_2186_, lean_object* v___y_2187_){
_start:
{
if (v_skipInstances_2171_ == 0)
{
lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___f_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; size_t v_sz_2196_; size_t v___x_2197_; lean_object* v___x_3257__overap_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; 
lean_dec(v___f_2185_);
lean_dec_ref(v_toApplicative_2184_);
v___x_2188_ = lean_box(v_usedLetOnly_2177_);
v___x_2189_ = lean_box(v_skipConstInApp_2178_);
v___x_2190_ = lean_box(v_skipInstances_2171_);
lean_inc_n(v___y_2187_, 2);
lean_inc(v_x_2180_);
lean_inc(v_post_2176_);
lean_inc(v_pre_2175_);
lean_inc_ref(v_inst_2174_);
lean_inc(v_inst_2173_);
lean_inc_ref(v_inst_2172_);
v___f_2191_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5___boxed), 13, 12);
lean_closure_set(v___f_2191_, 0, v_f_2186_);
lean_closure_set(v___f_2191_, 1, v_inst_2172_);
lean_closure_set(v___f_2191_, 2, v_inst_2173_);
lean_closure_set(v___f_2191_, 3, v_inst_2174_);
lean_closure_set(v___f_2191_, 4, v_pre_2175_);
lean_closure_set(v___f_2191_, 5, v_post_2176_);
lean_closure_set(v___f_2191_, 6, v___x_2188_);
lean_closure_set(v___f_2191_, 7, v___x_2189_);
lean_closure_set(v___f_2191_, 8, v___x_2190_);
lean_closure_set(v___f_2191_, 9, v_x_2179_);
lean_closure_set(v___f_2191_, 10, v_x_2180_);
lean_closure_set(v___f_2191_, 11, v___y_2187_);
v___x_2192_ = lean_box(v_usedLetOnly_2177_);
v___x_2193_ = lean_box(v_skipConstInApp_2178_);
v___x_2194_ = lean_box(v_skipInstances_2171_);
v___x_2195_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___boxed), 12, 10);
lean_closure_set(v___x_2195_, 0, v_inst_2172_);
lean_closure_set(v___x_2195_, 1, v_inst_2173_);
lean_closure_set(v___x_2195_, 2, v_inst_2174_);
lean_closure_set(v___x_2195_, 3, v_pre_2175_);
lean_closure_set(v___x_2195_, 4, v_post_2176_);
lean_closure_set(v___x_2195_, 5, v___x_2192_);
lean_closure_set(v___x_2195_, 6, v___x_2193_);
lean_closure_set(v___x_2195_, 7, v___x_2194_);
lean_closure_set(v___x_2195_, 8, v_x_2179_);
lean_closure_set(v___x_2195_, 9, v_x_2180_);
v_sz_2196_ = lean_array_size(v_args_2181_);
v___x_2197_ = ((size_t)0ULL);
v___x_3257__overap_2198_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2182_, v___x_2195_, v_sz_2196_, v___x_2197_, v_args_2181_);
v___x_2199_ = lean_apply_1(v___x_3257__overap_2198_, v___y_2187_);
v___x_2200_ = lean_apply_4(v_toBind_2183_, lean_box(0), lean_box(0), v___x_2199_, v___f_2191_);
return v___x_2200_;
}
else
{
lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___f_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___f_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; 
lean_dec_ref(v___x_2182_);
v___x_2201_ = lean_box(v_usedLetOnly_2177_);
v___x_2202_ = lean_box(v_skipConstInApp_2178_);
v___x_2203_ = lean_box(v_skipInstances_2171_);
lean_inc_n(v___y_2187_, 2);
lean_inc(v_x_2180_);
lean_inc(v_post_2176_);
lean_inc(v_pre_2175_);
lean_inc_ref(v_inst_2174_);
lean_inc_n(v_inst_2173_, 2);
lean_inc_ref(v_inst_2172_);
lean_inc_ref(v_f_2186_);
v___f_2204_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5___boxed), 13, 12);
lean_closure_set(v___f_2204_, 0, v_f_2186_);
lean_closure_set(v___f_2204_, 1, v_inst_2172_);
lean_closure_set(v___f_2204_, 2, v_inst_2173_);
lean_closure_set(v___f_2204_, 3, v_inst_2174_);
lean_closure_set(v___f_2204_, 4, v_pre_2175_);
lean_closure_set(v___f_2204_, 5, v_post_2176_);
lean_closure_set(v___f_2204_, 6, v___x_2201_);
lean_closure_set(v___f_2204_, 7, v___x_2202_);
lean_closure_set(v___f_2204_, 8, v___x_2203_);
lean_closure_set(v___f_2204_, 9, v_x_2179_);
lean_closure_set(v___f_2204_, 10, v_x_2180_);
lean_closure_set(v___f_2204_, 11, v___y_2187_);
v___x_2205_ = lean_array_get_size(v_args_2181_);
v___x_2206_ = lean_box(v_usedLetOnly_2177_);
v___x_2207_ = lean_box(v_skipConstInApp_2178_);
v___x_2208_ = lean_box(v_skipInstances_2171_);
lean_inc(v_toBind_2183_);
v___f_2209_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__3___boxed), 18, 17);
lean_closure_set(v___f_2209_, 0, v___x_2205_);
lean_closure_set(v___f_2209_, 1, v_toApplicative_2184_);
lean_closure_set(v___f_2209_, 2, v_toBind_2183_);
lean_closure_set(v___f_2209_, 3, v___f_2185_);
lean_closure_set(v___f_2209_, 4, v_inst_2172_);
lean_closure_set(v___f_2209_, 5, v_inst_2173_);
lean_closure_set(v___f_2209_, 6, v_inst_2174_);
lean_closure_set(v___f_2209_, 7, v_pre_2175_);
lean_closure_set(v___f_2209_, 8, v_post_2176_);
lean_closure_set(v___f_2209_, 9, v___x_2206_);
lean_closure_set(v___f_2209_, 10, v___x_2207_);
lean_closure_set(v___f_2209_, 11, v___x_2208_);
lean_closure_set(v___f_2209_, 12, v_x_2179_);
lean_closure_set(v___f_2209_, 13, v_x_2180_);
lean_closure_set(v___f_2209_, 14, v_args_2181_);
lean_closure_set(v___f_2209_, 15, v___y_2187_);
lean_closure_set(v___f_2209_, 16, v___f_2204_);
v___x_2210_ = lean_alloc_closure((void*)(l_Lean_Meta_getFunInfoNArgs___boxed), 7, 2);
lean_closure_set(v___x_2210_, 0, v_f_2186_);
lean_closure_set(v___x_2210_, 1, v___x_2205_);
v___x_2211_ = lean_apply_2(v_inst_2173_, lean_box(0), v___x_2210_);
v___x_2212_ = lean_apply_4(v_toBind_2183_, lean_box(0), lean_box(0), v___x_2211_, v___f_2209_);
return v___x_2212_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__6___boxed(lean_object** _args){
lean_object* v_skipInstances_2213_ = _args[0];
lean_object* v_inst_2214_ = _args[1];
lean_object* v_inst_2215_ = _args[2];
lean_object* v_inst_2216_ = _args[3];
lean_object* v_pre_2217_ = _args[4];
lean_object* v_post_2218_ = _args[5];
lean_object* v_usedLetOnly_2219_ = _args[6];
lean_object* v_skipConstInApp_2220_ = _args[7];
lean_object* v_x_2221_ = _args[8];
lean_object* v_x_2222_ = _args[9];
lean_object* v_args_2223_ = _args[10];
lean_object* v___x_2224_ = _args[11];
lean_object* v_toBind_2225_ = _args[12];
lean_object* v_toApplicative_2226_ = _args[13];
lean_object* v___f_2227_ = _args[14];
lean_object* v_f_2228_ = _args[15];
lean_object* v___y_2229_ = _args[16];
_start:
{
uint8_t v_skipInstances_boxed_2230_; uint8_t v_usedLetOnly_boxed_2231_; uint8_t v_skipConstInApp_boxed_2232_; lean_object* v_res_2233_; 
v_skipInstances_boxed_2230_ = lean_unbox(v_skipInstances_2213_);
v_usedLetOnly_boxed_2231_ = lean_unbox(v_usedLetOnly_2219_);
v_skipConstInApp_boxed_2232_ = lean_unbox(v_skipConstInApp_2220_);
v_res_2233_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__6(v_skipInstances_boxed_2230_, v_inst_2214_, v_inst_2215_, v_inst_2216_, v_pre_2217_, v_post_2218_, v_usedLetOnly_boxed_2231_, v_skipConstInApp_boxed_2232_, v_x_2221_, v_x_2222_, v_args_2223_, v___x_2224_, v_toBind_2225_, v_toApplicative_2226_, v___f_2227_, v_f_2228_, v___y_2229_);
lean_dec(v___y_2229_);
return v_res_2233_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__9(uint8_t v_skipInstances_2234_, lean_object* v_inst_2235_, lean_object* v_inst_2236_, lean_object* v_inst_2237_, lean_object* v_pre_2238_, lean_object* v_post_2239_, uint8_t v_usedLetOnly_2240_, uint8_t v_skipConstInApp_2241_, lean_object* v_x_2242_, lean_object* v_x_2243_, lean_object* v___x_2244_, lean_object* v_toBind_2245_, lean_object* v_toApplicative_2246_, lean_object* v___f_2247_, lean_object* v_f_2248_, lean_object* v_args_2249_, lean_object* v___y_2250_){
_start:
{
lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___f_2254_; lean_object* v___f_2255_; 
v___x_2251_ = lean_box(v_skipInstances_2234_);
v___x_2252_ = lean_box(v_usedLetOnly_2240_);
v___x_2253_ = lean_box(v_skipConstInApp_2241_);
lean_inc_ref(v_toApplicative_2246_);
lean_inc(v_toBind_2245_);
lean_inc(v_x_2243_);
lean_inc(v_post_2239_);
lean_inc(v_pre_2238_);
lean_inc_ref(v_inst_2237_);
lean_inc(v_inst_2236_);
lean_inc_ref(v_inst_2235_);
v___f_2254_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__6___boxed), 17, 15);
lean_closure_set(v___f_2254_, 0, v___x_2251_);
lean_closure_set(v___f_2254_, 1, v_inst_2235_);
lean_closure_set(v___f_2254_, 2, v_inst_2236_);
lean_closure_set(v___f_2254_, 3, v_inst_2237_);
lean_closure_set(v___f_2254_, 4, v_pre_2238_);
lean_closure_set(v___f_2254_, 5, v_post_2239_);
lean_closure_set(v___f_2254_, 6, v___x_2252_);
lean_closure_set(v___f_2254_, 7, v___x_2253_);
lean_closure_set(v___f_2254_, 8, v_x_2242_);
lean_closure_set(v___f_2254_, 9, v_x_2243_);
lean_closure_set(v___f_2254_, 10, v_args_2249_);
lean_closure_set(v___f_2254_, 11, v___x_2244_);
lean_closure_set(v___f_2254_, 12, v_toBind_2245_);
lean_closure_set(v___f_2254_, 13, v_toApplicative_2246_);
lean_closure_set(v___f_2254_, 14, v___f_2247_);
lean_inc(v___y_2250_);
v___f_2255_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__7___boxed), 3, 2);
lean_closure_set(v___f_2255_, 0, v___f_2254_);
lean_closure_set(v___f_2255_, 1, v___y_2250_);
if (v_skipConstInApp_2241_ == 0)
{
lean_dec_ref(v_toApplicative_2246_);
goto v___jp_2256_;
}
else
{
uint8_t v___x_2259_; 
v___x_2259_ = l_Lean_Expr_isConst(v_f_2248_);
if (v___x_2259_ == 0)
{
lean_dec_ref(v_toApplicative_2246_);
goto v___jp_2256_;
}
else
{
lean_object* v_toPure_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; 
lean_dec(v_x_2243_);
lean_dec(v_post_2239_);
lean_dec(v_pre_2238_);
lean_dec_ref(v_inst_2237_);
lean_dec(v_inst_2236_);
lean_dec_ref(v_inst_2235_);
v_toPure_2260_ = lean_ctor_get(v_toApplicative_2246_, 1);
lean_inc(v_toPure_2260_);
lean_dec_ref(v_toApplicative_2246_);
v___x_2261_ = lean_apply_2(v_toPure_2260_, lean_box(0), v_f_2248_);
v___x_2262_ = lean_apply_4(v_toBind_2245_, lean_box(0), lean_box(0), v___x_2261_, v___f_2255_);
return v___x_2262_;
}
}
v___jp_2256_:
{
lean_object* v___x_2257_; lean_object* v___x_2258_; 
v___x_2257_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2235_, v_inst_2236_, v_inst_2237_, v_pre_2238_, v_post_2239_, v_usedLetOnly_2240_, v_skipConstInApp_2241_, v_skipInstances_2234_, v_x_2242_, v_x_2243_, v_f_2248_, v___y_2250_);
v___x_2258_ = lean_apply_4(v_toBind_2245_, lean_box(0), lean_box(0), v___x_2257_, v___f_2255_);
return v___x_2258_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__9___boxed(lean_object** _args){
lean_object* v_skipInstances_2263_ = _args[0];
lean_object* v_inst_2264_ = _args[1];
lean_object* v_inst_2265_ = _args[2];
lean_object* v_inst_2266_ = _args[3];
lean_object* v_pre_2267_ = _args[4];
lean_object* v_post_2268_ = _args[5];
lean_object* v_usedLetOnly_2269_ = _args[6];
lean_object* v_skipConstInApp_2270_ = _args[7];
lean_object* v_x_2271_ = _args[8];
lean_object* v_x_2272_ = _args[9];
lean_object* v___x_2273_ = _args[10];
lean_object* v_toBind_2274_ = _args[11];
lean_object* v_toApplicative_2275_ = _args[12];
lean_object* v___f_2276_ = _args[13];
lean_object* v_f_2277_ = _args[14];
lean_object* v_args_2278_ = _args[15];
lean_object* v___y_2279_ = _args[16];
_start:
{
uint8_t v_skipInstances_boxed_2280_; uint8_t v_usedLetOnly_boxed_2281_; uint8_t v_skipConstInApp_boxed_2282_; lean_object* v_res_2283_; 
v_skipInstances_boxed_2280_ = lean_unbox(v_skipInstances_2263_);
v_usedLetOnly_boxed_2281_ = lean_unbox(v_usedLetOnly_2269_);
v_skipConstInApp_boxed_2282_ = lean_unbox(v_skipConstInApp_2270_);
v_res_2283_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__9(v_skipInstances_boxed_2280_, v_inst_2264_, v_inst_2265_, v_inst_2266_, v_pre_2267_, v_post_2268_, v_usedLetOnly_boxed_2281_, v_skipConstInApp_boxed_2282_, v_x_2271_, v_x_2272_, v___x_2273_, v_toBind_2274_, v_toApplicative_2275_, v___f_2276_, v_f_2277_, v_args_2278_, v___y_2279_);
lean_dec(v___y_2279_);
return v_res_2283_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__0(lean_object* v_fvars_2286_, lean_object* v_inst_2287_, lean_object* v_inst_2288_, lean_object* v_inst_2289_, lean_object* v_pre_2290_, lean_object* v_post_2291_, uint8_t v_usedLetOnly_2292_, uint8_t v_skipConstInApp_2293_, uint8_t v_skipInstances_2294_, lean_object* v_x_2295_, lean_object* v_x_2296_, lean_object* v_body_2297_, lean_object* v_x_2298_, lean_object* v___y_2299_){
_start:
{
lean_object* v___x_2300_; lean_object* v___x_2301_; 
v___x_2300_ = lean_array_push(v_fvars_2286_, v_x_2298_);
v___x_2301_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(v_inst_2287_, v_inst_2288_, v_inst_2289_, v_pre_2290_, v_post_2291_, v_usedLetOnly_2292_, v_skipConstInApp_2293_, v_skipInstances_2294_, v_x_2295_, v_x_2296_, v___x_2300_, v_body_2297_, v___y_2299_);
return v___x_2301_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__0___boxed(lean_object* v_fvars_2302_, lean_object* v_inst_2303_, lean_object* v_inst_2304_, lean_object* v_inst_2305_, lean_object* v_pre_2306_, lean_object* v_post_2307_, lean_object* v_usedLetOnly_2308_, lean_object* v_skipConstInApp_2309_, lean_object* v_skipInstances_2310_, lean_object* v_x_2311_, lean_object* v_x_2312_, lean_object* v_body_2313_, lean_object* v_x_2314_, lean_object* v___y_2315_){
_start:
{
uint8_t v_usedLetOnly_boxed_2316_; uint8_t v_skipConstInApp_boxed_2317_; uint8_t v_skipInstances_boxed_2318_; lean_object* v_res_2319_; 
v_usedLetOnly_boxed_2316_ = lean_unbox(v_usedLetOnly_2308_);
v_skipConstInApp_boxed_2317_ = lean_unbox(v_skipConstInApp_2309_);
v_skipInstances_boxed_2318_ = lean_unbox(v_skipInstances_2310_);
v_res_2319_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__0(v_fvars_2302_, v_inst_2303_, v_inst_2304_, v_inst_2305_, v_pre_2306_, v_post_2307_, v_usedLetOnly_boxed_2316_, v_skipConstInApp_boxed_2317_, v_skipInstances_boxed_2318_, v_x_2311_, v_x_2312_, v_body_2313_, v_x_2314_, v___y_2315_);
lean_dec(v___y_2315_);
return v_res_2319_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3___boxed(lean_object* v_inst_2320_, lean_object* v_inst_2321_, lean_object* v_inst_2322_, lean_object* v_pre_2323_, lean_object* v_post_2324_, lean_object* v_usedLetOnly_2325_, lean_object* v_skipConstInApp_2326_, lean_object* v_skipInstances_2327_, lean_object* v_x_2328_, lean_object* v_x_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_){
_start:
{
uint8_t v_usedLetOnly_boxed_2332_; uint8_t v_skipConstInApp_boxed_2333_; uint8_t v_skipInstances_boxed_2334_; lean_object* v_res_2335_; 
v_usedLetOnly_boxed_2332_ = lean_unbox(v_usedLetOnly_2325_);
v_skipConstInApp_boxed_2333_ = lean_unbox(v_skipConstInApp_2326_);
v_skipInstances_boxed_2334_ = lean_unbox(v_skipInstances_2327_);
v_res_2335_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3(v_inst_2320_, v_inst_2321_, v_inst_2322_, v_pre_2323_, v_post_2324_, v_usedLetOnly_boxed_2332_, v_skipConstInApp_boxed_2333_, v_skipInstances_boxed_2334_, v_x_2328_, v_x_2329_, v_a_2330_, v_a_2331_);
lean_dec(v_a_2330_);
return v_res_2335_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(lean_object* v_inst_2336_, lean_object* v_inst_2337_, lean_object* v_inst_2338_, lean_object* v_pre_2339_, lean_object* v_post_2340_, uint8_t v_usedLetOnly_2341_, uint8_t v_skipConstInApp_2342_, uint8_t v_skipInstances_2343_, lean_object* v_x_2344_, lean_object* v_x_2345_, lean_object* v_fvars_2346_, lean_object* v_e_2347_, lean_object* v_a_2348_){
_start:
{
lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___f_2353_; lean_object* v___f_2354_; lean_object* v___x_2355_; 
v___x_2349_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0));
v___x_2350_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1));
lean_inc_ref(v_inst_2336_);
v___x_2351_ = l_Lean_MonadCacheT_instMonad___redArg(v_x_2344_, v___x_2349_, v___x_2350_, v_inst_2336_);
v___x_2352_ = l_Lean_MonadCacheT_instMonadControl___redArg(v_x_2344_, v___x_2349_, v___x_2350_);
lean_inc_ref_n(v_inst_2338_, 2);
lean_inc_ref(v___x_2352_);
v___f_2353_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_2353_, 0, v___x_2352_);
lean_closure_set(v___f_2353_, 1, v_inst_2338_);
v___f_2354_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_2354_, 0, v___x_2352_);
lean_closure_set(v___f_2354_, 1, v_inst_2338_);
v___x_2355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2355_, 0, v___f_2353_);
lean_ctor_set(v___x_2355_, 1, v___f_2354_);
if (lean_obj_tag(v_e_2347_) == 7)
{
lean_object* v_binderName_2356_; lean_object* v_binderType_2357_; lean_object* v_body_2358_; uint8_t v_binderInfo_2359_; lean_object* v_toBind_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___f_2364_; lean_object* v___x_2365_; lean_object* v___f_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; 
v_binderName_2356_ = lean_ctor_get(v_e_2347_, 0);
lean_inc(v_binderName_2356_);
v_binderType_2357_ = lean_ctor_get(v_e_2347_, 1);
lean_inc_ref(v_binderType_2357_);
v_body_2358_ = lean_ctor_get(v_e_2347_, 2);
lean_inc_ref(v_body_2358_);
v_binderInfo_2359_ = lean_ctor_get_uint8(v_e_2347_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2347_, 3);
v_toBind_2360_ = lean_ctor_get(v_inst_2336_, 1);
lean_inc(v_toBind_2360_);
v___x_2361_ = lean_box(v_usedLetOnly_2341_);
v___x_2362_ = lean_box(v_skipConstInApp_2342_);
v___x_2363_ = lean_box(v_skipInstances_2343_);
lean_inc(v_x_2345_);
lean_inc(v_post_2340_);
lean_inc(v_pre_2339_);
lean_inc_ref(v_inst_2338_);
lean_inc(v_inst_2337_);
lean_inc_ref(v_inst_2336_);
lean_inc_ref(v_fvars_2346_);
v___f_2364_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__0___boxed), 14, 12);
lean_closure_set(v___f_2364_, 0, v_fvars_2346_);
lean_closure_set(v___f_2364_, 1, v_inst_2336_);
lean_closure_set(v___f_2364_, 2, v_inst_2337_);
lean_closure_set(v___f_2364_, 3, v_inst_2338_);
lean_closure_set(v___f_2364_, 4, v_pre_2339_);
lean_closure_set(v___f_2364_, 5, v_post_2340_);
lean_closure_set(v___f_2364_, 6, v___x_2361_);
lean_closure_set(v___f_2364_, 7, v___x_2362_);
lean_closure_set(v___f_2364_, 8, v___x_2363_);
lean_closure_set(v___f_2364_, 9, v_x_2344_);
lean_closure_set(v___f_2364_, 10, v_x_2345_);
lean_closure_set(v___f_2364_, 11, v_body_2358_);
v___x_2365_ = lean_box(v_binderInfo_2359_);
lean_inc(v_a_2348_);
v___f_2366_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_2366_, 0, v___x_2355_);
lean_closure_set(v___f_2366_, 1, v___x_2351_);
lean_closure_set(v___f_2366_, 2, v_binderName_2356_);
lean_closure_set(v___f_2366_, 3, v___x_2365_);
lean_closure_set(v___f_2366_, 4, v___f_2364_);
lean_closure_set(v___f_2366_, 5, v_a_2348_);
v___x_2367_ = lean_expr_instantiate_rev(v_binderType_2357_, v_fvars_2346_);
lean_dec_ref(v_fvars_2346_);
lean_dec_ref(v_binderType_2357_);
v___x_2368_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2336_, v_inst_2337_, v_inst_2338_, v_pre_2339_, v_post_2340_, v_usedLetOnly_2341_, v_skipConstInApp_2342_, v_skipInstances_2343_, v_x_2344_, v_x_2345_, v___x_2367_, v_a_2348_);
v___x_2369_ = lean_apply_4(v_toBind_2360_, lean_box(0), lean_box(0), v___x_2368_, v___f_2366_);
return v___x_2369_;
}
else
{
lean_object* v_toBind_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___f_2374_; lean_object* v___x_2375_; lean_object* v___f_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; 
lean_dec_ref_known(v___x_2355_, 2);
lean_dec_ref(v___x_2351_);
v_toBind_2370_ = lean_ctor_get(v_inst_2336_, 1);
lean_inc_n(v_toBind_2370_, 2);
v___x_2371_ = lean_box(v_usedLetOnly_2341_);
v___x_2372_ = lean_box(v_skipConstInApp_2342_);
v___x_2373_ = lean_box(v_skipInstances_2343_);
lean_inc(v_a_2348_);
lean_inc(v_x_2345_);
lean_inc(v_post_2340_);
lean_inc(v_pre_2339_);
lean_inc_ref(v_inst_2338_);
lean_inc_n(v_inst_2337_, 2);
lean_inc_ref(v_inst_2336_);
v___f_2374_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3___boxed), 12, 11);
lean_closure_set(v___f_2374_, 0, v_inst_2336_);
lean_closure_set(v___f_2374_, 1, v_inst_2337_);
lean_closure_set(v___f_2374_, 2, v_inst_2338_);
lean_closure_set(v___f_2374_, 3, v_pre_2339_);
lean_closure_set(v___f_2374_, 4, v_post_2340_);
lean_closure_set(v___f_2374_, 5, v___x_2371_);
lean_closure_set(v___f_2374_, 6, v___x_2372_);
lean_closure_set(v___f_2374_, 7, v___x_2373_);
lean_closure_set(v___f_2374_, 8, v_x_2344_);
lean_closure_set(v___f_2374_, 9, v_x_2345_);
lean_closure_set(v___f_2374_, 10, v_a_2348_);
v___x_2375_ = lean_box(v_usedLetOnly_2341_);
lean_inc_ref(v_fvars_2346_);
v___f_2376_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__3___boxed), 6, 5);
lean_closure_set(v___f_2376_, 0, v_fvars_2346_);
lean_closure_set(v___f_2376_, 1, v___x_2375_);
lean_closure_set(v___f_2376_, 2, v_inst_2337_);
lean_closure_set(v___f_2376_, 3, v_toBind_2370_);
lean_closure_set(v___f_2376_, 4, v___f_2374_);
v___x_2377_ = lean_expr_instantiate_rev(v_e_2347_, v_fvars_2346_);
lean_dec_ref(v_fvars_2346_);
lean_dec_ref(v_e_2347_);
v___x_2378_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2336_, v_inst_2337_, v_inst_2338_, v_pre_2339_, v_post_2340_, v_usedLetOnly_2341_, v_skipConstInApp_2342_, v_skipInstances_2343_, v_x_2344_, v_x_2345_, v___x_2377_, v_a_2348_);
v___x_2379_ = lean_apply_4(v_toBind_2370_, lean_box(0), lean_box(0), v___x_2378_, v___f_2376_);
return v___x_2379_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__0(lean_object* v_fvars_2380_, lean_object* v_inst_2381_, lean_object* v_inst_2382_, lean_object* v_inst_2383_, lean_object* v_pre_2384_, lean_object* v_post_2385_, uint8_t v_usedLetOnly_2386_, uint8_t v_skipConstInApp_2387_, uint8_t v_skipInstances_2388_, lean_object* v_x_2389_, lean_object* v_x_2390_, lean_object* v_body_2391_, lean_object* v_x_2392_, lean_object* v___y_2393_){
_start:
{
lean_object* v___x_2394_; lean_object* v___x_2395_; 
v___x_2394_ = lean_array_push(v_fvars_2380_, v_x_2392_);
v___x_2395_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(v_inst_2381_, v_inst_2382_, v_inst_2383_, v_pre_2384_, v_post_2385_, v_usedLetOnly_2386_, v_skipConstInApp_2387_, v_skipInstances_2388_, v_x_2389_, v_x_2390_, v___x_2394_, v_body_2391_, v___y_2393_);
return v___x_2395_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__0___boxed(lean_object* v_fvars_2396_, lean_object* v_inst_2397_, lean_object* v_inst_2398_, lean_object* v_inst_2399_, lean_object* v_pre_2400_, lean_object* v_post_2401_, lean_object* v_usedLetOnly_2402_, lean_object* v_skipConstInApp_2403_, lean_object* v_skipInstances_2404_, lean_object* v_x_2405_, lean_object* v_x_2406_, lean_object* v_body_2407_, lean_object* v_x_2408_, lean_object* v___y_2409_){
_start:
{
uint8_t v_usedLetOnly_boxed_2410_; uint8_t v_skipConstInApp_boxed_2411_; uint8_t v_skipInstances_boxed_2412_; lean_object* v_res_2413_; 
v_usedLetOnly_boxed_2410_ = lean_unbox(v_usedLetOnly_2402_);
v_skipConstInApp_boxed_2411_ = lean_unbox(v_skipConstInApp_2403_);
v_skipInstances_boxed_2412_ = lean_unbox(v_skipInstances_2404_);
v_res_2413_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__0(v_fvars_2396_, v_inst_2397_, v_inst_2398_, v_inst_2399_, v_pre_2400_, v_post_2401_, v_usedLetOnly_boxed_2410_, v_skipConstInApp_boxed_2411_, v_skipInstances_boxed_2412_, v_x_2405_, v_x_2406_, v_body_2407_, v_x_2408_, v___y_2409_);
lean_dec(v___y_2409_);
return v_res_2413_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(lean_object* v_inst_2414_, lean_object* v_inst_2415_, lean_object* v_inst_2416_, lean_object* v_pre_2417_, lean_object* v_post_2418_, uint8_t v_usedLetOnly_2419_, uint8_t v_skipConstInApp_2420_, uint8_t v_skipInstances_2421_, lean_object* v_x_2422_, lean_object* v_x_2423_, lean_object* v_fvars_2424_, lean_object* v_e_2425_, lean_object* v_a_2426_){
_start:
{
lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___f_2431_; lean_object* v___f_2432_; lean_object* v___x_2433_; 
v___x_2427_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0));
v___x_2428_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1));
lean_inc_ref(v_inst_2414_);
v___x_2429_ = l_Lean_MonadCacheT_instMonad___redArg(v_x_2422_, v___x_2427_, v___x_2428_, v_inst_2414_);
v___x_2430_ = l_Lean_MonadCacheT_instMonadControl___redArg(v_x_2422_, v___x_2427_, v___x_2428_);
lean_inc_ref_n(v_inst_2416_, 2);
lean_inc_ref(v___x_2430_);
v___f_2431_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_2431_, 0, v___x_2430_);
lean_closure_set(v___f_2431_, 1, v_inst_2416_);
v___f_2432_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_2432_, 0, v___x_2430_);
lean_closure_set(v___f_2432_, 1, v_inst_2416_);
v___x_2433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2433_, 0, v___f_2431_);
lean_ctor_set(v___x_2433_, 1, v___f_2432_);
if (lean_obj_tag(v_e_2425_) == 6)
{
lean_object* v_binderName_2434_; lean_object* v_binderType_2435_; lean_object* v_body_2436_; uint8_t v_binderInfo_2437_; lean_object* v_toBind_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___f_2442_; lean_object* v___x_2443_; lean_object* v___f_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; 
v_binderName_2434_ = lean_ctor_get(v_e_2425_, 0);
lean_inc(v_binderName_2434_);
v_binderType_2435_ = lean_ctor_get(v_e_2425_, 1);
lean_inc_ref(v_binderType_2435_);
v_body_2436_ = lean_ctor_get(v_e_2425_, 2);
lean_inc_ref(v_body_2436_);
v_binderInfo_2437_ = lean_ctor_get_uint8(v_e_2425_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2425_, 3);
v_toBind_2438_ = lean_ctor_get(v_inst_2414_, 1);
lean_inc(v_toBind_2438_);
v___x_2439_ = lean_box(v_usedLetOnly_2419_);
v___x_2440_ = lean_box(v_skipConstInApp_2420_);
v___x_2441_ = lean_box(v_skipInstances_2421_);
lean_inc(v_x_2423_);
lean_inc(v_post_2418_);
lean_inc(v_pre_2417_);
lean_inc_ref(v_inst_2416_);
lean_inc(v_inst_2415_);
lean_inc_ref(v_inst_2414_);
lean_inc_ref(v_fvars_2424_);
v___f_2442_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__0___boxed), 14, 12);
lean_closure_set(v___f_2442_, 0, v_fvars_2424_);
lean_closure_set(v___f_2442_, 1, v_inst_2414_);
lean_closure_set(v___f_2442_, 2, v_inst_2415_);
lean_closure_set(v___f_2442_, 3, v_inst_2416_);
lean_closure_set(v___f_2442_, 4, v_pre_2417_);
lean_closure_set(v___f_2442_, 5, v_post_2418_);
lean_closure_set(v___f_2442_, 6, v___x_2439_);
lean_closure_set(v___f_2442_, 7, v___x_2440_);
lean_closure_set(v___f_2442_, 8, v___x_2441_);
lean_closure_set(v___f_2442_, 9, v_x_2422_);
lean_closure_set(v___f_2442_, 10, v_x_2423_);
lean_closure_set(v___f_2442_, 11, v_body_2436_);
v___x_2443_ = lean_box(v_binderInfo_2437_);
lean_inc(v_a_2426_);
v___f_2444_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_2444_, 0, v___x_2433_);
lean_closure_set(v___f_2444_, 1, v___x_2429_);
lean_closure_set(v___f_2444_, 2, v_binderName_2434_);
lean_closure_set(v___f_2444_, 3, v___x_2443_);
lean_closure_set(v___f_2444_, 4, v___f_2442_);
lean_closure_set(v___f_2444_, 5, v_a_2426_);
v___x_2445_ = lean_expr_instantiate_rev(v_binderType_2435_, v_fvars_2424_);
lean_dec_ref(v_fvars_2424_);
lean_dec_ref(v_binderType_2435_);
v___x_2446_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2414_, v_inst_2415_, v_inst_2416_, v_pre_2417_, v_post_2418_, v_usedLetOnly_2419_, v_skipConstInApp_2420_, v_skipInstances_2421_, v_x_2422_, v_x_2423_, v___x_2445_, v_a_2426_);
v___x_2447_ = lean_apply_4(v_toBind_2438_, lean_box(0), lean_box(0), v___x_2446_, v___f_2444_);
return v___x_2447_;
}
else
{
lean_object* v_toBind_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___f_2452_; lean_object* v___x_2453_; lean_object* v___f_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; 
lean_dec_ref_known(v___x_2433_, 2);
lean_dec_ref(v___x_2429_);
v_toBind_2448_ = lean_ctor_get(v_inst_2414_, 1);
lean_inc_n(v_toBind_2448_, 2);
v___x_2449_ = lean_box(v_usedLetOnly_2419_);
v___x_2450_ = lean_box(v_skipConstInApp_2420_);
v___x_2451_ = lean_box(v_skipInstances_2421_);
lean_inc(v_a_2426_);
lean_inc(v_x_2423_);
lean_inc(v_post_2418_);
lean_inc(v_pre_2417_);
lean_inc_ref(v_inst_2416_);
lean_inc_n(v_inst_2415_, 2);
lean_inc_ref(v_inst_2414_);
v___f_2452_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3___boxed), 12, 11);
lean_closure_set(v___f_2452_, 0, v_inst_2414_);
lean_closure_set(v___f_2452_, 1, v_inst_2415_);
lean_closure_set(v___f_2452_, 2, v_inst_2416_);
lean_closure_set(v___f_2452_, 3, v_pre_2417_);
lean_closure_set(v___f_2452_, 4, v_post_2418_);
lean_closure_set(v___f_2452_, 5, v___x_2449_);
lean_closure_set(v___f_2452_, 6, v___x_2450_);
lean_closure_set(v___f_2452_, 7, v___x_2451_);
lean_closure_set(v___f_2452_, 8, v_x_2422_);
lean_closure_set(v___f_2452_, 9, v_x_2423_);
lean_closure_set(v___f_2452_, 10, v_a_2426_);
v___x_2453_ = lean_box(v_usedLetOnly_2419_);
lean_inc_ref(v_fvars_2424_);
v___f_2454_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__3___boxed), 6, 5);
lean_closure_set(v___f_2454_, 0, v_fvars_2424_);
lean_closure_set(v___f_2454_, 1, v___x_2453_);
lean_closure_set(v___f_2454_, 2, v_inst_2415_);
lean_closure_set(v___f_2454_, 3, v_toBind_2448_);
lean_closure_set(v___f_2454_, 4, v___f_2452_);
v___x_2455_ = lean_expr_instantiate_rev(v_e_2425_, v_fvars_2424_);
lean_dec_ref(v_fvars_2424_);
lean_dec_ref(v_e_2425_);
v___x_2456_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2414_, v_inst_2415_, v_inst_2416_, v_pre_2417_, v_post_2418_, v_usedLetOnly_2419_, v_skipConstInApp_2420_, v_skipInstances_2421_, v_x_2422_, v_x_2423_, v___x_2455_, v_a_2426_);
v___x_2457_ = lean_apply_4(v_toBind_2448_, lean_box(0), lean_box(0), v___x_2456_, v___f_2454_);
return v___x_2457_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__0(lean_object* v_fvars_2458_, lean_object* v_inst_2459_, lean_object* v_inst_2460_, lean_object* v_inst_2461_, lean_object* v_pre_2462_, lean_object* v_post_2463_, uint8_t v_usedLetOnly_2464_, uint8_t v_skipConstInApp_2465_, uint8_t v_skipInstances_2466_, lean_object* v_x_2467_, lean_object* v_x_2468_, lean_object* v_body_2469_, lean_object* v_x_2470_, lean_object* v___y_2471_){
_start:
{
lean_object* v___x_2472_; lean_object* v___x_2473_; 
v___x_2472_ = lean_array_push(v_fvars_2458_, v_x_2470_);
v___x_2473_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(v_inst_2459_, v_inst_2460_, v_inst_2461_, v_pre_2462_, v_post_2463_, v_usedLetOnly_2464_, v_skipConstInApp_2465_, v_skipInstances_2466_, v_x_2467_, v_x_2468_, v___x_2472_, v_body_2469_, v___y_2471_);
return v___x_2473_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__0___boxed(lean_object* v_fvars_2474_, lean_object* v_inst_2475_, lean_object* v_inst_2476_, lean_object* v_inst_2477_, lean_object* v_pre_2478_, lean_object* v_post_2479_, lean_object* v_usedLetOnly_2480_, lean_object* v_skipConstInApp_2481_, lean_object* v_skipInstances_2482_, lean_object* v_x_2483_, lean_object* v_x_2484_, lean_object* v_body_2485_, lean_object* v_x_2486_, lean_object* v___y_2487_){
_start:
{
uint8_t v_usedLetOnly_boxed_2488_; uint8_t v_skipConstInApp_boxed_2489_; uint8_t v_skipInstances_boxed_2490_; lean_object* v_res_2491_; 
v_usedLetOnly_boxed_2488_ = lean_unbox(v_usedLetOnly_2480_);
v_skipConstInApp_boxed_2489_ = lean_unbox(v_skipConstInApp_2481_);
v_skipInstances_boxed_2490_ = lean_unbox(v_skipInstances_2482_);
v_res_2491_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__0(v_fvars_2474_, v_inst_2475_, v_inst_2476_, v_inst_2477_, v_pre_2478_, v_post_2479_, v_usedLetOnly_boxed_2488_, v_skipConstInApp_boxed_2489_, v_skipInstances_boxed_2490_, v_x_2483_, v_x_2484_, v_body_2485_, v_x_2486_, v___y_2487_);
lean_dec(v___y_2487_);
return v_res_2491_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__2(lean_object* v___x_2492_, lean_object* v___x_2493_, lean_object* v_declName_2494_, lean_object* v___f_2495_, uint8_t v_nondep_2496_, lean_object* v_a_2497_, lean_object* v_value_2498_, lean_object* v_fvars_2499_, lean_object* v_inst_2500_, lean_object* v_inst_2501_, lean_object* v_inst_2502_, lean_object* v_pre_2503_, lean_object* v_post_2504_, uint8_t v_usedLetOnly_2505_, uint8_t v_skipConstInApp_2506_, uint8_t v_skipInstances_2507_, lean_object* v_x_2508_, lean_object* v_x_2509_, lean_object* v_toBind_2510_, lean_object* v_a_2511_){
_start:
{
lean_object* v___x_2512_; lean_object* v___f_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; 
v___x_2512_ = lean_box(v_nondep_2496_);
lean_inc(v_a_2497_);
v___f_2513_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_2513_, 0, v___x_2492_);
lean_closure_set(v___f_2513_, 1, v___x_2493_);
lean_closure_set(v___f_2513_, 2, v_declName_2494_);
lean_closure_set(v___f_2513_, 3, v_a_2511_);
lean_closure_set(v___f_2513_, 4, v___f_2495_);
lean_closure_set(v___f_2513_, 5, v___x_2512_);
lean_closure_set(v___f_2513_, 6, v_a_2497_);
v___x_2514_ = lean_expr_instantiate_rev(v_value_2498_, v_fvars_2499_);
v___x_2515_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2500_, v_inst_2501_, v_inst_2502_, v_pre_2503_, v_post_2504_, v_usedLetOnly_2505_, v_skipConstInApp_2506_, v_skipInstances_2507_, v_x_2508_, v_x_2509_, v___x_2514_, v_a_2497_);
v___x_2516_ = lean_apply_4(v_toBind_2510_, lean_box(0), lean_box(0), v___x_2515_, v___f_2513_);
return v___x_2516_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__2___boxed(lean_object** _args){
lean_object* v___x_2517_ = _args[0];
lean_object* v___x_2518_ = _args[1];
lean_object* v_declName_2519_ = _args[2];
lean_object* v___f_2520_ = _args[3];
lean_object* v_nondep_2521_ = _args[4];
lean_object* v_a_2522_ = _args[5];
lean_object* v_value_2523_ = _args[6];
lean_object* v_fvars_2524_ = _args[7];
lean_object* v_inst_2525_ = _args[8];
lean_object* v_inst_2526_ = _args[9];
lean_object* v_inst_2527_ = _args[10];
lean_object* v_pre_2528_ = _args[11];
lean_object* v_post_2529_ = _args[12];
lean_object* v_usedLetOnly_2530_ = _args[13];
lean_object* v_skipConstInApp_2531_ = _args[14];
lean_object* v_skipInstances_2532_ = _args[15];
lean_object* v_x_2533_ = _args[16];
lean_object* v_x_2534_ = _args[17];
lean_object* v_toBind_2535_ = _args[18];
lean_object* v_a_2536_ = _args[19];
_start:
{
uint8_t v_nondep_3815__boxed_2537_; uint8_t v_usedLetOnly_boxed_2538_; uint8_t v_skipConstInApp_boxed_2539_; uint8_t v_skipInstances_boxed_2540_; lean_object* v_res_2541_; 
v_nondep_3815__boxed_2537_ = lean_unbox(v_nondep_2521_);
v_usedLetOnly_boxed_2538_ = lean_unbox(v_usedLetOnly_2530_);
v_skipConstInApp_boxed_2539_ = lean_unbox(v_skipConstInApp_2531_);
v_skipInstances_boxed_2540_ = lean_unbox(v_skipInstances_2532_);
v_res_2541_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__2(v___x_2517_, v___x_2518_, v_declName_2519_, v___f_2520_, v_nondep_3815__boxed_2537_, v_a_2522_, v_value_2523_, v_fvars_2524_, v_inst_2525_, v_inst_2526_, v_inst_2527_, v_pre_2528_, v_post_2529_, v_usedLetOnly_boxed_2538_, v_skipConstInApp_boxed_2539_, v_skipInstances_boxed_2540_, v_x_2533_, v_x_2534_, v_toBind_2535_, v_a_2536_);
lean_dec_ref(v_fvars_2524_);
lean_dec_ref(v_value_2523_);
lean_dec(v_a_2522_);
return v_res_2541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(lean_object* v_inst_2542_, lean_object* v_inst_2543_, lean_object* v_inst_2544_, lean_object* v_pre_2545_, lean_object* v_post_2546_, uint8_t v_usedLetOnly_2547_, uint8_t v_skipConstInApp_2548_, uint8_t v_skipInstances_2549_, lean_object* v_x_2550_, lean_object* v_x_2551_, lean_object* v_fvars_2552_, lean_object* v_e_2553_, lean_object* v_a_2554_){
_start:
{
lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___f_2559_; lean_object* v___f_2560_; lean_object* v___x_2561_; 
v___x_2555_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0));
v___x_2556_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1));
lean_inc_ref(v_inst_2542_);
v___x_2557_ = l_Lean_MonadCacheT_instMonad___redArg(v_x_2550_, v___x_2555_, v___x_2556_, v_inst_2542_);
v___x_2558_ = l_Lean_MonadCacheT_instMonadControl___redArg(v_x_2550_, v___x_2555_, v___x_2556_);
lean_inc_ref_n(v_inst_2544_, 2);
lean_inc_ref(v___x_2558_);
v___f_2559_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_2559_, 0, v___x_2558_);
lean_closure_set(v___f_2559_, 1, v_inst_2544_);
v___f_2560_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_2560_, 0, v___x_2558_);
lean_closure_set(v___f_2560_, 1, v_inst_2544_);
v___x_2561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2561_, 0, v___f_2559_);
lean_ctor_set(v___x_2561_, 1, v___f_2560_);
if (lean_obj_tag(v_e_2553_) == 8)
{
lean_object* v_declName_2562_; lean_object* v_type_2563_; lean_object* v_value_2564_; lean_object* v_body_2565_; uint8_t v_nondep_2566_; lean_object* v_toBind_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___f_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___f_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; 
v_declName_2562_ = lean_ctor_get(v_e_2553_, 0);
lean_inc(v_declName_2562_);
v_type_2563_ = lean_ctor_get(v_e_2553_, 1);
lean_inc_ref(v_type_2563_);
v_value_2564_ = lean_ctor_get(v_e_2553_, 2);
lean_inc_ref(v_value_2564_);
v_body_2565_ = lean_ctor_get(v_e_2553_, 3);
lean_inc_ref(v_body_2565_);
v_nondep_2566_ = lean_ctor_get_uint8(v_e_2553_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_2553_, 4);
v_toBind_2567_ = lean_ctor_get(v_inst_2542_, 1);
lean_inc_n(v_toBind_2567_, 2);
v___x_2568_ = lean_box(v_usedLetOnly_2547_);
v___x_2569_ = lean_box(v_skipConstInApp_2548_);
v___x_2570_ = lean_box(v_skipInstances_2549_);
lean_inc_n(v_x_2551_, 2);
lean_inc_n(v_post_2546_, 2);
lean_inc_n(v_pre_2545_, 2);
lean_inc_ref_n(v_inst_2544_, 2);
lean_inc_n(v_inst_2543_, 2);
lean_inc_ref_n(v_inst_2542_, 2);
lean_inc_ref_n(v_fvars_2552_, 2);
v___f_2571_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__0___boxed), 14, 12);
lean_closure_set(v___f_2571_, 0, v_fvars_2552_);
lean_closure_set(v___f_2571_, 1, v_inst_2542_);
lean_closure_set(v___f_2571_, 2, v_inst_2543_);
lean_closure_set(v___f_2571_, 3, v_inst_2544_);
lean_closure_set(v___f_2571_, 4, v_pre_2545_);
lean_closure_set(v___f_2571_, 5, v_post_2546_);
lean_closure_set(v___f_2571_, 6, v___x_2568_);
lean_closure_set(v___f_2571_, 7, v___x_2569_);
lean_closure_set(v___f_2571_, 8, v___x_2570_);
lean_closure_set(v___f_2571_, 9, v_x_2550_);
lean_closure_set(v___f_2571_, 10, v_x_2551_);
lean_closure_set(v___f_2571_, 11, v_body_2565_);
v___x_2572_ = lean_box(v_nondep_2566_);
v___x_2573_ = lean_box(v_usedLetOnly_2547_);
v___x_2574_ = lean_box(v_skipConstInApp_2548_);
v___x_2575_ = lean_box(v_skipInstances_2549_);
lean_inc(v_a_2554_);
v___f_2576_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__2___boxed), 20, 19);
lean_closure_set(v___f_2576_, 0, v___x_2561_);
lean_closure_set(v___f_2576_, 1, v___x_2557_);
lean_closure_set(v___f_2576_, 2, v_declName_2562_);
lean_closure_set(v___f_2576_, 3, v___f_2571_);
lean_closure_set(v___f_2576_, 4, v___x_2572_);
lean_closure_set(v___f_2576_, 5, v_a_2554_);
lean_closure_set(v___f_2576_, 6, v_value_2564_);
lean_closure_set(v___f_2576_, 7, v_fvars_2552_);
lean_closure_set(v___f_2576_, 8, v_inst_2542_);
lean_closure_set(v___f_2576_, 9, v_inst_2543_);
lean_closure_set(v___f_2576_, 10, v_inst_2544_);
lean_closure_set(v___f_2576_, 11, v_pre_2545_);
lean_closure_set(v___f_2576_, 12, v_post_2546_);
lean_closure_set(v___f_2576_, 13, v___x_2573_);
lean_closure_set(v___f_2576_, 14, v___x_2574_);
lean_closure_set(v___f_2576_, 15, v___x_2575_);
lean_closure_set(v___f_2576_, 16, v_x_2550_);
lean_closure_set(v___f_2576_, 17, v_x_2551_);
lean_closure_set(v___f_2576_, 18, v_toBind_2567_);
v___x_2577_ = lean_expr_instantiate_rev(v_type_2563_, v_fvars_2552_);
lean_dec_ref(v_fvars_2552_);
lean_dec_ref(v_type_2563_);
v___x_2578_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2542_, v_inst_2543_, v_inst_2544_, v_pre_2545_, v_post_2546_, v_usedLetOnly_2547_, v_skipConstInApp_2548_, v_skipInstances_2549_, v_x_2550_, v_x_2551_, v___x_2577_, v_a_2554_);
v___x_2579_ = lean_apply_4(v_toBind_2567_, lean_box(0), lean_box(0), v___x_2578_, v___f_2576_);
return v___x_2579_;
}
else
{
lean_object* v_toBind_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___f_2584_; lean_object* v___x_2585_; lean_object* v___f_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; 
lean_dec_ref_known(v___x_2561_, 2);
lean_dec_ref(v___x_2557_);
v_toBind_2580_ = lean_ctor_get(v_inst_2542_, 1);
lean_inc_n(v_toBind_2580_, 2);
v___x_2581_ = lean_box(v_usedLetOnly_2547_);
v___x_2582_ = lean_box(v_skipConstInApp_2548_);
v___x_2583_ = lean_box(v_skipInstances_2549_);
lean_inc(v_a_2554_);
lean_inc(v_x_2551_);
lean_inc(v_post_2546_);
lean_inc(v_pre_2545_);
lean_inc_ref(v_inst_2544_);
lean_inc_n(v_inst_2543_, 2);
lean_inc_ref(v_inst_2542_);
v___f_2584_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3___boxed), 12, 11);
lean_closure_set(v___f_2584_, 0, v_inst_2542_);
lean_closure_set(v___f_2584_, 1, v_inst_2543_);
lean_closure_set(v___f_2584_, 2, v_inst_2544_);
lean_closure_set(v___f_2584_, 3, v_pre_2545_);
lean_closure_set(v___f_2584_, 4, v_post_2546_);
lean_closure_set(v___f_2584_, 5, v___x_2581_);
lean_closure_set(v___f_2584_, 6, v___x_2582_);
lean_closure_set(v___f_2584_, 7, v___x_2583_);
lean_closure_set(v___f_2584_, 8, v_x_2550_);
lean_closure_set(v___f_2584_, 9, v_x_2551_);
lean_closure_set(v___f_2584_, 10, v_a_2554_);
v___x_2585_ = lean_box(v_usedLetOnly_2547_);
lean_inc_ref(v_fvars_2552_);
v___f_2586_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__4___boxed), 6, 5);
lean_closure_set(v___f_2586_, 0, v_fvars_2552_);
lean_closure_set(v___f_2586_, 1, v___x_2585_);
lean_closure_set(v___f_2586_, 2, v_inst_2543_);
lean_closure_set(v___f_2586_, 3, v_toBind_2580_);
lean_closure_set(v___f_2586_, 4, v___f_2584_);
v___x_2587_ = lean_expr_instantiate_rev(v_e_2553_, v_fvars_2552_);
lean_dec_ref(v_fvars_2552_);
lean_dec_ref(v_e_2553_);
v___x_2588_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2542_, v_inst_2543_, v_inst_2544_, v_pre_2545_, v_post_2546_, v_usedLetOnly_2547_, v_skipConstInApp_2548_, v_skipInstances_2549_, v_x_2550_, v_x_2551_, v___x_2587_, v_a_2554_);
v___x_2589_ = lean_apply_4(v_toBind_2580_, lean_box(0), lean_box(0), v___x_2588_, v___f_2586_);
return v___x_2589_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__8(lean_object* v_expr_2590_, lean_object* v_data_2591_, lean_object* v_inst_2592_, lean_object* v_inst_2593_, lean_object* v_inst_2594_, lean_object* v_pre_2595_, lean_object* v_post_2596_, uint8_t v_usedLetOnly_2597_, uint8_t v_skipConstInApp_2598_, uint8_t v_skipInstances_2599_, lean_object* v_x_2600_, lean_object* v_x_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v_a_2604_){
_start:
{
size_t v___x_2605_; size_t v___x_2606_; uint8_t v___x_2607_; 
v___x_2605_ = lean_ptr_addr(v_expr_2590_);
v___x_2606_ = lean_ptr_addr(v_a_2604_);
v___x_2607_ = lean_usize_dec_eq(v___x_2605_, v___x_2606_);
if (v___x_2607_ == 0)
{
lean_object* v___x_2608_; lean_object* v___x_2609_; 
lean_dec_ref(v___y_2603_);
v___x_2608_ = l_Lean_Expr_mdata___override(v_data_2591_, v_a_2604_);
v___x_2609_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2592_, v_inst_2593_, v_inst_2594_, v_pre_2595_, v_post_2596_, v_usedLetOnly_2597_, v_skipConstInApp_2598_, v_skipInstances_2599_, v_x_2600_, v_x_2601_, v___x_2608_, v___y_2602_);
return v___x_2609_;
}
else
{
lean_object* v___x_2610_; 
lean_dec_ref(v_a_2604_);
lean_dec(v_data_2591_);
v___x_2610_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2592_, v_inst_2593_, v_inst_2594_, v_pre_2595_, v_post_2596_, v_usedLetOnly_2597_, v_skipConstInApp_2598_, v_skipInstances_2599_, v_x_2600_, v_x_2601_, v___y_2603_, v___y_2602_);
return v___x_2610_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__8___boxed(lean_object* v_expr_2611_, lean_object* v_data_2612_, lean_object* v_inst_2613_, lean_object* v_inst_2614_, lean_object* v_inst_2615_, lean_object* v_pre_2616_, lean_object* v_post_2617_, lean_object* v_usedLetOnly_2618_, lean_object* v_skipConstInApp_2619_, lean_object* v_skipInstances_2620_, lean_object* v_x_2621_, lean_object* v_x_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v_a_2625_){
_start:
{
uint8_t v_usedLetOnly_boxed_2626_; uint8_t v_skipConstInApp_boxed_2627_; uint8_t v_skipInstances_boxed_2628_; lean_object* v_res_2629_; 
v_usedLetOnly_boxed_2626_ = lean_unbox(v_usedLetOnly_2618_);
v_skipConstInApp_boxed_2627_ = lean_unbox(v_skipConstInApp_2619_);
v_skipInstances_boxed_2628_ = lean_unbox(v_skipInstances_2620_);
v_res_2629_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__8(v_expr_2611_, v_data_2612_, v_inst_2613_, v_inst_2614_, v_inst_2615_, v_pre_2616_, v_post_2617_, v_usedLetOnly_boxed_2626_, v_skipConstInApp_boxed_2627_, v_skipInstances_boxed_2628_, v_x_2621_, v_x_2622_, v___y_2623_, v___y_2624_, v_a_2625_);
lean_dec(v___y_2623_);
lean_dec_ref(v_expr_2611_);
return v_res_2629_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__10(lean_object* v_struct_2630_, lean_object* v_typeName_2631_, lean_object* v_idx_2632_, lean_object* v_inst_2633_, lean_object* v_inst_2634_, lean_object* v_inst_2635_, lean_object* v_pre_2636_, lean_object* v_post_2637_, uint8_t v_usedLetOnly_2638_, uint8_t v_skipConstInApp_2639_, uint8_t v_skipInstances_2640_, lean_object* v_x_2641_, lean_object* v_x_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v_a_2645_){
_start:
{
size_t v___x_2646_; size_t v___x_2647_; uint8_t v___x_2648_; 
v___x_2646_ = lean_ptr_addr(v_struct_2630_);
v___x_2647_ = lean_ptr_addr(v_a_2645_);
v___x_2648_ = lean_usize_dec_eq(v___x_2646_, v___x_2647_);
if (v___x_2648_ == 0)
{
lean_object* v___x_2649_; lean_object* v___x_2650_; 
lean_dec_ref(v___y_2644_);
v___x_2649_ = l_Lean_Expr_proj___override(v_typeName_2631_, v_idx_2632_, v_a_2645_);
v___x_2650_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2633_, v_inst_2634_, v_inst_2635_, v_pre_2636_, v_post_2637_, v_usedLetOnly_2638_, v_skipConstInApp_2639_, v_skipInstances_2640_, v_x_2641_, v_x_2642_, v___x_2649_, v___y_2643_);
return v___x_2650_;
}
else
{
lean_object* v___x_2651_; 
lean_dec_ref(v_a_2645_);
lean_dec(v_idx_2632_);
lean_dec(v_typeName_2631_);
v___x_2651_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2633_, v_inst_2634_, v_inst_2635_, v_pre_2636_, v_post_2637_, v_usedLetOnly_2638_, v_skipConstInApp_2639_, v_skipInstances_2640_, v_x_2641_, v_x_2642_, v___y_2644_, v___y_2643_);
return v___x_2651_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__10___boxed(lean_object* v_struct_2652_, lean_object* v_typeName_2653_, lean_object* v_idx_2654_, lean_object* v_inst_2655_, lean_object* v_inst_2656_, lean_object* v_inst_2657_, lean_object* v_pre_2658_, lean_object* v_post_2659_, lean_object* v_usedLetOnly_2660_, lean_object* v_skipConstInApp_2661_, lean_object* v_skipInstances_2662_, lean_object* v_x_2663_, lean_object* v_x_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v_a_2667_){
_start:
{
uint8_t v_usedLetOnly_boxed_2668_; uint8_t v_skipConstInApp_boxed_2669_; uint8_t v_skipInstances_boxed_2670_; lean_object* v_res_2671_; 
v_usedLetOnly_boxed_2668_ = lean_unbox(v_usedLetOnly_2660_);
v_skipConstInApp_boxed_2669_ = lean_unbox(v_skipConstInApp_2661_);
v_skipInstances_boxed_2670_ = lean_unbox(v_skipInstances_2662_);
v_res_2671_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__10(v_struct_2652_, v_typeName_2653_, v_idx_2654_, v_inst_2655_, v_inst_2656_, v_inst_2657_, v_pre_2658_, v_post_2659_, v_usedLetOnly_boxed_2668_, v_skipConstInApp_boxed_2669_, v_skipInstances_boxed_2670_, v_x_2663_, v_x_2664_, v___y_2665_, v___y_2666_, v_a_2667_);
lean_dec(v___y_2665_);
lean_dec_ref(v_struct_2652_);
return v_res_2671_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11(lean_object* v_toApplicative_2672_, lean_object* v_inst_2673_, lean_object* v_inst_2674_, lean_object* v_inst_2675_, lean_object* v_pre_2676_, lean_object* v_post_2677_, uint8_t v_usedLetOnly_2678_, uint8_t v_skipConstInApp_2679_, uint8_t v_skipInstances_2680_, lean_object* v_x_2681_, lean_object* v_x_2682_, lean_object* v___y_2683_, lean_object* v___f_2684_, lean_object* v_toBind_2685_, lean_object* v_e_2686_, lean_object* v_a_2687_){
_start:
{
lean_object* v___y_2689_; 
switch(lean_obj_tag(v_a_2687_))
{
case 0:
{
lean_object* v_e_2721_; lean_object* v_toPure_2722_; lean_object* v___x_2723_; 
lean_dec_ref(v_e_2686_);
lean_dec(v_toBind_2685_);
lean_dec(v___f_2684_);
lean_dec(v_x_2682_);
lean_dec(v_post_2677_);
lean_dec(v_pre_2676_);
lean_dec_ref(v_inst_2675_);
lean_dec(v_inst_2674_);
lean_dec_ref(v_inst_2673_);
v_e_2721_ = lean_ctor_get(v_a_2687_, 0);
lean_inc_ref(v_e_2721_);
lean_dec_ref_known(v_a_2687_, 1);
v_toPure_2722_ = lean_ctor_get(v_toApplicative_2672_, 1);
lean_inc(v_toPure_2722_);
lean_dec_ref(v_toApplicative_2672_);
v___x_2723_ = lean_apply_2(v_toPure_2722_, lean_box(0), v_e_2721_);
return v___x_2723_;
}
case 1:
{
lean_object* v_e_2724_; lean_object* v___x_2725_; 
lean_dec_ref(v_e_2686_);
lean_dec(v_toBind_2685_);
lean_dec(v___f_2684_);
lean_dec_ref(v_toApplicative_2672_);
v_e_2724_ = lean_ctor_get(v_a_2687_, 0);
lean_inc_ref(v_e_2724_);
lean_dec_ref_known(v_a_2687_, 1);
v___x_2725_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2673_, v_inst_2674_, v_inst_2675_, v_pre_2676_, v_post_2677_, v_usedLetOnly_2678_, v_skipConstInApp_2679_, v_skipInstances_2680_, v_x_2681_, v_x_2682_, v_e_2724_, v___y_2683_);
return v___x_2725_;
}
default: 
{
lean_object* v_e_x3f_2726_; 
lean_dec_ref(v_toApplicative_2672_);
v_e_x3f_2726_ = lean_ctor_get(v_a_2687_, 0);
lean_inc(v_e_x3f_2726_);
lean_dec_ref_known(v_a_2687_, 1);
if (lean_obj_tag(v_e_x3f_2726_) == 0)
{
v___y_2689_ = v_e_2686_;
goto v___jp_2688_;
}
else
{
lean_object* v_val_2727_; 
lean_dec_ref(v_e_2686_);
v_val_2727_ = lean_ctor_get(v_e_x3f_2726_, 0);
lean_inc(v_val_2727_);
lean_dec_ref_known(v_e_x3f_2726_, 1);
v___y_2689_ = v_val_2727_;
goto v___jp_2688_;
}
}
}
v___jp_2688_:
{
switch(lean_obj_tag(v___y_2689_))
{
case 7:
{
lean_object* v___x_2690_; lean_object* v___x_2691_; 
lean_dec(v_toBind_2685_);
lean_dec(v___f_2684_);
v___x_2690_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_2691_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(v_inst_2673_, v_inst_2674_, v_inst_2675_, v_pre_2676_, v_post_2677_, v_usedLetOnly_2678_, v_skipConstInApp_2679_, v_skipInstances_2680_, v_x_2681_, v_x_2682_, v___x_2690_, v___y_2689_, v___y_2683_);
return v___x_2691_;
}
case 6:
{
lean_object* v___x_2692_; lean_object* v___x_2693_; 
lean_dec(v_toBind_2685_);
lean_dec(v___f_2684_);
v___x_2692_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_2693_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(v_inst_2673_, v_inst_2674_, v_inst_2675_, v_pre_2676_, v_post_2677_, v_usedLetOnly_2678_, v_skipConstInApp_2679_, v_skipInstances_2680_, v_x_2681_, v_x_2682_, v___x_2692_, v___y_2689_, v___y_2683_);
return v___x_2693_;
}
case 8:
{
lean_object* v___x_2694_; lean_object* v___x_2695_; 
lean_dec(v_toBind_2685_);
lean_dec(v___f_2684_);
v___x_2694_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_2695_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(v_inst_2673_, v_inst_2674_, v_inst_2675_, v_pre_2676_, v_post_2677_, v_usedLetOnly_2678_, v_skipConstInApp_2679_, v_skipInstances_2680_, v_x_2681_, v_x_2682_, v___x_2694_, v___y_2689_, v___y_2683_);
return v___x_2695_;
}
case 5:
{
lean_object* v_dummy_2696_; lean_object* v_nargs_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_3361__overap_2701_; lean_object* v___x_2702_; 
lean_dec(v_toBind_2685_);
lean_dec(v_x_2682_);
lean_dec(v_post_2677_);
lean_dec(v_pre_2676_);
lean_dec_ref(v_inst_2675_);
lean_dec(v_inst_2674_);
lean_dec_ref(v_inst_2673_);
v_dummy_2696_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_2697_ = l_Lean_Expr_getAppNumArgs(v___y_2689_);
lean_inc(v_nargs_2697_);
v___x_2698_ = lean_mk_array(v_nargs_2697_, v_dummy_2696_);
v___x_2699_ = lean_unsigned_to_nat(1u);
v___x_2700_ = lean_nat_sub(v_nargs_2697_, v___x_2699_);
lean_dec(v_nargs_2697_);
v___x_3361__overap_2701_ = l_Lean_Expr_withAppAux___redArg(v___f_2684_, v___y_2689_, v___x_2698_, v___x_2700_);
lean_inc(v___y_2683_);
v___x_2702_ = lean_apply_1(v___x_3361__overap_2701_, v___y_2683_);
return v___x_2702_;
}
case 10:
{
lean_object* v_data_2703_; lean_object* v_expr_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___f_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; 
lean_dec(v___f_2684_);
v_data_2703_ = lean_ctor_get(v___y_2689_, 0);
lean_inc(v_data_2703_);
v_expr_2704_ = lean_ctor_get(v___y_2689_, 1);
lean_inc_ref_n(v_expr_2704_, 2);
v___x_2705_ = lean_box(v_usedLetOnly_2678_);
v___x_2706_ = lean_box(v_skipConstInApp_2679_);
v___x_2707_ = lean_box(v_skipInstances_2680_);
lean_inc(v___y_2683_);
lean_inc(v_x_2682_);
lean_inc(v_post_2677_);
lean_inc(v_pre_2676_);
lean_inc_ref(v_inst_2675_);
lean_inc(v_inst_2674_);
lean_inc_ref(v_inst_2673_);
v___f_2708_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__8___boxed), 15, 14);
lean_closure_set(v___f_2708_, 0, v_expr_2704_);
lean_closure_set(v___f_2708_, 1, v_data_2703_);
lean_closure_set(v___f_2708_, 2, v_inst_2673_);
lean_closure_set(v___f_2708_, 3, v_inst_2674_);
lean_closure_set(v___f_2708_, 4, v_inst_2675_);
lean_closure_set(v___f_2708_, 5, v_pre_2676_);
lean_closure_set(v___f_2708_, 6, v_post_2677_);
lean_closure_set(v___f_2708_, 7, v___x_2705_);
lean_closure_set(v___f_2708_, 8, v___x_2706_);
lean_closure_set(v___f_2708_, 9, v___x_2707_);
lean_closure_set(v___f_2708_, 10, v_x_2681_);
lean_closure_set(v___f_2708_, 11, v_x_2682_);
lean_closure_set(v___f_2708_, 12, v___y_2683_);
lean_closure_set(v___f_2708_, 13, v___y_2689_);
v___x_2709_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2673_, v_inst_2674_, v_inst_2675_, v_pre_2676_, v_post_2677_, v_usedLetOnly_2678_, v_skipConstInApp_2679_, v_skipInstances_2680_, v_x_2681_, v_x_2682_, v_expr_2704_, v___y_2683_);
v___x_2710_ = lean_apply_4(v_toBind_2685_, lean_box(0), lean_box(0), v___x_2709_, v___f_2708_);
return v___x_2710_;
}
case 11:
{
lean_object* v_typeName_2711_; lean_object* v_idx_2712_; lean_object* v_struct_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___f_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; 
lean_dec(v___f_2684_);
v_typeName_2711_ = lean_ctor_get(v___y_2689_, 0);
lean_inc(v_typeName_2711_);
v_idx_2712_ = lean_ctor_get(v___y_2689_, 1);
lean_inc(v_idx_2712_);
v_struct_2713_ = lean_ctor_get(v___y_2689_, 2);
lean_inc_ref_n(v_struct_2713_, 2);
v___x_2714_ = lean_box(v_usedLetOnly_2678_);
v___x_2715_ = lean_box(v_skipConstInApp_2679_);
v___x_2716_ = lean_box(v_skipInstances_2680_);
lean_inc(v___y_2683_);
lean_inc(v_x_2682_);
lean_inc(v_post_2677_);
lean_inc(v_pre_2676_);
lean_inc_ref(v_inst_2675_);
lean_inc(v_inst_2674_);
lean_inc_ref(v_inst_2673_);
v___f_2717_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__10___boxed), 16, 15);
lean_closure_set(v___f_2717_, 0, v_struct_2713_);
lean_closure_set(v___f_2717_, 1, v_typeName_2711_);
lean_closure_set(v___f_2717_, 2, v_idx_2712_);
lean_closure_set(v___f_2717_, 3, v_inst_2673_);
lean_closure_set(v___f_2717_, 4, v_inst_2674_);
lean_closure_set(v___f_2717_, 5, v_inst_2675_);
lean_closure_set(v___f_2717_, 6, v_pre_2676_);
lean_closure_set(v___f_2717_, 7, v_post_2677_);
lean_closure_set(v___f_2717_, 8, v___x_2714_);
lean_closure_set(v___f_2717_, 9, v___x_2715_);
lean_closure_set(v___f_2717_, 10, v___x_2716_);
lean_closure_set(v___f_2717_, 11, v_x_2681_);
lean_closure_set(v___f_2717_, 12, v_x_2682_);
lean_closure_set(v___f_2717_, 13, v___y_2683_);
lean_closure_set(v___f_2717_, 14, v___y_2689_);
v___x_2718_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2673_, v_inst_2674_, v_inst_2675_, v_pre_2676_, v_post_2677_, v_usedLetOnly_2678_, v_skipConstInApp_2679_, v_skipInstances_2680_, v_x_2681_, v_x_2682_, v_struct_2713_, v___y_2683_);
v___x_2719_ = lean_apply_4(v_toBind_2685_, lean_box(0), lean_box(0), v___x_2718_, v___f_2717_);
return v___x_2719_;
}
default: 
{
lean_object* v___x_2720_; 
lean_dec(v_toBind_2685_);
lean_dec(v___f_2684_);
v___x_2720_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2673_, v_inst_2674_, v_inst_2675_, v_pre_2676_, v_post_2677_, v_usedLetOnly_2678_, v_skipConstInApp_2679_, v_skipInstances_2680_, v_x_2681_, v_x_2682_, v___y_2689_, v___y_2683_);
return v___x_2720_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___boxed(lean_object* v_toApplicative_2728_, lean_object* v_inst_2729_, lean_object* v_inst_2730_, lean_object* v_inst_2731_, lean_object* v_pre_2732_, lean_object* v_post_2733_, lean_object* v_usedLetOnly_2734_, lean_object* v_skipConstInApp_2735_, lean_object* v_skipInstances_2736_, lean_object* v_x_2737_, lean_object* v_x_2738_, lean_object* v___y_2739_, lean_object* v___f_2740_, lean_object* v_toBind_2741_, lean_object* v_e_2742_, lean_object* v_a_2743_){
_start:
{
uint8_t v_usedLetOnly_boxed_2744_; uint8_t v_skipConstInApp_boxed_2745_; uint8_t v_skipInstances_boxed_2746_; lean_object* v_res_2747_; 
v_usedLetOnly_boxed_2744_ = lean_unbox(v_usedLetOnly_2734_);
v_skipConstInApp_boxed_2745_ = lean_unbox(v_skipConstInApp_2735_);
v_skipInstances_boxed_2746_ = lean_unbox(v_skipInstances_2736_);
v_res_2747_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11(v_toApplicative_2728_, v_inst_2729_, v_inst_2730_, v_inst_2731_, v_pre_2732_, v_post_2733_, v_usedLetOnly_boxed_2744_, v_skipConstInApp_boxed_2745_, v_skipInstances_boxed_2746_, v_x_2737_, v_x_2738_, v___y_2739_, v___f_2740_, v_toBind_2741_, v_e_2742_, v_a_2743_);
lean_dec(v___y_2739_);
return v_res_2747_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12(lean_object* v_toApplicative_2748_, lean_object* v_inst_2749_, lean_object* v_inst_2750_, lean_object* v_inst_2751_, lean_object* v_pre_2752_, lean_object* v_post_2753_, uint8_t v_usedLetOnly_2754_, uint8_t v_skipConstInApp_2755_, uint8_t v_skipInstances_2756_, lean_object* v_x_2757_, lean_object* v_x_2758_, lean_object* v___f_2759_, lean_object* v_toBind_2760_, lean_object* v_e_2761_, lean_object* v_____r_2762_, lean_object* v___y_2763_){
_start:
{
lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___f_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; 
v___x_2764_ = lean_box(v_usedLetOnly_2754_);
v___x_2765_ = lean_box(v_skipConstInApp_2755_);
v___x_2766_ = lean_box(v_skipInstances_2756_);
lean_inc_ref(v_e_2761_);
lean_inc(v_toBind_2760_);
lean_inc(v___y_2763_);
lean_inc(v_pre_2752_);
v___f_2767_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___boxed), 16, 15);
lean_closure_set(v___f_2767_, 0, v_toApplicative_2748_);
lean_closure_set(v___f_2767_, 1, v_inst_2749_);
lean_closure_set(v___f_2767_, 2, v_inst_2750_);
lean_closure_set(v___f_2767_, 3, v_inst_2751_);
lean_closure_set(v___f_2767_, 4, v_pre_2752_);
lean_closure_set(v___f_2767_, 5, v_post_2753_);
lean_closure_set(v___f_2767_, 6, v___x_2764_);
lean_closure_set(v___f_2767_, 7, v___x_2765_);
lean_closure_set(v___f_2767_, 8, v___x_2766_);
lean_closure_set(v___f_2767_, 9, v_x_2757_);
lean_closure_set(v___f_2767_, 10, v_x_2758_);
lean_closure_set(v___f_2767_, 11, v___y_2763_);
lean_closure_set(v___f_2767_, 12, v___f_2759_);
lean_closure_set(v___f_2767_, 13, v_toBind_2760_);
lean_closure_set(v___f_2767_, 14, v_e_2761_);
v___x_2768_ = lean_apply_1(v_pre_2752_, v_e_2761_);
v___x_2769_ = lean_apply_4(v_toBind_2760_, lean_box(0), lean_box(0), v___x_2768_, v___f_2767_);
return v___x_2769_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12___boxed(lean_object* v_toApplicative_2770_, lean_object* v_inst_2771_, lean_object* v_inst_2772_, lean_object* v_inst_2773_, lean_object* v_pre_2774_, lean_object* v_post_2775_, lean_object* v_usedLetOnly_2776_, lean_object* v_skipConstInApp_2777_, lean_object* v_skipInstances_2778_, lean_object* v_x_2779_, lean_object* v_x_2780_, lean_object* v___f_2781_, lean_object* v_toBind_2782_, lean_object* v_e_2783_, lean_object* v_____r_2784_, lean_object* v___y_2785_){
_start:
{
uint8_t v_usedLetOnly_boxed_2786_; uint8_t v_skipConstInApp_boxed_2787_; uint8_t v_skipInstances_boxed_2788_; lean_object* v_res_2789_; 
v_usedLetOnly_boxed_2786_ = lean_unbox(v_usedLetOnly_2776_);
v_skipConstInApp_boxed_2787_ = lean_unbox(v_skipConstInApp_2777_);
v_skipInstances_boxed_2788_ = lean_unbox(v_skipInstances_2778_);
v_res_2789_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12(v_toApplicative_2770_, v_inst_2771_, v_inst_2772_, v_inst_2773_, v_pre_2774_, v_post_2775_, v_usedLetOnly_boxed_2786_, v_skipConstInApp_boxed_2787_, v_skipInstances_boxed_2788_, v_x_2779_, v_x_2780_, v___f_2781_, v_toBind_2782_, v_e_2783_, v_____r_2784_, v___y_2785_);
lean_dec(v___y_2785_);
return v_res_2789_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(lean_object* v_inst_2790_, lean_object* v_inst_2791_, lean_object* v_inst_2792_, lean_object* v_pre_2793_, lean_object* v_post_2794_, uint8_t v_usedLetOnly_2795_, uint8_t v_skipConstInApp_2796_, uint8_t v_skipInstances_2797_, lean_object* v_x_2798_, lean_object* v_x_2799_, lean_object* v_e_2800_, lean_object* v_a_2801_){
_start:
{
lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___f_2806_; lean_object* v___f_2807_; lean_object* v___x_2808_; lean_object* v_toApplicative_2809_; lean_object* v_toBind_2810_; lean_object* v___f_2811_; lean_object* v___f_2812_; lean_object* v___f_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___f_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___f_2821_; lean_object* v___f_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; 
v___x_2802_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0));
v___x_2803_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1));
lean_inc_ref_n(v_inst_2790_, 3);
v___x_2804_ = l_Lean_MonadCacheT_instMonad___redArg(v_x_2798_, v___x_2802_, v___x_2803_, v_inst_2790_);
v___x_2805_ = l_Lean_MonadCacheT_instMonadControl___redArg(v_x_2798_, v___x_2802_, v___x_2803_);
lean_inc_ref_n(v_inst_2792_, 3);
lean_inc_ref(v___x_2805_);
v___f_2806_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_2806_, 0, v___x_2805_);
lean_closure_set(v___f_2806_, 1, v_inst_2792_);
v___f_2807_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_2807_, 0, v___x_2805_);
lean_closure_set(v___f_2807_, 1, v_inst_2792_);
v___x_2808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2808_, 0, v___f_2806_);
lean_ctor_set(v___x_2808_, 1, v___f_2807_);
v_toApplicative_2809_ = lean_ctor_get(v_inst_2790_, 0);
lean_inc_ref_n(v_toApplicative_2809_, 6);
v_toBind_2810_ = lean_ctor_get(v_inst_2790_, 1);
lean_inc_n(v_toBind_2810_, 6);
v___f_2811_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2811_, 0, v_toApplicative_2809_);
lean_inc_n(v_x_2799_, 3);
lean_inc_n(v_a_2801_, 3);
lean_inc_ref_n(v_e_2800_, 2);
v___f_2812_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_2812_, 0, v_toApplicative_2809_);
lean_closure_set(v___f_2812_, 1, v___x_2802_);
lean_closure_set(v___f_2812_, 2, v___x_2803_);
lean_closure_set(v___f_2812_, 3, v_e_2800_);
lean_closure_set(v___f_2812_, 4, v_a_2801_);
lean_closure_set(v___f_2812_, 5, v_x_2799_);
lean_closure_set(v___f_2812_, 6, v_toBind_2810_);
v___f_2813_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__3___boxed), 5, 4);
lean_closure_set(v___f_2813_, 0, v_toApplicative_2809_);
lean_closure_set(v___f_2813_, 1, v___x_2802_);
lean_closure_set(v___f_2813_, 2, v___x_2803_);
lean_closure_set(v___f_2813_, 3, v_e_2800_);
v___x_2814_ = lean_box(v_skipInstances_2797_);
v___x_2815_ = lean_box(v_usedLetOnly_2795_);
v___x_2816_ = lean_box(v_skipConstInApp_2796_);
lean_inc_ref(v___x_2804_);
lean_inc(v_post_2794_);
lean_inc(v_pre_2793_);
lean_inc_n(v_inst_2791_, 2);
v___f_2817_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__9___boxed), 17, 14);
lean_closure_set(v___f_2817_, 0, v___x_2814_);
lean_closure_set(v___f_2817_, 1, v_inst_2790_);
lean_closure_set(v___f_2817_, 2, v_inst_2791_);
lean_closure_set(v___f_2817_, 3, v_inst_2792_);
lean_closure_set(v___f_2817_, 4, v_pre_2793_);
lean_closure_set(v___f_2817_, 5, v_post_2794_);
lean_closure_set(v___f_2817_, 6, v___x_2815_);
lean_closure_set(v___f_2817_, 7, v___x_2816_);
lean_closure_set(v___f_2817_, 8, v_x_2798_);
lean_closure_set(v___f_2817_, 9, v_x_2799_);
lean_closure_set(v___f_2817_, 10, v___x_2804_);
lean_closure_set(v___f_2817_, 11, v_toBind_2810_);
lean_closure_set(v___f_2817_, 12, v_toApplicative_2809_);
lean_closure_set(v___f_2817_, 13, v___f_2811_);
v___x_2818_ = lean_box(v_usedLetOnly_2795_);
v___x_2819_ = lean_box(v_skipConstInApp_2796_);
v___x_2820_ = lean_box(v_skipInstances_2797_);
v___f_2821_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12___boxed), 16, 14);
lean_closure_set(v___f_2821_, 0, v_toApplicative_2809_);
lean_closure_set(v___f_2821_, 1, v_inst_2790_);
lean_closure_set(v___f_2821_, 2, v_inst_2791_);
lean_closure_set(v___f_2821_, 3, v_inst_2792_);
lean_closure_set(v___f_2821_, 4, v_pre_2793_);
lean_closure_set(v___f_2821_, 5, v_post_2794_);
lean_closure_set(v___f_2821_, 6, v___x_2818_);
lean_closure_set(v___f_2821_, 7, v___x_2819_);
lean_closure_set(v___f_2821_, 8, v___x_2820_);
lean_closure_set(v___f_2821_, 9, v_x_2798_);
lean_closure_set(v___f_2821_, 10, v_x_2799_);
lean_closure_set(v___f_2821_, 11, v___f_2817_);
lean_closure_set(v___f_2821_, 12, v_toBind_2810_);
lean_closure_set(v___f_2821_, 13, v_e_2800_);
v___f_2822_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14___boxed), 13, 12);
lean_closure_set(v___f_2822_, 0, v_inst_2791_);
lean_closure_set(v___f_2822_, 1, v_x_2798_);
lean_closure_set(v___f_2822_, 2, v___x_2802_);
lean_closure_set(v___f_2822_, 3, v___x_2803_);
lean_closure_set(v___f_2822_, 4, v_inst_2790_);
lean_closure_set(v___f_2822_, 5, v___f_2821_);
lean_closure_set(v___f_2822_, 6, v___x_2808_);
lean_closure_set(v___f_2822_, 7, v___x_2804_);
lean_closure_set(v___f_2822_, 8, v_a_2801_);
lean_closure_set(v___f_2822_, 9, v_toBind_2810_);
lean_closure_set(v___f_2822_, 10, v___f_2812_);
lean_closure_set(v___f_2822_, 11, v_toApplicative_2809_);
v___x_2823_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2823_, 0, lean_box(0));
lean_closure_set(v___x_2823_, 1, lean_box(0));
lean_closure_set(v___x_2823_, 2, v_a_2801_);
v___x_2824_ = lean_apply_2(v_x_2799_, lean_box(0), v___x_2823_);
v___x_2825_ = lean_apply_4(v_toBind_2810_, lean_box(0), lean_box(0), v___x_2824_, v___f_2813_);
v___x_2826_ = lean_apply_4(v_toBind_2810_, lean_box(0), lean_box(0), v___x_2825_, v___f_2822_);
return v___x_2826_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___lam__0(lean_object* v_toApplicative_2827_, lean_object* v_inst_2828_, lean_object* v_inst_2829_, lean_object* v_inst_2830_, lean_object* v_pre_2831_, lean_object* v_post_2832_, uint8_t v_usedLetOnly_2833_, uint8_t v_skipConstInApp_2834_, uint8_t v_skipInstances_2835_, lean_object* v_x_2836_, lean_object* v_x_2837_, lean_object* v_a_2838_, lean_object* v_e_2839_, lean_object* v_a_2840_){
_start:
{
lean_object* v___y_2842_; 
switch(lean_obj_tag(v_a_2840_))
{
case 0:
{
lean_object* v_e_2845_; lean_object* v_toPure_2846_; lean_object* v___x_2847_; 
lean_dec_ref(v_e_2839_);
lean_dec(v_x_2837_);
lean_dec(v_post_2832_);
lean_dec(v_pre_2831_);
lean_dec_ref(v_inst_2830_);
lean_dec(v_inst_2829_);
lean_dec_ref(v_inst_2828_);
v_e_2845_ = lean_ctor_get(v_a_2840_, 0);
lean_inc_ref(v_e_2845_);
lean_dec_ref_known(v_a_2840_, 1);
v_toPure_2846_ = lean_ctor_get(v_toApplicative_2827_, 1);
lean_inc(v_toPure_2846_);
lean_dec_ref(v_toApplicative_2827_);
v___x_2847_ = lean_apply_2(v_toPure_2846_, lean_box(0), v_e_2845_);
return v___x_2847_;
}
case 1:
{
lean_object* v_e_2848_; lean_object* v___x_2849_; 
lean_dec_ref(v_e_2839_);
lean_dec_ref(v_toApplicative_2827_);
v_e_2848_ = lean_ctor_get(v_a_2840_, 0);
lean_inc_ref(v_e_2848_);
lean_dec_ref_known(v_a_2840_, 1);
v___x_2849_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2828_, v_inst_2829_, v_inst_2830_, v_pre_2831_, v_post_2832_, v_usedLetOnly_2833_, v_skipConstInApp_2834_, v_skipInstances_2835_, v_x_2836_, v_x_2837_, v_e_2848_, v_a_2838_);
return v___x_2849_;
}
default: 
{
lean_object* v_e_x3f_2850_; 
lean_dec(v_x_2837_);
lean_dec(v_post_2832_);
lean_dec(v_pre_2831_);
lean_dec_ref(v_inst_2830_);
lean_dec(v_inst_2829_);
lean_dec_ref(v_inst_2828_);
v_e_x3f_2850_ = lean_ctor_get(v_a_2840_, 0);
lean_inc(v_e_x3f_2850_);
lean_dec_ref_known(v_a_2840_, 1);
if (lean_obj_tag(v_e_x3f_2850_) == 0)
{
v___y_2842_ = v_e_2839_;
goto v___jp_2841_;
}
else
{
lean_object* v_val_2851_; 
lean_dec_ref(v_e_2839_);
v_val_2851_ = lean_ctor_get(v_e_x3f_2850_, 0);
lean_inc(v_val_2851_);
lean_dec_ref_known(v_e_x3f_2850_, 1);
v___y_2842_ = v_val_2851_;
goto v___jp_2841_;
}
}
}
v___jp_2841_:
{
lean_object* v_toPure_2843_; lean_object* v___x_2844_; 
v_toPure_2843_ = lean_ctor_get(v_toApplicative_2827_, 1);
lean_inc(v_toPure_2843_);
lean_dec_ref(v_toApplicative_2827_);
v___x_2844_ = lean_apply_2(v_toPure_2843_, lean_box(0), v___y_2842_);
return v___x_2844_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___lam__0___boxed(lean_object* v_toApplicative_2852_, lean_object* v_inst_2853_, lean_object* v_inst_2854_, lean_object* v_inst_2855_, lean_object* v_pre_2856_, lean_object* v_post_2857_, lean_object* v_usedLetOnly_2858_, lean_object* v_skipConstInApp_2859_, lean_object* v_skipInstances_2860_, lean_object* v_x_2861_, lean_object* v_x_2862_, lean_object* v_a_2863_, lean_object* v_e_2864_, lean_object* v_a_2865_){
_start:
{
uint8_t v_usedLetOnly_boxed_2866_; uint8_t v_skipConstInApp_boxed_2867_; uint8_t v_skipInstances_boxed_2868_; lean_object* v_res_2869_; 
v_usedLetOnly_boxed_2866_ = lean_unbox(v_usedLetOnly_2858_);
v_skipConstInApp_boxed_2867_ = lean_unbox(v_skipConstInApp_2859_);
v_skipInstances_boxed_2868_ = lean_unbox(v_skipInstances_2860_);
v_res_2869_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___lam__0(v_toApplicative_2852_, v_inst_2853_, v_inst_2854_, v_inst_2855_, v_pre_2856_, v_post_2857_, v_usedLetOnly_boxed_2866_, v_skipConstInApp_boxed_2867_, v_skipInstances_boxed_2868_, v_x_2861_, v_x_2862_, v_a_2863_, v_e_2864_, v_a_2865_);
lean_dec(v_a_2863_);
return v_res_2869_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(lean_object* v_inst_2870_, lean_object* v_inst_2871_, lean_object* v_inst_2872_, lean_object* v_pre_2873_, lean_object* v_post_2874_, uint8_t v_usedLetOnly_2875_, uint8_t v_skipConstInApp_2876_, uint8_t v_skipInstances_2877_, lean_object* v_x_2878_, lean_object* v_x_2879_, lean_object* v_e_2880_, lean_object* v_a_2881_){
_start:
{
lean_object* v_toApplicative_2882_; lean_object* v_toBind_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___f_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; 
v_toApplicative_2882_ = lean_ctor_get(v_inst_2870_, 0);
lean_inc_ref(v_toApplicative_2882_);
v_toBind_2883_ = lean_ctor_get(v_inst_2870_, 1);
lean_inc(v_toBind_2883_);
v___x_2884_ = lean_box(v_usedLetOnly_2875_);
v___x_2885_ = lean_box(v_skipConstInApp_2876_);
v___x_2886_ = lean_box(v_skipInstances_2877_);
lean_inc_ref(v_e_2880_);
lean_inc(v_a_2881_);
lean_inc(v_post_2874_);
v___f_2887_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___lam__0___boxed), 14, 13);
lean_closure_set(v___f_2887_, 0, v_toApplicative_2882_);
lean_closure_set(v___f_2887_, 1, v_inst_2870_);
lean_closure_set(v___f_2887_, 2, v_inst_2871_);
lean_closure_set(v___f_2887_, 3, v_inst_2872_);
lean_closure_set(v___f_2887_, 4, v_pre_2873_);
lean_closure_set(v___f_2887_, 5, v_post_2874_);
lean_closure_set(v___f_2887_, 6, v___x_2884_);
lean_closure_set(v___f_2887_, 7, v___x_2885_);
lean_closure_set(v___f_2887_, 8, v___x_2886_);
lean_closure_set(v___f_2887_, 9, v_x_2878_);
lean_closure_set(v___f_2887_, 10, v_x_2879_);
lean_closure_set(v___f_2887_, 11, v_a_2881_);
lean_closure_set(v___f_2887_, 12, v_e_2880_);
v___x_2888_ = lean_apply_1(v_post_2874_, v_e_2880_);
v___x_2889_ = lean_apply_4(v_toBind_2883_, lean_box(0), lean_box(0), v___x_2888_, v___f_2887_);
return v___x_2889_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3(lean_object* v_inst_2890_, lean_object* v_inst_2891_, lean_object* v_inst_2892_, lean_object* v_pre_2893_, lean_object* v_post_2894_, uint8_t v_usedLetOnly_2895_, uint8_t v_skipConstInApp_2896_, uint8_t v_skipInstances_2897_, lean_object* v_x_2898_, lean_object* v_x_2899_, lean_object* v_a_2900_, lean_object* v_a_2901_){
_start:
{
lean_object* v___x_2902_; 
v___x_2902_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2890_, v_inst_2891_, v_inst_2892_, v_pre_2893_, v_post_2894_, v_usedLetOnly_2895_, v_skipConstInApp_2896_, v_skipInstances_2897_, v_x_2898_, v_x_2899_, v_a_2901_, v_a_2900_);
return v___x_2902_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___boxed(lean_object* v_inst_2903_, lean_object* v_inst_2904_, lean_object* v_inst_2905_, lean_object* v_pre_2906_, lean_object* v_post_2907_, lean_object* v_usedLetOnly_2908_, lean_object* v_skipConstInApp_2909_, lean_object* v_skipInstances_2910_, lean_object* v_x_2911_, lean_object* v_x_2912_, lean_object* v_e_2913_, lean_object* v_a_2914_){
_start:
{
uint8_t v_usedLetOnly_boxed_2915_; uint8_t v_skipConstInApp_boxed_2916_; uint8_t v_skipInstances_boxed_2917_; lean_object* v_res_2918_; 
v_usedLetOnly_boxed_2915_ = lean_unbox(v_usedLetOnly_2908_);
v_skipConstInApp_boxed_2916_ = lean_unbox(v_skipConstInApp_2909_);
v_skipInstances_boxed_2917_ = lean_unbox(v_skipInstances_2910_);
v_res_2918_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2903_, v_inst_2904_, v_inst_2905_, v_pre_2906_, v_post_2907_, v_usedLetOnly_boxed_2915_, v_skipConstInApp_boxed_2916_, v_skipInstances_boxed_2917_, v_x_2911_, v_x_2912_, v_e_2913_, v_a_2914_);
lean_dec(v_a_2914_);
return v_res_2918_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___boxed(lean_object* v_inst_2919_, lean_object* v_inst_2920_, lean_object* v_inst_2921_, lean_object* v_pre_2922_, lean_object* v_post_2923_, lean_object* v_usedLetOnly_2924_, lean_object* v_skipConstInApp_2925_, lean_object* v_skipInstances_2926_, lean_object* v_x_2927_, lean_object* v_x_2928_, lean_object* v_fvars_2929_, lean_object* v_e_2930_, lean_object* v_a_2931_){
_start:
{
uint8_t v_usedLetOnly_boxed_2932_; uint8_t v_skipConstInApp_boxed_2933_; uint8_t v_skipInstances_boxed_2934_; lean_object* v_res_2935_; 
v_usedLetOnly_boxed_2932_ = lean_unbox(v_usedLetOnly_2924_);
v_skipConstInApp_boxed_2933_ = lean_unbox(v_skipConstInApp_2925_);
v_skipInstances_boxed_2934_ = lean_unbox(v_skipInstances_2926_);
v_res_2935_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(v_inst_2919_, v_inst_2920_, v_inst_2921_, v_pre_2922_, v_post_2923_, v_usedLetOnly_boxed_2932_, v_skipConstInApp_boxed_2933_, v_skipInstances_boxed_2934_, v_x_2927_, v_x_2928_, v_fvars_2929_, v_e_2930_, v_a_2931_);
lean_dec(v_a_2931_);
return v_res_2935_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___boxed(lean_object* v_inst_2936_, lean_object* v_inst_2937_, lean_object* v_inst_2938_, lean_object* v_pre_2939_, lean_object* v_post_2940_, lean_object* v_usedLetOnly_2941_, lean_object* v_skipConstInApp_2942_, lean_object* v_skipInstances_2943_, lean_object* v_x_2944_, lean_object* v_x_2945_, lean_object* v_fvars_2946_, lean_object* v_e_2947_, lean_object* v_a_2948_){
_start:
{
uint8_t v_usedLetOnly_boxed_2949_; uint8_t v_skipConstInApp_boxed_2950_; uint8_t v_skipInstances_boxed_2951_; lean_object* v_res_2952_; 
v_usedLetOnly_boxed_2949_ = lean_unbox(v_usedLetOnly_2941_);
v_skipConstInApp_boxed_2950_ = lean_unbox(v_skipConstInApp_2942_);
v_skipInstances_boxed_2951_ = lean_unbox(v_skipInstances_2943_);
v_res_2952_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(v_inst_2936_, v_inst_2937_, v_inst_2938_, v_pre_2939_, v_post_2940_, v_usedLetOnly_boxed_2949_, v_skipConstInApp_boxed_2950_, v_skipInstances_boxed_2951_, v_x_2944_, v_x_2945_, v_fvars_2946_, v_e_2947_, v_a_2948_);
lean_dec(v_a_2948_);
return v_res_2952_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___boxed(lean_object* v_inst_2953_, lean_object* v_inst_2954_, lean_object* v_inst_2955_, lean_object* v_pre_2956_, lean_object* v_post_2957_, lean_object* v_usedLetOnly_2958_, lean_object* v_skipConstInApp_2959_, lean_object* v_skipInstances_2960_, lean_object* v_x_2961_, lean_object* v_x_2962_, lean_object* v_fvars_2963_, lean_object* v_e_2964_, lean_object* v_a_2965_){
_start:
{
uint8_t v_usedLetOnly_boxed_2966_; uint8_t v_skipConstInApp_boxed_2967_; uint8_t v_skipInstances_boxed_2968_; lean_object* v_res_2969_; 
v_usedLetOnly_boxed_2966_ = lean_unbox(v_usedLetOnly_2958_);
v_skipConstInApp_boxed_2967_ = lean_unbox(v_skipConstInApp_2959_);
v_skipInstances_boxed_2968_ = lean_unbox(v_skipInstances_2960_);
v_res_2969_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(v_inst_2953_, v_inst_2954_, v_inst_2955_, v_pre_2956_, v_post_2957_, v_usedLetOnly_boxed_2966_, v_skipConstInApp_boxed_2967_, v_skipInstances_boxed_2968_, v_x_2961_, v_x_2962_, v_fvars_2963_, v_e_2964_, v_a_2965_);
lean_dec(v_a_2965_);
return v_res_2969_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit(lean_object* v_m_2970_, lean_object* v_inst_2971_, lean_object* v_inst_2972_, lean_object* v_inst_2973_, lean_object* v_pre_2974_, lean_object* v_post_2975_, uint8_t v_usedLetOnly_2976_, uint8_t v_skipConstInApp_2977_, uint8_t v_skipInstances_2978_, lean_object* v_x_2979_, lean_object* v_x_2980_, lean_object* v_e_2981_, lean_object* v_a_2982_){
_start:
{
lean_object* v___x_2983_; 
v___x_2983_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2971_, v_inst_2972_, v_inst_2973_, v_pre_2974_, v_post_2975_, v_usedLetOnly_2976_, v_skipConstInApp_2977_, v_skipInstances_2978_, v_x_2979_, v_x_2980_, v_e_2981_, v_a_2982_);
return v___x_2983_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___boxed(lean_object* v_m_2984_, lean_object* v_inst_2985_, lean_object* v_inst_2986_, lean_object* v_inst_2987_, lean_object* v_pre_2988_, lean_object* v_post_2989_, lean_object* v_usedLetOnly_2990_, lean_object* v_skipConstInApp_2991_, lean_object* v_skipInstances_2992_, lean_object* v_x_2993_, lean_object* v_x_2994_, lean_object* v_e_2995_, lean_object* v_a_2996_){
_start:
{
uint8_t v_usedLetOnly_boxed_2997_; uint8_t v_skipConstInApp_boxed_2998_; uint8_t v_skipInstances_boxed_2999_; lean_object* v_res_3000_; 
v_usedLetOnly_boxed_2997_ = lean_unbox(v_usedLetOnly_2990_);
v_skipConstInApp_boxed_2998_ = lean_unbox(v_skipConstInApp_2991_);
v_skipInstances_boxed_2999_ = lean_unbox(v_skipInstances_2992_);
v_res_3000_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit(v_m_2984_, v_inst_2985_, v_inst_2986_, v_inst_2987_, v_pre_2988_, v_post_2989_, v_usedLetOnly_boxed_2997_, v_skipConstInApp_boxed_2998_, v_skipInstances_boxed_2999_, v_x_2993_, v_x_2994_, v_e_2995_, v_a_2996_);
lean_dec(v_a_2996_);
return v_res_3000_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet(lean_object* v_m_3001_, lean_object* v_inst_3002_, lean_object* v_inst_3003_, lean_object* v_inst_3004_, lean_object* v_pre_3005_, lean_object* v_post_3006_, uint8_t v_usedLetOnly_3007_, uint8_t v_skipConstInApp_3008_, uint8_t v_skipInstances_3009_, lean_object* v_x_3010_, lean_object* v_x_3011_, lean_object* v_fvars_3012_, lean_object* v_e_3013_, lean_object* v_a_3014_){
_start:
{
lean_object* v___x_3015_; 
v___x_3015_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(v_inst_3002_, v_inst_3003_, v_inst_3004_, v_pre_3005_, v_post_3006_, v_usedLetOnly_3007_, v_skipConstInApp_3008_, v_skipInstances_3009_, v_x_3010_, v_x_3011_, v_fvars_3012_, v_e_3013_, v_a_3014_);
return v___x_3015_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___boxed(lean_object* v_m_3016_, lean_object* v_inst_3017_, lean_object* v_inst_3018_, lean_object* v_inst_3019_, lean_object* v_pre_3020_, lean_object* v_post_3021_, lean_object* v_usedLetOnly_3022_, lean_object* v_skipConstInApp_3023_, lean_object* v_skipInstances_3024_, lean_object* v_x_3025_, lean_object* v_x_3026_, lean_object* v_fvars_3027_, lean_object* v_e_3028_, lean_object* v_a_3029_){
_start:
{
uint8_t v_usedLetOnly_boxed_3030_; uint8_t v_skipConstInApp_boxed_3031_; uint8_t v_skipInstances_boxed_3032_; lean_object* v_res_3033_; 
v_usedLetOnly_boxed_3030_ = lean_unbox(v_usedLetOnly_3022_);
v_skipConstInApp_boxed_3031_ = lean_unbox(v_skipConstInApp_3023_);
v_skipInstances_boxed_3032_ = lean_unbox(v_skipInstances_3024_);
v_res_3033_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet(v_m_3016_, v_inst_3017_, v_inst_3018_, v_inst_3019_, v_pre_3020_, v_post_3021_, v_usedLetOnly_boxed_3030_, v_skipConstInApp_boxed_3031_, v_skipInstances_boxed_3032_, v_x_3025_, v_x_3026_, v_fvars_3027_, v_e_3028_, v_a_3029_);
lean_dec(v_a_3029_);
return v_res_3033_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost(lean_object* v_m_3034_, lean_object* v_inst_3035_, lean_object* v_inst_3036_, lean_object* v_inst_3037_, lean_object* v_pre_3038_, lean_object* v_post_3039_, uint8_t v_usedLetOnly_3040_, uint8_t v_skipConstInApp_3041_, uint8_t v_skipInstances_3042_, lean_object* v_x_3043_, lean_object* v_x_3044_, lean_object* v_e_3045_, lean_object* v_a_3046_){
_start:
{
lean_object* v___x_3047_; 
v___x_3047_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_3035_, v_inst_3036_, v_inst_3037_, v_pre_3038_, v_post_3039_, v_usedLetOnly_3040_, v_skipConstInApp_3041_, v_skipInstances_3042_, v_x_3043_, v_x_3044_, v_e_3045_, v_a_3046_);
return v___x_3047_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___boxed(lean_object* v_m_3048_, lean_object* v_inst_3049_, lean_object* v_inst_3050_, lean_object* v_inst_3051_, lean_object* v_pre_3052_, lean_object* v_post_3053_, lean_object* v_usedLetOnly_3054_, lean_object* v_skipConstInApp_3055_, lean_object* v_skipInstances_3056_, lean_object* v_x_3057_, lean_object* v_x_3058_, lean_object* v_e_3059_, lean_object* v_a_3060_){
_start:
{
uint8_t v_usedLetOnly_boxed_3061_; uint8_t v_skipConstInApp_boxed_3062_; uint8_t v_skipInstances_boxed_3063_; lean_object* v_res_3064_; 
v_usedLetOnly_boxed_3061_ = lean_unbox(v_usedLetOnly_3054_);
v_skipConstInApp_boxed_3062_ = lean_unbox(v_skipConstInApp_3055_);
v_skipInstances_boxed_3063_ = lean_unbox(v_skipInstances_3056_);
v_res_3064_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost(v_m_3048_, v_inst_3049_, v_inst_3050_, v_inst_3051_, v_pre_3052_, v_post_3053_, v_usedLetOnly_boxed_3061_, v_skipConstInApp_boxed_3062_, v_skipInstances_boxed_3063_, v_x_3057_, v_x_3058_, v_e_3059_, v_a_3060_);
lean_dec(v_a_3060_);
return v_res_3064_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda(lean_object* v_m_3065_, lean_object* v_inst_3066_, lean_object* v_inst_3067_, lean_object* v_inst_3068_, lean_object* v_pre_3069_, lean_object* v_post_3070_, uint8_t v_usedLetOnly_3071_, uint8_t v_skipConstInApp_3072_, uint8_t v_skipInstances_3073_, lean_object* v_x_3074_, lean_object* v_x_3075_, lean_object* v_fvars_3076_, lean_object* v_e_3077_, lean_object* v_a_3078_){
_start:
{
lean_object* v___x_3079_; 
v___x_3079_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(v_inst_3066_, v_inst_3067_, v_inst_3068_, v_pre_3069_, v_post_3070_, v_usedLetOnly_3071_, v_skipConstInApp_3072_, v_skipInstances_3073_, v_x_3074_, v_x_3075_, v_fvars_3076_, v_e_3077_, v_a_3078_);
return v___x_3079_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___boxed(lean_object* v_m_3080_, lean_object* v_inst_3081_, lean_object* v_inst_3082_, lean_object* v_inst_3083_, lean_object* v_pre_3084_, lean_object* v_post_3085_, lean_object* v_usedLetOnly_3086_, lean_object* v_skipConstInApp_3087_, lean_object* v_skipInstances_3088_, lean_object* v_x_3089_, lean_object* v_x_3090_, lean_object* v_fvars_3091_, lean_object* v_e_3092_, lean_object* v_a_3093_){
_start:
{
uint8_t v_usedLetOnly_boxed_3094_; uint8_t v_skipConstInApp_boxed_3095_; uint8_t v_skipInstances_boxed_3096_; lean_object* v_res_3097_; 
v_usedLetOnly_boxed_3094_ = lean_unbox(v_usedLetOnly_3086_);
v_skipConstInApp_boxed_3095_ = lean_unbox(v_skipConstInApp_3087_);
v_skipInstances_boxed_3096_ = lean_unbox(v_skipInstances_3088_);
v_res_3097_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda(v_m_3080_, v_inst_3081_, v_inst_3082_, v_inst_3083_, v_pre_3084_, v_post_3085_, v_usedLetOnly_boxed_3094_, v_skipConstInApp_boxed_3095_, v_skipInstances_boxed_3096_, v_x_3089_, v_x_3090_, v_fvars_3091_, v_e_3092_, v_a_3093_);
lean_dec(v_a_3093_);
return v_res_3097_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall(lean_object* v_m_3098_, lean_object* v_inst_3099_, lean_object* v_inst_3100_, lean_object* v_inst_3101_, lean_object* v_pre_3102_, lean_object* v_post_3103_, uint8_t v_usedLetOnly_3104_, uint8_t v_skipConstInApp_3105_, uint8_t v_skipInstances_3106_, lean_object* v_x_3107_, lean_object* v_x_3108_, lean_object* v_fvars_3109_, lean_object* v_e_3110_, lean_object* v_a_3111_){
_start:
{
lean_object* v___x_3112_; 
v___x_3112_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(v_inst_3099_, v_inst_3100_, v_inst_3101_, v_pre_3102_, v_post_3103_, v_usedLetOnly_3104_, v_skipConstInApp_3105_, v_skipInstances_3106_, v_x_3107_, v_x_3108_, v_fvars_3109_, v_e_3110_, v_a_3111_);
return v___x_3112_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___boxed(lean_object* v_m_3113_, lean_object* v_inst_3114_, lean_object* v_inst_3115_, lean_object* v_inst_3116_, lean_object* v_pre_3117_, lean_object* v_post_3118_, lean_object* v_usedLetOnly_3119_, lean_object* v_skipConstInApp_3120_, lean_object* v_skipInstances_3121_, lean_object* v_x_3122_, lean_object* v_x_3123_, lean_object* v_fvars_3124_, lean_object* v_e_3125_, lean_object* v_a_3126_){
_start:
{
uint8_t v_usedLetOnly_boxed_3127_; uint8_t v_skipConstInApp_boxed_3128_; uint8_t v_skipInstances_boxed_3129_; lean_object* v_res_3130_; 
v_usedLetOnly_boxed_3127_ = lean_unbox(v_usedLetOnly_3119_);
v_skipConstInApp_boxed_3128_ = lean_unbox(v_skipConstInApp_3120_);
v_skipInstances_boxed_3129_ = lean_unbox(v_skipInstances_3121_);
v_res_3130_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall(v_m_3113_, v_inst_3114_, v_inst_3115_, v_inst_3116_, v_pre_3117_, v_post_3118_, v_usedLetOnly_boxed_3127_, v_skipConstInApp_boxed_3128_, v_skipInstances_boxed_3129_, v_x_3122_, v_x_3123_, v_fvars_3124_, v_e_3125_, v_a_3126_);
lean_dec(v_a_3126_);
return v_res_3130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__0(lean_object* v_x_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_){
_start:
{
lean_object* v___x_3137_; lean_object* v___x_3138_; 
v___x_3137_ = lean_apply_1(v_x_3131_, lean_box(0));
v___x_3138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3138_, 0, v___x_3137_);
return v___x_3138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__0___boxed(lean_object* v_x_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_){
_start:
{
lean_object* v_res_3145_; 
v_res_3145_ = l_Lean_Meta_transformWithCache___redArg___lam__0(v_x_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_);
lean_dec(v___y_3143_);
lean_dec_ref(v___y_3142_);
lean_dec(v___y_3141_);
lean_dec_ref(v___y_3140_);
return v_res_3145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__1(lean_object* v_inst_3146_, lean_object* v_00_u03b1_3147_, lean_object* v_x_3148_){
_start:
{
lean_object* v___f_3149_; lean_object* v___x_3150_; 
v___f_3149_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_3149_, 0, v_x_3148_);
v___x_3150_ = lean_apply_2(v_inst_3146_, lean_box(0), v___f_3149_);
return v___x_3150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__4(lean_object* v_toPure_3151_, lean_object* v_x_3152_, lean_object* v_toBind_3153_, lean_object* v_inst_3154_, lean_object* v_inst_3155_, lean_object* v_inst_3156_, lean_object* v_pre_3157_, lean_object* v_post_3158_, uint8_t v_usedLetOnly_3159_, uint8_t v_skipConstInApp_3160_, uint8_t v_skipInstances_3161_, lean_object* v_x_3162_, lean_object* v_input_3163_, lean_object* v_ref_3164_){
_start:
{
lean_object* v___f_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; 
lean_inc(v_toBind_3153_);
lean_inc(v_x_3152_);
lean_inc(v_ref_3164_);
v___f_3165_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__4), 5, 4);
lean_closure_set(v___f_3165_, 0, v_toPure_3151_);
lean_closure_set(v___f_3165_, 1, v_ref_3164_);
lean_closure_set(v___f_3165_, 2, v_x_3152_);
lean_closure_set(v___f_3165_, 3, v_toBind_3153_);
v___x_3166_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_3154_, v_inst_3155_, v_inst_3156_, v_pre_3157_, v_post_3158_, v_usedLetOnly_3159_, v_skipConstInApp_3160_, v_skipInstances_3161_, v_x_3162_, v_x_3152_, v_input_3163_, v_ref_3164_);
lean_dec(v_ref_3164_);
v___x_3167_ = lean_apply_4(v_toBind_3153_, lean_box(0), lean_box(0), v___x_3166_, v___f_3165_);
return v___x_3167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__4___boxed(lean_object* v_toPure_3168_, lean_object* v_x_3169_, lean_object* v_toBind_3170_, lean_object* v_inst_3171_, lean_object* v_inst_3172_, lean_object* v_inst_3173_, lean_object* v_pre_3174_, lean_object* v_post_3175_, lean_object* v_usedLetOnly_3176_, lean_object* v_skipConstInApp_3177_, lean_object* v_skipInstances_3178_, lean_object* v_x_3179_, lean_object* v_input_3180_, lean_object* v_ref_3181_){
_start:
{
uint8_t v_usedLetOnly_boxed_3182_; uint8_t v_skipConstInApp_boxed_3183_; uint8_t v_skipInstances_boxed_3184_; lean_object* v_res_3185_; 
v_usedLetOnly_boxed_3182_ = lean_unbox(v_usedLetOnly_3176_);
v_skipConstInApp_boxed_3183_ = lean_unbox(v_skipConstInApp_3177_);
v_skipInstances_boxed_3184_ = lean_unbox(v_skipInstances_3178_);
v_res_3185_ = l_Lean_Meta_transformWithCache___redArg___lam__4(v_toPure_3168_, v_x_3169_, v_toBind_3170_, v_inst_3171_, v_inst_3172_, v_inst_3173_, v_pre_3174_, v_post_3175_, v_usedLetOnly_boxed_3182_, v_skipConstInApp_boxed_3183_, v_skipInstances_boxed_3184_, v_x_3179_, v_input_3180_, v_ref_3181_);
return v_res_3185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg(lean_object* v_inst_3186_, lean_object* v_inst_3187_, lean_object* v_inst_3188_, lean_object* v_input_3189_, lean_object* v_cache_3190_, lean_object* v_pre_3191_, lean_object* v_post_3192_, uint8_t v_usedLetOnly_3193_, uint8_t v_skipConstInApp_3194_, uint8_t v_skipInstances_3195_){
_start:
{
lean_object* v_x_3196_; lean_object* v_toApplicative_3197_; lean_object* v_toBind_3198_; lean_object* v_toPure_3199_; lean_object* v_x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___f_3206_; lean_object* v___x_3207_; 
v_x_3196_ = lean_box(0);
v_toApplicative_3197_ = lean_ctor_get(v_inst_3186_, 0);
v_toBind_3198_ = lean_ctor_get(v_inst_3186_, 1);
lean_inc_n(v_toBind_3198_, 2);
v_toPure_3199_ = lean_ctor_get(v_toApplicative_3197_, 1);
lean_inc(v_toPure_3199_);
lean_inc_n(v_inst_3187_, 2);
v_x_3200_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__1), 3, 1);
lean_closure_set(v_x_3200_, 0, v_inst_3187_);
v___x_3201_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_3201_, 0, lean_box(0));
lean_closure_set(v___x_3201_, 1, lean_box(0));
lean_closure_set(v___x_3201_, 2, v_cache_3190_);
v___x_3202_ = l_Lean_Meta_transformWithCache___redArg___lam__1(v_inst_3187_, lean_box(0), v___x_3201_);
v___x_3203_ = lean_box(v_usedLetOnly_3193_);
v___x_3204_ = lean_box(v_skipConstInApp_3194_);
v___x_3205_ = lean_box(v_skipInstances_3195_);
v___f_3206_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__4___boxed), 14, 13);
lean_closure_set(v___f_3206_, 0, v_toPure_3199_);
lean_closure_set(v___f_3206_, 1, v_x_3200_);
lean_closure_set(v___f_3206_, 2, v_toBind_3198_);
lean_closure_set(v___f_3206_, 3, v_inst_3186_);
lean_closure_set(v___f_3206_, 4, v_inst_3187_);
lean_closure_set(v___f_3206_, 5, v_inst_3188_);
lean_closure_set(v___f_3206_, 6, v_pre_3191_);
lean_closure_set(v___f_3206_, 7, v_post_3192_);
lean_closure_set(v___f_3206_, 8, v___x_3203_);
lean_closure_set(v___f_3206_, 9, v___x_3204_);
lean_closure_set(v___f_3206_, 10, v___x_3205_);
lean_closure_set(v___f_3206_, 11, v_x_3196_);
lean_closure_set(v___f_3206_, 12, v_input_3189_);
v___x_3207_ = lean_apply_4(v_toBind_3198_, lean_box(0), lean_box(0), v___x_3202_, v___f_3206_);
return v___x_3207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___boxed(lean_object* v_inst_3208_, lean_object* v_inst_3209_, lean_object* v_inst_3210_, lean_object* v_input_3211_, lean_object* v_cache_3212_, lean_object* v_pre_3213_, lean_object* v_post_3214_, lean_object* v_usedLetOnly_3215_, lean_object* v_skipConstInApp_3216_, lean_object* v_skipInstances_3217_){
_start:
{
uint8_t v_usedLetOnly_boxed_3218_; uint8_t v_skipConstInApp_boxed_3219_; uint8_t v_skipInstances_boxed_3220_; lean_object* v_res_3221_; 
v_usedLetOnly_boxed_3218_ = lean_unbox(v_usedLetOnly_3215_);
v_skipConstInApp_boxed_3219_ = lean_unbox(v_skipConstInApp_3216_);
v_skipInstances_boxed_3220_ = lean_unbox(v_skipInstances_3217_);
v_res_3221_ = l_Lean_Meta_transformWithCache___redArg(v_inst_3208_, v_inst_3209_, v_inst_3210_, v_input_3211_, v_cache_3212_, v_pre_3213_, v_post_3214_, v_usedLetOnly_boxed_3218_, v_skipConstInApp_boxed_3219_, v_skipInstances_boxed_3220_);
return v_res_3221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache(lean_object* v_m_3222_, lean_object* v_inst_3223_, lean_object* v_inst_3224_, lean_object* v_inst_3225_, lean_object* v_input_3226_, lean_object* v_cache_3227_, lean_object* v_pre_3228_, lean_object* v_post_3229_, uint8_t v_usedLetOnly_3230_, uint8_t v_skipConstInApp_3231_, uint8_t v_skipInstances_3232_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___boxed(lean_object* v_m_3245_, lean_object* v_inst_3246_, lean_object* v_inst_3247_, lean_object* v_inst_3248_, lean_object* v_input_3249_, lean_object* v_cache_3250_, lean_object* v_pre_3251_, lean_object* v_post_3252_, lean_object* v_usedLetOnly_3253_, lean_object* v_skipConstInApp_3254_, lean_object* v_skipInstances_3255_){
_start:
{
uint8_t v_usedLetOnly_boxed_3256_; uint8_t v_skipConstInApp_boxed_3257_; uint8_t v_skipInstances_boxed_3258_; lean_object* v_res_3259_; 
v_usedLetOnly_boxed_3256_ = lean_unbox(v_usedLetOnly_3253_);
v_skipConstInApp_boxed_3257_ = lean_unbox(v_skipConstInApp_3254_);
v_skipInstances_boxed_3258_ = lean_unbox(v_skipInstances_3255_);
v_res_3259_ = l_Lean_Meta_transformWithCache(v_m_3245_, v_inst_3246_, v_inst_3247_, v_inst_3248_, v_input_3249_, v_cache_3250_, v_pre_3251_, v_post_3252_, v_usedLetOnly_boxed_3256_, v_skipConstInApp_boxed_3257_, v_skipInstances_boxed_3258_);
return v_res_3259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___redArg___lam__5(lean_object* v_toPure_3260_, lean_object* v_x_3261_, lean_object* v_toBind_3262_, lean_object* v_inst_3263_, lean_object* v_inst_3264_, lean_object* v_inst_3265_, lean_object* v_pre_3266_, lean_object* v_post_3267_, uint8_t v_usedLetOnly_3268_, uint8_t v_skipConstInApp_3269_, uint8_t v___x_3270_, lean_object* v_x_3271_, lean_object* v_input_3272_, lean_object* v_ref_3273_){
_start:
{
lean_object* v___f_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; 
lean_inc(v_toBind_3262_);
lean_inc(v_x_3261_);
lean_inc(v_ref_3273_);
v___f_3274_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__4), 5, 4);
lean_closure_set(v___f_3274_, 0, v_toPure_3260_);
lean_closure_set(v___f_3274_, 1, v_ref_3273_);
lean_closure_set(v___f_3274_, 2, v_x_3261_);
lean_closure_set(v___f_3274_, 3, v_toBind_3262_);
v___x_3275_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_3263_, v_inst_3264_, v_inst_3265_, v_pre_3266_, v_post_3267_, v_usedLetOnly_3268_, v_skipConstInApp_3269_, v___x_3270_, v_x_3271_, v_x_3261_, v_input_3272_, v_ref_3273_);
lean_dec(v_ref_3273_);
v___x_3276_ = lean_apply_4(v_toBind_3262_, lean_box(0), lean_box(0), v___x_3275_, v___f_3274_);
return v___x_3276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___redArg___lam__5___boxed(lean_object* v_toPure_3277_, lean_object* v_x_3278_, lean_object* v_toBind_3279_, lean_object* v_inst_3280_, lean_object* v_inst_3281_, lean_object* v_inst_3282_, lean_object* v_pre_3283_, lean_object* v_post_3284_, lean_object* v_usedLetOnly_3285_, lean_object* v_skipConstInApp_3286_, lean_object* v___x_3287_, lean_object* v_x_3288_, lean_object* v_input_3289_, lean_object* v_ref_3290_){
_start:
{
uint8_t v_usedLetOnly_boxed_3291_; uint8_t v_skipConstInApp_boxed_3292_; uint8_t v___x_114__boxed_3293_; lean_object* v_res_3294_; 
v_usedLetOnly_boxed_3291_ = lean_unbox(v_usedLetOnly_3285_);
v_skipConstInApp_boxed_3292_ = lean_unbox(v_skipConstInApp_3286_);
v___x_114__boxed_3293_ = lean_unbox(v___x_3287_);
v_res_3294_ = l_Lean_Meta_transform___redArg___lam__5(v_toPure_3277_, v_x_3278_, v_toBind_3279_, v_inst_3280_, v_inst_3281_, v_inst_3282_, v_pre_3283_, v_post_3284_, v_usedLetOnly_boxed_3291_, v_skipConstInApp_boxed_3292_, v___x_114__boxed_3293_, v_x_3288_, v_input_3289_, v_ref_3290_);
return v_res_3294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___redArg(lean_object* v_inst_3295_, lean_object* v_inst_3296_, lean_object* v_inst_3297_, lean_object* v_input_3298_, lean_object* v_pre_3299_, lean_object* v_post_3300_, uint8_t v_usedLetOnly_3301_, uint8_t v_skipConstInApp_3302_){
_start:
{
lean_object* v_toApplicative_3303_; lean_object* v_toBind_3304_; lean_object* v_x_3305_; lean_object* v_toPure_3306_; lean_object* v_x_3307_; uint8_t v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___f_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___f_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; 
v_toApplicative_3303_ = lean_ctor_get(v_inst_3295_, 0);
v_toBind_3304_ = lean_ctor_get(v_inst_3295_, 1);
lean_inc_n(v_toBind_3304_, 3);
v_x_3305_ = lean_box(0);
v_toPure_3306_ = lean_ctor_get(v_toApplicative_3303_, 1);
lean_inc_n(v_toPure_3306_, 2);
lean_inc_n(v_inst_3296_, 2);
v_x_3307_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__1), 3, 1);
lean_closure_set(v_x_3307_, 0, v_inst_3296_);
v___x_3308_ = 0;
v___x_3309_ = lean_obj_once(&l_Lean_Core_transform___redArg___closed__2, &l_Lean_Core_transform___redArg___closed__2_once, _init_l_Lean_Core_transform___redArg___closed__2);
v___x_3310_ = l_Lean_Meta_transformWithCache___redArg___lam__1(v_inst_3296_, lean_box(0), v___x_3309_);
v___f_3311_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__2), 2, 1);
lean_closure_set(v___f_3311_, 0, v_toPure_3306_);
v___x_3312_ = lean_box(v_usedLetOnly_3301_);
v___x_3313_ = lean_box(v_skipConstInApp_3302_);
v___x_3314_ = lean_box(v___x_3308_);
v___f_3315_ = lean_alloc_closure((void*)(l_Lean_Meta_transform___redArg___lam__5___boxed), 14, 13);
lean_closure_set(v___f_3315_, 0, v_toPure_3306_);
lean_closure_set(v___f_3315_, 1, v_x_3307_);
lean_closure_set(v___f_3315_, 2, v_toBind_3304_);
lean_closure_set(v___f_3315_, 3, v_inst_3295_);
lean_closure_set(v___f_3315_, 4, v_inst_3296_);
lean_closure_set(v___f_3315_, 5, v_inst_3297_);
lean_closure_set(v___f_3315_, 6, v_pre_3299_);
lean_closure_set(v___f_3315_, 7, v_post_3300_);
lean_closure_set(v___f_3315_, 8, v___x_3312_);
lean_closure_set(v___f_3315_, 9, v___x_3313_);
lean_closure_set(v___f_3315_, 10, v___x_3314_);
lean_closure_set(v___f_3315_, 11, v_x_3305_);
lean_closure_set(v___f_3315_, 12, v_input_3298_);
v___x_3316_ = lean_apply_4(v_toBind_3304_, lean_box(0), lean_box(0), v___x_3310_, v___f_3315_);
v___x_3317_ = lean_apply_4(v_toBind_3304_, lean_box(0), lean_box(0), v___x_3316_, v___f_3311_);
return v___x_3317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___redArg___boxed(lean_object* v_inst_3318_, lean_object* v_inst_3319_, lean_object* v_inst_3320_, lean_object* v_input_3321_, lean_object* v_pre_3322_, lean_object* v_post_3323_, lean_object* v_usedLetOnly_3324_, lean_object* v_skipConstInApp_3325_){
_start:
{
uint8_t v_usedLetOnly_boxed_3326_; uint8_t v_skipConstInApp_boxed_3327_; lean_object* v_res_3328_; 
v_usedLetOnly_boxed_3326_ = lean_unbox(v_usedLetOnly_3324_);
v_skipConstInApp_boxed_3327_ = lean_unbox(v_skipConstInApp_3325_);
v_res_3328_ = l_Lean_Meta_transform___redArg(v_inst_3318_, v_inst_3319_, v_inst_3320_, v_input_3321_, v_pre_3322_, v_post_3323_, v_usedLetOnly_boxed_3326_, v_skipConstInApp_boxed_3327_);
return v_res_3328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform(lean_object* v_m_3329_, lean_object* v_inst_3330_, lean_object* v_inst_3331_, lean_object* v_inst_3332_, lean_object* v_input_3333_, lean_object* v_pre_3334_, lean_object* v_post_3335_, uint8_t v_usedLetOnly_3336_, uint8_t v_skipConstInApp_3337_){
_start:
{
lean_object* v___x_3338_; 
v___x_3338_ = l_Lean_Meta_transform___redArg(v_inst_3330_, v_inst_3331_, v_inst_3332_, v_input_3333_, v_pre_3334_, v_post_3335_, v_usedLetOnly_3336_, v_skipConstInApp_3337_);
return v___x_3338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___boxed(lean_object* v_m_3339_, lean_object* v_inst_3340_, lean_object* v_inst_3341_, lean_object* v_inst_3342_, lean_object* v_input_3343_, lean_object* v_pre_3344_, lean_object* v_post_3345_, lean_object* v_usedLetOnly_3346_, lean_object* v_skipConstInApp_3347_){
_start:
{
uint8_t v_usedLetOnly_boxed_3348_; uint8_t v_skipConstInApp_boxed_3349_; lean_object* v_res_3350_; 
v_usedLetOnly_boxed_3348_ = lean_unbox(v_usedLetOnly_3346_);
v_skipConstInApp_boxed_3349_ = lean_unbox(v_skipConstInApp_3347_);
v_res_3350_ = l_Lean_Meta_transform(v_m_3339_, v_inst_3340_, v_inst_3341_, v_inst_3342_, v_input_3343_, v_pre_3344_, v_post_3345_, v_usedLetOnly_boxed_3348_, v_skipConstInApp_boxed_3349_);
return v_res_3350_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(lean_object* v_e_3351_, lean_object* v___y_3352_){
_start:
{
uint8_t v___x_3354_; 
v___x_3354_ = l_Lean_Expr_hasMVar(v_e_3351_);
if (v___x_3354_ == 0)
{
lean_object* v___x_3355_; 
v___x_3355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3355_, 0, v_e_3351_);
return v___x_3355_;
}
else
{
lean_object* v___x_3356_; lean_object* v_mctx_3357_; lean_object* v___x_3358_; lean_object* v_fst_3359_; lean_object* v_snd_3360_; lean_object* v___x_3361_; lean_object* v_cache_3362_; lean_object* v_zetaDeltaFVarIds_3363_; lean_object* v_postponed_3364_; lean_object* v_diag_3365_; lean_object* v___x_3367_; uint8_t v_isShared_3368_; uint8_t v_isSharedCheck_3374_; 
v___x_3356_ = lean_st_ref_get(v___y_3352_);
v_mctx_3357_ = lean_ctor_get(v___x_3356_, 0);
lean_inc_ref(v_mctx_3357_);
lean_dec(v___x_3356_);
v___x_3358_ = l_Lean_instantiateMVarsCore(v_mctx_3357_, v_e_3351_);
v_fst_3359_ = lean_ctor_get(v___x_3358_, 0);
lean_inc(v_fst_3359_);
v_snd_3360_ = lean_ctor_get(v___x_3358_, 1);
lean_inc(v_snd_3360_);
lean_dec_ref(v___x_3358_);
v___x_3361_ = lean_st_ref_take(v___y_3352_);
v_cache_3362_ = lean_ctor_get(v___x_3361_, 1);
v_zetaDeltaFVarIds_3363_ = lean_ctor_get(v___x_3361_, 2);
v_postponed_3364_ = lean_ctor_get(v___x_3361_, 3);
v_diag_3365_ = lean_ctor_get(v___x_3361_, 4);
v_isSharedCheck_3374_ = !lean_is_exclusive(v___x_3361_);
if (v_isSharedCheck_3374_ == 0)
{
lean_object* v_unused_3375_; 
v_unused_3375_ = lean_ctor_get(v___x_3361_, 0);
lean_dec(v_unused_3375_);
v___x_3367_ = v___x_3361_;
v_isShared_3368_ = v_isSharedCheck_3374_;
goto v_resetjp_3366_;
}
else
{
lean_inc(v_diag_3365_);
lean_inc(v_postponed_3364_);
lean_inc(v_zetaDeltaFVarIds_3363_);
lean_inc(v_cache_3362_);
lean_dec(v___x_3361_);
v___x_3367_ = lean_box(0);
v_isShared_3368_ = v_isSharedCheck_3374_;
goto v_resetjp_3366_;
}
v_resetjp_3366_:
{
lean_object* v___x_3370_; 
if (v_isShared_3368_ == 0)
{
lean_ctor_set(v___x_3367_, 0, v_snd_3360_);
v___x_3370_ = v___x_3367_;
goto v_reusejp_3369_;
}
else
{
lean_object* v_reuseFailAlloc_3373_; 
v_reuseFailAlloc_3373_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3373_, 0, v_snd_3360_);
lean_ctor_set(v_reuseFailAlloc_3373_, 1, v_cache_3362_);
lean_ctor_set(v_reuseFailAlloc_3373_, 2, v_zetaDeltaFVarIds_3363_);
lean_ctor_set(v_reuseFailAlloc_3373_, 3, v_postponed_3364_);
lean_ctor_set(v_reuseFailAlloc_3373_, 4, v_diag_3365_);
v___x_3370_ = v_reuseFailAlloc_3373_;
goto v_reusejp_3369_;
}
v_reusejp_3369_:
{
lean_object* v___x_3371_; lean_object* v___x_3372_; 
v___x_3371_ = lean_st_ref_put(v___y_3352_, v___x_3370_);
v___x_3372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3372_, 0, v_fst_3359_);
return v___x_3372_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg___boxed(lean_object* v_e_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_){
_start:
{
lean_object* v_res_3379_; 
v_res_3379_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(v_e_3376_, v___y_3377_);
lean_dec(v___y_3377_);
return v_res_3379_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0(lean_object* v_e_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_){
_start:
{
lean_object* v___x_3386_; 
v___x_3386_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(v_e_3380_, v___y_3382_);
return v___x_3386_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___boxed(lean_object* v_e_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_){
_start:
{
lean_object* v_res_3393_; 
v_res_3393_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0(v_e_3387_, v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_);
lean_dec(v___y_3391_);
lean_dec_ref(v___y_3390_);
lean_dec(v___y_3389_);
lean_dec_ref(v___y_3388_);
return v_res_3393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__0(uint8_t v_zetaHave_3394_, lean_object* v___x_3395_, uint8_t v_zetaDelta_3396_, lean_object* v_fvarId_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_){
_start:
{
lean_object* v___x_3403_; 
v___x_3403_ = l_Lean_FVarId_findDecl_x3f___redArg(v_fvarId_3397_, v___y_3398_);
if (lean_obj_tag(v___x_3403_) == 0)
{
lean_object* v_a_3404_; lean_object* v___x_3406_; uint8_t v_isShared_3407_; uint8_t v_isSharedCheck_3432_; 
v_a_3404_ = lean_ctor_get(v___x_3403_, 0);
v_isSharedCheck_3432_ = !lean_is_exclusive(v___x_3403_);
if (v_isSharedCheck_3432_ == 0)
{
v___x_3406_ = v___x_3403_;
v_isShared_3407_ = v_isSharedCheck_3432_;
goto v_resetjp_3405_;
}
else
{
lean_inc(v_a_3404_);
lean_dec(v___x_3403_);
v___x_3406_ = lean_box(0);
v_isShared_3407_ = v_isSharedCheck_3432_;
goto v_resetjp_3405_;
}
v_resetjp_3405_:
{
if (lean_obj_tag(v_a_3404_) == 1)
{
lean_object* v_val_3408_; lean_object* v___x_3410_; uint8_t v_isShared_3411_; uint8_t v_isSharedCheck_3427_; 
v_val_3408_ = lean_ctor_get(v_a_3404_, 0);
v_isSharedCheck_3427_ = !lean_is_exclusive(v_a_3404_);
if (v_isSharedCheck_3427_ == 0)
{
v___x_3410_ = v_a_3404_;
v_isShared_3411_ = v_isSharedCheck_3427_;
goto v_resetjp_3409_;
}
else
{
lean_inc(v_val_3408_);
lean_dec(v_a_3404_);
v___x_3410_ = lean_box(0);
v_isShared_3411_ = v_isSharedCheck_3427_;
goto v_resetjp_3409_;
}
v_resetjp_3409_:
{
uint8_t v___y_3413_; 
if (v_zetaDelta_3396_ == 0)
{
lean_object* v___x_3421_; uint8_t v___x_3422_; 
v___x_3421_ = l_Lean_LocalDecl_index(v_val_3408_);
v___x_3422_ = lean_nat_dec_lt(v___x_3421_, v___x_3395_);
lean_dec(v___x_3421_);
if (v___x_3422_ == 0)
{
lean_del_object(v___x_3410_);
goto v___jp_3418_;
}
else
{
lean_object* v___x_3423_; lean_object* v___x_3425_; 
lean_dec(v_val_3408_);
lean_del_object(v___x_3406_);
v___x_3423_ = lean_box(0);
if (v_isShared_3411_ == 0)
{
lean_ctor_set_tag(v___x_3410_, 0);
lean_ctor_set(v___x_3410_, 0, v___x_3423_);
v___x_3425_ = v___x_3410_;
goto v_reusejp_3424_;
}
else
{
lean_object* v_reuseFailAlloc_3426_; 
v_reuseFailAlloc_3426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3426_, 0, v___x_3423_);
v___x_3425_ = v_reuseFailAlloc_3426_;
goto v_reusejp_3424_;
}
v_reusejp_3424_:
{
return v___x_3425_;
}
}
}
else
{
lean_del_object(v___x_3410_);
goto v___jp_3418_;
}
v___jp_3412_:
{
lean_object* v___x_3414_; lean_object* v___x_3416_; 
v___x_3414_ = l_Lean_LocalDecl_value_x3f(v_val_3408_, v___y_3413_);
lean_dec(v_val_3408_);
if (v_isShared_3407_ == 0)
{
lean_ctor_set(v___x_3406_, 0, v___x_3414_);
v___x_3416_ = v___x_3406_;
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
v___jp_3418_:
{
if (v_zetaHave_3394_ == 0)
{
v___y_3413_ = v_zetaHave_3394_;
goto v___jp_3412_;
}
else
{
lean_object* v___x_3419_; uint8_t v___x_3420_; 
v___x_3419_ = l_Lean_LocalDecl_index(v_val_3408_);
v___x_3420_ = lean_nat_dec_le(v___x_3395_, v___x_3419_);
lean_dec(v___x_3419_);
v___y_3413_ = v___x_3420_;
goto v___jp_3412_;
}
}
}
}
else
{
lean_object* v___x_3428_; lean_object* v___x_3430_; 
lean_dec(v_a_3404_);
v___x_3428_ = lean_box(0);
if (v_isShared_3407_ == 0)
{
lean_ctor_set(v___x_3406_, 0, v___x_3428_);
v___x_3430_ = v___x_3406_;
goto v_reusejp_3429_;
}
else
{
lean_object* v_reuseFailAlloc_3431_; 
v_reuseFailAlloc_3431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3431_, 0, v___x_3428_);
v___x_3430_ = v_reuseFailAlloc_3431_;
goto v_reusejp_3429_;
}
v_reusejp_3429_:
{
return v___x_3430_;
}
}
}
}
else
{
lean_object* v_a_3433_; lean_object* v___x_3435_; uint8_t v_isShared_3436_; uint8_t v_isSharedCheck_3440_; 
v_a_3433_ = lean_ctor_get(v___x_3403_, 0);
v_isSharedCheck_3440_ = !lean_is_exclusive(v___x_3403_);
if (v_isSharedCheck_3440_ == 0)
{
v___x_3435_ = v___x_3403_;
v_isShared_3436_ = v_isSharedCheck_3440_;
goto v_resetjp_3434_;
}
else
{
lean_inc(v_a_3433_);
lean_dec(v___x_3403_);
v___x_3435_ = lean_box(0);
v_isShared_3436_ = v_isSharedCheck_3440_;
goto v_resetjp_3434_;
}
v_resetjp_3434_:
{
lean_object* v___x_3438_; 
if (v_isShared_3436_ == 0)
{
v___x_3438_ = v___x_3435_;
goto v_reusejp_3437_;
}
else
{
lean_object* v_reuseFailAlloc_3439_; 
v_reuseFailAlloc_3439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3439_, 0, v_a_3433_);
v___x_3438_ = v_reuseFailAlloc_3439_;
goto v_reusejp_3437_;
}
v_reusejp_3437_:
{
return v___x_3438_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__0___boxed(lean_object* v_zetaHave_3441_, lean_object* v___x_3442_, lean_object* v_zetaDelta_3443_, lean_object* v_fvarId_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_){
_start:
{
uint8_t v_zetaHave_boxed_3450_; uint8_t v_zetaDelta_boxed_3451_; lean_object* v_res_3452_; 
v_zetaHave_boxed_3450_ = lean_unbox(v_zetaHave_3441_);
v_zetaDelta_boxed_3451_ = lean_unbox(v_zetaDelta_3443_);
v_res_3452_ = l_Lean_Meta_zetaReduce___lam__0(v_zetaHave_boxed_3450_, v___x_3442_, v_zetaDelta_boxed_3451_, v_fvarId_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_);
lean_dec(v___y_3448_);
lean_dec_ref(v___y_3447_);
lean_dec(v___y_3446_);
lean_dec_ref(v___y_3445_);
lean_dec(v___x_3442_);
return v_res_3452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__1(lean_object* v_e_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_){
_start:
{
lean_object* v___x_3459_; lean_object* v___x_3460_; 
v___x_3459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3459_, 0, v_e_3453_);
v___x_3460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3460_, 0, v___x_3459_);
return v___x_3460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__1___boxed(lean_object* v_e_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_){
_start:
{
lean_object* v_res_3467_; 
v_res_3467_ = l_Lean_Meta_zetaReduce___lam__1(v_e_3461_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_);
lean_dec(v___y_3465_);
lean_dec_ref(v___y_3464_);
lean_dec(v___y_3463_);
lean_dec_ref(v___y_3462_);
return v_res_3467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__2(lean_object* v___f_3468_, lean_object* v_e_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_){
_start:
{
if (lean_obj_tag(v_e_3469_) == 1)
{
lean_object* v_fvarId_3475_; lean_object* v___x_3476_; 
v_fvarId_3475_ = lean_ctor_get(v_e_3469_, 0);
lean_inc(v___y_3473_);
lean_inc_ref(v___y_3472_);
lean_inc(v___y_3471_);
lean_inc_ref(v___y_3470_);
lean_inc(v_fvarId_3475_);
v___x_3476_ = lean_apply_6(v___f_3468_, v_fvarId_3475_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_, lean_box(0));
if (lean_obj_tag(v___x_3476_) == 0)
{
lean_object* v_a_3477_; lean_object* v___x_3479_; uint8_t v_isShared_3480_; uint8_t v_isSharedCheck_3502_; 
v_a_3477_ = lean_ctor_get(v___x_3476_, 0);
v_isSharedCheck_3502_ = !lean_is_exclusive(v___x_3476_);
if (v_isSharedCheck_3502_ == 0)
{
v___x_3479_ = v___x_3476_;
v_isShared_3480_ = v_isSharedCheck_3502_;
goto v_resetjp_3478_;
}
else
{
lean_inc(v_a_3477_);
lean_dec(v___x_3476_);
v___x_3479_ = lean_box(0);
v_isShared_3480_ = v_isSharedCheck_3502_;
goto v_resetjp_3478_;
}
v_resetjp_3478_:
{
if (lean_obj_tag(v_a_3477_) == 1)
{
lean_object* v_val_3481_; lean_object* v___x_3483_; uint8_t v_isShared_3484_; uint8_t v_isSharedCheck_3497_; 
lean_del_object(v___x_3479_);
lean_dec_ref_known(v_e_3469_, 1);
v_val_3481_ = lean_ctor_get(v_a_3477_, 0);
v_isSharedCheck_3497_ = !lean_is_exclusive(v_a_3477_);
if (v_isSharedCheck_3497_ == 0)
{
v___x_3483_ = v_a_3477_;
v_isShared_3484_ = v_isSharedCheck_3497_;
goto v_resetjp_3482_;
}
else
{
lean_inc(v_val_3481_);
lean_dec(v_a_3477_);
v___x_3483_ = lean_box(0);
v_isShared_3484_ = v_isSharedCheck_3497_;
goto v_resetjp_3482_;
}
v_resetjp_3482_:
{
lean_object* v___x_3485_; lean_object* v_a_3486_; lean_object* v___x_3488_; uint8_t v_isShared_3489_; uint8_t v_isSharedCheck_3496_; 
v___x_3485_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(v_val_3481_, v___y_3471_);
v_a_3486_ = lean_ctor_get(v___x_3485_, 0);
v_isSharedCheck_3496_ = !lean_is_exclusive(v___x_3485_);
if (v_isSharedCheck_3496_ == 0)
{
v___x_3488_ = v___x_3485_;
v_isShared_3489_ = v_isSharedCheck_3496_;
goto v_resetjp_3487_;
}
else
{
lean_inc(v_a_3486_);
lean_dec(v___x_3485_);
v___x_3488_ = lean_box(0);
v_isShared_3489_ = v_isSharedCheck_3496_;
goto v_resetjp_3487_;
}
v_resetjp_3487_:
{
lean_object* v___x_3491_; 
if (v_isShared_3484_ == 0)
{
lean_ctor_set(v___x_3483_, 0, v_a_3486_);
v___x_3491_ = v___x_3483_;
goto v_reusejp_3490_;
}
else
{
lean_object* v_reuseFailAlloc_3495_; 
v_reuseFailAlloc_3495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3495_, 0, v_a_3486_);
v___x_3491_ = v_reuseFailAlloc_3495_;
goto v_reusejp_3490_;
}
v_reusejp_3490_:
{
lean_object* v___x_3493_; 
if (v_isShared_3489_ == 0)
{
lean_ctor_set(v___x_3488_, 0, v___x_3491_);
v___x_3493_ = v___x_3488_;
goto v_reusejp_3492_;
}
else
{
lean_object* v_reuseFailAlloc_3494_; 
v_reuseFailAlloc_3494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3494_, 0, v___x_3491_);
v___x_3493_ = v_reuseFailAlloc_3494_;
goto v_reusejp_3492_;
}
v_reusejp_3492_:
{
return v___x_3493_;
}
}
}
}
}
else
{
lean_object* v___x_3498_; lean_object* v___x_3500_; 
lean_dec(v_a_3477_);
v___x_3498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3498_, 0, v_e_3469_);
if (v_isShared_3480_ == 0)
{
lean_ctor_set(v___x_3479_, 0, v___x_3498_);
v___x_3500_ = v___x_3479_;
goto v_reusejp_3499_;
}
else
{
lean_object* v_reuseFailAlloc_3501_; 
v_reuseFailAlloc_3501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3501_, 0, v___x_3498_);
v___x_3500_ = v_reuseFailAlloc_3501_;
goto v_reusejp_3499_;
}
v_reusejp_3499_:
{
return v___x_3500_;
}
}
}
}
else
{
lean_object* v_a_3503_; lean_object* v___x_3505_; uint8_t v_isShared_3506_; uint8_t v_isSharedCheck_3510_; 
lean_dec_ref_known(v_e_3469_, 1);
v_a_3503_ = lean_ctor_get(v___x_3476_, 0);
v_isSharedCheck_3510_ = !lean_is_exclusive(v___x_3476_);
if (v_isSharedCheck_3510_ == 0)
{
v___x_3505_ = v___x_3476_;
v_isShared_3506_ = v_isSharedCheck_3510_;
goto v_resetjp_3504_;
}
else
{
lean_inc(v_a_3503_);
lean_dec(v___x_3476_);
v___x_3505_ = lean_box(0);
v_isShared_3506_ = v_isSharedCheck_3510_;
goto v_resetjp_3504_;
}
v_resetjp_3504_:
{
lean_object* v___x_3508_; 
if (v_isShared_3506_ == 0)
{
v___x_3508_ = v___x_3505_;
goto v_reusejp_3507_;
}
else
{
lean_object* v_reuseFailAlloc_3509_; 
v_reuseFailAlloc_3509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3509_, 0, v_a_3503_);
v___x_3508_ = v_reuseFailAlloc_3509_;
goto v_reusejp_3507_;
}
v_reusejp_3507_:
{
return v___x_3508_;
}
}
}
}
else
{
lean_object* v___x_3511_; lean_object* v___x_3512_; 
lean_dec_ref(v_e_3469_);
lean_dec_ref(v___f_3468_);
v___x_3511_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_3512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3512_, 0, v___x_3511_);
return v___x_3512_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__2___boxed(lean_object* v___f_3513_, lean_object* v_e_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_){
_start:
{
lean_object* v_res_3520_; 
v_res_3520_ = l_Lean_Meta_zetaReduce___lam__2(v___f_3513_, v_e_3514_, v___y_3515_, v___y_3516_, v___y_3517_, v___y_3518_);
lean_dec(v___y_3518_);
lean_dec_ref(v___y_3517_);
lean_dec(v___y_3516_);
lean_dec_ref(v___y_3515_);
return v_res_3520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__4(lean_object* v___f_3521_, lean_object* v_e_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_){
_start:
{
lean_object* v___x_3528_; 
v___x_3528_ = l_Lean_Expr_getAppFn(v_e_3522_);
if (lean_obj_tag(v___x_3528_) == 1)
{
lean_object* v_fvarId_3529_; lean_object* v___x_3530_; 
v_fvarId_3529_ = lean_ctor_get(v___x_3528_, 0);
lean_inc(v_fvarId_3529_);
lean_dec_ref_known(v___x_3528_, 1);
lean_inc(v___y_3526_);
lean_inc_ref(v___y_3525_);
lean_inc(v___y_3524_);
lean_inc_ref(v___y_3523_);
v___x_3530_ = lean_apply_6(v___f_3521_, v_fvarId_3529_, v___y_3523_, v___y_3524_, v___y_3525_, v___y_3526_, lean_box(0));
if (lean_obj_tag(v___x_3530_) == 0)
{
lean_object* v_a_3531_; lean_object* v___x_3533_; uint8_t v_isShared_3534_; uint8_t v_isSharedCheck_3563_; 
v_a_3531_ = lean_ctor_get(v___x_3530_, 0);
v_isSharedCheck_3563_ = !lean_is_exclusive(v___x_3530_);
if (v_isSharedCheck_3563_ == 0)
{
v___x_3533_ = v___x_3530_;
v_isShared_3534_ = v_isSharedCheck_3563_;
goto v_resetjp_3532_;
}
else
{
lean_inc(v_a_3531_);
lean_dec(v___x_3530_);
v___x_3533_ = lean_box(0);
v_isShared_3534_ = v_isSharedCheck_3563_;
goto v_resetjp_3532_;
}
v_resetjp_3532_:
{
if (lean_obj_tag(v_a_3531_) == 1)
{
lean_object* v_val_3535_; lean_object* v___x_3537_; uint8_t v_isShared_3538_; uint8_t v_isSharedCheck_3558_; 
lean_del_object(v___x_3533_);
v_val_3535_ = lean_ctor_get(v_a_3531_, 0);
v_isSharedCheck_3558_ = !lean_is_exclusive(v_a_3531_);
if (v_isSharedCheck_3558_ == 0)
{
v___x_3537_ = v_a_3531_;
v_isShared_3538_ = v_isSharedCheck_3558_;
goto v_resetjp_3536_;
}
else
{
lean_inc(v_val_3535_);
lean_dec(v_a_3531_);
v___x_3537_ = lean_box(0);
v_isShared_3538_ = v_isSharedCheck_3558_;
goto v_resetjp_3536_;
}
v_resetjp_3536_:
{
lean_object* v___x_3539_; lean_object* v_a_3540_; lean_object* v___x_3542_; uint8_t v_isShared_3543_; uint8_t v_isSharedCheck_3557_; 
v___x_3539_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(v_val_3535_, v___y_3524_);
v_a_3540_ = lean_ctor_get(v___x_3539_, 0);
v_isSharedCheck_3557_ = !lean_is_exclusive(v___x_3539_);
if (v_isSharedCheck_3557_ == 0)
{
v___x_3542_ = v___x_3539_;
v_isShared_3543_ = v_isSharedCheck_3557_;
goto v_resetjp_3541_;
}
else
{
lean_inc(v_a_3540_);
lean_dec(v___x_3539_);
v___x_3542_ = lean_box(0);
v_isShared_3543_ = v_isSharedCheck_3557_;
goto v_resetjp_3541_;
}
v_resetjp_3541_:
{
lean_object* v_dummy_3544_; lean_object* v_nargs_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3552_; 
v_dummy_3544_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_3545_ = l_Lean_Expr_getAppNumArgs(v_e_3522_);
lean_inc(v_nargs_3545_);
v___x_3546_ = lean_mk_array(v_nargs_3545_, v_dummy_3544_);
v___x_3547_ = lean_unsigned_to_nat(1u);
v___x_3548_ = lean_nat_sub(v_nargs_3545_, v___x_3547_);
lean_dec(v_nargs_3545_);
v___x_3549_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3522_, v___x_3546_, v___x_3548_);
v___x_3550_ = l_Lean_Expr_beta(v_a_3540_, v___x_3549_);
if (v_isShared_3538_ == 0)
{
lean_ctor_set(v___x_3537_, 0, v___x_3550_);
v___x_3552_ = v___x_3537_;
goto v_reusejp_3551_;
}
else
{
lean_object* v_reuseFailAlloc_3556_; 
v_reuseFailAlloc_3556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3556_, 0, v___x_3550_);
v___x_3552_ = v_reuseFailAlloc_3556_;
goto v_reusejp_3551_;
}
v_reusejp_3551_:
{
lean_object* v___x_3554_; 
if (v_isShared_3543_ == 0)
{
lean_ctor_set(v___x_3542_, 0, v___x_3552_);
v___x_3554_ = v___x_3542_;
goto v_reusejp_3553_;
}
else
{
lean_object* v_reuseFailAlloc_3555_; 
v_reuseFailAlloc_3555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3555_, 0, v___x_3552_);
v___x_3554_ = v_reuseFailAlloc_3555_;
goto v_reusejp_3553_;
}
v_reusejp_3553_:
{
return v___x_3554_;
}
}
}
}
}
else
{
lean_object* v___x_3559_; lean_object* v___x_3561_; 
lean_dec(v_a_3531_);
lean_dec_ref(v_e_3522_);
v___x_3559_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
if (v_isShared_3534_ == 0)
{
lean_ctor_set(v___x_3533_, 0, v___x_3559_);
v___x_3561_ = v___x_3533_;
goto v_reusejp_3560_;
}
else
{
lean_object* v_reuseFailAlloc_3562_; 
v_reuseFailAlloc_3562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3562_, 0, v___x_3559_);
v___x_3561_ = v_reuseFailAlloc_3562_;
goto v_reusejp_3560_;
}
v_reusejp_3560_:
{
return v___x_3561_;
}
}
}
}
else
{
lean_object* v_a_3564_; lean_object* v___x_3566_; uint8_t v_isShared_3567_; uint8_t v_isSharedCheck_3571_; 
lean_dec_ref(v_e_3522_);
v_a_3564_ = lean_ctor_get(v___x_3530_, 0);
v_isSharedCheck_3571_ = !lean_is_exclusive(v___x_3530_);
if (v_isSharedCheck_3571_ == 0)
{
v___x_3566_ = v___x_3530_;
v_isShared_3567_ = v_isSharedCheck_3571_;
goto v_resetjp_3565_;
}
else
{
lean_inc(v_a_3564_);
lean_dec(v___x_3530_);
v___x_3566_ = lean_box(0);
v_isShared_3567_ = v_isSharedCheck_3571_;
goto v_resetjp_3565_;
}
v_resetjp_3565_:
{
lean_object* v___x_3569_; 
if (v_isShared_3567_ == 0)
{
v___x_3569_ = v___x_3566_;
goto v_reusejp_3568_;
}
else
{
lean_object* v_reuseFailAlloc_3570_; 
v_reuseFailAlloc_3570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3570_, 0, v_a_3564_);
v___x_3569_ = v_reuseFailAlloc_3570_;
goto v_reusejp_3568_;
}
v_reusejp_3568_:
{
return v___x_3569_;
}
}
}
}
else
{
lean_object* v___x_3572_; lean_object* v___x_3573_; 
lean_dec_ref(v___x_3528_);
lean_dec_ref(v_e_3522_);
lean_dec_ref(v___f_3521_);
v___x_3572_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_3573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3573_, 0, v___x_3572_);
return v___x_3573_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__4___boxed(lean_object* v___f_3574_, lean_object* v_e_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_){
_start:
{
lean_object* v_res_3581_; 
v_res_3581_ = l_Lean_Meta_zetaReduce___lam__4(v___f_3574_, v_e_3575_, v___y_3576_, v___y_3577_, v___y_3578_, v___y_3579_);
lean_dec(v___y_3579_);
lean_dec_ref(v___y_3578_);
lean_dec(v___y_3577_);
lean_dec_ref(v___y_3576_);
return v_res_3581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0(lean_object* v_00_u03b1_3582_, lean_object* v_x_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_){
_start:
{
lean_object* v___x_3589_; lean_object* v___x_3590_; 
v___x_3589_ = lean_apply_1(v_x_3583_, lean_box(0));
v___x_3590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3590_, 0, v___x_3589_);
return v___x_3590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0___boxed(lean_object* v_00_u03b1_3591_, lean_object* v_x_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_){
_start:
{
lean_object* v_res_3598_; 
v_res_3598_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0(v_00_u03b1_3591_, v_x_3592_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_);
lean_dec(v___y_3596_);
lean_dec_ref(v___y_3595_);
lean_dec(v___y_3594_);
lean_dec_ref(v___y_3593_);
return v_res_3598_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__2(lean_object* v___x_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_){
_start:
{
lean_object* v___x_3605_; 
v___x_3605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3605_, 0, v___x_3599_);
return v___x_3605_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__2___boxed(lean_object* v___x_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_){
_start:
{
lean_object* v_res_3612_; 
v_res_3612_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__2(v___x_3606_, v___y_3607_, v___y_3608_, v___y_3609_, v___y_3610_);
lean_dec(v___y_3610_);
lean_dec_ref(v___y_3609_);
lean_dec(v___y_3608_);
lean_dec_ref(v___y_3607_);
return v_res_3612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0(lean_object* v_k_3613_, lean_object* v___y_3614_, lean_object* v_b_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_){
_start:
{
lean_object* v___x_3621_; 
lean_inc(v___y_3619_);
lean_inc_ref(v___y_3618_);
lean_inc(v___y_3617_);
lean_inc_ref(v___y_3616_);
lean_inc(v___y_3614_);
v___x_3621_ = lean_apply_7(v_k_3613_, v_b_3615_, v___y_3614_, v___y_3616_, v___y_3617_, v___y_3618_, v___y_3619_, lean_box(0));
return v___x_3621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0___boxed(lean_object* v_k_3622_, lean_object* v___y_3623_, lean_object* v_b_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_){
_start:
{
lean_object* v_res_3630_; 
v_res_3630_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0(v_k_3622_, v___y_3623_, v_b_3624_, v___y_3625_, v___y_3626_, v___y_3627_, v___y_3628_);
lean_dec(v___y_3628_);
lean_dec_ref(v___y_3627_);
lean_dec(v___y_3626_);
lean_dec_ref(v___y_3625_);
lean_dec(v___y_3623_);
return v_res_3630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(lean_object* v_name_3631_, uint8_t v_bi_3632_, lean_object* v_type_3633_, lean_object* v_k_3634_, uint8_t v_kind_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_){
_start:
{
lean_object* v___f_3642_; lean_object* v___x_3643_; 
lean_inc(v___y_3636_);
v___f_3642_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3642_, 0, v_k_3634_);
lean_closure_set(v___f_3642_, 1, v___y_3636_);
v___x_3643_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3631_, v_bi_3632_, v_type_3633_, v___f_3642_, v_kind_3635_, v___y_3637_, v___y_3638_, v___y_3639_, v___y_3640_);
if (lean_obj_tag(v___x_3643_) == 0)
{
return v___x_3643_;
}
else
{
lean_object* v_a_3644_; lean_object* v___x_3646_; uint8_t v_isShared_3647_; uint8_t v_isSharedCheck_3651_; 
v_a_3644_ = lean_ctor_get(v___x_3643_, 0);
v_isSharedCheck_3651_ = !lean_is_exclusive(v___x_3643_);
if (v_isSharedCheck_3651_ == 0)
{
v___x_3646_ = v___x_3643_;
v_isShared_3647_ = v_isSharedCheck_3651_;
goto v_resetjp_3645_;
}
else
{
lean_inc(v_a_3644_);
lean_dec(v___x_3643_);
v___x_3646_ = lean_box(0);
v_isShared_3647_ = v_isSharedCheck_3651_;
goto v_resetjp_3645_;
}
v_resetjp_3645_:
{
lean_object* v___x_3649_; 
if (v_isShared_3647_ == 0)
{
v___x_3649_ = v___x_3646_;
goto v_reusejp_3648_;
}
else
{
lean_object* v_reuseFailAlloc_3650_; 
v_reuseFailAlloc_3650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3650_, 0, v_a_3644_);
v___x_3649_ = v_reuseFailAlloc_3650_;
goto v_reusejp_3648_;
}
v_reusejp_3648_:
{
return v___x_3649_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___boxed(lean_object* v_name_3652_, lean_object* v_bi_3653_, lean_object* v_type_3654_, lean_object* v_k_3655_, lean_object* v_kind_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_){
_start:
{
uint8_t v_bi_boxed_3663_; uint8_t v_kind_boxed_3664_; lean_object* v_res_3665_; 
v_bi_boxed_3663_ = lean_unbox(v_bi_3653_);
v_kind_boxed_3664_ = lean_unbox(v_kind_3656_);
v_res_3665_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_name_3652_, v_bi_boxed_3663_, v_type_3654_, v_k_3655_, v_kind_boxed_3664_, v___y_3657_, v___y_3658_, v___y_3659_, v___y_3660_, v___y_3661_);
lean_dec(v___y_3661_);
lean_dec_ref(v___y_3660_);
lean_dec(v___y_3659_);
lean_dec_ref(v___y_3658_);
lean_dec(v___y_3657_);
return v_res_3665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg(lean_object* v_name_3666_, lean_object* v_type_3667_, lean_object* v_val_3668_, lean_object* v_k_3669_, uint8_t v_nondep_3670_, uint8_t v_kind_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_){
_start:
{
lean_object* v___f_3678_; lean_object* v___x_3679_; 
lean_inc(v___y_3672_);
v___f_3678_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3678_, 0, v_k_3669_);
lean_closure_set(v___f_3678_, 1, v___y_3672_);
v___x_3679_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_3666_, v_type_3667_, v_val_3668_, v___f_3678_, v_nondep_3670_, v_kind_3671_, v___y_3673_, v___y_3674_, v___y_3675_, v___y_3676_);
if (lean_obj_tag(v___x_3679_) == 0)
{
return v___x_3679_;
}
else
{
lean_object* v_a_3680_; lean_object* v___x_3682_; uint8_t v_isShared_3683_; uint8_t v_isSharedCheck_3687_; 
v_a_3680_ = lean_ctor_get(v___x_3679_, 0);
v_isSharedCheck_3687_ = !lean_is_exclusive(v___x_3679_);
if (v_isSharedCheck_3687_ == 0)
{
v___x_3682_ = v___x_3679_;
v_isShared_3683_ = v_isSharedCheck_3687_;
goto v_resetjp_3681_;
}
else
{
lean_inc(v_a_3680_);
lean_dec(v___x_3679_);
v___x_3682_ = lean_box(0);
v_isShared_3683_ = v_isSharedCheck_3687_;
goto v_resetjp_3681_;
}
v_resetjp_3681_:
{
lean_object* v___x_3685_; 
if (v_isShared_3683_ == 0)
{
v___x_3685_ = v___x_3682_;
goto v_reusejp_3684_;
}
else
{
lean_object* v_reuseFailAlloc_3686_; 
v_reuseFailAlloc_3686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3686_, 0, v_a_3680_);
v___x_3685_ = v_reuseFailAlloc_3686_;
goto v_reusejp_3684_;
}
v_reusejp_3684_:
{
return v___x_3685_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg___boxed(lean_object* v_name_3688_, lean_object* v_type_3689_, lean_object* v_val_3690_, lean_object* v_k_3691_, lean_object* v_nondep_3692_, lean_object* v_kind_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_){
_start:
{
uint8_t v_nondep_boxed_3700_; uint8_t v_kind_boxed_3701_; lean_object* v_res_3702_; 
v_nondep_boxed_3700_ = lean_unbox(v_nondep_3692_);
v_kind_boxed_3701_ = lean_unbox(v_kind_3693_);
v_res_3702_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg(v_name_3688_, v_type_3689_, v_val_3690_, v_k_3691_, v_nondep_boxed_3700_, v_kind_boxed_3701_, v___y_3694_, v___y_3695_, v___y_3696_, v___y_3697_, v___y_3698_);
lean_dec(v___y_3698_);
lean_dec_ref(v___y_3697_);
lean_dec(v___y_3696_);
lean_dec_ref(v___y_3695_);
lean_dec(v___y_3694_);
return v_res_3702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0(lean_object* v_00_u03b1_3703_, lean_object* v_x_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_){
_start:
{
lean_object* v___x_3710_; lean_object* v___x_3711_; 
v___x_3710_ = lean_apply_1(v_x_3704_, lean_box(0));
v___x_3711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3711_, 0, v___x_3710_);
return v___x_3711_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0___boxed(lean_object* v_00_u03b1_3712_, lean_object* v_x_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_){
_start:
{
lean_object* v_res_3719_; 
v_res_3719_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0(v_00_u03b1_3712_, v_x_3713_, v___y_3714_, v___y_3715_, v___y_3716_, v___y_3717_);
lean_dec(v___y_3717_);
lean_dec_ref(v___y_3716_);
lean_dec(v___y_3715_);
lean_dec_ref(v___y_3714_);
return v_res_3719_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg(lean_object* v_ref_3720_){
_start:
{
lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; 
v___x_3722_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5);
v___x_3723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3723_, 0, v_ref_3720_);
lean_ctor_set(v___x_3723_, 1, v___x_3722_);
v___x_3724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3724_, 0, v___x_3723_);
return v___x_3724_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg___boxed(lean_object* v_ref_3725_, lean_object* v___y_3726_){
_start:
{
lean_object* v_res_3727_; 
v_res_3727_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg(v_ref_3725_);
return v_res_3727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg(lean_object* v_x_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_){
_start:
{
lean_object* v___y_3736_; lean_object* v_toCold_3745_; lean_object* v_currRecDepth_3746_; lean_object* v_ref_3747_; uint8_t v_diag_3748_; uint8_t v_suppressElabErrors_3749_; lean_object* v_maxRecDepth_3755_; lean_object* v___x_3756_; uint8_t v___x_3757_; 
v_toCold_3745_ = lean_ctor_get(v___y_3732_, 0);
v_currRecDepth_3746_ = lean_ctor_get(v___y_3732_, 1);
v_ref_3747_ = lean_ctor_get(v___y_3732_, 2);
v_diag_3748_ = lean_ctor_get_uint8(v___y_3732_, sizeof(void*)*3);
v_suppressElabErrors_3749_ = lean_ctor_get_uint8(v___y_3732_, sizeof(void*)*3 + 1);
v_maxRecDepth_3755_ = lean_ctor_get(v_toCold_3745_, 3);
v___x_3756_ = lean_unsigned_to_nat(0u);
v___x_3757_ = lean_nat_dec_eq(v_maxRecDepth_3755_, v___x_3756_);
if (v___x_3757_ == 0)
{
uint8_t v___x_3758_; 
v___x_3758_ = lean_nat_dec_eq(v_currRecDepth_3746_, v_maxRecDepth_3755_);
if (v___x_3758_ == 0)
{
goto v___jp_3750_;
}
else
{
lean_object* v___x_3759_; 
lean_dec_ref(v_x_3728_);
lean_inc(v_ref_3747_);
v___x_3759_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg(v_ref_3747_);
v___y_3736_ = v___x_3759_;
goto v___jp_3735_;
}
}
else
{
goto v___jp_3750_;
}
v___jp_3735_:
{
if (lean_obj_tag(v___y_3736_) == 0)
{
return v___y_3736_;
}
else
{
lean_object* v_a_3737_; lean_object* v___x_3739_; uint8_t v_isShared_3740_; uint8_t v_isSharedCheck_3744_; 
v_a_3737_ = lean_ctor_get(v___y_3736_, 0);
v_isSharedCheck_3744_ = !lean_is_exclusive(v___y_3736_);
if (v_isSharedCheck_3744_ == 0)
{
v___x_3739_ = v___y_3736_;
v_isShared_3740_ = v_isSharedCheck_3744_;
goto v_resetjp_3738_;
}
else
{
lean_inc(v_a_3737_);
lean_dec(v___y_3736_);
v___x_3739_ = lean_box(0);
v_isShared_3740_ = v_isSharedCheck_3744_;
goto v_resetjp_3738_;
}
v_resetjp_3738_:
{
lean_object* v___x_3742_; 
if (v_isShared_3740_ == 0)
{
v___x_3742_ = v___x_3739_;
goto v_reusejp_3741_;
}
else
{
lean_object* v_reuseFailAlloc_3743_; 
v_reuseFailAlloc_3743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3743_, 0, v_a_3737_);
v___x_3742_ = v_reuseFailAlloc_3743_;
goto v_reusejp_3741_;
}
v_reusejp_3741_:
{
return v___x_3742_;
}
}
}
}
v___jp_3750_:
{
lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; 
v___x_3751_ = lean_unsigned_to_nat(1u);
v___x_3752_ = lean_nat_add(v_currRecDepth_3746_, v___x_3751_);
lean_inc(v_ref_3747_);
lean_inc_ref(v_toCold_3745_);
v___x_3753_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_3753_, 0, v_toCold_3745_);
lean_ctor_set(v___x_3753_, 1, v___x_3752_);
lean_ctor_set(v___x_3753_, 2, v_ref_3747_);
lean_ctor_set_uint8(v___x_3753_, sizeof(void*)*3, v_diag_3748_);
lean_ctor_set_uint8(v___x_3753_, sizeof(void*)*3 + 1, v_suppressElabErrors_3749_);
lean_inc(v___y_3733_);
lean_inc(v___y_3731_);
lean_inc_ref(v___y_3730_);
lean_inc(v___y_3729_);
v___x_3754_ = lean_apply_6(v_x_3728_, v___y_3729_, v___y_3730_, v___y_3731_, v___x_3753_, v___y_3733_, lean_box(0));
v___y_3736_ = v___x_3754_;
goto v___jp_3735_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg___boxed(lean_object* v_x_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_){
_start:
{
lean_object* v_res_3767_; 
v_res_3767_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg(v_x_3760_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_, v___y_3765_);
lean_dec(v___y_3765_);
lean_dec_ref(v___y_3764_);
lean_dec(v___y_3763_);
lean_dec_ref(v___y_3762_);
lean_dec(v___y_3761_);
return v_res_3767_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___lam__0(lean_object* v_fvars_3768_, lean_object* v_pre_3769_, lean_object* v_post_3770_, uint8_t v_usedLetOnly_3771_, uint8_t v_skipConstInApp_3772_, uint8_t v_skipInstances_3773_, lean_object* v_body_3774_, lean_object* v_x_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_){
_start:
{
lean_object* v___x_3782_; lean_object* v___x_3783_; 
v___x_3782_ = lean_array_push(v_fvars_3768_, v_x_3775_);
v___x_3783_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6(v_pre_3769_, v_post_3770_, v_usedLetOnly_3771_, v_skipConstInApp_3772_, v_skipInstances_3773_, v___x_3782_, v_body_3774_, v___y_3776_, v___y_3777_, v___y_3778_, v___y_3779_, v___y_3780_);
return v___x_3783_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___lam__0___boxed(lean_object* v_fvars_3784_, lean_object* v_pre_3785_, lean_object* v_post_3786_, lean_object* v_usedLetOnly_3787_, lean_object* v_skipConstInApp_3788_, lean_object* v_skipInstances_3789_, lean_object* v_body_3790_, lean_object* v_x_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_){
_start:
{
uint8_t v_usedLetOnly_boxed_3798_; uint8_t v_skipConstInApp_boxed_3799_; uint8_t v_skipInstances_boxed_3800_; lean_object* v_res_3801_; 
v_usedLetOnly_boxed_3798_ = lean_unbox(v_usedLetOnly_3787_);
v_skipConstInApp_boxed_3799_ = lean_unbox(v_skipConstInApp_3788_);
v_skipInstances_boxed_3800_ = lean_unbox(v_skipInstances_3789_);
v_res_3801_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___lam__0(v_fvars_3784_, v_pre_3785_, v_post_3786_, v_usedLetOnly_boxed_3798_, v_skipConstInApp_boxed_3799_, v_skipInstances_boxed_3800_, v_body_3790_, v_x_3791_, v___y_3792_, v___y_3793_, v___y_3794_, v___y_3795_, v___y_3796_);
lean_dec(v___y_3796_);
lean_dec_ref(v___y_3795_);
lean_dec(v___y_3794_);
lean_dec_ref(v___y_3793_);
lean_dec(v___y_3792_);
return v_res_3801_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(lean_object* v_pre_3802_, lean_object* v_post_3803_, uint8_t v_usedLetOnly_3804_, uint8_t v_skipConstInApp_3805_, uint8_t v_skipInstances_3806_, lean_object* v_e_3807_, lean_object* v_a_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_){
_start:
{
lean_object* v___x_3814_; 
lean_inc_ref(v_post_3803_);
lean_inc(v___y_3812_);
lean_inc_ref(v___y_3811_);
lean_inc(v___y_3810_);
lean_inc_ref(v___y_3809_);
lean_inc_ref(v_e_3807_);
v___x_3814_ = lean_apply_6(v_post_3803_, v_e_3807_, v___y_3809_, v___y_3810_, v___y_3811_, v___y_3812_, lean_box(0));
if (lean_obj_tag(v___x_3814_) == 0)
{
lean_object* v_a_3815_; lean_object* v___x_3817_; uint8_t v_isShared_3818_; uint8_t v_isSharedCheck_3833_; 
v_a_3815_ = lean_ctor_get(v___x_3814_, 0);
v_isSharedCheck_3833_ = !lean_is_exclusive(v___x_3814_);
if (v_isSharedCheck_3833_ == 0)
{
v___x_3817_ = v___x_3814_;
v_isShared_3818_ = v_isSharedCheck_3833_;
goto v_resetjp_3816_;
}
else
{
lean_inc(v_a_3815_);
lean_dec(v___x_3814_);
v___x_3817_ = lean_box(0);
v_isShared_3818_ = v_isSharedCheck_3833_;
goto v_resetjp_3816_;
}
v_resetjp_3816_:
{
switch(lean_obj_tag(v_a_3815_))
{
case 0:
{
lean_object* v_e_3819_; lean_object* v___x_3821_; 
lean_dec_ref(v_e_3807_);
lean_dec_ref(v_post_3803_);
lean_dec_ref(v_pre_3802_);
v_e_3819_ = lean_ctor_get(v_a_3815_, 0);
lean_inc_ref(v_e_3819_);
lean_dec_ref_known(v_a_3815_, 1);
if (v_isShared_3818_ == 0)
{
lean_ctor_set(v___x_3817_, 0, v_e_3819_);
v___x_3821_ = v___x_3817_;
goto v_reusejp_3820_;
}
else
{
lean_object* v_reuseFailAlloc_3822_; 
v_reuseFailAlloc_3822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3822_, 0, v_e_3819_);
v___x_3821_ = v_reuseFailAlloc_3822_;
goto v_reusejp_3820_;
}
v_reusejp_3820_:
{
return v___x_3821_;
}
}
case 1:
{
lean_object* v_e_3823_; lean_object* v___x_3824_; 
lean_del_object(v___x_3817_);
lean_dec_ref(v_e_3807_);
v_e_3823_ = lean_ctor_get(v_a_3815_, 0);
lean_inc_ref(v_e_3823_);
lean_dec_ref_known(v_a_3815_, 1);
v___x_3824_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3802_, v_post_3803_, v_usedLetOnly_3804_, v_skipConstInApp_3805_, v_skipInstances_3806_, v_e_3823_, v_a_3808_, v___y_3809_, v___y_3810_, v___y_3811_, v___y_3812_);
return v___x_3824_;
}
default: 
{
lean_object* v_e_x3f_3825_; 
lean_dec_ref(v_post_3803_);
lean_dec_ref(v_pre_3802_);
v_e_x3f_3825_ = lean_ctor_get(v_a_3815_, 0);
lean_inc(v_e_x3f_3825_);
lean_dec_ref_known(v_a_3815_, 1);
if (lean_obj_tag(v_e_x3f_3825_) == 0)
{
lean_object* v___x_3827_; 
if (v_isShared_3818_ == 0)
{
lean_ctor_set(v___x_3817_, 0, v_e_3807_);
v___x_3827_ = v___x_3817_;
goto v_reusejp_3826_;
}
else
{
lean_object* v_reuseFailAlloc_3828_; 
v_reuseFailAlloc_3828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3828_, 0, v_e_3807_);
v___x_3827_ = v_reuseFailAlloc_3828_;
goto v_reusejp_3826_;
}
v_reusejp_3826_:
{
return v___x_3827_;
}
}
else
{
lean_object* v_val_3829_; lean_object* v___x_3831_; 
lean_dec_ref(v_e_3807_);
v_val_3829_ = lean_ctor_get(v_e_x3f_3825_, 0);
lean_inc(v_val_3829_);
lean_dec_ref_known(v_e_x3f_3825_, 1);
if (v_isShared_3818_ == 0)
{
lean_ctor_set(v___x_3817_, 0, v_val_3829_);
v___x_3831_ = v___x_3817_;
goto v_reusejp_3830_;
}
else
{
lean_object* v_reuseFailAlloc_3832_; 
v_reuseFailAlloc_3832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3832_, 0, v_val_3829_);
v___x_3831_ = v_reuseFailAlloc_3832_;
goto v_reusejp_3830_;
}
v_reusejp_3830_:
{
return v___x_3831_;
}
}
}
}
}
}
else
{
lean_object* v_a_3834_; lean_object* v___x_3836_; uint8_t v_isShared_3837_; uint8_t v_isSharedCheck_3841_; 
lean_dec_ref(v_e_3807_);
lean_dec_ref(v_post_3803_);
lean_dec_ref(v_pre_3802_);
v_a_3834_ = lean_ctor_get(v___x_3814_, 0);
v_isSharedCheck_3841_ = !lean_is_exclusive(v___x_3814_);
if (v_isSharedCheck_3841_ == 0)
{
v___x_3836_ = v___x_3814_;
v_isShared_3837_ = v_isSharedCheck_3841_;
goto v_resetjp_3835_;
}
else
{
lean_inc(v_a_3834_);
lean_dec(v___x_3814_);
v___x_3836_ = lean_box(0);
v_isShared_3837_ = v_isSharedCheck_3841_;
goto v_resetjp_3835_;
}
v_resetjp_3835_:
{
lean_object* v___x_3839_; 
if (v_isShared_3837_ == 0)
{
v___x_3839_ = v___x_3836_;
goto v_reusejp_3838_;
}
else
{
lean_object* v_reuseFailAlloc_3840_; 
v_reuseFailAlloc_3840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3840_, 0, v_a_3834_);
v___x_3839_ = v_reuseFailAlloc_3840_;
goto v_reusejp_3838_;
}
v_reusejp_3838_:
{
return v___x_3839_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6(lean_object* v_pre_3842_, lean_object* v_post_3843_, uint8_t v_usedLetOnly_3844_, uint8_t v_skipConstInApp_3845_, uint8_t v_skipInstances_3846_, lean_object* v_fvars_3847_, lean_object* v_e_3848_, lean_object* v_a_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_){
_start:
{
if (lean_obj_tag(v_e_3848_) == 6)
{
lean_object* v_binderName_3855_; lean_object* v_binderType_3856_; lean_object* v_body_3857_; uint8_t v_binderInfo_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; 
v_binderName_3855_ = lean_ctor_get(v_e_3848_, 0);
lean_inc(v_binderName_3855_);
v_binderType_3856_ = lean_ctor_get(v_e_3848_, 1);
lean_inc_ref(v_binderType_3856_);
v_body_3857_ = lean_ctor_get(v_e_3848_, 2);
lean_inc_ref(v_body_3857_);
v_binderInfo_3858_ = lean_ctor_get_uint8(v_e_3848_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_3848_, 3);
v___x_3859_ = lean_expr_instantiate_rev(v_binderType_3856_, v_fvars_3847_);
lean_dec_ref(v_binderType_3856_);
lean_inc_ref(v_post_3843_);
lean_inc_ref(v_pre_3842_);
v___x_3860_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3842_, v_post_3843_, v_usedLetOnly_3844_, v_skipConstInApp_3845_, v_skipInstances_3846_, v___x_3859_, v_a_3849_, v___y_3850_, v___y_3851_, v___y_3852_, v___y_3853_);
if (lean_obj_tag(v___x_3860_) == 0)
{
lean_object* v_a_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___f_3865_; uint8_t v___x_3866_; lean_object* v___x_3867_; 
v_a_3861_ = lean_ctor_get(v___x_3860_, 0);
lean_inc(v_a_3861_);
lean_dec_ref_known(v___x_3860_, 1);
v___x_3862_ = lean_box(v_usedLetOnly_3844_);
v___x_3863_ = lean_box(v_skipConstInApp_3845_);
v___x_3864_ = lean_box(v_skipInstances_3846_);
v___f_3865_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___lam__0___boxed), 14, 7);
lean_closure_set(v___f_3865_, 0, v_fvars_3847_);
lean_closure_set(v___f_3865_, 1, v_pre_3842_);
lean_closure_set(v___f_3865_, 2, v_post_3843_);
lean_closure_set(v___f_3865_, 3, v___x_3862_);
lean_closure_set(v___f_3865_, 4, v___x_3863_);
lean_closure_set(v___f_3865_, 5, v___x_3864_);
lean_closure_set(v___f_3865_, 6, v_body_3857_);
v___x_3866_ = 0;
v___x_3867_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_binderName_3855_, v_binderInfo_3858_, v_a_3861_, v___f_3865_, v___x_3866_, v_a_3849_, v___y_3850_, v___y_3851_, v___y_3852_, v___y_3853_);
return v___x_3867_;
}
else
{
lean_dec_ref(v_body_3857_);
lean_dec(v_binderName_3855_);
lean_dec_ref(v_fvars_3847_);
lean_dec_ref(v_post_3843_);
lean_dec_ref(v_pre_3842_);
return v___x_3860_;
}
}
else
{
lean_object* v___x_3868_; lean_object* v___x_3869_; 
v___x_3868_ = lean_expr_instantiate_rev(v_e_3848_, v_fvars_3847_);
lean_dec_ref(v_e_3848_);
lean_inc_ref(v_post_3843_);
lean_inc_ref(v_pre_3842_);
v___x_3869_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3842_, v_post_3843_, v_usedLetOnly_3844_, v_skipConstInApp_3845_, v_skipInstances_3846_, v___x_3868_, v_a_3849_, v___y_3850_, v___y_3851_, v___y_3852_, v___y_3853_);
if (lean_obj_tag(v___x_3869_) == 0)
{
lean_object* v_a_3870_; uint8_t v___x_3871_; uint8_t v___x_3872_; uint8_t v___x_3873_; lean_object* v___x_3874_; 
v_a_3870_ = lean_ctor_get(v___x_3869_, 0);
lean_inc(v_a_3870_);
lean_dec_ref_known(v___x_3869_, 1);
v___x_3871_ = 0;
v___x_3872_ = 1;
v___x_3873_ = 1;
v___x_3874_ = l_Lean_Meta_mkLambdaFVars(v_fvars_3847_, v_a_3870_, v___x_3871_, v_usedLetOnly_3844_, v___x_3871_, v___x_3872_, v___x_3873_, v___y_3850_, v___y_3851_, v___y_3852_, v___y_3853_);
lean_dec_ref(v_fvars_3847_);
if (lean_obj_tag(v___x_3874_) == 0)
{
lean_object* v_a_3875_; lean_object* v___x_3876_; 
v_a_3875_ = lean_ctor_get(v___x_3874_, 0);
lean_inc(v_a_3875_);
lean_dec_ref_known(v___x_3874_, 1);
v___x_3876_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_3842_, v_post_3843_, v_usedLetOnly_3844_, v_skipConstInApp_3845_, v_skipInstances_3846_, v_a_3875_, v_a_3849_, v___y_3850_, v___y_3851_, v___y_3852_, v___y_3853_);
return v___x_3876_;
}
else
{
lean_dec_ref(v_post_3843_);
lean_dec_ref(v_pre_3842_);
return v___x_3874_;
}
}
else
{
lean_dec_ref(v_fvars_3847_);
lean_dec_ref(v_post_3843_);
lean_dec_ref(v_pre_3842_);
return v___x_3869_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___lam__0(lean_object* v_fvars_3877_, lean_object* v_pre_3878_, lean_object* v_post_3879_, uint8_t v_usedLetOnly_3880_, uint8_t v_skipConstInApp_3881_, uint8_t v_skipInstances_3882_, lean_object* v_body_3883_, lean_object* v_x_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_){
_start:
{
lean_object* v___x_3891_; lean_object* v___x_3892_; 
v___x_3891_ = lean_array_push(v_fvars_3877_, v_x_3884_);
v___x_3892_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7(v_pre_3878_, v_post_3879_, v_usedLetOnly_3880_, v_skipConstInApp_3881_, v_skipInstances_3882_, v___x_3891_, v_body_3883_, v___y_3885_, v___y_3886_, v___y_3887_, v___y_3888_, v___y_3889_);
return v___x_3892_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___lam__0___boxed(lean_object* v_fvars_3893_, lean_object* v_pre_3894_, lean_object* v_post_3895_, lean_object* v_usedLetOnly_3896_, lean_object* v_skipConstInApp_3897_, lean_object* v_skipInstances_3898_, lean_object* v_body_3899_, lean_object* v_x_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_){
_start:
{
uint8_t v_usedLetOnly_boxed_3907_; uint8_t v_skipConstInApp_boxed_3908_; uint8_t v_skipInstances_boxed_3909_; lean_object* v_res_3910_; 
v_usedLetOnly_boxed_3907_ = lean_unbox(v_usedLetOnly_3896_);
v_skipConstInApp_boxed_3908_ = lean_unbox(v_skipConstInApp_3897_);
v_skipInstances_boxed_3909_ = lean_unbox(v_skipInstances_3898_);
v_res_3910_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___lam__0(v_fvars_3893_, v_pre_3894_, v_post_3895_, v_usedLetOnly_boxed_3907_, v_skipConstInApp_boxed_3908_, v_skipInstances_boxed_3909_, v_body_3899_, v_x_3900_, v___y_3901_, v___y_3902_, v___y_3903_, v___y_3904_, v___y_3905_);
lean_dec(v___y_3905_);
lean_dec_ref(v___y_3904_);
lean_dec(v___y_3903_);
lean_dec_ref(v___y_3902_);
lean_dec(v___y_3901_);
return v_res_3910_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7(lean_object* v_pre_3911_, lean_object* v_post_3912_, uint8_t v_usedLetOnly_3913_, uint8_t v_skipConstInApp_3914_, uint8_t v_skipInstances_3915_, lean_object* v_fvars_3916_, lean_object* v_e_3917_, lean_object* v_a_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_){
_start:
{
if (lean_obj_tag(v_e_3917_) == 8)
{
lean_object* v_declName_3924_; lean_object* v_type_3925_; lean_object* v_value_3926_; lean_object* v_body_3927_; uint8_t v_nondep_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; 
v_declName_3924_ = lean_ctor_get(v_e_3917_, 0);
lean_inc(v_declName_3924_);
v_type_3925_ = lean_ctor_get(v_e_3917_, 1);
lean_inc_ref(v_type_3925_);
v_value_3926_ = lean_ctor_get(v_e_3917_, 2);
lean_inc_ref(v_value_3926_);
v_body_3927_ = lean_ctor_get(v_e_3917_, 3);
lean_inc_ref(v_body_3927_);
v_nondep_3928_ = lean_ctor_get_uint8(v_e_3917_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_3917_, 4);
v___x_3929_ = lean_expr_instantiate_rev(v_type_3925_, v_fvars_3916_);
lean_dec_ref(v_type_3925_);
lean_inc_ref(v_post_3912_);
lean_inc_ref(v_pre_3911_);
v___x_3930_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3911_, v_post_3912_, v_usedLetOnly_3913_, v_skipConstInApp_3914_, v_skipInstances_3915_, v___x_3929_, v_a_3918_, v___y_3919_, v___y_3920_, v___y_3921_, v___y_3922_);
if (lean_obj_tag(v___x_3930_) == 0)
{
lean_object* v_a_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; 
v_a_3931_ = lean_ctor_get(v___x_3930_, 0);
lean_inc(v_a_3931_);
lean_dec_ref_known(v___x_3930_, 1);
v___x_3932_ = lean_expr_instantiate_rev(v_value_3926_, v_fvars_3916_);
lean_dec_ref(v_value_3926_);
lean_inc_ref(v_post_3912_);
lean_inc_ref(v_pre_3911_);
v___x_3933_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3911_, v_post_3912_, v_usedLetOnly_3913_, v_skipConstInApp_3914_, v_skipInstances_3915_, v___x_3932_, v_a_3918_, v___y_3919_, v___y_3920_, v___y_3921_, v___y_3922_);
if (lean_obj_tag(v___x_3933_) == 0)
{
lean_object* v_a_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___f_3938_; uint8_t v___x_3939_; lean_object* v___x_3940_; 
v_a_3934_ = lean_ctor_get(v___x_3933_, 0);
lean_inc(v_a_3934_);
lean_dec_ref_known(v___x_3933_, 1);
v___x_3935_ = lean_box(v_usedLetOnly_3913_);
v___x_3936_ = lean_box(v_skipConstInApp_3914_);
v___x_3937_ = lean_box(v_skipInstances_3915_);
v___f_3938_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___lam__0___boxed), 14, 7);
lean_closure_set(v___f_3938_, 0, v_fvars_3916_);
lean_closure_set(v___f_3938_, 1, v_pre_3911_);
lean_closure_set(v___f_3938_, 2, v_post_3912_);
lean_closure_set(v___f_3938_, 3, v___x_3935_);
lean_closure_set(v___f_3938_, 4, v___x_3936_);
lean_closure_set(v___f_3938_, 5, v___x_3937_);
lean_closure_set(v___f_3938_, 6, v_body_3927_);
v___x_3939_ = 0;
v___x_3940_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg(v_declName_3924_, v_a_3931_, v_a_3934_, v___f_3938_, v_nondep_3928_, v___x_3939_, v_a_3918_, v___y_3919_, v___y_3920_, v___y_3921_, v___y_3922_);
return v___x_3940_;
}
else
{
lean_dec(v_a_3931_);
lean_dec_ref(v_body_3927_);
lean_dec(v_declName_3924_);
lean_dec_ref(v_fvars_3916_);
lean_dec_ref(v_post_3912_);
lean_dec_ref(v_pre_3911_);
return v___x_3933_;
}
}
else
{
lean_dec_ref(v_body_3927_);
lean_dec_ref(v_value_3926_);
lean_dec(v_declName_3924_);
lean_dec_ref(v_fvars_3916_);
lean_dec_ref(v_post_3912_);
lean_dec_ref(v_pre_3911_);
return v___x_3930_;
}
}
else
{
lean_object* v___x_3941_; lean_object* v___x_3942_; 
v___x_3941_ = lean_expr_instantiate_rev(v_e_3917_, v_fvars_3916_);
lean_dec_ref(v_e_3917_);
lean_inc_ref(v_post_3912_);
lean_inc_ref(v_pre_3911_);
v___x_3942_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3911_, v_post_3912_, v_usedLetOnly_3913_, v_skipConstInApp_3914_, v_skipInstances_3915_, v___x_3941_, v_a_3918_, v___y_3919_, v___y_3920_, v___y_3921_, v___y_3922_);
if (lean_obj_tag(v___x_3942_) == 0)
{
lean_object* v_a_3943_; uint8_t v___x_3944_; uint8_t v___x_3945_; lean_object* v___x_3946_; 
v_a_3943_ = lean_ctor_get(v___x_3942_, 0);
lean_inc(v_a_3943_);
lean_dec_ref_known(v___x_3942_, 1);
v___x_3944_ = 0;
v___x_3945_ = 1;
v___x_3946_ = l_Lean_Meta_mkLetFVars(v_fvars_3916_, v_a_3943_, v_usedLetOnly_3913_, v___x_3944_, v___x_3945_, v___y_3919_, v___y_3920_, v___y_3921_, v___y_3922_);
lean_dec_ref(v_fvars_3916_);
if (lean_obj_tag(v___x_3946_) == 0)
{
lean_object* v_a_3947_; lean_object* v___x_3948_; 
v_a_3947_ = lean_ctor_get(v___x_3946_, 0);
lean_inc(v_a_3947_);
lean_dec_ref_known(v___x_3946_, 1);
v___x_3948_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_3911_, v_post_3912_, v_usedLetOnly_3913_, v_skipConstInApp_3914_, v_skipInstances_3915_, v_a_3947_, v_a_3918_, v___y_3919_, v___y_3920_, v___y_3921_, v___y_3922_);
return v___x_3948_;
}
else
{
lean_dec_ref(v_post_3912_);
lean_dec_ref(v_pre_3911_);
return v___x_3946_;
}
}
else
{
lean_dec_ref(v_fvars_3916_);
lean_dec_ref(v_post_3912_);
lean_dec_ref(v_pre_3911_);
return v___x_3942_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__2(lean_object* v_pre_3949_, lean_object* v_post_3950_, uint8_t v_usedLetOnly_3951_, uint8_t v_skipConstInApp_3952_, uint8_t v_skipInstances_3953_, size_t v_sz_3954_, size_t v_i_3955_, lean_object* v_bs_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_){
_start:
{
uint8_t v___x_3963_; 
v___x_3963_ = lean_usize_dec_lt(v_i_3955_, v_sz_3954_);
if (v___x_3963_ == 0)
{
lean_object* v___x_3964_; 
lean_dec_ref(v_post_3950_);
lean_dec_ref(v_pre_3949_);
v___x_3964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3964_, 0, v_bs_3956_);
return v___x_3964_;
}
else
{
lean_object* v_v_3965_; lean_object* v___x_3966_; 
v_v_3965_ = lean_array_uget_borrowed(v_bs_3956_, v_i_3955_);
lean_inc(v_v_3965_);
lean_inc_ref(v_post_3950_);
lean_inc_ref(v_pre_3949_);
v___x_3966_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3949_, v_post_3950_, v_usedLetOnly_3951_, v_skipConstInApp_3952_, v_skipInstances_3953_, v_v_3965_, v___y_3957_, v___y_3958_, v___y_3959_, v___y_3960_, v___y_3961_);
if (lean_obj_tag(v___x_3966_) == 0)
{
lean_object* v_a_3967_; lean_object* v___x_3968_; lean_object* v_bs_x27_3969_; size_t v___x_3970_; size_t v___x_3971_; lean_object* v___x_3972_; 
v_a_3967_ = lean_ctor_get(v___x_3966_, 0);
lean_inc(v_a_3967_);
lean_dec_ref_known(v___x_3966_, 1);
v___x_3968_ = lean_unsigned_to_nat(0u);
v_bs_x27_3969_ = lean_array_uset(v_bs_3956_, v_i_3955_, v___x_3968_);
v___x_3970_ = ((size_t)1ULL);
v___x_3971_ = lean_usize_add(v_i_3955_, v___x_3970_);
v___x_3972_ = lean_array_uset(v_bs_x27_3969_, v_i_3955_, v_a_3967_);
v_i_3955_ = v___x_3971_;
v_bs_3956_ = v___x_3972_;
goto _start;
}
else
{
lean_object* v_a_3974_; lean_object* v___x_3976_; uint8_t v_isShared_3977_; uint8_t v_isSharedCheck_3981_; 
lean_dec_ref(v_bs_3956_);
lean_dec_ref(v_post_3950_);
lean_dec_ref(v_pre_3949_);
v_a_3974_ = lean_ctor_get(v___x_3966_, 0);
v_isSharedCheck_3981_ = !lean_is_exclusive(v___x_3966_);
if (v_isSharedCheck_3981_ == 0)
{
v___x_3976_ = v___x_3966_;
v_isShared_3977_ = v_isSharedCheck_3981_;
goto v_resetjp_3975_;
}
else
{
lean_inc(v_a_3974_);
lean_dec(v___x_3966_);
v___x_3976_ = lean_box(0);
v_isShared_3977_ = v_isSharedCheck_3981_;
goto v_resetjp_3975_;
}
v_resetjp_3975_:
{
lean_object* v___x_3979_; 
if (v_isShared_3977_ == 0)
{
v___x_3979_ = v___x_3976_;
goto v_reusejp_3978_;
}
else
{
lean_object* v_reuseFailAlloc_3980_; 
v_reuseFailAlloc_3980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3980_, 0, v_a_3974_);
v___x_3979_ = v_reuseFailAlloc_3980_;
goto v_reusejp_3978_;
}
v_reusejp_3978_:
{
return v___x_3979_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0(lean_object* v_pre_3982_, lean_object* v_post_3983_, uint8_t v_usedLetOnly_3984_, uint8_t v_skipConstInApp_3985_, uint8_t v_skipInstances_3986_, lean_object* v___x_3987_, lean_object* v___y_3988_, lean_object* v_b_3989_, lean_object* v_a_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_){
_start:
{
lean_object* v___x_3996_; 
v___x_3996_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3982_, v_post_3983_, v_usedLetOnly_3984_, v_skipConstInApp_3985_, v_skipInstances_3986_, v___x_3987_, v___y_3988_, v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_);
if (lean_obj_tag(v___x_3996_) == 0)
{
lean_object* v_a_3997_; lean_object* v___x_3999_; uint8_t v_isShared_4000_; uint8_t v_isSharedCheck_4006_; 
v_a_3997_ = lean_ctor_get(v___x_3996_, 0);
v_isSharedCheck_4006_ = !lean_is_exclusive(v___x_3996_);
if (v_isSharedCheck_4006_ == 0)
{
v___x_3999_ = v___x_3996_;
v_isShared_4000_ = v_isSharedCheck_4006_;
goto v_resetjp_3998_;
}
else
{
lean_inc(v_a_3997_);
lean_dec(v___x_3996_);
v___x_3999_ = lean_box(0);
v_isShared_4000_ = v_isSharedCheck_4006_;
goto v_resetjp_3998_;
}
v_resetjp_3998_:
{
lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4004_; 
v___x_4001_ = lean_array_fset(v_b_3989_, v_a_3990_, v_a_3997_);
v___x_4002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4002_, 0, v___x_4001_);
if (v_isShared_4000_ == 0)
{
lean_ctor_set(v___x_3999_, 0, v___x_4002_);
v___x_4004_ = v___x_3999_;
goto v_reusejp_4003_;
}
else
{
lean_object* v_reuseFailAlloc_4005_; 
v_reuseFailAlloc_4005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4005_, 0, v___x_4002_);
v___x_4004_ = v_reuseFailAlloc_4005_;
goto v_reusejp_4003_;
}
v_reusejp_4003_:
{
return v___x_4004_;
}
}
}
else
{
lean_object* v_a_4007_; lean_object* v___x_4009_; uint8_t v_isShared_4010_; uint8_t v_isSharedCheck_4014_; 
lean_dec_ref(v_b_3989_);
v_a_4007_ = lean_ctor_get(v___x_3996_, 0);
v_isSharedCheck_4014_ = !lean_is_exclusive(v___x_3996_);
if (v_isSharedCheck_4014_ == 0)
{
v___x_4009_ = v___x_3996_;
v_isShared_4010_ = v_isSharedCheck_4014_;
goto v_resetjp_4008_;
}
else
{
lean_inc(v_a_4007_);
lean_dec(v___x_3996_);
v___x_4009_ = lean_box(0);
v_isShared_4010_ = v_isSharedCheck_4014_;
goto v_resetjp_4008_;
}
v_resetjp_4008_:
{
lean_object* v___x_4012_; 
if (v_isShared_4010_ == 0)
{
v___x_4012_ = v___x_4009_;
goto v_reusejp_4011_;
}
else
{
lean_object* v_reuseFailAlloc_4013_; 
v_reuseFailAlloc_4013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4013_, 0, v_a_4007_);
v___x_4012_ = v_reuseFailAlloc_4013_;
goto v_reusejp_4011_;
}
v_reusejp_4011_:
{
return v___x_4012_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed(lean_object* v_pre_4015_, lean_object* v_post_4016_, lean_object* v_usedLetOnly_4017_, lean_object* v_skipConstInApp_4018_, lean_object* v_skipInstances_4019_, lean_object* v___x_4020_, lean_object* v___y_4021_, lean_object* v_b_4022_, lean_object* v_a_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_){
_start:
{
uint8_t v_usedLetOnly_boxed_4029_; uint8_t v_skipConstInApp_boxed_4030_; uint8_t v_skipInstances_boxed_4031_; lean_object* v_res_4032_; 
v_usedLetOnly_boxed_4029_ = lean_unbox(v_usedLetOnly_4017_);
v_skipConstInApp_boxed_4030_ = lean_unbox(v_skipConstInApp_4018_);
v_skipInstances_boxed_4031_ = lean_unbox(v_skipInstances_4019_);
v_res_4032_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0(v_pre_4015_, v_post_4016_, v_usedLetOnly_boxed_4029_, v_skipConstInApp_boxed_4030_, v_skipInstances_boxed_4031_, v___x_4020_, v___y_4021_, v_b_4022_, v_a_4023_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_);
lean_dec(v___y_4027_);
lean_dec_ref(v___y_4026_);
lean_dec(v___y_4025_);
lean_dec_ref(v___y_4024_);
lean_dec(v_a_4023_);
lean_dec(v___y_4021_);
return v_res_4032_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg(lean_object* v_upperBound_4033_, lean_object* v___x_4034_, lean_object* v_pre_4035_, lean_object* v_post_4036_, uint8_t v_usedLetOnly_4037_, uint8_t v_skipConstInApp_4038_, uint8_t v_skipInstances_4039_, lean_object* v_a_4040_, lean_object* v_b_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_){
_start:
{
lean_object* v___y_4049_; uint8_t v___x_4072_; 
v___x_4072_ = lean_nat_dec_lt(v_a_4040_, v_upperBound_4033_);
if (v___x_4072_ == 0)
{
lean_object* v___x_4073_; 
lean_dec(v_a_4040_);
lean_dec_ref(v_post_4036_);
lean_dec_ref(v_pre_4035_);
v___x_4073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4073_, 0, v_b_4041_);
return v___x_4073_;
}
else
{
lean_object* v___x_4074_; lean_object* v___x_4075_; uint8_t v___x_4076_; 
v___x_4074_ = lean_array_fget_borrowed(v_b_4041_, v_a_4040_);
v___x_4075_ = lean_array_get_size(v___x_4034_);
v___x_4076_ = lean_nat_dec_lt(v_a_4040_, v___x_4075_);
if (v___x_4076_ == 0)
{
lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___f_4080_; 
lean_inc(v___x_4074_);
v___x_4077_ = lean_box(v_usedLetOnly_4037_);
v___x_4078_ = lean_box(v_skipConstInApp_4038_);
v___x_4079_ = lean_box(v_skipInstances_4039_);
lean_inc(v_a_4040_);
lean_inc(v___y_4042_);
lean_inc_ref(v_post_4036_);
lean_inc_ref(v_pre_4035_);
v___f_4080_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_4080_, 0, v_pre_4035_);
lean_closure_set(v___f_4080_, 1, v_post_4036_);
lean_closure_set(v___f_4080_, 2, v___x_4077_);
lean_closure_set(v___f_4080_, 3, v___x_4078_);
lean_closure_set(v___f_4080_, 4, v___x_4079_);
lean_closure_set(v___f_4080_, 5, v___x_4074_);
lean_closure_set(v___f_4080_, 6, v___y_4042_);
lean_closure_set(v___f_4080_, 7, v_b_4041_);
lean_closure_set(v___f_4080_, 8, v_a_4040_);
v___y_4049_ = v___f_4080_;
goto v___jp_4048_;
}
else
{
lean_object* v___x_4081_; uint8_t v_isInstance_4082_; 
v___x_4081_ = lean_array_fget_borrowed(v___x_4034_, v_a_4040_);
v_isInstance_4082_ = lean_ctor_get_uint8(v___x_4081_, sizeof(void*)*1 + 4);
if (v_isInstance_4082_ == 0)
{
lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___f_4086_; 
lean_inc(v___x_4074_);
v___x_4083_ = lean_box(v_usedLetOnly_4037_);
v___x_4084_ = lean_box(v_skipConstInApp_4038_);
v___x_4085_ = lean_box(v_skipInstances_4039_);
lean_inc(v_a_4040_);
lean_inc(v___y_4042_);
lean_inc_ref(v_post_4036_);
lean_inc_ref(v_pre_4035_);
v___f_4086_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_4086_, 0, v_pre_4035_);
lean_closure_set(v___f_4086_, 1, v_post_4036_);
lean_closure_set(v___f_4086_, 2, v___x_4083_);
lean_closure_set(v___f_4086_, 3, v___x_4084_);
lean_closure_set(v___f_4086_, 4, v___x_4085_);
lean_closure_set(v___f_4086_, 5, v___x_4074_);
lean_closure_set(v___f_4086_, 6, v___y_4042_);
lean_closure_set(v___f_4086_, 7, v_b_4041_);
lean_closure_set(v___f_4086_, 8, v_a_4040_);
v___y_4049_ = v___f_4086_;
goto v___jp_4048_;
}
else
{
lean_object* v___x_4087_; lean_object* v___f_4088_; 
v___x_4087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4087_, 0, v_b_4041_);
v___f_4088_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_4088_, 0, v___x_4087_);
v___y_4049_ = v___f_4088_;
goto v___jp_4048_;
}
}
}
v___jp_4048_:
{
lean_object* v___x_4050_; 
lean_inc(v___y_4046_);
lean_inc_ref(v___y_4045_);
lean_inc(v___y_4044_);
lean_inc_ref(v___y_4043_);
v___x_4050_ = lean_apply_5(v___y_4049_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_, lean_box(0));
if (lean_obj_tag(v___x_4050_) == 0)
{
lean_object* v_a_4051_; lean_object* v___x_4053_; uint8_t v_isShared_4054_; uint8_t v_isSharedCheck_4063_; 
v_a_4051_ = lean_ctor_get(v___x_4050_, 0);
v_isSharedCheck_4063_ = !lean_is_exclusive(v___x_4050_);
if (v_isSharedCheck_4063_ == 0)
{
v___x_4053_ = v___x_4050_;
v_isShared_4054_ = v_isSharedCheck_4063_;
goto v_resetjp_4052_;
}
else
{
lean_inc(v_a_4051_);
lean_dec(v___x_4050_);
v___x_4053_ = lean_box(0);
v_isShared_4054_ = v_isSharedCheck_4063_;
goto v_resetjp_4052_;
}
v_resetjp_4052_:
{
if (lean_obj_tag(v_a_4051_) == 0)
{
lean_object* v_a_4055_; lean_object* v___x_4057_; 
lean_dec(v_a_4040_);
lean_dec_ref(v_post_4036_);
lean_dec_ref(v_pre_4035_);
v_a_4055_ = lean_ctor_get(v_a_4051_, 0);
lean_inc(v_a_4055_);
lean_dec_ref_known(v_a_4051_, 1);
if (v_isShared_4054_ == 0)
{
lean_ctor_set(v___x_4053_, 0, v_a_4055_);
v___x_4057_ = v___x_4053_;
goto v_reusejp_4056_;
}
else
{
lean_object* v_reuseFailAlloc_4058_; 
v_reuseFailAlloc_4058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4058_, 0, v_a_4055_);
v___x_4057_ = v_reuseFailAlloc_4058_;
goto v_reusejp_4056_;
}
v_reusejp_4056_:
{
return v___x_4057_;
}
}
else
{
lean_object* v_a_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; 
lean_del_object(v___x_4053_);
v_a_4059_ = lean_ctor_get(v_a_4051_, 0);
lean_inc(v_a_4059_);
lean_dec_ref_known(v_a_4051_, 1);
v___x_4060_ = lean_unsigned_to_nat(1u);
v___x_4061_ = lean_nat_add(v_a_4040_, v___x_4060_);
lean_dec(v_a_4040_);
v_a_4040_ = v___x_4061_;
v_b_4041_ = v_a_4059_;
goto _start;
}
}
}
else
{
lean_object* v_a_4064_; lean_object* v___x_4066_; uint8_t v_isShared_4067_; uint8_t v_isSharedCheck_4071_; 
lean_dec(v_a_4040_);
lean_dec_ref(v_post_4036_);
lean_dec_ref(v_pre_4035_);
v_a_4064_ = lean_ctor_get(v___x_4050_, 0);
v_isSharedCheck_4071_ = !lean_is_exclusive(v___x_4050_);
if (v_isSharedCheck_4071_ == 0)
{
v___x_4066_ = v___x_4050_;
v_isShared_4067_ = v_isSharedCheck_4071_;
goto v_resetjp_4065_;
}
else
{
lean_inc(v_a_4064_);
lean_dec(v___x_4050_);
v___x_4066_ = lean_box(0);
v_isShared_4067_ = v_isSharedCheck_4071_;
goto v_resetjp_4065_;
}
v_resetjp_4065_:
{
lean_object* v___x_4069_; 
if (v_isShared_4067_ == 0)
{
v___x_4069_ = v___x_4066_;
goto v_reusejp_4068_;
}
else
{
lean_object* v_reuseFailAlloc_4070_; 
v_reuseFailAlloc_4070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4070_, 0, v_a_4064_);
v___x_4069_ = v_reuseFailAlloc_4070_;
goto v_reusejp_4068_;
}
v_reusejp_4068_:
{
return v___x_4069_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__8(uint8_t v_skipInstances_4089_, lean_object* v_pre_4090_, lean_object* v_post_4091_, uint8_t v_usedLetOnly_4092_, uint8_t v_skipConstInApp_4093_, lean_object* v_x_4094_, lean_object* v_x_4095_, lean_object* v_x_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_){
_start:
{
lean_object* v_f_4104_; lean_object* v___y_4105_; lean_object* v___y_4106_; lean_object* v___y_4107_; lean_object* v___y_4108_; lean_object* v___y_4109_; 
if (lean_obj_tag(v_x_4094_) == 5)
{
lean_object* v_fn_4152_; lean_object* v_arg_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; 
v_fn_4152_ = lean_ctor_get(v_x_4094_, 0);
lean_inc_ref(v_fn_4152_);
v_arg_4153_ = lean_ctor_get(v_x_4094_, 1);
lean_inc_ref(v_arg_4153_);
lean_dec_ref_known(v_x_4094_, 2);
v___x_4154_ = lean_array_set(v_x_4095_, v_x_4096_, v_arg_4153_);
v___x_4155_ = lean_unsigned_to_nat(1u);
v___x_4156_ = lean_nat_sub(v_x_4096_, v___x_4155_);
lean_dec(v_x_4096_);
v_x_4094_ = v_fn_4152_;
v_x_4095_ = v___x_4154_;
v_x_4096_ = v___x_4156_;
goto _start;
}
else
{
lean_dec(v_x_4096_);
if (v_skipConstInApp_4093_ == 0)
{
goto v___jp_4149_;
}
else
{
uint8_t v___x_4158_; 
v___x_4158_ = l_Lean_Expr_isConst(v_x_4094_);
if (v___x_4158_ == 0)
{
goto v___jp_4149_;
}
else
{
v_f_4104_ = v_x_4094_;
v___y_4105_ = v___y_4097_;
v___y_4106_ = v___y_4098_;
v___y_4107_ = v___y_4099_;
v___y_4108_ = v___y_4100_;
v___y_4109_ = v___y_4101_;
goto v___jp_4103_;
}
}
}
v___jp_4103_:
{
if (v_skipInstances_4089_ == 0)
{
size_t v_sz_4110_; size_t v___x_4111_; lean_object* v___x_4112_; 
v_sz_4110_ = lean_array_size(v_x_4095_);
v___x_4111_ = ((size_t)0ULL);
lean_inc_ref(v_post_4091_);
lean_inc_ref(v_pre_4090_);
v___x_4112_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__2(v_pre_4090_, v_post_4091_, v_usedLetOnly_4092_, v_skipConstInApp_4093_, v_skipInstances_4089_, v_sz_4110_, v___x_4111_, v_x_4095_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_);
if (lean_obj_tag(v___x_4112_) == 0)
{
lean_object* v_a_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; 
v_a_4113_ = lean_ctor_get(v___x_4112_, 0);
lean_inc(v_a_4113_);
lean_dec_ref_known(v___x_4112_, 1);
v___x_4114_ = l_Lean_mkAppN(v_f_4104_, v_a_4113_);
lean_dec(v_a_4113_);
v___x_4115_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4090_, v_post_4091_, v_usedLetOnly_4092_, v_skipConstInApp_4093_, v_skipInstances_4089_, v___x_4114_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_);
return v___x_4115_;
}
else
{
lean_object* v_a_4116_; lean_object* v___x_4118_; uint8_t v_isShared_4119_; uint8_t v_isSharedCheck_4123_; 
lean_dec_ref(v_f_4104_);
lean_dec_ref(v_post_4091_);
lean_dec_ref(v_pre_4090_);
v_a_4116_ = lean_ctor_get(v___x_4112_, 0);
v_isSharedCheck_4123_ = !lean_is_exclusive(v___x_4112_);
if (v_isSharedCheck_4123_ == 0)
{
v___x_4118_ = v___x_4112_;
v_isShared_4119_ = v_isSharedCheck_4123_;
goto v_resetjp_4117_;
}
else
{
lean_inc(v_a_4116_);
lean_dec(v___x_4112_);
v___x_4118_ = lean_box(0);
v_isShared_4119_ = v_isSharedCheck_4123_;
goto v_resetjp_4117_;
}
v_resetjp_4117_:
{
lean_object* v___x_4121_; 
if (v_isShared_4119_ == 0)
{
v___x_4121_ = v___x_4118_;
goto v_reusejp_4120_;
}
else
{
lean_object* v_reuseFailAlloc_4122_; 
v_reuseFailAlloc_4122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4122_, 0, v_a_4116_);
v___x_4121_ = v_reuseFailAlloc_4122_;
goto v_reusejp_4120_;
}
v_reusejp_4120_:
{
return v___x_4121_;
}
}
}
}
else
{
lean_object* v___x_4124_; lean_object* v___x_4125_; 
v___x_4124_ = lean_array_get_size(v_x_4095_);
lean_inc_ref(v_f_4104_);
v___x_4125_ = l_Lean_Meta_getFunInfoNArgs(v_f_4104_, v___x_4124_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_);
if (lean_obj_tag(v___x_4125_) == 0)
{
lean_object* v_a_4126_; lean_object* v_paramInfo_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; 
v_a_4126_ = lean_ctor_get(v___x_4125_, 0);
lean_inc(v_a_4126_);
lean_dec_ref_known(v___x_4125_, 1);
v_paramInfo_4127_ = lean_ctor_get(v_a_4126_, 0);
lean_inc_ref(v_paramInfo_4127_);
lean_dec(v_a_4126_);
v___x_4128_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_4091_);
lean_inc_ref(v_pre_4090_);
v___x_4129_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg(v___x_4124_, v_paramInfo_4127_, v_pre_4090_, v_post_4091_, v_usedLetOnly_4092_, v_skipConstInApp_4093_, v_skipInstances_4089_, v___x_4128_, v_x_4095_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_);
lean_dec_ref(v_paramInfo_4127_);
if (lean_obj_tag(v___x_4129_) == 0)
{
lean_object* v_a_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; 
v_a_4130_ = lean_ctor_get(v___x_4129_, 0);
lean_inc(v_a_4130_);
lean_dec_ref_known(v___x_4129_, 1);
v___x_4131_ = l_Lean_mkAppN(v_f_4104_, v_a_4130_);
lean_dec(v_a_4130_);
v___x_4132_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4090_, v_post_4091_, v_usedLetOnly_4092_, v_skipConstInApp_4093_, v_skipInstances_4089_, v___x_4131_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_);
return v___x_4132_;
}
else
{
lean_object* v_a_4133_; lean_object* v___x_4135_; uint8_t v_isShared_4136_; uint8_t v_isSharedCheck_4140_; 
lean_dec_ref(v_f_4104_);
lean_dec_ref(v_post_4091_);
lean_dec_ref(v_pre_4090_);
v_a_4133_ = lean_ctor_get(v___x_4129_, 0);
v_isSharedCheck_4140_ = !lean_is_exclusive(v___x_4129_);
if (v_isSharedCheck_4140_ == 0)
{
v___x_4135_ = v___x_4129_;
v_isShared_4136_ = v_isSharedCheck_4140_;
goto v_resetjp_4134_;
}
else
{
lean_inc(v_a_4133_);
lean_dec(v___x_4129_);
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
lean_object* v_a_4141_; lean_object* v___x_4143_; uint8_t v_isShared_4144_; uint8_t v_isSharedCheck_4148_; 
lean_dec_ref(v_f_4104_);
lean_dec_ref(v_x_4095_);
lean_dec_ref(v_post_4091_);
lean_dec_ref(v_pre_4090_);
v_a_4141_ = lean_ctor_get(v___x_4125_, 0);
v_isSharedCheck_4148_ = !lean_is_exclusive(v___x_4125_);
if (v_isSharedCheck_4148_ == 0)
{
v___x_4143_ = v___x_4125_;
v_isShared_4144_ = v_isSharedCheck_4148_;
goto v_resetjp_4142_;
}
else
{
lean_inc(v_a_4141_);
lean_dec(v___x_4125_);
v___x_4143_ = lean_box(0);
v_isShared_4144_ = v_isSharedCheck_4148_;
goto v_resetjp_4142_;
}
v_resetjp_4142_:
{
lean_object* v___x_4146_; 
if (v_isShared_4144_ == 0)
{
v___x_4146_ = v___x_4143_;
goto v_reusejp_4145_;
}
else
{
lean_object* v_reuseFailAlloc_4147_; 
v_reuseFailAlloc_4147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4147_, 0, v_a_4141_);
v___x_4146_ = v_reuseFailAlloc_4147_;
goto v_reusejp_4145_;
}
v_reusejp_4145_:
{
return v___x_4146_;
}
}
}
}
}
v___jp_4149_:
{
lean_object* v___x_4150_; 
lean_inc_ref(v_post_4091_);
lean_inc_ref(v_pre_4090_);
v___x_4150_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4090_, v_post_4091_, v_usedLetOnly_4092_, v_skipConstInApp_4093_, v_skipInstances_4089_, v_x_4094_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_, v___y_4101_);
if (lean_obj_tag(v___x_4150_) == 0)
{
lean_object* v_a_4151_; 
v_a_4151_ = lean_ctor_get(v___x_4150_, 0);
lean_inc(v_a_4151_);
lean_dec_ref_known(v___x_4150_, 1);
v_f_4104_ = v_a_4151_;
v___y_4105_ = v___y_4097_;
v___y_4106_ = v___y_4098_;
v___y_4107_ = v___y_4099_;
v___y_4108_ = v___y_4100_;
v___y_4109_ = v___y_4101_;
goto v___jp_4103_;
}
else
{
lean_dec_ref(v_x_4095_);
lean_dec_ref(v_post_4091_);
lean_dec_ref(v_pre_4090_);
return v___x_4150_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1(lean_object* v___x_4159_, lean_object* v_pre_4160_, lean_object* v_e_4161_, lean_object* v_post_4162_, uint8_t v_usedLetOnly_4163_, uint8_t v_skipConstInApp_4164_, uint8_t v_skipInstances_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_){
_start:
{
lean_object* v___x_4172_; 
v___x_4172_ = l_Lean_Core_checkSystem(v___x_4159_, v___y_4169_, v___y_4170_);
if (lean_obj_tag(v___x_4172_) == 0)
{
lean_object* v___x_4173_; 
lean_dec_ref_known(v___x_4172_, 1);
lean_inc_ref(v_pre_4160_);
lean_inc(v___y_4170_);
lean_inc_ref(v___y_4169_);
lean_inc(v___y_4168_);
lean_inc_ref(v___y_4167_);
lean_inc_ref(v_e_4161_);
v___x_4173_ = lean_apply_6(v_pre_4160_, v_e_4161_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_, lean_box(0));
if (lean_obj_tag(v___x_4173_) == 0)
{
lean_object* v_a_4174_; lean_object* v___x_4176_; uint8_t v_isShared_4177_; uint8_t v_isSharedCheck_4222_; 
v_a_4174_ = lean_ctor_get(v___x_4173_, 0);
v_isSharedCheck_4222_ = !lean_is_exclusive(v___x_4173_);
if (v_isSharedCheck_4222_ == 0)
{
v___x_4176_ = v___x_4173_;
v_isShared_4177_ = v_isSharedCheck_4222_;
goto v_resetjp_4175_;
}
else
{
lean_inc(v_a_4174_);
lean_dec(v___x_4173_);
v___x_4176_ = lean_box(0);
v_isShared_4177_ = v_isSharedCheck_4222_;
goto v_resetjp_4175_;
}
v_resetjp_4175_:
{
lean_object* v___y_4179_; 
switch(lean_obj_tag(v_a_4174_))
{
case 0:
{
lean_object* v_e_4214_; lean_object* v___x_4216_; 
lean_dec_ref(v_post_4162_);
lean_dec_ref(v_e_4161_);
lean_dec_ref(v_pre_4160_);
v_e_4214_ = lean_ctor_get(v_a_4174_, 0);
lean_inc_ref(v_e_4214_);
lean_dec_ref_known(v_a_4174_, 1);
if (v_isShared_4177_ == 0)
{
lean_ctor_set(v___x_4176_, 0, v_e_4214_);
v___x_4216_ = v___x_4176_;
goto v_reusejp_4215_;
}
else
{
lean_object* v_reuseFailAlloc_4217_; 
v_reuseFailAlloc_4217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4217_, 0, v_e_4214_);
v___x_4216_ = v_reuseFailAlloc_4217_;
goto v_reusejp_4215_;
}
v_reusejp_4215_:
{
return v___x_4216_;
}
}
case 1:
{
lean_object* v_e_4218_; lean_object* v___x_4219_; 
lean_del_object(v___x_4176_);
lean_dec_ref(v_e_4161_);
v_e_4218_ = lean_ctor_get(v_a_4174_, 0);
lean_inc_ref(v_e_4218_);
lean_dec_ref_known(v_a_4174_, 1);
v___x_4219_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4160_, v_post_4162_, v_usedLetOnly_4163_, v_skipConstInApp_4164_, v_skipInstances_4165_, v_e_4218_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_);
return v___x_4219_;
}
default: 
{
lean_object* v_e_x3f_4220_; 
lean_del_object(v___x_4176_);
v_e_x3f_4220_ = lean_ctor_get(v_a_4174_, 0);
lean_inc(v_e_x3f_4220_);
lean_dec_ref_known(v_a_4174_, 1);
if (lean_obj_tag(v_e_x3f_4220_) == 0)
{
v___y_4179_ = v_e_4161_;
goto v___jp_4178_;
}
else
{
lean_object* v_val_4221_; 
lean_dec_ref(v_e_4161_);
v_val_4221_ = lean_ctor_get(v_e_x3f_4220_, 0);
lean_inc(v_val_4221_);
lean_dec_ref_known(v_e_x3f_4220_, 1);
v___y_4179_ = v_val_4221_;
goto v___jp_4178_;
}
}
}
v___jp_4178_:
{
switch(lean_obj_tag(v___y_4179_))
{
case 7:
{
lean_object* v___x_4180_; lean_object* v___x_4181_; 
v___x_4180_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_4181_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5(v_pre_4160_, v_post_4162_, v_usedLetOnly_4163_, v_skipConstInApp_4164_, v_skipInstances_4165_, v___x_4180_, v___y_4179_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_);
return v___x_4181_;
}
case 6:
{
lean_object* v___x_4182_; lean_object* v___x_4183_; 
v___x_4182_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_4183_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6(v_pre_4160_, v_post_4162_, v_usedLetOnly_4163_, v_skipConstInApp_4164_, v_skipInstances_4165_, v___x_4182_, v___y_4179_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_);
return v___x_4183_;
}
case 8:
{
lean_object* v___x_4184_; lean_object* v___x_4185_; 
v___x_4184_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_4185_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7(v_pre_4160_, v_post_4162_, v_usedLetOnly_4163_, v_skipConstInApp_4164_, v_skipInstances_4165_, v___x_4184_, v___y_4179_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_);
return v___x_4185_;
}
case 5:
{
lean_object* v_dummy_4186_; lean_object* v_nargs_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; 
v_dummy_4186_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_4187_ = l_Lean_Expr_getAppNumArgs(v___y_4179_);
lean_inc(v_nargs_4187_);
v___x_4188_ = lean_mk_array(v_nargs_4187_, v_dummy_4186_);
v___x_4189_ = lean_unsigned_to_nat(1u);
v___x_4190_ = lean_nat_sub(v_nargs_4187_, v___x_4189_);
lean_dec(v_nargs_4187_);
v___x_4191_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__8(v_skipInstances_4165_, v_pre_4160_, v_post_4162_, v_usedLetOnly_4163_, v_skipConstInApp_4164_, v___y_4179_, v___x_4188_, v___x_4190_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_);
return v___x_4191_;
}
case 10:
{
lean_object* v_data_4192_; lean_object* v_expr_4193_; lean_object* v___x_4194_; 
v_data_4192_ = lean_ctor_get(v___y_4179_, 0);
v_expr_4193_ = lean_ctor_get(v___y_4179_, 1);
lean_inc_ref(v_expr_4193_);
lean_inc_ref(v_post_4162_);
lean_inc_ref(v_pre_4160_);
v___x_4194_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4160_, v_post_4162_, v_usedLetOnly_4163_, v_skipConstInApp_4164_, v_skipInstances_4165_, v_expr_4193_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_);
if (lean_obj_tag(v___x_4194_) == 0)
{
lean_object* v_a_4195_; size_t v___x_4196_; size_t v___x_4197_; uint8_t v___x_4198_; 
v_a_4195_ = lean_ctor_get(v___x_4194_, 0);
lean_inc(v_a_4195_);
lean_dec_ref_known(v___x_4194_, 1);
v___x_4196_ = lean_ptr_addr(v_expr_4193_);
v___x_4197_ = lean_ptr_addr(v_a_4195_);
v___x_4198_ = lean_usize_dec_eq(v___x_4196_, v___x_4197_);
if (v___x_4198_ == 0)
{
lean_object* v___x_4199_; lean_object* v___x_4200_; 
lean_inc(v_data_4192_);
lean_dec_ref_known(v___y_4179_, 2);
v___x_4199_ = l_Lean_Expr_mdata___override(v_data_4192_, v_a_4195_);
v___x_4200_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4160_, v_post_4162_, v_usedLetOnly_4163_, v_skipConstInApp_4164_, v_skipInstances_4165_, v___x_4199_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_);
return v___x_4200_;
}
else
{
lean_object* v___x_4201_; 
lean_dec(v_a_4195_);
v___x_4201_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4160_, v_post_4162_, v_usedLetOnly_4163_, v_skipConstInApp_4164_, v_skipInstances_4165_, v___y_4179_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_);
return v___x_4201_;
}
}
else
{
lean_dec_ref_known(v___y_4179_, 2);
lean_dec_ref(v_post_4162_);
lean_dec_ref(v_pre_4160_);
return v___x_4194_;
}
}
case 11:
{
lean_object* v_typeName_4202_; lean_object* v_idx_4203_; lean_object* v_struct_4204_; lean_object* v___x_4205_; 
v_typeName_4202_ = lean_ctor_get(v___y_4179_, 0);
v_idx_4203_ = lean_ctor_get(v___y_4179_, 1);
v_struct_4204_ = lean_ctor_get(v___y_4179_, 2);
lean_inc_ref(v_struct_4204_);
lean_inc_ref(v_post_4162_);
lean_inc_ref(v_pre_4160_);
v___x_4205_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4160_, v_post_4162_, v_usedLetOnly_4163_, v_skipConstInApp_4164_, v_skipInstances_4165_, v_struct_4204_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_);
if (lean_obj_tag(v___x_4205_) == 0)
{
lean_object* v_a_4206_; size_t v___x_4207_; size_t v___x_4208_; uint8_t v___x_4209_; 
v_a_4206_ = lean_ctor_get(v___x_4205_, 0);
lean_inc(v_a_4206_);
lean_dec_ref_known(v___x_4205_, 1);
v___x_4207_ = lean_ptr_addr(v_struct_4204_);
v___x_4208_ = lean_ptr_addr(v_a_4206_);
v___x_4209_ = lean_usize_dec_eq(v___x_4207_, v___x_4208_);
if (v___x_4209_ == 0)
{
lean_object* v___x_4210_; lean_object* v___x_4211_; 
lean_inc(v_idx_4203_);
lean_inc(v_typeName_4202_);
lean_dec_ref_known(v___y_4179_, 3);
v___x_4210_ = l_Lean_Expr_proj___override(v_typeName_4202_, v_idx_4203_, v_a_4206_);
v___x_4211_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4160_, v_post_4162_, v_usedLetOnly_4163_, v_skipConstInApp_4164_, v_skipInstances_4165_, v___x_4210_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_);
return v___x_4211_;
}
else
{
lean_object* v___x_4212_; 
lean_dec(v_a_4206_);
v___x_4212_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4160_, v_post_4162_, v_usedLetOnly_4163_, v_skipConstInApp_4164_, v_skipInstances_4165_, v___y_4179_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_);
return v___x_4212_;
}
}
else
{
lean_dec_ref_known(v___y_4179_, 3);
lean_dec_ref(v_post_4162_);
lean_dec_ref(v_pre_4160_);
return v___x_4205_;
}
}
default: 
{
lean_object* v___x_4213_; 
v___x_4213_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4160_, v_post_4162_, v_usedLetOnly_4163_, v_skipConstInApp_4164_, v_skipInstances_4165_, v___y_4179_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_);
return v___x_4213_;
}
}
}
}
}
else
{
lean_object* v_a_4223_; lean_object* v___x_4225_; uint8_t v_isShared_4226_; uint8_t v_isSharedCheck_4230_; 
lean_dec_ref(v_post_4162_);
lean_dec_ref(v_e_4161_);
lean_dec_ref(v_pre_4160_);
v_a_4223_ = lean_ctor_get(v___x_4173_, 0);
v_isSharedCheck_4230_ = !lean_is_exclusive(v___x_4173_);
if (v_isSharedCheck_4230_ == 0)
{
v___x_4225_ = v___x_4173_;
v_isShared_4226_ = v_isSharedCheck_4230_;
goto v_resetjp_4224_;
}
else
{
lean_inc(v_a_4223_);
lean_dec(v___x_4173_);
v___x_4225_ = lean_box(0);
v_isShared_4226_ = v_isSharedCheck_4230_;
goto v_resetjp_4224_;
}
v_resetjp_4224_:
{
lean_object* v___x_4228_; 
if (v_isShared_4226_ == 0)
{
v___x_4228_ = v___x_4225_;
goto v_reusejp_4227_;
}
else
{
lean_object* v_reuseFailAlloc_4229_; 
v_reuseFailAlloc_4229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4229_, 0, v_a_4223_);
v___x_4228_ = v_reuseFailAlloc_4229_;
goto v_reusejp_4227_;
}
v_reusejp_4227_:
{
return v___x_4228_;
}
}
}
}
else
{
lean_object* v_a_4231_; lean_object* v___x_4233_; uint8_t v_isShared_4234_; uint8_t v_isSharedCheck_4238_; 
lean_dec_ref(v_post_4162_);
lean_dec_ref(v_e_4161_);
lean_dec_ref(v_pre_4160_);
v_a_4231_ = lean_ctor_get(v___x_4172_, 0);
v_isSharedCheck_4238_ = !lean_is_exclusive(v___x_4172_);
if (v_isSharedCheck_4238_ == 0)
{
v___x_4233_ = v___x_4172_;
v_isShared_4234_ = v_isSharedCheck_4238_;
goto v_resetjp_4232_;
}
else
{
lean_inc(v_a_4231_);
lean_dec(v___x_4172_);
v___x_4233_ = lean_box(0);
v_isShared_4234_ = v_isSharedCheck_4238_;
goto v_resetjp_4232_;
}
v_resetjp_4232_:
{
lean_object* v___x_4236_; 
if (v_isShared_4234_ == 0)
{
v___x_4236_ = v___x_4233_;
goto v_reusejp_4235_;
}
else
{
lean_object* v_reuseFailAlloc_4237_; 
v_reuseFailAlloc_4237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4237_, 0, v_a_4231_);
v___x_4236_ = v_reuseFailAlloc_4237_;
goto v_reusejp_4235_;
}
v_reusejp_4235_:
{
return v___x_4236_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1___boxed(lean_object* v___x_4239_, lean_object* v_pre_4240_, lean_object* v_e_4241_, lean_object* v_post_4242_, lean_object* v_usedLetOnly_4243_, lean_object* v_skipConstInApp_4244_, lean_object* v_skipInstances_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_){
_start:
{
uint8_t v_usedLetOnly_boxed_4252_; uint8_t v_skipConstInApp_boxed_4253_; uint8_t v_skipInstances_boxed_4254_; lean_object* v_res_4255_; 
v_usedLetOnly_boxed_4252_ = lean_unbox(v_usedLetOnly_4243_);
v_skipConstInApp_boxed_4253_ = lean_unbox(v_skipConstInApp_4244_);
v_skipInstances_boxed_4254_ = lean_unbox(v_skipInstances_4245_);
v_res_4255_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1(v___x_4239_, v_pre_4240_, v_e_4241_, v_post_4242_, v_usedLetOnly_boxed_4252_, v_skipConstInApp_boxed_4253_, v_skipInstances_boxed_4254_, v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_, v___y_4250_);
lean_dec(v___y_4250_);
lean_dec_ref(v___y_4249_);
lean_dec(v___y_4248_);
lean_dec_ref(v___y_4247_);
lean_dec(v___y_4246_);
return v_res_4255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(lean_object* v_pre_4256_, lean_object* v_post_4257_, uint8_t v_usedLetOnly_4258_, uint8_t v_skipConstInApp_4259_, uint8_t v_skipInstances_4260_, lean_object* v_e_4261_, lean_object* v_a_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_){
_start:
{
lean_object* v___x_4268_; lean_object* v___x_4269_; 
lean_inc(v_a_4262_);
v___x_4268_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_4268_, 0, lean_box(0));
lean_closure_set(v___x_4268_, 1, lean_box(0));
lean_closure_set(v___x_4268_, 2, v_a_4262_);
v___x_4269_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0(lean_box(0), v___x_4268_, v___y_4263_, v___y_4264_, v___y_4265_, v___y_4266_);
if (lean_obj_tag(v___x_4269_) == 0)
{
lean_object* v_a_4270_; lean_object* v___x_4272_; uint8_t v_isShared_4273_; uint8_t v_isSharedCheck_4304_; 
v_a_4270_ = lean_ctor_get(v___x_4269_, 0);
v_isSharedCheck_4304_ = !lean_is_exclusive(v___x_4269_);
if (v_isSharedCheck_4304_ == 0)
{
v___x_4272_ = v___x_4269_;
v_isShared_4273_ = v_isSharedCheck_4304_;
goto v_resetjp_4271_;
}
else
{
lean_inc(v_a_4270_);
lean_dec(v___x_4269_);
v___x_4272_ = lean_box(0);
v_isShared_4273_ = v_isSharedCheck_4304_;
goto v_resetjp_4271_;
}
v_resetjp_4271_:
{
lean_object* v___x_4274_; 
v___x_4274_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg(v_a_4270_, v_e_4261_);
lean_dec(v_a_4270_);
if (lean_obj_tag(v___x_4274_) == 0)
{
lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; lean_object* v___f_4279_; lean_object* v___x_4280_; 
lean_del_object(v___x_4272_);
v___x_4275_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__19___closed__0));
v___x_4276_ = lean_box(v_usedLetOnly_4258_);
v___x_4277_ = lean_box(v_skipConstInApp_4259_);
v___x_4278_ = lean_box(v_skipInstances_4260_);
lean_inc_ref(v_e_4261_);
v___f_4279_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1___boxed), 13, 7);
lean_closure_set(v___f_4279_, 0, v___x_4275_);
lean_closure_set(v___f_4279_, 1, v_pre_4256_);
lean_closure_set(v___f_4279_, 2, v_e_4261_);
lean_closure_set(v___f_4279_, 3, v_post_4257_);
lean_closure_set(v___f_4279_, 4, v___x_4276_);
lean_closure_set(v___f_4279_, 5, v___x_4277_);
lean_closure_set(v___f_4279_, 6, v___x_4278_);
v___x_4280_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg(v___f_4279_, v_a_4262_, v___y_4263_, v___y_4264_, v___y_4265_, v___y_4266_);
if (lean_obj_tag(v___x_4280_) == 0)
{
lean_object* v_a_4281_; lean_object* v___f_4282_; lean_object* v___x_4283_; 
v_a_4281_ = lean_ctor_get(v___x_4280_, 0);
lean_inc_n(v_a_4281_, 2);
lean_dec_ref_known(v___x_4280_, 1);
lean_inc(v_a_4262_);
v___f_4282_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_4282_, 0, v_a_4262_);
lean_closure_set(v___f_4282_, 1, v_e_4261_);
lean_closure_set(v___f_4282_, 2, v_a_4281_);
v___x_4283_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0(lean_box(0), v___f_4282_, v___y_4263_, v___y_4264_, v___y_4265_, v___y_4266_);
if (lean_obj_tag(v___x_4283_) == 0)
{
lean_object* v___x_4285_; uint8_t v_isShared_4286_; uint8_t v_isSharedCheck_4290_; 
v_isSharedCheck_4290_ = !lean_is_exclusive(v___x_4283_);
if (v_isSharedCheck_4290_ == 0)
{
lean_object* v_unused_4291_; 
v_unused_4291_ = lean_ctor_get(v___x_4283_, 0);
lean_dec(v_unused_4291_);
v___x_4285_ = v___x_4283_;
v_isShared_4286_ = v_isSharedCheck_4290_;
goto v_resetjp_4284_;
}
else
{
lean_dec(v___x_4283_);
v___x_4285_ = lean_box(0);
v_isShared_4286_ = v_isSharedCheck_4290_;
goto v_resetjp_4284_;
}
v_resetjp_4284_:
{
lean_object* v___x_4288_; 
if (v_isShared_4286_ == 0)
{
lean_ctor_set(v___x_4285_, 0, v_a_4281_);
v___x_4288_ = v___x_4285_;
goto v_reusejp_4287_;
}
else
{
lean_object* v_reuseFailAlloc_4289_; 
v_reuseFailAlloc_4289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4289_, 0, v_a_4281_);
v___x_4288_ = v_reuseFailAlloc_4289_;
goto v_reusejp_4287_;
}
v_reusejp_4287_:
{
return v___x_4288_;
}
}
}
else
{
lean_object* v_a_4292_; lean_object* v___x_4294_; uint8_t v_isShared_4295_; uint8_t v_isSharedCheck_4299_; 
lean_dec(v_a_4281_);
v_a_4292_ = lean_ctor_get(v___x_4283_, 0);
v_isSharedCheck_4299_ = !lean_is_exclusive(v___x_4283_);
if (v_isSharedCheck_4299_ == 0)
{
v___x_4294_ = v___x_4283_;
v_isShared_4295_ = v_isSharedCheck_4299_;
goto v_resetjp_4293_;
}
else
{
lean_inc(v_a_4292_);
lean_dec(v___x_4283_);
v___x_4294_ = lean_box(0);
v_isShared_4295_ = v_isSharedCheck_4299_;
goto v_resetjp_4293_;
}
v_resetjp_4293_:
{
lean_object* v___x_4297_; 
if (v_isShared_4295_ == 0)
{
v___x_4297_ = v___x_4294_;
goto v_reusejp_4296_;
}
else
{
lean_object* v_reuseFailAlloc_4298_; 
v_reuseFailAlloc_4298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4298_, 0, v_a_4292_);
v___x_4297_ = v_reuseFailAlloc_4298_;
goto v_reusejp_4296_;
}
v_reusejp_4296_:
{
return v___x_4297_;
}
}
}
}
else
{
lean_dec_ref(v_e_4261_);
return v___x_4280_;
}
}
else
{
lean_object* v_val_4300_; lean_object* v___x_4302_; 
lean_dec_ref(v_e_4261_);
lean_dec_ref(v_post_4257_);
lean_dec_ref(v_pre_4256_);
v_val_4300_ = lean_ctor_get(v___x_4274_, 0);
lean_inc(v_val_4300_);
lean_dec_ref_known(v___x_4274_, 1);
if (v_isShared_4273_ == 0)
{
lean_ctor_set(v___x_4272_, 0, v_val_4300_);
v___x_4302_ = v___x_4272_;
goto v_reusejp_4301_;
}
else
{
lean_object* v_reuseFailAlloc_4303_; 
v_reuseFailAlloc_4303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4303_, 0, v_val_4300_);
v___x_4302_ = v_reuseFailAlloc_4303_;
goto v_reusejp_4301_;
}
v_reusejp_4301_:
{
return v___x_4302_;
}
}
}
}
else
{
lean_object* v_a_4305_; lean_object* v___x_4307_; uint8_t v_isShared_4308_; uint8_t v_isSharedCheck_4312_; 
lean_dec_ref(v_e_4261_);
lean_dec_ref(v_post_4257_);
lean_dec_ref(v_pre_4256_);
v_a_4305_ = lean_ctor_get(v___x_4269_, 0);
v_isSharedCheck_4312_ = !lean_is_exclusive(v___x_4269_);
if (v_isSharedCheck_4312_ == 0)
{
v___x_4307_ = v___x_4269_;
v_isShared_4308_ = v_isSharedCheck_4312_;
goto v_resetjp_4306_;
}
else
{
lean_inc(v_a_4305_);
lean_dec(v___x_4269_);
v___x_4307_ = lean_box(0);
v_isShared_4308_ = v_isSharedCheck_4312_;
goto v_resetjp_4306_;
}
v_resetjp_4306_:
{
lean_object* v___x_4310_; 
if (v_isShared_4308_ == 0)
{
v___x_4310_ = v___x_4307_;
goto v_reusejp_4309_;
}
else
{
lean_object* v_reuseFailAlloc_4311_; 
v_reuseFailAlloc_4311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4311_, 0, v_a_4305_);
v___x_4310_ = v_reuseFailAlloc_4311_;
goto v_reusejp_4309_;
}
v_reusejp_4309_:
{
return v___x_4310_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___lam__0___boxed(lean_object* v_fvars_4313_, lean_object* v_pre_4314_, lean_object* v_post_4315_, lean_object* v_usedLetOnly_4316_, lean_object* v_skipConstInApp_4317_, lean_object* v_skipInstances_4318_, lean_object* v_body_4319_, lean_object* v_x_4320_, lean_object* v___y_4321_, lean_object* v___y_4322_, lean_object* v___y_4323_, lean_object* v___y_4324_, lean_object* v___y_4325_, lean_object* v___y_4326_){
_start:
{
uint8_t v_usedLetOnly_boxed_4327_; uint8_t v_skipConstInApp_boxed_4328_; uint8_t v_skipInstances_boxed_4329_; lean_object* v_res_4330_; 
v_usedLetOnly_boxed_4327_ = lean_unbox(v_usedLetOnly_4316_);
v_skipConstInApp_boxed_4328_ = lean_unbox(v_skipConstInApp_4317_);
v_skipInstances_boxed_4329_ = lean_unbox(v_skipInstances_4318_);
v_res_4330_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___lam__0(v_fvars_4313_, v_pre_4314_, v_post_4315_, v_usedLetOnly_boxed_4327_, v_skipConstInApp_boxed_4328_, v_skipInstances_boxed_4329_, v_body_4319_, v_x_4320_, v___y_4321_, v___y_4322_, v___y_4323_, v___y_4324_, v___y_4325_);
lean_dec(v___y_4325_);
lean_dec_ref(v___y_4324_);
lean_dec(v___y_4323_);
lean_dec_ref(v___y_4322_);
lean_dec(v___y_4321_);
return v_res_4330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5(lean_object* v_pre_4331_, lean_object* v_post_4332_, uint8_t v_usedLetOnly_4333_, uint8_t v_skipConstInApp_4334_, uint8_t v_skipInstances_4335_, lean_object* v_fvars_4336_, lean_object* v_e_4337_, lean_object* v_a_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_, lean_object* v___y_4341_, lean_object* v___y_4342_){
_start:
{
if (lean_obj_tag(v_e_4337_) == 7)
{
lean_object* v_binderName_4344_; lean_object* v_binderType_4345_; lean_object* v_body_4346_; uint8_t v_binderInfo_4347_; lean_object* v___x_4348_; lean_object* v___x_4349_; 
v_binderName_4344_ = lean_ctor_get(v_e_4337_, 0);
lean_inc(v_binderName_4344_);
v_binderType_4345_ = lean_ctor_get(v_e_4337_, 1);
lean_inc_ref(v_binderType_4345_);
v_body_4346_ = lean_ctor_get(v_e_4337_, 2);
lean_inc_ref(v_body_4346_);
v_binderInfo_4347_ = lean_ctor_get_uint8(v_e_4337_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_4337_, 3);
v___x_4348_ = lean_expr_instantiate_rev(v_binderType_4345_, v_fvars_4336_);
lean_dec_ref(v_binderType_4345_);
lean_inc_ref(v_post_4332_);
lean_inc_ref(v_pre_4331_);
v___x_4349_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4331_, v_post_4332_, v_usedLetOnly_4333_, v_skipConstInApp_4334_, v_skipInstances_4335_, v___x_4348_, v_a_4338_, v___y_4339_, v___y_4340_, v___y_4341_, v___y_4342_);
if (lean_obj_tag(v___x_4349_) == 0)
{
lean_object* v_a_4350_; lean_object* v___x_4351_; lean_object* v___x_4352_; lean_object* v___x_4353_; lean_object* v___f_4354_; uint8_t v___x_4355_; lean_object* v___x_4356_; 
v_a_4350_ = lean_ctor_get(v___x_4349_, 0);
lean_inc(v_a_4350_);
lean_dec_ref_known(v___x_4349_, 1);
v___x_4351_ = lean_box(v_usedLetOnly_4333_);
v___x_4352_ = lean_box(v_skipConstInApp_4334_);
v___x_4353_ = lean_box(v_skipInstances_4335_);
v___f_4354_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___lam__0___boxed), 14, 7);
lean_closure_set(v___f_4354_, 0, v_fvars_4336_);
lean_closure_set(v___f_4354_, 1, v_pre_4331_);
lean_closure_set(v___f_4354_, 2, v_post_4332_);
lean_closure_set(v___f_4354_, 3, v___x_4351_);
lean_closure_set(v___f_4354_, 4, v___x_4352_);
lean_closure_set(v___f_4354_, 5, v___x_4353_);
lean_closure_set(v___f_4354_, 6, v_body_4346_);
v___x_4355_ = 0;
v___x_4356_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_binderName_4344_, v_binderInfo_4347_, v_a_4350_, v___f_4354_, v___x_4355_, v_a_4338_, v___y_4339_, v___y_4340_, v___y_4341_, v___y_4342_);
return v___x_4356_;
}
else
{
lean_dec_ref(v_body_4346_);
lean_dec(v_binderName_4344_);
lean_dec_ref(v_fvars_4336_);
lean_dec_ref(v_post_4332_);
lean_dec_ref(v_pre_4331_);
return v___x_4349_;
}
}
else
{
lean_object* v___x_4357_; lean_object* v___x_4358_; 
v___x_4357_ = lean_expr_instantiate_rev(v_e_4337_, v_fvars_4336_);
lean_dec_ref(v_e_4337_);
lean_inc_ref(v_post_4332_);
lean_inc_ref(v_pre_4331_);
v___x_4358_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4331_, v_post_4332_, v_usedLetOnly_4333_, v_skipConstInApp_4334_, v_skipInstances_4335_, v___x_4357_, v_a_4338_, v___y_4339_, v___y_4340_, v___y_4341_, v___y_4342_);
if (lean_obj_tag(v___x_4358_) == 0)
{
lean_object* v_a_4359_; uint8_t v___x_4360_; uint8_t v___x_4361_; uint8_t v___x_4362_; lean_object* v___x_4363_; 
v_a_4359_ = lean_ctor_get(v___x_4358_, 0);
lean_inc(v_a_4359_);
lean_dec_ref_known(v___x_4358_, 1);
v___x_4360_ = 0;
v___x_4361_ = 1;
v___x_4362_ = 1;
v___x_4363_ = l_Lean_Meta_mkForallFVars(v_fvars_4336_, v_a_4359_, v___x_4360_, v_usedLetOnly_4333_, v___x_4361_, v___x_4362_, v___y_4339_, v___y_4340_, v___y_4341_, v___y_4342_);
lean_dec_ref(v_fvars_4336_);
if (lean_obj_tag(v___x_4363_) == 0)
{
lean_object* v_a_4364_; lean_object* v___x_4365_; 
v_a_4364_ = lean_ctor_get(v___x_4363_, 0);
lean_inc(v_a_4364_);
lean_dec_ref_known(v___x_4363_, 1);
v___x_4365_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4331_, v_post_4332_, v_usedLetOnly_4333_, v_skipConstInApp_4334_, v_skipInstances_4335_, v_a_4364_, v_a_4338_, v___y_4339_, v___y_4340_, v___y_4341_, v___y_4342_);
return v___x_4365_;
}
else
{
lean_dec_ref(v_post_4332_);
lean_dec_ref(v_pre_4331_);
return v___x_4363_;
}
}
else
{
lean_dec_ref(v_fvars_4336_);
lean_dec_ref(v_post_4332_);
lean_dec_ref(v_pre_4331_);
return v___x_4358_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___lam__0(lean_object* v_fvars_4366_, lean_object* v_pre_4367_, lean_object* v_post_4368_, uint8_t v_usedLetOnly_4369_, uint8_t v_skipConstInApp_4370_, uint8_t v_skipInstances_4371_, lean_object* v_body_4372_, lean_object* v_x_4373_, lean_object* v___y_4374_, lean_object* v___y_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_){
_start:
{
lean_object* v___x_4380_; lean_object* v___x_4381_; 
v___x_4380_ = lean_array_push(v_fvars_4366_, v_x_4373_);
v___x_4381_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5(v_pre_4367_, v_post_4368_, v_usedLetOnly_4369_, v_skipConstInApp_4370_, v_skipInstances_4371_, v___x_4380_, v_body_4372_, v___y_4374_, v___y_4375_, v___y_4376_, v___y_4377_, v___y_4378_);
return v___x_4381_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3___boxed(lean_object* v_pre_4382_, lean_object* v_post_4383_, lean_object* v_usedLetOnly_4384_, lean_object* v_skipConstInApp_4385_, lean_object* v_skipInstances_4386_, lean_object* v_e_4387_, lean_object* v_a_4388_, lean_object* v___y_4389_, lean_object* v___y_4390_, lean_object* v___y_4391_, lean_object* v___y_4392_, lean_object* v___y_4393_){
_start:
{
uint8_t v_usedLetOnly_boxed_4394_; uint8_t v_skipConstInApp_boxed_4395_; uint8_t v_skipInstances_boxed_4396_; lean_object* v_res_4397_; 
v_usedLetOnly_boxed_4394_ = lean_unbox(v_usedLetOnly_4384_);
v_skipConstInApp_boxed_4395_ = lean_unbox(v_skipConstInApp_4385_);
v_skipInstances_boxed_4396_ = lean_unbox(v_skipInstances_4386_);
v_res_4397_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4382_, v_post_4383_, v_usedLetOnly_boxed_4394_, v_skipConstInApp_boxed_4395_, v_skipInstances_boxed_4396_, v_e_4387_, v_a_4388_, v___y_4389_, v___y_4390_, v___y_4391_, v___y_4392_);
lean_dec(v___y_4392_);
lean_dec_ref(v___y_4391_);
lean_dec(v___y_4390_);
lean_dec_ref(v___y_4389_);
lean_dec(v_a_4388_);
return v_res_4397_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__2___boxed(lean_object* v_pre_4398_, lean_object* v_post_4399_, lean_object* v_usedLetOnly_4400_, lean_object* v_skipConstInApp_4401_, lean_object* v_skipInstances_4402_, lean_object* v_sz_4403_, lean_object* v_i_4404_, lean_object* v_bs_4405_, lean_object* v___y_4406_, lean_object* v___y_4407_, lean_object* v___y_4408_, lean_object* v___y_4409_, lean_object* v___y_4410_, lean_object* v___y_4411_){
_start:
{
uint8_t v_usedLetOnly_boxed_4412_; uint8_t v_skipConstInApp_boxed_4413_; uint8_t v_skipInstances_boxed_4414_; size_t v_sz_boxed_4415_; size_t v_i_boxed_4416_; lean_object* v_res_4417_; 
v_usedLetOnly_boxed_4412_ = lean_unbox(v_usedLetOnly_4400_);
v_skipConstInApp_boxed_4413_ = lean_unbox(v_skipConstInApp_4401_);
v_skipInstances_boxed_4414_ = lean_unbox(v_skipInstances_4402_);
v_sz_boxed_4415_ = lean_unbox_usize(v_sz_4403_);
lean_dec(v_sz_4403_);
v_i_boxed_4416_ = lean_unbox_usize(v_i_4404_);
lean_dec(v_i_4404_);
v_res_4417_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__2(v_pre_4398_, v_post_4399_, v_usedLetOnly_boxed_4412_, v_skipConstInApp_boxed_4413_, v_skipInstances_boxed_4414_, v_sz_boxed_4415_, v_i_boxed_4416_, v_bs_4405_, v___y_4406_, v___y_4407_, v___y_4408_, v___y_4409_, v___y_4410_);
lean_dec(v___y_4410_);
lean_dec_ref(v___y_4409_);
lean_dec(v___y_4408_);
lean_dec_ref(v___y_4407_);
lean_dec(v___y_4406_);
return v_res_4417_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___boxed(lean_object* v_pre_4418_, lean_object* v_post_4419_, lean_object* v_usedLetOnly_4420_, lean_object* v_skipConstInApp_4421_, lean_object* v_skipInstances_4422_, lean_object* v_e_4423_, lean_object* v_a_4424_, lean_object* v___y_4425_, lean_object* v___y_4426_, lean_object* v___y_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_){
_start:
{
uint8_t v_usedLetOnly_boxed_4430_; uint8_t v_skipConstInApp_boxed_4431_; uint8_t v_skipInstances_boxed_4432_; lean_object* v_res_4433_; 
v_usedLetOnly_boxed_4430_ = lean_unbox(v_usedLetOnly_4420_);
v_skipConstInApp_boxed_4431_ = lean_unbox(v_skipConstInApp_4421_);
v_skipInstances_boxed_4432_ = lean_unbox(v_skipInstances_4422_);
v_res_4433_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4418_, v_post_4419_, v_usedLetOnly_boxed_4430_, v_skipConstInApp_boxed_4431_, v_skipInstances_boxed_4432_, v_e_4423_, v_a_4424_, v___y_4425_, v___y_4426_, v___y_4427_, v___y_4428_);
lean_dec(v___y_4428_);
lean_dec_ref(v___y_4427_);
lean_dec(v___y_4426_);
lean_dec_ref(v___y_4425_);
lean_dec(v_a_4424_);
return v_res_4433_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___boxed(lean_object* v_pre_4434_, lean_object* v_post_4435_, lean_object* v_usedLetOnly_4436_, lean_object* v_skipConstInApp_4437_, lean_object* v_skipInstances_4438_, lean_object* v_fvars_4439_, lean_object* v_e_4440_, lean_object* v_a_4441_, lean_object* v___y_4442_, lean_object* v___y_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_, lean_object* v___y_4446_){
_start:
{
uint8_t v_usedLetOnly_boxed_4447_; uint8_t v_skipConstInApp_boxed_4448_; uint8_t v_skipInstances_boxed_4449_; lean_object* v_res_4450_; 
v_usedLetOnly_boxed_4447_ = lean_unbox(v_usedLetOnly_4436_);
v_skipConstInApp_boxed_4448_ = lean_unbox(v_skipConstInApp_4437_);
v_skipInstances_boxed_4449_ = lean_unbox(v_skipInstances_4438_);
v_res_4450_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5(v_pre_4434_, v_post_4435_, v_usedLetOnly_boxed_4447_, v_skipConstInApp_boxed_4448_, v_skipInstances_boxed_4449_, v_fvars_4439_, v_e_4440_, v_a_4441_, v___y_4442_, v___y_4443_, v___y_4444_, v___y_4445_);
lean_dec(v___y_4445_);
lean_dec_ref(v___y_4444_);
lean_dec(v___y_4443_);
lean_dec_ref(v___y_4442_);
lean_dec(v_a_4441_);
return v_res_4450_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___boxed(lean_object* v_pre_4451_, lean_object* v_post_4452_, lean_object* v_usedLetOnly_4453_, lean_object* v_skipConstInApp_4454_, lean_object* v_skipInstances_4455_, lean_object* v_fvars_4456_, lean_object* v_e_4457_, lean_object* v_a_4458_, lean_object* v___y_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_, lean_object* v___y_4463_){
_start:
{
uint8_t v_usedLetOnly_boxed_4464_; uint8_t v_skipConstInApp_boxed_4465_; uint8_t v_skipInstances_boxed_4466_; lean_object* v_res_4467_; 
v_usedLetOnly_boxed_4464_ = lean_unbox(v_usedLetOnly_4453_);
v_skipConstInApp_boxed_4465_ = lean_unbox(v_skipConstInApp_4454_);
v_skipInstances_boxed_4466_ = lean_unbox(v_skipInstances_4455_);
v_res_4467_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6(v_pre_4451_, v_post_4452_, v_usedLetOnly_boxed_4464_, v_skipConstInApp_boxed_4465_, v_skipInstances_boxed_4466_, v_fvars_4456_, v_e_4457_, v_a_4458_, v___y_4459_, v___y_4460_, v___y_4461_, v___y_4462_);
lean_dec(v___y_4462_);
lean_dec_ref(v___y_4461_);
lean_dec(v___y_4460_);
lean_dec_ref(v___y_4459_);
lean_dec(v_a_4458_);
return v_res_4467_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___boxed(lean_object* v_pre_4468_, lean_object* v_post_4469_, lean_object* v_usedLetOnly_4470_, lean_object* v_skipConstInApp_4471_, lean_object* v_skipInstances_4472_, lean_object* v_fvars_4473_, lean_object* v_e_4474_, lean_object* v_a_4475_, lean_object* v___y_4476_, lean_object* v___y_4477_, lean_object* v___y_4478_, lean_object* v___y_4479_, lean_object* v___y_4480_){
_start:
{
uint8_t v_usedLetOnly_boxed_4481_; uint8_t v_skipConstInApp_boxed_4482_; uint8_t v_skipInstances_boxed_4483_; lean_object* v_res_4484_; 
v_usedLetOnly_boxed_4481_ = lean_unbox(v_usedLetOnly_4470_);
v_skipConstInApp_boxed_4482_ = lean_unbox(v_skipConstInApp_4471_);
v_skipInstances_boxed_4483_ = lean_unbox(v_skipInstances_4472_);
v_res_4484_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7(v_pre_4468_, v_post_4469_, v_usedLetOnly_boxed_4481_, v_skipConstInApp_boxed_4482_, v_skipInstances_boxed_4483_, v_fvars_4473_, v_e_4474_, v_a_4475_, v___y_4476_, v___y_4477_, v___y_4478_, v___y_4479_);
lean_dec(v___y_4479_);
lean_dec_ref(v___y_4478_);
lean_dec(v___y_4477_);
lean_dec_ref(v___y_4476_);
lean_dec(v_a_4475_);
return v_res_4484_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_upperBound_4485_, lean_object* v___x_4486_, lean_object* v_pre_4487_, lean_object* v_post_4488_, lean_object* v_usedLetOnly_4489_, lean_object* v_skipConstInApp_4490_, lean_object* v_skipInstances_4491_, lean_object* v_a_4492_, lean_object* v_b_4493_, lean_object* v___y_4494_, lean_object* v___y_4495_, lean_object* v___y_4496_, lean_object* v___y_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_){
_start:
{
uint8_t v_usedLetOnly_boxed_4500_; uint8_t v_skipConstInApp_boxed_4501_; uint8_t v_skipInstances_boxed_4502_; lean_object* v_res_4503_; 
v_usedLetOnly_boxed_4500_ = lean_unbox(v_usedLetOnly_4489_);
v_skipConstInApp_boxed_4501_ = lean_unbox(v_skipConstInApp_4490_);
v_skipInstances_boxed_4502_ = lean_unbox(v_skipInstances_4491_);
v_res_4503_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg(v_upperBound_4485_, v___x_4486_, v_pre_4487_, v_post_4488_, v_usedLetOnly_boxed_4500_, v_skipConstInApp_boxed_4501_, v_skipInstances_boxed_4502_, v_a_4492_, v_b_4493_, v___y_4494_, v___y_4495_, v___y_4496_, v___y_4497_, v___y_4498_);
lean_dec(v___y_4498_);
lean_dec_ref(v___y_4497_);
lean_dec(v___y_4496_);
lean_dec_ref(v___y_4495_);
lean_dec(v___y_4494_);
lean_dec_ref(v___x_4486_);
lean_dec(v_upperBound_4485_);
return v_res_4503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__8___boxed(lean_object* v_skipInstances_4504_, lean_object* v_pre_4505_, lean_object* v_post_4506_, lean_object* v_usedLetOnly_4507_, lean_object* v_skipConstInApp_4508_, lean_object* v_x_4509_, lean_object* v_x_4510_, lean_object* v_x_4511_, lean_object* v___y_4512_, lean_object* v___y_4513_, lean_object* v___y_4514_, lean_object* v___y_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_){
_start:
{
uint8_t v_skipInstances_boxed_4518_; uint8_t v_usedLetOnly_boxed_4519_; uint8_t v_skipConstInApp_boxed_4520_; lean_object* v_res_4521_; 
v_skipInstances_boxed_4518_ = lean_unbox(v_skipInstances_4504_);
v_usedLetOnly_boxed_4519_ = lean_unbox(v_usedLetOnly_4507_);
v_skipConstInApp_boxed_4520_ = lean_unbox(v_skipConstInApp_4508_);
v_res_4521_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__8(v_skipInstances_boxed_4518_, v_pre_4505_, v_post_4506_, v_usedLetOnly_boxed_4519_, v_skipConstInApp_boxed_4520_, v_x_4509_, v_x_4510_, v_x_4511_, v___y_4512_, v___y_4513_, v___y_4514_, v___y_4515_, v___y_4516_);
lean_dec(v___y_4516_);
lean_dec_ref(v___y_4515_);
lean_dec(v___y_4514_);
lean_dec_ref(v___y_4513_);
lean_dec(v___y_4512_);
return v_res_4521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(lean_object* v_input_4522_, lean_object* v_pre_4523_, lean_object* v_post_4524_, uint8_t v_usedLetOnly_4525_, uint8_t v_skipConstInApp_4526_, lean_object* v___y_4527_, lean_object* v___y_4528_, lean_object* v___y_4529_, lean_object* v___y_4530_){
_start:
{
lean_object* v___x_4532_; lean_object* v___x_4533_; lean_object* v_a_4534_; uint8_t v___x_4535_; lean_object* v___x_4536_; 
v___x_4532_ = lean_obj_once(&l_Lean_Core_transform___redArg___closed__2, &l_Lean_Core_transform___redArg___closed__2_once, _init_l_Lean_Core_transform___redArg___closed__2);
v___x_4533_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0(lean_box(0), v___x_4532_, v___y_4527_, v___y_4528_, v___y_4529_, v___y_4530_);
v_a_4534_ = lean_ctor_get(v___x_4533_, 0);
lean_inc(v_a_4534_);
lean_dec_ref(v___x_4533_);
v___x_4535_ = 0;
v___x_4536_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4523_, v_post_4524_, v_usedLetOnly_4525_, v_skipConstInApp_4526_, v___x_4535_, v_input_4522_, v_a_4534_, v___y_4527_, v___y_4528_, v___y_4529_, v___y_4530_);
if (lean_obj_tag(v___x_4536_) == 0)
{
lean_object* v_a_4537_; lean_object* v___x_4538_; lean_object* v___x_4539_; lean_object* v___x_4541_; uint8_t v_isShared_4542_; uint8_t v_isSharedCheck_4546_; 
v_a_4537_ = lean_ctor_get(v___x_4536_, 0);
lean_inc(v_a_4537_);
lean_dec_ref_known(v___x_4536_, 1);
v___x_4538_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_4538_, 0, lean_box(0));
lean_closure_set(v___x_4538_, 1, lean_box(0));
lean_closure_set(v___x_4538_, 2, v_a_4534_);
v___x_4539_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0(lean_box(0), v___x_4538_, v___y_4527_, v___y_4528_, v___y_4529_, v___y_4530_);
v_isSharedCheck_4546_ = !lean_is_exclusive(v___x_4539_);
if (v_isSharedCheck_4546_ == 0)
{
lean_object* v_unused_4547_; 
v_unused_4547_ = lean_ctor_get(v___x_4539_, 0);
lean_dec(v_unused_4547_);
v___x_4541_ = v___x_4539_;
v_isShared_4542_ = v_isSharedCheck_4546_;
goto v_resetjp_4540_;
}
else
{
lean_dec(v___x_4539_);
v___x_4541_ = lean_box(0);
v_isShared_4542_ = v_isSharedCheck_4546_;
goto v_resetjp_4540_;
}
v_resetjp_4540_:
{
lean_object* v___x_4544_; 
if (v_isShared_4542_ == 0)
{
lean_ctor_set(v___x_4541_, 0, v_a_4537_);
v___x_4544_ = v___x_4541_;
goto v_reusejp_4543_;
}
else
{
lean_object* v_reuseFailAlloc_4545_; 
v_reuseFailAlloc_4545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4545_, 0, v_a_4537_);
v___x_4544_ = v_reuseFailAlloc_4545_;
goto v_reusejp_4543_;
}
v_reusejp_4543_:
{
return v___x_4544_;
}
}
}
else
{
lean_dec(v_a_4534_);
return v___x_4536_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___boxed(lean_object* v_input_4548_, lean_object* v_pre_4549_, lean_object* v_post_4550_, lean_object* v_usedLetOnly_4551_, lean_object* v_skipConstInApp_4552_, lean_object* v___y_4553_, lean_object* v___y_4554_, lean_object* v___y_4555_, lean_object* v___y_4556_, lean_object* v___y_4557_){
_start:
{
uint8_t v_usedLetOnly_boxed_4558_; uint8_t v_skipConstInApp_boxed_4559_; lean_object* v_res_4560_; 
v_usedLetOnly_boxed_4558_ = lean_unbox(v_usedLetOnly_4551_);
v_skipConstInApp_boxed_4559_ = lean_unbox(v_skipConstInApp_4552_);
v_res_4560_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(v_input_4548_, v_pre_4549_, v_post_4550_, v_usedLetOnly_boxed_4558_, v_skipConstInApp_boxed_4559_, v___y_4553_, v___y_4554_, v___y_4555_, v___y_4556_);
lean_dec(v___y_4556_);
lean_dec_ref(v___y_4555_);
lean_dec(v___y_4554_);
lean_dec_ref(v___y_4553_);
return v_res_4560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce(lean_object* v_e_4562_, uint8_t v_zetaDelta_4563_, uint8_t v_zetaHave_4564_, uint8_t v_beta_4565_, lean_object* v_a_4566_, lean_object* v_a_4567_, lean_object* v_a_4568_, lean_object* v_a_4569_){
_start:
{
lean_object* v_lctx_4571_; lean_object* v___x_4572_; lean_object* v___x_4573_; lean_object* v___x_4574_; lean_object* v___f_4575_; uint8_t v___x_4576_; 
v_lctx_4571_ = lean_ctor_get(v_a_4566_, 2);
lean_inc_ref(v_lctx_4571_);
v___x_4572_ = lean_local_ctx_num_indices(v_lctx_4571_);
v___x_4573_ = lean_box(v_zetaHave_4564_);
v___x_4574_ = lean_box(v_zetaDelta_4563_);
v___f_4575_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaReduce___lam__0___boxed), 9, 3);
lean_closure_set(v___f_4575_, 0, v___x_4573_);
lean_closure_set(v___f_4575_, 1, v___x_4572_);
lean_closure_set(v___f_4575_, 2, v___x_4574_);
v___x_4576_ = 1;
if (v_beta_4565_ == 0)
{
lean_object* v___f_4577_; lean_object* v___f_4578_; lean_object* v___x_4579_; 
v___f_4577_ = ((lean_object*)(l_Lean_Meta_zetaReduce___closed__0));
v___f_4578_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaReduce___lam__2___boxed), 7, 1);
lean_closure_set(v___f_4578_, 0, v___f_4575_);
v___x_4579_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(v_e_4562_, v___f_4578_, v___f_4577_, v___x_4576_, v_beta_4565_, v_a_4566_, v_a_4567_, v_a_4568_, v_a_4569_);
return v___x_4579_;
}
else
{
lean_object* v___f_4580_; lean_object* v___f_4581_; uint8_t v___x_4582_; lean_object* v___x_4583_; 
v___f_4580_ = ((lean_object*)(l_Lean_Meta_zetaReduce___closed__0));
v___f_4581_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaReduce___lam__4___boxed), 7, 1);
lean_closure_set(v___f_4581_, 0, v___f_4575_);
v___x_4582_ = 0;
v___x_4583_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(v_e_4562_, v___f_4581_, v___f_4580_, v___x_4576_, v___x_4582_, v_a_4566_, v_a_4567_, v_a_4568_, v_a_4569_);
return v___x_4583_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___boxed(lean_object* v_e_4584_, lean_object* v_zetaDelta_4585_, lean_object* v_zetaHave_4586_, lean_object* v_beta_4587_, lean_object* v_a_4588_, lean_object* v_a_4589_, lean_object* v_a_4590_, lean_object* v_a_4591_, lean_object* v_a_4592_){
_start:
{
uint8_t v_zetaDelta_boxed_4593_; uint8_t v_zetaHave_boxed_4594_; uint8_t v_beta_boxed_4595_; lean_object* v_res_4596_; 
v_zetaDelta_boxed_4593_ = lean_unbox(v_zetaDelta_4585_);
v_zetaHave_boxed_4594_ = lean_unbox(v_zetaHave_4586_);
v_beta_boxed_4595_ = lean_unbox(v_beta_4587_);
v_res_4596_ = l_Lean_Meta_zetaReduce(v_e_4584_, v_zetaDelta_boxed_4593_, v_zetaHave_boxed_4594_, v_beta_boxed_4595_, v_a_4588_, v_a_4589_, v_a_4590_, v_a_4591_);
lean_dec(v_a_4591_);
lean_dec_ref(v_a_4590_);
lean_dec(v_a_4589_);
lean_dec_ref(v_a_4588_);
return v_res_4596_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4(lean_object* v_upperBound_4597_, lean_object* v___x_4598_, lean_object* v_pre_4599_, lean_object* v_post_4600_, uint8_t v_usedLetOnly_4601_, uint8_t v_skipConstInApp_4602_, uint8_t v_skipInstances_4603_, lean_object* v___x_4604_, lean_object* v_inst_4605_, lean_object* v_R_4606_, lean_object* v_a_4607_, lean_object* v_b_4608_, lean_object* v_c_4609_, lean_object* v___y_4610_, lean_object* v___y_4611_, lean_object* v___y_4612_, lean_object* v___y_4613_, lean_object* v___y_4614_){
_start:
{
lean_object* v___x_4616_; 
v___x_4616_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg(v_upperBound_4597_, v___x_4598_, v_pre_4599_, v_post_4600_, v_usedLetOnly_4601_, v_skipConstInApp_4602_, v_skipInstances_4603_, v_a_4607_, v_b_4608_, v___y_4610_, v___y_4611_, v___y_4612_, v___y_4613_, v___y_4614_);
return v___x_4616_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___boxed(lean_object** _args){
lean_object* v_upperBound_4617_ = _args[0];
lean_object* v___x_4618_ = _args[1];
lean_object* v_pre_4619_ = _args[2];
lean_object* v_post_4620_ = _args[3];
lean_object* v_usedLetOnly_4621_ = _args[4];
lean_object* v_skipConstInApp_4622_ = _args[5];
lean_object* v_skipInstances_4623_ = _args[6];
lean_object* v___x_4624_ = _args[7];
lean_object* v_inst_4625_ = _args[8];
lean_object* v_R_4626_ = _args[9];
lean_object* v_a_4627_ = _args[10];
lean_object* v_b_4628_ = _args[11];
lean_object* v_c_4629_ = _args[12];
lean_object* v___y_4630_ = _args[13];
lean_object* v___y_4631_ = _args[14];
lean_object* v___y_4632_ = _args[15];
lean_object* v___y_4633_ = _args[16];
lean_object* v___y_4634_ = _args[17];
lean_object* v___y_4635_ = _args[18];
_start:
{
uint8_t v_usedLetOnly_boxed_4636_; uint8_t v_skipConstInApp_boxed_4637_; uint8_t v_skipInstances_boxed_4638_; lean_object* v_res_4639_; 
v_usedLetOnly_boxed_4636_ = lean_unbox(v_usedLetOnly_4621_);
v_skipConstInApp_boxed_4637_ = lean_unbox(v_skipConstInApp_4622_);
v_skipInstances_boxed_4638_ = lean_unbox(v_skipInstances_4623_);
v_res_4639_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4(v_upperBound_4617_, v___x_4618_, v_pre_4619_, v_post_4620_, v_usedLetOnly_boxed_4636_, v_skipConstInApp_boxed_4637_, v_skipInstances_boxed_4638_, v___x_4624_, v_inst_4625_, v_R_4626_, v_a_4627_, v_b_4628_, v_c_4629_, v___y_4630_, v___y_4631_, v___y_4632_, v___y_4633_, v___y_4634_);
lean_dec(v___y_4634_);
lean_dec_ref(v___y_4633_);
lean_dec(v___y_4632_);
lean_dec_ref(v___y_4631_);
lean_dec(v___y_4630_);
lean_dec(v___x_4624_);
lean_dec_ref(v___x_4618_);
lean_dec(v_upperBound_4617_);
return v_res_4639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6(lean_object* v_00_u03b1_4640_, lean_object* v_name_4641_, uint8_t v_bi_4642_, lean_object* v_type_4643_, lean_object* v_k_4644_, uint8_t v_kind_4645_, lean_object* v___y_4646_, lean_object* v___y_4647_, lean_object* v___y_4648_, lean_object* v___y_4649_, lean_object* v___y_4650_){
_start:
{
lean_object* v___x_4652_; 
v___x_4652_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_name_4641_, v_bi_4642_, v_type_4643_, v_k_4644_, v_kind_4645_, v___y_4646_, v___y_4647_, v___y_4648_, v___y_4649_, v___y_4650_);
return v___x_4652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___boxed(lean_object* v_00_u03b1_4653_, lean_object* v_name_4654_, lean_object* v_bi_4655_, lean_object* v_type_4656_, lean_object* v_k_4657_, lean_object* v_kind_4658_, lean_object* v___y_4659_, lean_object* v___y_4660_, lean_object* v___y_4661_, lean_object* v___y_4662_, lean_object* v___y_4663_, lean_object* v___y_4664_){
_start:
{
uint8_t v_bi_boxed_4665_; uint8_t v_kind_boxed_4666_; lean_object* v_res_4667_; 
v_bi_boxed_4665_ = lean_unbox(v_bi_4655_);
v_kind_boxed_4666_ = lean_unbox(v_kind_4658_);
v_res_4667_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6(v_00_u03b1_4653_, v_name_4654_, v_bi_boxed_4665_, v_type_4656_, v_k_4657_, v_kind_boxed_4666_, v___y_4659_, v___y_4660_, v___y_4661_, v___y_4662_, v___y_4663_);
lean_dec(v___y_4663_);
lean_dec_ref(v___y_4662_);
lean_dec(v___y_4661_);
lean_dec_ref(v___y_4660_);
lean_dec(v___y_4659_);
return v_res_4667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9(lean_object* v_00_u03b1_4668_, lean_object* v_name_4669_, lean_object* v_type_4670_, lean_object* v_val_4671_, lean_object* v_k_4672_, uint8_t v_nondep_4673_, uint8_t v_kind_4674_, lean_object* v___y_4675_, lean_object* v___y_4676_, lean_object* v___y_4677_, lean_object* v___y_4678_, lean_object* v___y_4679_){
_start:
{
lean_object* v___x_4681_; 
v___x_4681_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg(v_name_4669_, v_type_4670_, v_val_4671_, v_k_4672_, v_nondep_4673_, v_kind_4674_, v___y_4675_, v___y_4676_, v___y_4677_, v___y_4678_, v___y_4679_);
return v___x_4681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___boxed(lean_object* v_00_u03b1_4682_, lean_object* v_name_4683_, lean_object* v_type_4684_, lean_object* v_val_4685_, lean_object* v_k_4686_, lean_object* v_nondep_4687_, lean_object* v_kind_4688_, lean_object* v___y_4689_, lean_object* v___y_4690_, lean_object* v___y_4691_, lean_object* v___y_4692_, lean_object* v___y_4693_, lean_object* v___y_4694_){
_start:
{
uint8_t v_nondep_boxed_4695_; uint8_t v_kind_boxed_4696_; lean_object* v_res_4697_; 
v_nondep_boxed_4695_ = lean_unbox(v_nondep_4687_);
v_kind_boxed_4696_ = lean_unbox(v_kind_4688_);
v_res_4697_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9(v_00_u03b1_4682_, v_name_4683_, v_type_4684_, v_val_4685_, v_k_4686_, v_nondep_boxed_4695_, v_kind_boxed_4696_, v___y_4689_, v___y_4690_, v___y_4691_, v___y_4692_, v___y_4693_);
lean_dec(v___y_4693_);
lean_dec_ref(v___y_4692_);
lean_dec(v___y_4691_);
lean_dec_ref(v___y_4690_);
lean_dec(v___y_4689_);
return v_res_4697_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12(lean_object* v_00_u03b1_4698_, lean_object* v_ref_4699_, lean_object* v___y_4700_, lean_object* v___y_4701_, lean_object* v___y_4702_, lean_object* v___y_4703_){
_start:
{
lean_object* v___x_4705_; 
v___x_4705_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg(v_ref_4699_);
return v___x_4705_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___boxed(lean_object* v_00_u03b1_4706_, lean_object* v_ref_4707_, lean_object* v___y_4708_, lean_object* v___y_4709_, lean_object* v___y_4710_, lean_object* v___y_4711_, lean_object* v___y_4712_){
_start:
{
lean_object* v_res_4713_; 
v_res_4713_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12(v_00_u03b1_4706_, v_ref_4707_, v___y_4708_, v___y_4709_, v___y_4710_, v___y_4711_);
lean_dec(v___y_4711_);
lean_dec_ref(v___y_4710_);
lean_dec(v___y_4709_);
lean_dec_ref(v___y_4708_);
return v_res_4713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9(lean_object* v_00_u03b1_4714_, lean_object* v_x_4715_, lean_object* v___y_4716_, lean_object* v___y_4717_, lean_object* v___y_4718_, lean_object* v___y_4719_, lean_object* v___y_4720_){
_start:
{
lean_object* v___x_4722_; 
v___x_4722_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg(v_x_4715_, v___y_4716_, v___y_4717_, v___y_4718_, v___y_4719_, v___y_4720_);
return v___x_4722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___boxed(lean_object* v_00_u03b1_4723_, lean_object* v_x_4724_, lean_object* v___y_4725_, lean_object* v___y_4726_, lean_object* v___y_4727_, lean_object* v___y_4728_, lean_object* v___y_4729_, lean_object* v___y_4730_){
_start:
{
lean_object* v_res_4731_; 
v_res_4731_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9(v_00_u03b1_4723_, v_x_4724_, v___y_4725_, v___y_4726_, v___y_4727_, v___y_4728_, v___y_4729_);
lean_dec(v___y_4729_);
lean_dec_ref(v___y_4728_);
lean_dec(v___y_4727_);
lean_dec_ref(v___y_4726_);
lean_dec(v___y_4725_);
return v_res_4731_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0_spec__0(lean_object* v_a_4732_, lean_object* v_as_4733_, size_t v_i_4734_, size_t v_stop_4735_){
_start:
{
uint8_t v___x_4736_; 
v___x_4736_ = lean_usize_dec_eq(v_i_4734_, v_stop_4735_);
if (v___x_4736_ == 0)
{
lean_object* v___x_4737_; uint8_t v___x_4738_; 
v___x_4737_ = lean_array_uget_borrowed(v_as_4733_, v_i_4734_);
v___x_4738_ = l_Lean_instBEqFVarId_beq(v_a_4732_, v___x_4737_);
if (v___x_4738_ == 0)
{
size_t v___x_4739_; size_t v___x_4740_; 
v___x_4739_ = ((size_t)1ULL);
v___x_4740_ = lean_usize_add(v_i_4734_, v___x_4739_);
v_i_4734_ = v___x_4740_;
goto _start;
}
else
{
return v___x_4738_;
}
}
else
{
uint8_t v___x_4742_; 
v___x_4742_ = 0;
return v___x_4742_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0_spec__0___boxed(lean_object* v_a_4743_, lean_object* v_as_4744_, lean_object* v_i_4745_, lean_object* v_stop_4746_){
_start:
{
size_t v_i_boxed_4747_; size_t v_stop_boxed_4748_; uint8_t v_res_4749_; lean_object* v_r_4750_; 
v_i_boxed_4747_ = lean_unbox_usize(v_i_4745_);
lean_dec(v_i_4745_);
v_stop_boxed_4748_ = lean_unbox_usize(v_stop_4746_);
lean_dec(v_stop_4746_);
v_res_4749_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0_spec__0(v_a_4743_, v_as_4744_, v_i_boxed_4747_, v_stop_boxed_4748_);
lean_dec_ref(v_as_4744_);
lean_dec(v_a_4743_);
v_r_4750_ = lean_box(v_res_4749_);
return v_r_4750_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0(lean_object* v_as_4751_, lean_object* v_a_4752_){
_start:
{
lean_object* v___x_4753_; lean_object* v___x_4754_; uint8_t v___x_4755_; 
v___x_4753_ = lean_unsigned_to_nat(0u);
v___x_4754_ = lean_array_get_size(v_as_4751_);
v___x_4755_ = lean_nat_dec_lt(v___x_4753_, v___x_4754_);
if (v___x_4755_ == 0)
{
return v___x_4755_;
}
else
{
if (v___x_4755_ == 0)
{
return v___x_4755_;
}
else
{
size_t v___x_4756_; size_t v___x_4757_; uint8_t v___x_4758_; 
v___x_4756_ = ((size_t)0ULL);
v___x_4757_ = lean_usize_of_nat(v___x_4754_);
v___x_4758_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0_spec__0(v_a_4752_, v_as_4751_, v___x_4756_, v___x_4757_);
return v___x_4758_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0___boxed(lean_object* v_as_4759_, lean_object* v_a_4760_){
_start:
{
uint8_t v_res_4761_; lean_object* v_r_4762_; 
v_res_4761_ = l_Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0(v_as_4759_, v_a_4760_);
lean_dec(v_a_4760_);
lean_dec_ref(v_as_4759_);
v_r_4762_ = lean_box(v_res_4761_);
return v_r_4762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaFVars___lam__1(lean_object* v_fvars_4763_, lean_object* v_e_4764_, lean_object* v___y_4765_, lean_object* v___y_4766_, lean_object* v___y_4767_, lean_object* v___y_4768_){
_start:
{
lean_object* v___x_4773_; 
v___x_4773_ = l_Lean_Expr_getAppFn(v_e_4764_);
if (lean_obj_tag(v___x_4773_) == 1)
{
lean_object* v_fvarId_4774_; uint8_t v___x_4775_; 
v_fvarId_4774_ = lean_ctor_get(v___x_4773_, 0);
lean_inc(v_fvarId_4774_);
lean_dec_ref_known(v___x_4773_, 1);
v___x_4775_ = l_Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0(v_fvars_4763_, v_fvarId_4774_);
if (v___x_4775_ == 0)
{
lean_dec(v_fvarId_4774_);
lean_dec_ref(v_e_4764_);
goto v___jp_4770_;
}
else
{
uint8_t v___x_4776_; lean_object* v___x_4777_; 
v___x_4776_ = 0;
v___x_4777_ = l_Lean_FVarId_getValue_x3f___redArg(v_fvarId_4774_, v___x_4776_, v___y_4765_, v___y_4767_, v___y_4768_);
if (lean_obj_tag(v___x_4777_) == 0)
{
lean_object* v_a_4778_; 
v_a_4778_ = lean_ctor_get(v___x_4777_, 0);
lean_inc(v_a_4778_);
lean_dec_ref_known(v___x_4777_, 1);
if (lean_obj_tag(v_a_4778_) == 1)
{
lean_object* v_val_4779_; lean_object* v___x_4781_; uint8_t v_isShared_4782_; uint8_t v_isSharedCheck_4802_; 
v_val_4779_ = lean_ctor_get(v_a_4778_, 0);
v_isSharedCheck_4802_ = !lean_is_exclusive(v_a_4778_);
if (v_isSharedCheck_4802_ == 0)
{
v___x_4781_ = v_a_4778_;
v_isShared_4782_ = v_isSharedCheck_4802_;
goto v_resetjp_4780_;
}
else
{
lean_inc(v_val_4779_);
lean_dec(v_a_4778_);
v___x_4781_ = lean_box(0);
v_isShared_4782_ = v_isSharedCheck_4802_;
goto v_resetjp_4780_;
}
v_resetjp_4780_:
{
lean_object* v___x_4783_; lean_object* v_a_4784_; lean_object* v___x_4786_; uint8_t v_isShared_4787_; uint8_t v_isSharedCheck_4801_; 
v___x_4783_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(v_val_4779_, v___y_4766_);
v_a_4784_ = lean_ctor_get(v___x_4783_, 0);
v_isSharedCheck_4801_ = !lean_is_exclusive(v___x_4783_);
if (v_isSharedCheck_4801_ == 0)
{
v___x_4786_ = v___x_4783_;
v_isShared_4787_ = v_isSharedCheck_4801_;
goto v_resetjp_4785_;
}
else
{
lean_inc(v_a_4784_);
lean_dec(v___x_4783_);
v___x_4786_ = lean_box(0);
v_isShared_4787_ = v_isSharedCheck_4801_;
goto v_resetjp_4785_;
}
v_resetjp_4785_:
{
lean_object* v_dummy_4788_; lean_object* v_nargs_4789_; lean_object* v___x_4790_; lean_object* v___x_4791_; lean_object* v___x_4792_; lean_object* v___x_4793_; lean_object* v___x_4794_; lean_object* v___x_4796_; 
v_dummy_4788_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_4789_ = l_Lean_Expr_getAppNumArgs(v_e_4764_);
lean_inc(v_nargs_4789_);
v___x_4790_ = lean_mk_array(v_nargs_4789_, v_dummy_4788_);
v___x_4791_ = lean_unsigned_to_nat(1u);
v___x_4792_ = lean_nat_sub(v_nargs_4789_, v___x_4791_);
lean_dec(v_nargs_4789_);
v___x_4793_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_4764_, v___x_4790_, v___x_4792_);
v___x_4794_ = l_Lean_Expr_beta(v_a_4784_, v___x_4793_);
if (v_isShared_4782_ == 0)
{
lean_ctor_set(v___x_4781_, 0, v___x_4794_);
v___x_4796_ = v___x_4781_;
goto v_reusejp_4795_;
}
else
{
lean_object* v_reuseFailAlloc_4800_; 
v_reuseFailAlloc_4800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4800_, 0, v___x_4794_);
v___x_4796_ = v_reuseFailAlloc_4800_;
goto v_reusejp_4795_;
}
v_reusejp_4795_:
{
lean_object* v___x_4798_; 
if (v_isShared_4787_ == 0)
{
lean_ctor_set(v___x_4786_, 0, v___x_4796_);
v___x_4798_ = v___x_4786_;
goto v_reusejp_4797_;
}
else
{
lean_object* v_reuseFailAlloc_4799_; 
v_reuseFailAlloc_4799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4799_, 0, v___x_4796_);
v___x_4798_ = v_reuseFailAlloc_4799_;
goto v_reusejp_4797_;
}
v_reusejp_4797_:
{
return v___x_4798_;
}
}
}
}
}
else
{
lean_dec(v_a_4778_);
lean_dec_ref(v_e_4764_);
goto v___jp_4770_;
}
}
else
{
lean_object* v_a_4803_; lean_object* v___x_4805_; uint8_t v_isShared_4806_; uint8_t v_isSharedCheck_4810_; 
lean_dec_ref(v_e_4764_);
v_a_4803_ = lean_ctor_get(v___x_4777_, 0);
v_isSharedCheck_4810_ = !lean_is_exclusive(v___x_4777_);
if (v_isSharedCheck_4810_ == 0)
{
v___x_4805_ = v___x_4777_;
v_isShared_4806_ = v_isSharedCheck_4810_;
goto v_resetjp_4804_;
}
else
{
lean_inc(v_a_4803_);
lean_dec(v___x_4777_);
v___x_4805_ = lean_box(0);
v_isShared_4806_ = v_isSharedCheck_4810_;
goto v_resetjp_4804_;
}
v_resetjp_4804_:
{
lean_object* v___x_4808_; 
if (v_isShared_4806_ == 0)
{
v___x_4808_ = v___x_4805_;
goto v_reusejp_4807_;
}
else
{
lean_object* v_reuseFailAlloc_4809_; 
v_reuseFailAlloc_4809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4809_, 0, v_a_4803_);
v___x_4808_ = v_reuseFailAlloc_4809_;
goto v_reusejp_4807_;
}
v_reusejp_4807_:
{
return v___x_4808_;
}
}
}
}
}
else
{
lean_object* v___x_4811_; lean_object* v___x_4812_; 
lean_dec_ref(v___x_4773_);
lean_dec_ref(v_e_4764_);
v___x_4811_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_4812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4812_, 0, v___x_4811_);
return v___x_4812_;
}
v___jp_4770_:
{
lean_object* v___x_4771_; lean_object* v___x_4772_; 
v___x_4771_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_4772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4772_, 0, v___x_4771_);
return v___x_4772_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaFVars___lam__1___boxed(lean_object* v_fvars_4813_, lean_object* v_e_4814_, lean_object* v___y_4815_, lean_object* v___y_4816_, lean_object* v___y_4817_, lean_object* v___y_4818_, lean_object* v___y_4819_){
_start:
{
lean_object* v_res_4820_; 
v_res_4820_ = l_Lean_Meta_zetaDeltaFVars___lam__1(v_fvars_4813_, v_e_4814_, v___y_4815_, v___y_4816_, v___y_4817_, v___y_4818_);
lean_dec(v___y_4818_);
lean_dec_ref(v___y_4817_);
lean_dec(v___y_4816_);
lean_dec_ref(v___y_4815_);
lean_dec_ref(v_fvars_4813_);
return v_res_4820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaFVars(lean_object* v_e_4821_, lean_object* v_fvars_4822_, lean_object* v_a_4823_, lean_object* v_a_4824_, lean_object* v_a_4825_, lean_object* v_a_4826_){
_start:
{
lean_object* v___f_4828_; lean_object* v_pre_4829_; uint8_t v___x_4830_; lean_object* v___x_4831_; 
v___f_4828_ = ((lean_object*)(l_Lean_Meta_zetaReduce___closed__0));
v_pre_4829_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaDeltaFVars___lam__1___boxed), 7, 1);
lean_closure_set(v_pre_4829_, 0, v_fvars_4822_);
v___x_4830_ = 0;
v___x_4831_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(v_e_4821_, v_pre_4829_, v___f_4828_, v___x_4830_, v___x_4830_, v_a_4823_, v_a_4824_, v_a_4825_, v_a_4826_);
return v___x_4831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaFVars___boxed(lean_object* v_e_4832_, lean_object* v_fvars_4833_, lean_object* v_a_4834_, lean_object* v_a_4835_, lean_object* v_a_4836_, lean_object* v_a_4837_, lean_object* v_a_4838_){
_start:
{
lean_object* v_res_4839_; 
v_res_4839_ = l_Lean_Meta_zetaDeltaFVars(v_e_4832_, v_fvars_4833_, v_a_4834_, v_a_4835_, v_a_4836_, v_a_4837_);
lean_dec(v_a_4837_);
lean_dec_ref(v_a_4836_);
lean_dec(v_a_4835_);
lean_dec_ref(v_a_4834_);
return v_res_4839_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_4840_; 
v___x_4840_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4840_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_4841_; lean_object* v___x_4842_; 
v___x_4841_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__0, &l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__0);
v___x_4842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4842_, 0, v___x_4841_);
return v___x_4842_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_4843_; lean_object* v___x_4844_; 
v___x_4843_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__1, &l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__1);
v___x_4844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4844_, 0, v___x_4843_);
lean_ctor_set(v___x_4844_, 1, v___x_4843_);
return v___x_4844_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(lean_object* v_env_4845_, lean_object* v___y_4846_){
_start:
{
lean_object* v___x_4848_; lean_object* v_nextMacroScope_4849_; lean_object* v_ngen_4850_; lean_object* v_auxDeclNGen_4851_; lean_object* v_traceState_4852_; lean_object* v_messages_4853_; lean_object* v_infoState_4854_; lean_object* v_snapshotTasks_4855_; lean_object* v___x_4857_; uint8_t v_isShared_4858_; uint8_t v_isSharedCheck_4866_; 
v___x_4848_ = lean_st_ref_take(v___y_4846_);
v_nextMacroScope_4849_ = lean_ctor_get(v___x_4848_, 1);
v_ngen_4850_ = lean_ctor_get(v___x_4848_, 2);
v_auxDeclNGen_4851_ = lean_ctor_get(v___x_4848_, 3);
v_traceState_4852_ = lean_ctor_get(v___x_4848_, 4);
v_messages_4853_ = lean_ctor_get(v___x_4848_, 6);
v_infoState_4854_ = lean_ctor_get(v___x_4848_, 7);
v_snapshotTasks_4855_ = lean_ctor_get(v___x_4848_, 8);
v_isSharedCheck_4866_ = !lean_is_exclusive(v___x_4848_);
if (v_isSharedCheck_4866_ == 0)
{
lean_object* v_unused_4867_; lean_object* v_unused_4868_; 
v_unused_4867_ = lean_ctor_get(v___x_4848_, 5);
lean_dec(v_unused_4867_);
v_unused_4868_ = lean_ctor_get(v___x_4848_, 0);
lean_dec(v_unused_4868_);
v___x_4857_ = v___x_4848_;
v_isShared_4858_ = v_isSharedCheck_4866_;
goto v_resetjp_4856_;
}
else
{
lean_inc(v_snapshotTasks_4855_);
lean_inc(v_infoState_4854_);
lean_inc(v_messages_4853_);
lean_inc(v_traceState_4852_);
lean_inc(v_auxDeclNGen_4851_);
lean_inc(v_ngen_4850_);
lean_inc(v_nextMacroScope_4849_);
lean_dec(v___x_4848_);
v___x_4857_ = lean_box(0);
v_isShared_4858_ = v_isSharedCheck_4866_;
goto v_resetjp_4856_;
}
v_resetjp_4856_:
{
lean_object* v___x_4859_; lean_object* v___x_4861_; 
v___x_4859_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2, &l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2);
if (v_isShared_4858_ == 0)
{
lean_ctor_set(v___x_4857_, 5, v___x_4859_);
lean_ctor_set(v___x_4857_, 0, v_env_4845_);
v___x_4861_ = v___x_4857_;
goto v_reusejp_4860_;
}
else
{
lean_object* v_reuseFailAlloc_4865_; 
v_reuseFailAlloc_4865_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4865_, 0, v_env_4845_);
lean_ctor_set(v_reuseFailAlloc_4865_, 1, v_nextMacroScope_4849_);
lean_ctor_set(v_reuseFailAlloc_4865_, 2, v_ngen_4850_);
lean_ctor_set(v_reuseFailAlloc_4865_, 3, v_auxDeclNGen_4851_);
lean_ctor_set(v_reuseFailAlloc_4865_, 4, v_traceState_4852_);
lean_ctor_set(v_reuseFailAlloc_4865_, 5, v___x_4859_);
lean_ctor_set(v_reuseFailAlloc_4865_, 6, v_messages_4853_);
lean_ctor_set(v_reuseFailAlloc_4865_, 7, v_infoState_4854_);
lean_ctor_set(v_reuseFailAlloc_4865_, 8, v_snapshotTasks_4855_);
v___x_4861_ = v_reuseFailAlloc_4865_;
goto v_reusejp_4860_;
}
v_reusejp_4860_:
{
lean_object* v___x_4862_; lean_object* v___x_4863_; lean_object* v___x_4864_; 
v___x_4862_ = lean_st_ref_put(v___y_4846_, v___x_4861_);
v___x_4863_ = lean_box(0);
v___x_4864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4864_, 0, v___x_4863_);
return v___x_4864_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___boxed(lean_object* v_env_4869_, lean_object* v___y_4870_, lean_object* v___y_4871_){
_start:
{
lean_object* v_res_4872_; 
v_res_4872_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_4869_, v___y_4870_);
lean_dec(v___y_4870_);
return v_res_4872_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0(lean_object* v_env_4873_, lean_object* v___y_4874_, lean_object* v___y_4875_){
_start:
{
lean_object* v___x_4877_; 
v___x_4877_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_4873_, v___y_4875_);
return v___x_4877_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___boxed(lean_object* v_env_4878_, lean_object* v___y_4879_, lean_object* v___y_4880_, lean_object* v___y_4881_){
_start:
{
lean_object* v_res_4882_; 
v_res_4882_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0(v_env_4878_, v___y_4879_, v___y_4880_);
lean_dec(v___y_4880_);
lean_dec_ref(v___y_4879_);
return v_res_4882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___lam__1(lean_object* v_env_4883_, lean_object* v___x_4884_, uint8_t v___x_4885_, lean_object* v_e_4886_, lean_object* v___y_4887_, lean_object* v___y_4888_){
_start:
{
if (lean_obj_tag(v_e_4886_) == 4)
{
lean_object* v_declName_4890_; lean_object* v_us_4891_; uint8_t v___x_4892_; uint8_t v___x_4893_; 
v_declName_4890_ = lean_ctor_get(v_e_4886_, 0);
v_us_4891_ = lean_ctor_get(v_e_4886_, 1);
v___x_4892_ = 1;
lean_inc(v_declName_4890_);
v___x_4893_ = l_Lean_Environment_contains(v_env_4883_, v_declName_4890_, v___x_4892_);
if (v___x_4893_ == 0)
{
lean_object* v___x_4894_; 
lean_inc(v_declName_4890_);
v___x_4894_ = l_Lean_Environment_find_x3f(v___x_4884_, v_declName_4890_, v___x_4885_);
if (lean_obj_tag(v___x_4894_) == 1)
{
lean_object* v_val_4895_; lean_object* v___x_4897_; uint8_t v_isShared_4898_; uint8_t v_isSharedCheck_4924_; 
v_val_4895_ = lean_ctor_get(v___x_4894_, 0);
v_isSharedCheck_4924_ = !lean_is_exclusive(v___x_4894_);
if (v_isSharedCheck_4924_ == 0)
{
v___x_4897_ = v___x_4894_;
v_isShared_4898_ = v_isSharedCheck_4924_;
goto v_resetjp_4896_;
}
else
{
lean_inc(v_val_4895_);
lean_dec(v___x_4894_);
v___x_4897_ = lean_box(0);
v_isShared_4898_ = v_isSharedCheck_4924_;
goto v_resetjp_4896_;
}
v_resetjp_4896_:
{
uint8_t v___x_4899_; 
v___x_4899_ = l_Lean_ConstantInfo_hasValue(v_val_4895_, v___x_4892_);
if (v___x_4899_ == 0)
{
lean_object* v___x_4901_; 
lean_dec(v_val_4895_);
if (v_isShared_4898_ == 0)
{
lean_ctor_set_tag(v___x_4897_, 0);
lean_ctor_set(v___x_4897_, 0, v_e_4886_);
v___x_4901_ = v___x_4897_;
goto v_reusejp_4900_;
}
else
{
lean_object* v_reuseFailAlloc_4903_; 
v_reuseFailAlloc_4903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4903_, 0, v_e_4886_);
v___x_4901_ = v_reuseFailAlloc_4903_;
goto v_reusejp_4900_;
}
v_reusejp_4900_:
{
lean_object* v___x_4902_; 
v___x_4902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4902_, 0, v___x_4901_);
return v___x_4902_;
}
}
else
{
lean_object* v___x_4904_; 
lean_inc(v_us_4891_);
lean_dec_ref_known(v_e_4886_, 2);
v___x_4904_ = l_Lean_Core_instantiateValueLevelParams(v_val_4895_, v_us_4891_, v___x_4892_, v___y_4887_, v___y_4888_);
lean_dec(v_val_4895_);
if (lean_obj_tag(v___x_4904_) == 0)
{
lean_object* v_a_4905_; lean_object* v___x_4907_; uint8_t v_isShared_4908_; uint8_t v_isSharedCheck_4915_; 
v_a_4905_ = lean_ctor_get(v___x_4904_, 0);
v_isSharedCheck_4915_ = !lean_is_exclusive(v___x_4904_);
if (v_isSharedCheck_4915_ == 0)
{
v___x_4907_ = v___x_4904_;
v_isShared_4908_ = v_isSharedCheck_4915_;
goto v_resetjp_4906_;
}
else
{
lean_inc(v_a_4905_);
lean_dec(v___x_4904_);
v___x_4907_ = lean_box(0);
v_isShared_4908_ = v_isSharedCheck_4915_;
goto v_resetjp_4906_;
}
v_resetjp_4906_:
{
lean_object* v___x_4910_; 
if (v_isShared_4898_ == 0)
{
lean_ctor_set(v___x_4897_, 0, v_a_4905_);
v___x_4910_ = v___x_4897_;
goto v_reusejp_4909_;
}
else
{
lean_object* v_reuseFailAlloc_4914_; 
v_reuseFailAlloc_4914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4914_, 0, v_a_4905_);
v___x_4910_ = v_reuseFailAlloc_4914_;
goto v_reusejp_4909_;
}
v_reusejp_4909_:
{
lean_object* v___x_4912_; 
if (v_isShared_4908_ == 0)
{
lean_ctor_set(v___x_4907_, 0, v___x_4910_);
v___x_4912_ = v___x_4907_;
goto v_reusejp_4911_;
}
else
{
lean_object* v_reuseFailAlloc_4913_; 
v_reuseFailAlloc_4913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4913_, 0, v___x_4910_);
v___x_4912_ = v_reuseFailAlloc_4913_;
goto v_reusejp_4911_;
}
v_reusejp_4911_:
{
return v___x_4912_;
}
}
}
}
else
{
lean_object* v_a_4916_; lean_object* v___x_4918_; uint8_t v_isShared_4919_; uint8_t v_isSharedCheck_4923_; 
lean_del_object(v___x_4897_);
v_a_4916_ = lean_ctor_get(v___x_4904_, 0);
v_isSharedCheck_4923_ = !lean_is_exclusive(v___x_4904_);
if (v_isSharedCheck_4923_ == 0)
{
v___x_4918_ = v___x_4904_;
v_isShared_4919_ = v_isSharedCheck_4923_;
goto v_resetjp_4917_;
}
else
{
lean_inc(v_a_4916_);
lean_dec(v___x_4904_);
v___x_4918_ = lean_box(0);
v_isShared_4919_ = v_isSharedCheck_4923_;
goto v_resetjp_4917_;
}
v_resetjp_4917_:
{
lean_object* v___x_4921_; 
if (v_isShared_4919_ == 0)
{
v___x_4921_ = v___x_4918_;
goto v_reusejp_4920_;
}
else
{
lean_object* v_reuseFailAlloc_4922_; 
v_reuseFailAlloc_4922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4922_, 0, v_a_4916_);
v___x_4921_ = v_reuseFailAlloc_4922_;
goto v_reusejp_4920_;
}
v_reusejp_4920_:
{
return v___x_4921_;
}
}
}
}
}
}
else
{
lean_object* v___x_4925_; lean_object* v___x_4926_; 
lean_dec(v___x_4894_);
v___x_4925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4925_, 0, v_e_4886_);
v___x_4926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4926_, 0, v___x_4925_);
return v___x_4926_;
}
}
else
{
lean_object* v___x_4927_; lean_object* v___x_4928_; 
lean_dec_ref(v___x_4884_);
v___x_4927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4927_, 0, v_e_4886_);
v___x_4928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4928_, 0, v___x_4927_);
return v___x_4928_;
}
}
else
{
lean_object* v___x_4929_; lean_object* v___x_4930_; 
lean_dec_ref(v_e_4886_);
lean_dec_ref(v___x_4884_);
lean_dec_ref(v_env_4883_);
v___x_4929_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_4930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4930_, 0, v___x_4929_);
return v___x_4930_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___lam__1___boxed(lean_object* v_env_4931_, lean_object* v___x_4932_, lean_object* v___x_4933_, lean_object* v_e_4934_, lean_object* v___y_4935_, lean_object* v___y_4936_, lean_object* v___y_4937_){
_start:
{
uint8_t v___x_1992__boxed_4938_; lean_object* v_res_4939_; 
v___x_1992__boxed_4938_ = lean_unbox(v___x_4933_);
v_res_4939_ = l_Lean_Meta_unfoldDeclsFrom___lam__1(v_env_4931_, v___x_4932_, v___x_1992__boxed_4938_, v_e_4934_, v___y_4935_, v___y_4936_);
lean_dec(v___y_4936_);
lean_dec_ref(v___y_4935_);
return v_res_4939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___lam__0(lean_object* v_biggerEnv_4940_, lean_object* v_e_4941_, lean_object* v___f_4942_, lean_object* v___y_4943_, lean_object* v___y_4944_){
_start:
{
lean_object* v___x_4946_; uint8_t v___x_4947_; lean_object* v___x_4948_; lean_object* v___x_4949_; lean_object* v_env_4950_; lean_object* v___x_4951_; lean_object* v___f_4952_; lean_object* v___x_4953_; 
v___x_4946_ = lean_st_ref_get(v___y_4944_);
v___x_4947_ = 0;
v___x_4948_ = l_Lean_Environment_setExporting(v_biggerEnv_4940_, v___x_4947_);
lean_inc_ref(v___x_4948_);
v___x_4949_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v___x_4948_, v___y_4944_);
lean_dec_ref(v___x_4949_);
v_env_4950_ = lean_ctor_get(v___x_4946_, 0);
lean_inc_ref(v_env_4950_);
lean_dec(v___x_4946_);
v___x_4951_ = lean_box(v___x_4947_);
v___f_4952_ = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDeclsFrom___lam__1___boxed), 7, 3);
lean_closure_set(v___f_4952_, 0, v_env_4950_);
lean_closure_set(v___f_4952_, 1, v___x_4948_);
lean_closure_set(v___f_4952_, 2, v___x_4951_);
v___x_4953_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_4941_, v___f_4952_, v___f_4942_, v___y_4943_, v___y_4944_);
return v___x_4953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___lam__0___boxed(lean_object* v_biggerEnv_4954_, lean_object* v_e_4955_, lean_object* v___f_4956_, lean_object* v___y_4957_, lean_object* v___y_4958_, lean_object* v___y_4959_){
_start:
{
lean_object* v_res_4960_; 
v_res_4960_ = l_Lean_Meta_unfoldDeclsFrom___lam__0(v_biggerEnv_4954_, v_e_4955_, v___f_4956_, v___y_4957_, v___y_4958_);
lean_dec(v___y_4958_);
lean_dec_ref(v___y_4957_);
return v_res_4960_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg(lean_object* v_env_4961_, lean_object* v_x_4962_, lean_object* v___y_4963_, lean_object* v___y_4964_){
_start:
{
lean_object* v___x_4966_; lean_object* v_env_4967_; lean_object* v_a_4969_; lean_object* v___x_4979_; lean_object* v___x_4980_; 
v___x_4966_ = lean_st_ref_get(v___y_4964_);
v_env_4967_ = lean_ctor_get(v___x_4966_, 0);
lean_inc_ref(v_env_4967_);
lean_dec(v___x_4966_);
v___x_4979_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_4961_, v___y_4964_);
lean_dec_ref(v___x_4979_);
lean_inc(v___y_4964_);
lean_inc_ref(v___y_4963_);
v___x_4980_ = lean_apply_3(v_x_4962_, v___y_4963_, v___y_4964_, lean_box(0));
if (lean_obj_tag(v___x_4980_) == 0)
{
lean_object* v_a_4981_; lean_object* v___x_4982_; lean_object* v___x_4984_; uint8_t v_isShared_4985_; uint8_t v_isSharedCheck_4989_; 
v_a_4981_ = lean_ctor_get(v___x_4980_, 0);
lean_inc(v_a_4981_);
lean_dec_ref_known(v___x_4980_, 1);
v___x_4982_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_4967_, v___y_4964_);
v_isSharedCheck_4989_ = !lean_is_exclusive(v___x_4982_);
if (v_isSharedCheck_4989_ == 0)
{
lean_object* v_unused_4990_; 
v_unused_4990_ = lean_ctor_get(v___x_4982_, 0);
lean_dec(v_unused_4990_);
v___x_4984_ = v___x_4982_;
v_isShared_4985_ = v_isSharedCheck_4989_;
goto v_resetjp_4983_;
}
else
{
lean_dec(v___x_4982_);
v___x_4984_ = lean_box(0);
v_isShared_4985_ = v_isSharedCheck_4989_;
goto v_resetjp_4983_;
}
v_resetjp_4983_:
{
lean_object* v___x_4987_; 
if (v_isShared_4985_ == 0)
{
lean_ctor_set(v___x_4984_, 0, v_a_4981_);
v___x_4987_ = v___x_4984_;
goto v_reusejp_4986_;
}
else
{
lean_object* v_reuseFailAlloc_4988_; 
v_reuseFailAlloc_4988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4988_, 0, v_a_4981_);
v___x_4987_ = v_reuseFailAlloc_4988_;
goto v_reusejp_4986_;
}
v_reusejp_4986_:
{
return v___x_4987_;
}
}
}
else
{
lean_object* v_a_4991_; 
v_a_4991_ = lean_ctor_get(v___x_4980_, 0);
lean_inc(v_a_4991_);
lean_dec_ref_known(v___x_4980_, 1);
v_a_4969_ = v_a_4991_;
goto v___jp_4968_;
}
v___jp_4968_:
{
lean_object* v___x_4970_; lean_object* v___x_4972_; uint8_t v_isShared_4973_; uint8_t v_isSharedCheck_4977_; 
v___x_4970_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_4967_, v___y_4964_);
v_isSharedCheck_4977_ = !lean_is_exclusive(v___x_4970_);
if (v_isSharedCheck_4977_ == 0)
{
lean_object* v_unused_4978_; 
v_unused_4978_ = lean_ctor_get(v___x_4970_, 0);
lean_dec(v_unused_4978_);
v___x_4972_ = v___x_4970_;
v_isShared_4973_ = v_isSharedCheck_4977_;
goto v_resetjp_4971_;
}
else
{
lean_dec(v___x_4970_);
v___x_4972_ = lean_box(0);
v_isShared_4973_ = v_isSharedCheck_4977_;
goto v_resetjp_4971_;
}
v_resetjp_4971_:
{
lean_object* v___x_4975_; 
if (v_isShared_4973_ == 0)
{
lean_ctor_set_tag(v___x_4972_, 1);
lean_ctor_set(v___x_4972_, 0, v_a_4969_);
v___x_4975_ = v___x_4972_;
goto v_reusejp_4974_;
}
else
{
lean_object* v_reuseFailAlloc_4976_; 
v_reuseFailAlloc_4976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4976_, 0, v_a_4969_);
v___x_4975_ = v_reuseFailAlloc_4976_;
goto v_reusejp_4974_;
}
v_reusejp_4974_:
{
return v___x_4975_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg___boxed(lean_object* v_env_4992_, lean_object* v_x_4993_, lean_object* v___y_4994_, lean_object* v___y_4995_, lean_object* v___y_4996_){
_start:
{
lean_object* v_res_4997_; 
v_res_4997_ = l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg(v_env_4992_, v_x_4993_, v___y_4994_, v___y_4995_);
lean_dec(v___y_4995_);
lean_dec_ref(v___y_4994_);
return v_res_4997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom(lean_object* v_biggerEnv_4998_, lean_object* v_e_4999_, lean_object* v_a_5000_, lean_object* v_a_5001_){
_start:
{
lean_object* v___x_5003_; lean_object* v_env_5004_; lean_object* v___f_5005_; lean_object* v___f_5006_; lean_object* v___x_5007_; lean_object* v___x_5008_; 
v___x_5003_ = lean_st_ref_get(v_a_5001_);
v_env_5004_ = lean_ctor_get(v___x_5003_, 0);
lean_inc_ref(v_env_5004_);
lean_dec(v___x_5003_);
v___f_5005_ = ((lean_object*)(l_Lean_Core_betaReduce___closed__1));
v___f_5006_ = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDeclsFrom___lam__0___boxed), 6, 3);
lean_closure_set(v___f_5006_, 0, v_biggerEnv_4998_);
lean_closure_set(v___f_5006_, 1, v_e_4999_);
lean_closure_set(v___f_5006_, 2, v___f_5005_);
v___x_5007_ = l_Lean_Environment_unlockAsync(v_env_5004_);
v___x_5008_ = l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg(v___x_5007_, v___f_5006_, v_a_5000_, v_a_5001_);
return v___x_5008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___boxed(lean_object* v_biggerEnv_5009_, lean_object* v_e_5010_, lean_object* v_a_5011_, lean_object* v_a_5012_, lean_object* v_a_5013_){
_start:
{
lean_object* v_res_5014_; 
v_res_5014_ = l_Lean_Meta_unfoldDeclsFrom(v_biggerEnv_5009_, v_e_5010_, v_a_5011_, v_a_5012_);
lean_dec(v_a_5012_);
lean_dec_ref(v_a_5011_);
return v_res_5014_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1(lean_object* v_00_u03b1_5015_, lean_object* v_env_5016_, lean_object* v_x_5017_, lean_object* v___y_5018_, lean_object* v___y_5019_){
_start:
{
lean_object* v___x_5021_; 
v___x_5021_ = l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg(v_env_5016_, v_x_5017_, v___y_5018_, v___y_5019_);
return v___x_5021_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___boxed(lean_object* v_00_u03b1_5022_, lean_object* v_env_5023_, lean_object* v_x_5024_, lean_object* v___y_5025_, lean_object* v___y_5026_, lean_object* v___y_5027_){
_start:
{
lean_object* v_res_5028_; 
v_res_5028_ = l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1(v_00_u03b1_5022_, v_env_5023_, v_x_5024_, v___y_5025_, v___y_5026_);
lean_dec(v___y_5026_);
lean_dec_ref(v___y_5025_);
return v_res_5028_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0(lean_object* v_af_5029_, lean_object* v_axs_5030_, lean_object* v_numSectionVars_5031_, lean_object* v_as_5032_, size_t v_i_5033_, size_t v_stop_5034_){
_start:
{
uint8_t v___x_5035_; 
v___x_5035_ = lean_usize_dec_eq(v_i_5033_, v_stop_5034_);
if (v___x_5035_ == 0)
{
uint8_t v___x_5036_; uint8_t v___y_5038_; lean_object* v___x_5042_; lean_object* v___x_5043_; uint8_t v___x_5044_; 
v___x_5036_ = 1;
v___x_5042_ = lean_array_uget_borrowed(v_as_5032_, v_i_5033_);
v___x_5043_ = l_Lean_Expr_constName_x21(v_af_5029_);
v___x_5044_ = lean_name_eq(v___x_5043_, v___x_5042_);
lean_dec(v___x_5043_);
if (v___x_5044_ == 0)
{
v___y_5038_ = v___x_5044_;
goto v___jp_5037_;
}
else
{
lean_object* v___x_5045_; uint8_t v___x_5046_; 
v___x_5045_ = lean_array_get_size(v_axs_5030_);
v___x_5046_ = lean_nat_dec_le(v___x_5045_, v_numSectionVars_5031_);
v___y_5038_ = v___x_5046_;
goto v___jp_5037_;
}
v___jp_5037_:
{
if (v___y_5038_ == 0)
{
size_t v___x_5039_; size_t v___x_5040_; 
v___x_5039_ = ((size_t)1ULL);
v___x_5040_ = lean_usize_add(v_i_5033_, v___x_5039_);
v_i_5033_ = v___x_5040_;
goto _start;
}
else
{
return v___x_5036_;
}
}
}
else
{
uint8_t v___x_5047_; 
v___x_5047_ = 0;
return v___x_5047_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0___boxed(lean_object* v_af_5048_, lean_object* v_axs_5049_, lean_object* v_numSectionVars_5050_, lean_object* v_as_5051_, lean_object* v_i_5052_, lean_object* v_stop_5053_){
_start:
{
size_t v_i_boxed_5054_; size_t v_stop_boxed_5055_; uint8_t v_res_5056_; lean_object* v_r_5057_; 
v_i_boxed_5054_ = lean_unbox_usize(v_i_5052_);
lean_dec(v_i_5052_);
v_stop_boxed_5055_ = lean_unbox_usize(v_stop_5053_);
lean_dec(v_stop_5053_);
v_res_5056_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0(v_af_5048_, v_axs_5049_, v_numSectionVars_5050_, v_as_5051_, v_i_boxed_5054_, v_stop_boxed_5055_);
lean_dec_ref(v_as_5051_);
lean_dec(v_numSectionVars_5050_);
lean_dec_ref(v_axs_5049_);
lean_dec_ref(v_af_5048_);
v_r_5057_ = lean_box(v_res_5056_);
return v_r_5057_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1_spec__1(lean_object* v_fnNames_5058_, lean_object* v_numSectionVars_5059_, lean_object* v_x_5060_, lean_object* v_x_5061_, lean_object* v_x_5062_){
_start:
{
if (lean_obj_tag(v_x_5060_) == 5)
{
lean_object* v_fn_5063_; lean_object* v_arg_5064_; lean_object* v___x_5065_; lean_object* v___x_5066_; lean_object* v___x_5067_; 
v_fn_5063_ = lean_ctor_get(v_x_5060_, 0);
lean_inc_ref(v_fn_5063_);
v_arg_5064_ = lean_ctor_get(v_x_5060_, 1);
lean_inc_ref(v_arg_5064_);
lean_dec_ref_known(v_x_5060_, 2);
v___x_5065_ = lean_array_set(v_x_5061_, v_x_5062_, v_arg_5064_);
v___x_5066_ = lean_unsigned_to_nat(1u);
v___x_5067_ = lean_nat_sub(v_x_5062_, v___x_5066_);
lean_dec(v_x_5062_);
v_x_5060_ = v_fn_5063_;
v_x_5061_ = v___x_5065_;
v_x_5062_ = v___x_5067_;
goto _start;
}
else
{
uint8_t v___x_5069_; 
lean_dec(v_x_5062_);
v___x_5069_ = l_Lean_Expr_isConst(v_x_5060_);
if (v___x_5069_ == 0)
{
lean_dec_ref(v_x_5061_);
lean_dec_ref(v_x_5060_);
return v___x_5069_;
}
else
{
lean_object* v___x_5070_; lean_object* v___x_5071_; uint8_t v___x_5072_; 
v___x_5070_ = lean_unsigned_to_nat(0u);
v___x_5071_ = lean_array_get_size(v_fnNames_5058_);
v___x_5072_ = lean_nat_dec_lt(v___x_5070_, v___x_5071_);
if (v___x_5072_ == 0)
{
lean_dec_ref(v_x_5061_);
lean_dec_ref(v_x_5060_);
return v___x_5072_;
}
else
{
if (v___x_5072_ == 0)
{
lean_dec_ref(v_x_5061_);
lean_dec_ref(v_x_5060_);
return v___x_5072_;
}
else
{
size_t v___x_5073_; size_t v___x_5074_; uint8_t v___x_5075_; 
v___x_5073_ = ((size_t)0ULL);
v___x_5074_ = lean_usize_of_nat(v___x_5071_);
v___x_5075_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0(v_x_5060_, v_x_5061_, v_numSectionVars_5059_, v_fnNames_5058_, v___x_5073_, v___x_5074_);
lean_dec_ref(v_x_5061_);
lean_dec_ref(v_x_5060_);
return v___x_5075_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1_spec__1___boxed(lean_object* v_fnNames_5076_, lean_object* v_numSectionVars_5077_, lean_object* v_x_5078_, lean_object* v_x_5079_, lean_object* v_x_5080_){
_start:
{
uint8_t v_res_5081_; lean_object* v_r_5082_; 
v_res_5081_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1_spec__1(v_fnNames_5076_, v_numSectionVars_5077_, v_x_5078_, v_x_5079_, v_x_5080_);
lean_dec(v_numSectionVars_5077_);
lean_dec_ref(v_fnNames_5076_);
v_r_5082_ = lean_box(v_res_5081_);
return v_r_5082_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1(lean_object* v_numSectionVars_5083_, lean_object* v_fnNames_5084_, lean_object* v_x_5085_, lean_object* v_x_5086_, lean_object* v_x_5087_){
_start:
{
if (lean_obj_tag(v_x_5085_) == 5)
{
lean_object* v_fn_5088_; lean_object* v_arg_5089_; lean_object* v___x_5090_; lean_object* v___x_5091_; lean_object* v___x_5092_; uint8_t v___x_5093_; 
v_fn_5088_ = lean_ctor_get(v_x_5085_, 0);
lean_inc_ref(v_fn_5088_);
v_arg_5089_ = lean_ctor_get(v_x_5085_, 1);
lean_inc_ref(v_arg_5089_);
lean_dec_ref_known(v_x_5085_, 2);
v___x_5090_ = lean_array_set(v_x_5086_, v_x_5087_, v_arg_5089_);
v___x_5091_ = lean_unsigned_to_nat(1u);
v___x_5092_ = lean_nat_sub(v_x_5087_, v___x_5091_);
v___x_5093_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1_spec__1(v_fnNames_5084_, v_numSectionVars_5083_, v_fn_5088_, v___x_5090_, v___x_5092_);
return v___x_5093_;
}
else
{
uint8_t v___x_5094_; 
v___x_5094_ = l_Lean_Expr_isConst(v_x_5085_);
if (v___x_5094_ == 0)
{
lean_dec_ref(v_x_5086_);
lean_dec_ref(v_x_5085_);
return v___x_5094_;
}
else
{
lean_object* v___x_5095_; lean_object* v___x_5096_; uint8_t v___x_5097_; 
v___x_5095_ = lean_unsigned_to_nat(0u);
v___x_5096_ = lean_array_get_size(v_fnNames_5084_);
v___x_5097_ = lean_nat_dec_lt(v___x_5095_, v___x_5096_);
if (v___x_5097_ == 0)
{
lean_dec_ref(v_x_5086_);
lean_dec_ref(v_x_5085_);
return v___x_5097_;
}
else
{
if (v___x_5097_ == 0)
{
lean_dec_ref(v_x_5086_);
lean_dec_ref(v_x_5085_);
return v___x_5097_;
}
else
{
size_t v___x_5098_; size_t v___x_5099_; uint8_t v___x_5100_; 
v___x_5098_ = ((size_t)0ULL);
v___x_5099_ = lean_usize_of_nat(v___x_5096_);
v___x_5100_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0(v_x_5085_, v_x_5086_, v_numSectionVars_5083_, v_fnNames_5084_, v___x_5098_, v___x_5099_);
lean_dec_ref(v_x_5086_);
lean_dec_ref(v_x_5085_);
return v___x_5100_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1___boxed(lean_object* v_numSectionVars_5101_, lean_object* v_fnNames_5102_, lean_object* v_x_5103_, lean_object* v_x_5104_, lean_object* v_x_5105_){
_start:
{
uint8_t v_res_5106_; lean_object* v_r_5107_; 
v_res_5106_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1(v_numSectionVars_5101_, v_fnNames_5102_, v_x_5103_, v_x_5104_, v_x_5105_);
lean_dec(v_x_5105_);
lean_dec_ref(v_fnNames_5102_);
lean_dec(v_numSectionVars_5101_);
v_r_5107_ = lean_box(v_res_5106_);
return v_r_5107_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg(lean_object* v_fnNames_5108_, lean_object* v_numSectionVars_5109_, lean_object* v_a_5110_){
_start:
{
lean_object* v_dummy_5111_; lean_object* v_nargs_5112_; lean_object* v___x_5113_; lean_object* v___x_5114_; lean_object* v___x_5115_; uint8_t v___x_5116_; 
v_dummy_5111_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_5112_ = l_Lean_Expr_getAppNumArgs(v_a_5110_);
lean_inc(v_nargs_5112_);
v___x_5113_ = lean_mk_array(v_nargs_5112_, v_dummy_5111_);
v___x_5114_ = lean_unsigned_to_nat(1u);
v___x_5115_ = lean_nat_sub(v_nargs_5112_, v___x_5114_);
lean_dec(v_nargs_5112_);
v___x_5116_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1(v_numSectionVars_5109_, v_fnNames_5108_, v_a_5110_, v___x_5113_, v___x_5115_);
lean_dec(v___x_5115_);
return v___x_5116_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg___boxed(lean_object* v_fnNames_5117_, lean_object* v_numSectionVars_5118_, lean_object* v_a_5119_){
_start:
{
uint8_t v_res_5120_; lean_object* v_r_5121_; 
v_res_5120_ = l___private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg(v_fnNames_5117_, v_numSectionVars_5118_, v_a_5119_);
lean_dec(v_numSectionVars_5118_);
lean_dec_ref(v_fnNames_5117_);
v_r_5121_ = lean_box(v_res_5120_);
return v_r_5121_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__0(lean_object* v_fnNames_5122_, lean_object* v_numSectionVars_5123_, lean_object* v_as_5124_, size_t v_i_5125_, size_t v_stop_5126_){
_start:
{
uint8_t v___x_5127_; 
v___x_5127_ = lean_usize_dec_eq(v_i_5125_, v_stop_5126_);
if (v___x_5127_ == 0)
{
lean_object* v___x_5128_; uint8_t v___x_5129_; 
v___x_5128_ = lean_array_uget_borrowed(v_as_5124_, v_i_5125_);
lean_inc(v___x_5128_);
v___x_5129_ = l___private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg(v_fnNames_5122_, v_numSectionVars_5123_, v___x_5128_);
if (v___x_5129_ == 0)
{
size_t v___x_5130_; size_t v___x_5131_; 
v___x_5130_ = ((size_t)1ULL);
v___x_5131_ = lean_usize_add(v_i_5125_, v___x_5130_);
v_i_5125_ = v___x_5131_;
goto _start;
}
else
{
return v___x_5129_;
}
}
else
{
uint8_t v___x_5133_; 
v___x_5133_ = 0;
return v___x_5133_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__0___boxed(lean_object* v_fnNames_5134_, lean_object* v_numSectionVars_5135_, lean_object* v_as_5136_, lean_object* v_i_5137_, lean_object* v_stop_5138_){
_start:
{
size_t v_i_boxed_5139_; size_t v_stop_boxed_5140_; uint8_t v_res_5141_; lean_object* v_r_5142_; 
v_i_boxed_5139_ = lean_unbox_usize(v_i_5137_);
lean_dec(v_i_5137_);
v_stop_boxed_5140_ = lean_unbox_usize(v_stop_5138_);
lean_dec(v_stop_5138_);
v_res_5141_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__0(v_fnNames_5134_, v_numSectionVars_5135_, v_as_5136_, v_i_boxed_5139_, v_stop_boxed_5140_);
lean_dec_ref(v_as_5136_);
lean_dec(v_numSectionVars_5135_);
lean_dec_ref(v_fnNames_5134_);
v_r_5142_ = lean_box(v_res_5141_);
return v_r_5142_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__1(lean_object* v_fnNames_5143_, lean_object* v_numSectionVars_5144_, lean_object* v___x_5145_, lean_object* v_x_5146_, lean_object* v_x_5147_, lean_object* v___y_5148_, lean_object* v___y_5149_){
_start:
{
if (lean_obj_tag(v_x_5146_) == 5)
{
lean_object* v_fn_5154_; lean_object* v_arg_5155_; lean_object* v___x_5156_; 
v_fn_5154_ = lean_ctor_get(v_x_5146_, 0);
lean_inc_ref(v_fn_5154_);
v_arg_5155_ = lean_ctor_get(v_x_5146_, 1);
lean_inc_ref(v_arg_5155_);
lean_dec_ref_known(v_x_5146_, 2);
v___x_5156_ = lean_array_push(v_x_5147_, v_arg_5155_);
v_x_5146_ = v_fn_5154_;
v_x_5147_ = v___x_5156_;
goto _start;
}
else
{
uint8_t v___x_5158_; 
v___x_5158_ = l_Lean_Expr_isConst(v_x_5146_);
if (v___x_5158_ == 0)
{
lean_dec_ref(v_x_5147_);
lean_dec_ref(v_x_5146_);
lean_dec_ref(v___x_5145_);
goto v___jp_5151_;
}
else
{
lean_object* v___x_5159_; lean_object* v___x_5160_; uint8_t v___x_5161_; 
v___x_5159_ = lean_unsigned_to_nat(0u);
v___x_5160_ = lean_array_get_size(v_x_5147_);
v___x_5161_ = lean_nat_dec_lt(v___x_5159_, v___x_5160_);
if (v___x_5161_ == 0)
{
lean_dec_ref(v_x_5147_);
lean_dec_ref(v_x_5146_);
lean_dec_ref(v___x_5145_);
goto v___jp_5151_;
}
else
{
if (v___x_5161_ == 0)
{
lean_dec_ref(v_x_5147_);
lean_dec_ref(v_x_5146_);
lean_dec_ref(v___x_5145_);
goto v___jp_5151_;
}
else
{
size_t v___x_5162_; size_t v___x_5163_; uint8_t v___x_5164_; 
v___x_5162_ = ((size_t)0ULL);
v___x_5163_ = lean_usize_of_nat(v___x_5160_);
v___x_5164_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__0(v_fnNames_5143_, v_numSectionVars_5144_, v_x_5147_, v___x_5162_, v___x_5163_);
if (v___x_5164_ == 0)
{
lean_dec_ref(v_x_5147_);
lean_dec_ref(v_x_5146_);
lean_dec_ref(v___x_5145_);
goto v___jp_5151_;
}
else
{
lean_object* v___x_5165_; uint8_t v___x_5166_; lean_object* v___x_5167_; 
v___x_5165_ = l_Lean_Expr_constName_x21(v_x_5146_);
v___x_5166_ = 0;
v___x_5167_ = l_Lean_Environment_find_x3f(v___x_5145_, v___x_5165_, v___x_5166_);
if (lean_obj_tag(v___x_5167_) == 1)
{
lean_object* v_val_5168_; 
v_val_5168_ = lean_ctor_get(v___x_5167_, 0);
lean_inc(v_val_5168_);
lean_dec_ref_known(v___x_5167_, 1);
if (lean_obj_tag(v_val_5168_) == 2)
{
lean_object* v___x_5169_; lean_object* v___x_5170_; lean_object* v___x_5172_; uint8_t v_isShared_5173_; uint8_t v_isSharedCheck_5194_; 
v___x_5169_ = l_Lean_Expr_constLevels_x21(v_x_5146_);
lean_dec_ref(v_x_5146_);
v___x_5170_ = l_Lean_Core_instantiateValueLevelParams(v_val_5168_, v___x_5169_, v___x_5161_, v___y_5148_, v___y_5149_);
v_isSharedCheck_5194_ = !lean_is_exclusive(v_val_5168_);
if (v_isSharedCheck_5194_ == 0)
{
lean_object* v_unused_5195_; 
v_unused_5195_ = lean_ctor_get(v_val_5168_, 0);
lean_dec(v_unused_5195_);
v___x_5172_ = v_val_5168_;
v_isShared_5173_ = v_isSharedCheck_5194_;
goto v_resetjp_5171_;
}
else
{
lean_dec(v_val_5168_);
v___x_5172_ = lean_box(0);
v_isShared_5173_ = v_isSharedCheck_5194_;
goto v_resetjp_5171_;
}
v_resetjp_5171_:
{
if (lean_obj_tag(v___x_5170_) == 0)
{
lean_object* v_a_5174_; lean_object* v___x_5176_; uint8_t v_isShared_5177_; uint8_t v_isSharedCheck_5185_; 
v_a_5174_ = lean_ctor_get(v___x_5170_, 0);
v_isSharedCheck_5185_ = !lean_is_exclusive(v___x_5170_);
if (v_isSharedCheck_5185_ == 0)
{
v___x_5176_ = v___x_5170_;
v_isShared_5177_ = v_isSharedCheck_5185_;
goto v_resetjp_5175_;
}
else
{
lean_inc(v_a_5174_);
lean_dec(v___x_5170_);
v___x_5176_ = lean_box(0);
v_isShared_5177_ = v_isSharedCheck_5185_;
goto v_resetjp_5175_;
}
v_resetjp_5175_:
{
lean_object* v___x_5178_; lean_object* v___x_5180_; 
v___x_5178_ = l_Lean_Expr_betaRev(v_a_5174_, v_x_5147_, v___x_5166_, v___x_5166_);
lean_dec_ref(v_x_5147_);
if (v_isShared_5173_ == 0)
{
lean_ctor_set_tag(v___x_5172_, 1);
lean_ctor_set(v___x_5172_, 0, v___x_5178_);
v___x_5180_ = v___x_5172_;
goto v_reusejp_5179_;
}
else
{
lean_object* v_reuseFailAlloc_5184_; 
v_reuseFailAlloc_5184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5184_, 0, v___x_5178_);
v___x_5180_ = v_reuseFailAlloc_5184_;
goto v_reusejp_5179_;
}
v_reusejp_5179_:
{
lean_object* v___x_5182_; 
if (v_isShared_5177_ == 0)
{
lean_ctor_set(v___x_5176_, 0, v___x_5180_);
v___x_5182_ = v___x_5176_;
goto v_reusejp_5181_;
}
else
{
lean_object* v_reuseFailAlloc_5183_; 
v_reuseFailAlloc_5183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5183_, 0, v___x_5180_);
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
else
{
lean_object* v_a_5186_; lean_object* v___x_5188_; uint8_t v_isShared_5189_; uint8_t v_isSharedCheck_5193_; 
lean_del_object(v___x_5172_);
lean_dec_ref(v_x_5147_);
v_a_5186_ = lean_ctor_get(v___x_5170_, 0);
v_isSharedCheck_5193_ = !lean_is_exclusive(v___x_5170_);
if (v_isSharedCheck_5193_ == 0)
{
v___x_5188_ = v___x_5170_;
v_isShared_5189_ = v_isSharedCheck_5193_;
goto v_resetjp_5187_;
}
else
{
lean_inc(v_a_5186_);
lean_dec(v___x_5170_);
v___x_5188_ = lean_box(0);
v_isShared_5189_ = v_isSharedCheck_5193_;
goto v_resetjp_5187_;
}
v_resetjp_5187_:
{
lean_object* v___x_5191_; 
if (v_isShared_5189_ == 0)
{
v___x_5191_ = v___x_5188_;
goto v_reusejp_5190_;
}
else
{
lean_object* v_reuseFailAlloc_5192_; 
v_reuseFailAlloc_5192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5192_, 0, v_a_5186_);
v___x_5191_ = v_reuseFailAlloc_5192_;
goto v_reusejp_5190_;
}
v_reusejp_5190_:
{
return v___x_5191_;
}
}
}
}
}
else
{
lean_dec(v_val_5168_);
lean_dec_ref(v_x_5147_);
lean_dec_ref(v_x_5146_);
goto v___jp_5151_;
}
}
else
{
lean_dec(v___x_5167_);
lean_dec_ref(v_x_5147_);
lean_dec_ref(v_x_5146_);
goto v___jp_5151_;
}
}
}
}
}
}
v___jp_5151_:
{
lean_object* v___x_5152_; lean_object* v___x_5153_; 
v___x_5152_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_5153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5153_, 0, v___x_5152_);
return v___x_5153_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__1___boxed(lean_object* v_fnNames_5196_, lean_object* v_numSectionVars_5197_, lean_object* v___x_5198_, lean_object* v_x_5199_, lean_object* v_x_5200_, lean_object* v___y_5201_, lean_object* v___y_5202_, lean_object* v___y_5203_){
_start:
{
lean_object* v_res_5204_; 
v_res_5204_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__1(v_fnNames_5196_, v_numSectionVars_5197_, v___x_5198_, v_x_5199_, v_x_5200_, v___y_5201_, v___y_5202_);
lean_dec(v___y_5202_);
lean_dec_ref(v___y_5201_);
lean_dec(v_numSectionVars_5197_);
lean_dec_ref(v_fnNames_5196_);
return v_res_5204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___lam__1(lean_object* v_fnNames_5205_, lean_object* v_numSectionVars_5206_, lean_object* v_env_5207_, lean_object* v_e_5208_, lean_object* v___y_5209_, lean_object* v___y_5210_){
_start:
{
lean_object* v___x_5212_; lean_object* v___x_5213_; lean_object* v___x_5214_; 
v___x_5212_ = l_Lean_Expr_getAppNumArgs(v_e_5208_);
v___x_5213_ = lean_mk_empty_array_with_capacity(v___x_5212_);
lean_dec(v___x_5212_);
v___x_5214_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__1(v_fnNames_5205_, v_numSectionVars_5206_, v_env_5207_, v_e_5208_, v___x_5213_, v___y_5209_, v___y_5210_);
return v___x_5214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___lam__1___boxed(lean_object* v_fnNames_5215_, lean_object* v_numSectionVars_5216_, lean_object* v_env_5217_, lean_object* v_e_5218_, lean_object* v___y_5219_, lean_object* v___y_5220_, lean_object* v___y_5221_){
_start:
{
lean_object* v_res_5222_; 
v_res_5222_ = l_Lean_Meta_unfoldIfArgIsAppOf___lam__1(v_fnNames_5215_, v_numSectionVars_5216_, v_env_5217_, v_e_5218_, v___y_5219_, v___y_5220_);
lean_dec(v___y_5220_);
lean_dec_ref(v___y_5219_);
lean_dec(v_numSectionVars_5216_);
lean_dec_ref(v_fnNames_5215_);
return v_res_5222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___lam__0(lean_object* v_fnNames_5223_, lean_object* v_numSectionVars_5224_, lean_object* v_e_5225_, lean_object* v___f_5226_, lean_object* v___y_5227_, lean_object* v___y_5228_){
_start:
{
lean_object* v___x_5230_; lean_object* v_env_5231_; lean_object* v___f_5232_; lean_object* v___x_5233_; 
v___x_5230_ = lean_st_ref_get(v___y_5228_);
v_env_5231_ = lean_ctor_get(v___x_5230_, 0);
lean_inc_ref(v_env_5231_);
lean_dec(v___x_5230_);
v___f_5232_ = lean_alloc_closure((void*)(l_Lean_Meta_unfoldIfArgIsAppOf___lam__1___boxed), 7, 3);
lean_closure_set(v___f_5232_, 0, v_fnNames_5223_);
lean_closure_set(v___f_5232_, 1, v_numSectionVars_5224_);
lean_closure_set(v___f_5232_, 2, v_env_5231_);
v___x_5233_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_5225_, v___f_5232_, v___f_5226_, v___y_5227_, v___y_5228_);
return v___x_5233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___lam__0___boxed(lean_object* v_fnNames_5234_, lean_object* v_numSectionVars_5235_, lean_object* v_e_5236_, lean_object* v___f_5237_, lean_object* v___y_5238_, lean_object* v___y_5239_, lean_object* v___y_5240_){
_start:
{
lean_object* v_res_5241_; 
v_res_5241_ = l_Lean_Meta_unfoldIfArgIsAppOf___lam__0(v_fnNames_5234_, v_numSectionVars_5235_, v_e_5236_, v___f_5237_, v___y_5238_, v___y_5239_);
lean_dec(v___y_5239_);
lean_dec_ref(v___y_5238_);
return v_res_5241_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0(lean_object* v___y_5242_, uint8_t v_isExporting_5243_, lean_object* v___x_5244_, lean_object* v_a_x3f_5245_){
_start:
{
lean_object* v___x_5247_; lean_object* v_env_5248_; lean_object* v_nextMacroScope_5249_; lean_object* v_ngen_5250_; lean_object* v_auxDeclNGen_5251_; lean_object* v_traceState_5252_; lean_object* v_messages_5253_; lean_object* v_infoState_5254_; lean_object* v_snapshotTasks_5255_; lean_object* v___x_5257_; uint8_t v_isShared_5258_; uint8_t v_isSharedCheck_5266_; 
v___x_5247_ = lean_st_ref_take(v___y_5242_);
v_env_5248_ = lean_ctor_get(v___x_5247_, 0);
v_nextMacroScope_5249_ = lean_ctor_get(v___x_5247_, 1);
v_ngen_5250_ = lean_ctor_get(v___x_5247_, 2);
v_auxDeclNGen_5251_ = lean_ctor_get(v___x_5247_, 3);
v_traceState_5252_ = lean_ctor_get(v___x_5247_, 4);
v_messages_5253_ = lean_ctor_get(v___x_5247_, 6);
v_infoState_5254_ = lean_ctor_get(v___x_5247_, 7);
v_snapshotTasks_5255_ = lean_ctor_get(v___x_5247_, 8);
v_isSharedCheck_5266_ = !lean_is_exclusive(v___x_5247_);
if (v_isSharedCheck_5266_ == 0)
{
lean_object* v_unused_5267_; 
v_unused_5267_ = lean_ctor_get(v___x_5247_, 5);
lean_dec(v_unused_5267_);
v___x_5257_ = v___x_5247_;
v_isShared_5258_ = v_isSharedCheck_5266_;
goto v_resetjp_5256_;
}
else
{
lean_inc(v_snapshotTasks_5255_);
lean_inc(v_infoState_5254_);
lean_inc(v_messages_5253_);
lean_inc(v_traceState_5252_);
lean_inc(v_auxDeclNGen_5251_);
lean_inc(v_ngen_5250_);
lean_inc(v_nextMacroScope_5249_);
lean_inc(v_env_5248_);
lean_dec(v___x_5247_);
v___x_5257_ = lean_box(0);
v_isShared_5258_ = v_isSharedCheck_5266_;
goto v_resetjp_5256_;
}
v_resetjp_5256_:
{
lean_object* v___x_5259_; lean_object* v___x_5261_; 
v___x_5259_ = l_Lean_Environment_setExporting(v_env_5248_, v_isExporting_5243_);
if (v_isShared_5258_ == 0)
{
lean_ctor_set(v___x_5257_, 5, v___x_5244_);
lean_ctor_set(v___x_5257_, 0, v___x_5259_);
v___x_5261_ = v___x_5257_;
goto v_reusejp_5260_;
}
else
{
lean_object* v_reuseFailAlloc_5265_; 
v_reuseFailAlloc_5265_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5265_, 0, v___x_5259_);
lean_ctor_set(v_reuseFailAlloc_5265_, 1, v_nextMacroScope_5249_);
lean_ctor_set(v_reuseFailAlloc_5265_, 2, v_ngen_5250_);
lean_ctor_set(v_reuseFailAlloc_5265_, 3, v_auxDeclNGen_5251_);
lean_ctor_set(v_reuseFailAlloc_5265_, 4, v_traceState_5252_);
lean_ctor_set(v_reuseFailAlloc_5265_, 5, v___x_5244_);
lean_ctor_set(v_reuseFailAlloc_5265_, 6, v_messages_5253_);
lean_ctor_set(v_reuseFailAlloc_5265_, 7, v_infoState_5254_);
lean_ctor_set(v_reuseFailAlloc_5265_, 8, v_snapshotTasks_5255_);
v___x_5261_ = v_reuseFailAlloc_5265_;
goto v_reusejp_5260_;
}
v_reusejp_5260_:
{
lean_object* v___x_5262_; lean_object* v___x_5263_; lean_object* v___x_5264_; 
v___x_5262_ = lean_st_ref_put(v___y_5242_, v___x_5261_);
v___x_5263_ = lean_box(0);
v___x_5264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5264_, 0, v___x_5263_);
return v___x_5264_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0___boxed(lean_object* v___y_5268_, lean_object* v_isExporting_5269_, lean_object* v___x_5270_, lean_object* v_a_x3f_5271_, lean_object* v___y_5272_){
_start:
{
uint8_t v_isExporting_boxed_5273_; lean_object* v_res_5274_; 
v_isExporting_boxed_5273_ = lean_unbox(v_isExporting_5269_);
v_res_5274_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0(v___y_5268_, v_isExporting_boxed_5273_, v___x_5270_, v_a_x3f_5271_);
lean_dec(v_a_x3f_5271_);
lean_dec(v___y_5268_);
return v_res_5274_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg(lean_object* v_x_5275_, uint8_t v_isExporting_5276_, lean_object* v___y_5277_, lean_object* v___y_5278_){
_start:
{
lean_object* v___x_5280_; lean_object* v_env_5281_; lean_object* v___x_5282_; uint8_t v_isModule_5283_; 
v___x_5280_ = lean_st_ref_get(v___y_5278_);
v_env_5281_ = lean_ctor_get(v___x_5280_, 0);
lean_inc_ref(v_env_5281_);
lean_dec(v___x_5280_);
v___x_5282_ = l_Lean_Environment_header(v_env_5281_);
v_isModule_5283_ = lean_ctor_get_uint8(v___x_5282_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_5282_);
if (v_isModule_5283_ == 0)
{
lean_object* v___x_5284_; 
lean_dec_ref(v_env_5281_);
lean_inc(v___y_5278_);
lean_inc_ref(v___y_5277_);
v___x_5284_ = lean_apply_3(v_x_5275_, v___y_5277_, v___y_5278_, lean_box(0));
return v___x_5284_;
}
else
{
uint8_t v_isExporting_5285_; 
v_isExporting_5285_ = lean_ctor_get_uint8(v_env_5281_, sizeof(void*)*8);
lean_dec_ref(v_env_5281_);
if (v_isExporting_5276_ == 0)
{
if (v_isExporting_5285_ == 0)
{
lean_object* v___x_5336_; 
lean_inc(v___y_5278_);
lean_inc_ref(v___y_5277_);
v___x_5336_ = lean_apply_3(v_x_5275_, v___y_5277_, v___y_5278_, lean_box(0));
return v___x_5336_;
}
else
{
goto v___jp_5286_;
}
}
else
{
if (v_isExporting_5285_ == 0)
{
goto v___jp_5286_;
}
else
{
lean_object* v___x_5337_; 
lean_inc(v___y_5278_);
lean_inc_ref(v___y_5277_);
v___x_5337_ = lean_apply_3(v_x_5275_, v___y_5277_, v___y_5278_, lean_box(0));
return v___x_5337_;
}
}
v___jp_5286_:
{
lean_object* v___x_5287_; lean_object* v_env_5288_; lean_object* v_nextMacroScope_5289_; lean_object* v_ngen_5290_; lean_object* v_auxDeclNGen_5291_; lean_object* v_traceState_5292_; lean_object* v_messages_5293_; lean_object* v_infoState_5294_; lean_object* v_snapshotTasks_5295_; lean_object* v___x_5297_; uint8_t v_isShared_5298_; uint8_t v_isSharedCheck_5334_; 
v___x_5287_ = lean_st_ref_take(v___y_5278_);
v_env_5288_ = lean_ctor_get(v___x_5287_, 0);
v_nextMacroScope_5289_ = lean_ctor_get(v___x_5287_, 1);
v_ngen_5290_ = lean_ctor_get(v___x_5287_, 2);
v_auxDeclNGen_5291_ = lean_ctor_get(v___x_5287_, 3);
v_traceState_5292_ = lean_ctor_get(v___x_5287_, 4);
v_messages_5293_ = lean_ctor_get(v___x_5287_, 6);
v_infoState_5294_ = lean_ctor_get(v___x_5287_, 7);
v_snapshotTasks_5295_ = lean_ctor_get(v___x_5287_, 8);
v_isSharedCheck_5334_ = !lean_is_exclusive(v___x_5287_);
if (v_isSharedCheck_5334_ == 0)
{
lean_object* v_unused_5335_; 
v_unused_5335_ = lean_ctor_get(v___x_5287_, 5);
lean_dec(v_unused_5335_);
v___x_5297_ = v___x_5287_;
v_isShared_5298_ = v_isSharedCheck_5334_;
goto v_resetjp_5296_;
}
else
{
lean_inc(v_snapshotTasks_5295_);
lean_inc(v_infoState_5294_);
lean_inc(v_messages_5293_);
lean_inc(v_traceState_5292_);
lean_inc(v_auxDeclNGen_5291_);
lean_inc(v_ngen_5290_);
lean_inc(v_nextMacroScope_5289_);
lean_inc(v_env_5288_);
lean_dec(v___x_5287_);
v___x_5297_ = lean_box(0);
v_isShared_5298_ = v_isSharedCheck_5334_;
goto v_resetjp_5296_;
}
v_resetjp_5296_:
{
lean_object* v___x_5299_; lean_object* v___x_5300_; lean_object* v___x_5302_; 
v___x_5299_ = l_Lean_Environment_setExporting(v_env_5288_, v_isExporting_5276_);
v___x_5300_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2, &l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2);
if (v_isShared_5298_ == 0)
{
lean_ctor_set(v___x_5297_, 5, v___x_5300_);
lean_ctor_set(v___x_5297_, 0, v___x_5299_);
v___x_5302_ = v___x_5297_;
goto v_reusejp_5301_;
}
else
{
lean_object* v_reuseFailAlloc_5333_; 
v_reuseFailAlloc_5333_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5333_, 0, v___x_5299_);
lean_ctor_set(v_reuseFailAlloc_5333_, 1, v_nextMacroScope_5289_);
lean_ctor_set(v_reuseFailAlloc_5333_, 2, v_ngen_5290_);
lean_ctor_set(v_reuseFailAlloc_5333_, 3, v_auxDeclNGen_5291_);
lean_ctor_set(v_reuseFailAlloc_5333_, 4, v_traceState_5292_);
lean_ctor_set(v_reuseFailAlloc_5333_, 5, v___x_5300_);
lean_ctor_set(v_reuseFailAlloc_5333_, 6, v_messages_5293_);
lean_ctor_set(v_reuseFailAlloc_5333_, 7, v_infoState_5294_);
lean_ctor_set(v_reuseFailAlloc_5333_, 8, v_snapshotTasks_5295_);
v___x_5302_ = v_reuseFailAlloc_5333_;
goto v_reusejp_5301_;
}
v_reusejp_5301_:
{
lean_object* v___x_5303_; lean_object* v_r_5304_; 
v___x_5303_ = lean_st_ref_put(v___y_5278_, v___x_5302_);
lean_inc(v___y_5278_);
lean_inc_ref(v___y_5277_);
v_r_5304_ = lean_apply_3(v_x_5275_, v___y_5277_, v___y_5278_, lean_box(0));
if (lean_obj_tag(v_r_5304_) == 0)
{
lean_object* v_a_5305_; lean_object* v___x_5307_; uint8_t v_isShared_5308_; uint8_t v_isSharedCheck_5321_; 
v_a_5305_ = lean_ctor_get(v_r_5304_, 0);
v_isSharedCheck_5321_ = !lean_is_exclusive(v_r_5304_);
if (v_isSharedCheck_5321_ == 0)
{
v___x_5307_ = v_r_5304_;
v_isShared_5308_ = v_isSharedCheck_5321_;
goto v_resetjp_5306_;
}
else
{
lean_inc(v_a_5305_);
lean_dec(v_r_5304_);
v___x_5307_ = lean_box(0);
v_isShared_5308_ = v_isSharedCheck_5321_;
goto v_resetjp_5306_;
}
v_resetjp_5306_:
{
lean_object* v___x_5310_; 
lean_inc(v_a_5305_);
if (v_isShared_5308_ == 0)
{
lean_ctor_set_tag(v___x_5307_, 1);
v___x_5310_ = v___x_5307_;
goto v_reusejp_5309_;
}
else
{
lean_object* v_reuseFailAlloc_5320_; 
v_reuseFailAlloc_5320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5320_, 0, v_a_5305_);
v___x_5310_ = v_reuseFailAlloc_5320_;
goto v_reusejp_5309_;
}
v_reusejp_5309_:
{
lean_object* v___x_5311_; lean_object* v___x_5313_; uint8_t v_isShared_5314_; uint8_t v_isSharedCheck_5318_; 
v___x_5311_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0(v___y_5278_, v_isExporting_5285_, v___x_5300_, v___x_5310_);
lean_dec_ref(v___x_5310_);
v_isSharedCheck_5318_ = !lean_is_exclusive(v___x_5311_);
if (v_isSharedCheck_5318_ == 0)
{
lean_object* v_unused_5319_; 
v_unused_5319_ = lean_ctor_get(v___x_5311_, 0);
lean_dec(v_unused_5319_);
v___x_5313_ = v___x_5311_;
v_isShared_5314_ = v_isSharedCheck_5318_;
goto v_resetjp_5312_;
}
else
{
lean_dec(v___x_5311_);
v___x_5313_ = lean_box(0);
v_isShared_5314_ = v_isSharedCheck_5318_;
goto v_resetjp_5312_;
}
v_resetjp_5312_:
{
lean_object* v___x_5316_; 
if (v_isShared_5314_ == 0)
{
lean_ctor_set(v___x_5313_, 0, v_a_5305_);
v___x_5316_ = v___x_5313_;
goto v_reusejp_5315_;
}
else
{
lean_object* v_reuseFailAlloc_5317_; 
v_reuseFailAlloc_5317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5317_, 0, v_a_5305_);
v___x_5316_ = v_reuseFailAlloc_5317_;
goto v_reusejp_5315_;
}
v_reusejp_5315_:
{
return v___x_5316_;
}
}
}
}
}
else
{
lean_object* v_a_5322_; lean_object* v___x_5323_; lean_object* v___x_5324_; lean_object* v___x_5326_; uint8_t v_isShared_5327_; uint8_t v_isSharedCheck_5331_; 
v_a_5322_ = lean_ctor_get(v_r_5304_, 0);
lean_inc(v_a_5322_);
lean_dec_ref_known(v_r_5304_, 1);
v___x_5323_ = lean_box(0);
v___x_5324_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0(v___y_5278_, v_isExporting_5285_, v___x_5300_, v___x_5323_);
v_isSharedCheck_5331_ = !lean_is_exclusive(v___x_5324_);
if (v_isSharedCheck_5331_ == 0)
{
lean_object* v_unused_5332_; 
v_unused_5332_ = lean_ctor_get(v___x_5324_, 0);
lean_dec(v_unused_5332_);
v___x_5326_ = v___x_5324_;
v_isShared_5327_ = v_isSharedCheck_5331_;
goto v_resetjp_5325_;
}
else
{
lean_dec(v___x_5324_);
v___x_5326_ = lean_box(0);
v_isShared_5327_ = v_isSharedCheck_5331_;
goto v_resetjp_5325_;
}
v_resetjp_5325_:
{
lean_object* v___x_5329_; 
if (v_isShared_5327_ == 0)
{
lean_ctor_set_tag(v___x_5326_, 1);
lean_ctor_set(v___x_5326_, 0, v_a_5322_);
v___x_5329_ = v___x_5326_;
goto v_reusejp_5328_;
}
else
{
lean_object* v_reuseFailAlloc_5330_; 
v_reuseFailAlloc_5330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5330_, 0, v_a_5322_);
v___x_5329_ = v_reuseFailAlloc_5330_;
goto v_reusejp_5328_;
}
v_reusejp_5328_:
{
return v___x_5329_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___boxed(lean_object* v_x_5338_, lean_object* v_isExporting_5339_, lean_object* v___y_5340_, lean_object* v___y_5341_, lean_object* v___y_5342_){
_start:
{
uint8_t v_isExporting_boxed_5343_; lean_object* v_res_5344_; 
v_isExporting_boxed_5343_ = lean_unbox(v_isExporting_5339_);
v_res_5344_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg(v_x_5338_, v_isExporting_boxed_5343_, v___y_5340_, v___y_5341_);
lean_dec(v___y_5341_);
lean_dec_ref(v___y_5340_);
return v_res_5344_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg(lean_object* v_x_5345_, uint8_t v_when_5346_, lean_object* v___y_5347_, lean_object* v___y_5348_){
_start:
{
if (v_when_5346_ == 0)
{
lean_object* v___x_5350_; 
lean_inc(v___y_5348_);
lean_inc_ref(v___y_5347_);
v___x_5350_ = lean_apply_3(v_x_5345_, v___y_5347_, v___y_5348_, lean_box(0));
return v___x_5350_;
}
else
{
uint8_t v___x_5351_; lean_object* v___x_5352_; 
v___x_5351_ = 0;
v___x_5352_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg(v_x_5345_, v___x_5351_, v___y_5347_, v___y_5348_);
return v___x_5352_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg___boxed(lean_object* v_x_5353_, lean_object* v_when_5354_, lean_object* v___y_5355_, lean_object* v___y_5356_, lean_object* v___y_5357_){
_start:
{
uint8_t v_when_boxed_5358_; lean_object* v_res_5359_; 
v_when_boxed_5358_ = lean_unbox(v_when_5354_);
v_res_5359_ = l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg(v_x_5353_, v_when_boxed_5358_, v___y_5355_, v___y_5356_);
lean_dec(v___y_5356_);
lean_dec_ref(v___y_5355_);
return v_res_5359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf(lean_object* v_fnNames_5360_, lean_object* v_numSectionVars_5361_, lean_object* v_e_5362_, lean_object* v_a_5363_, lean_object* v_a_5364_){
_start:
{
lean_object* v___f_5366_; lean_object* v___f_5367_; uint8_t v___x_5368_; lean_object* v___x_5369_; 
v___f_5366_ = ((lean_object*)(l_Lean_Core_betaReduce___closed__1));
v___f_5367_ = lean_alloc_closure((void*)(l_Lean_Meta_unfoldIfArgIsAppOf___lam__0___boxed), 7, 4);
lean_closure_set(v___f_5367_, 0, v_fnNames_5360_);
lean_closure_set(v___f_5367_, 1, v_numSectionVars_5361_);
lean_closure_set(v___f_5367_, 2, v_e_5362_);
lean_closure_set(v___f_5367_, 3, v___f_5366_);
v___x_5368_ = 1;
v___x_5369_ = l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg(v___f_5367_, v___x_5368_, v_a_5363_, v_a_5364_);
return v___x_5369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___boxed(lean_object* v_fnNames_5370_, lean_object* v_numSectionVars_5371_, lean_object* v_e_5372_, lean_object* v_a_5373_, lean_object* v_a_5374_, lean_object* v_a_5375_){
_start:
{
lean_object* v_res_5376_; 
v_res_5376_ = l_Lean_Meta_unfoldIfArgIsAppOf(v_fnNames_5370_, v_numSectionVars_5371_, v_e_5372_, v_a_5373_, v_a_5374_);
lean_dec(v_a_5374_);
lean_dec_ref(v_a_5373_);
return v_res_5376_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2(lean_object* v_00_u03b1_5377_, lean_object* v_x_5378_, uint8_t v_isExporting_5379_, lean_object* v___y_5380_, lean_object* v___y_5381_){
_start:
{
lean_object* v___x_5383_; 
v___x_5383_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg(v_x_5378_, v_isExporting_5379_, v___y_5380_, v___y_5381_);
return v___x_5383_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___boxed(lean_object* v_00_u03b1_5384_, lean_object* v_x_5385_, lean_object* v_isExporting_5386_, lean_object* v___y_5387_, lean_object* v___y_5388_, lean_object* v___y_5389_){
_start:
{
uint8_t v_isExporting_boxed_5390_; lean_object* v_res_5391_; 
v_isExporting_boxed_5390_ = lean_unbox(v_isExporting_5386_);
v_res_5391_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2(v_00_u03b1_5384_, v_x_5385_, v_isExporting_boxed_5390_, v___y_5387_, v___y_5388_);
lean_dec(v___y_5388_);
lean_dec_ref(v___y_5387_);
return v_res_5391_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2(lean_object* v_00_u03b1_5392_, lean_object* v_x_5393_, uint8_t v_when_5394_, lean_object* v___y_5395_, lean_object* v___y_5396_){
_start:
{
lean_object* v___x_5398_; 
v___x_5398_ = l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg(v_x_5393_, v_when_5394_, v___y_5395_, v___y_5396_);
return v___x_5398_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___boxed(lean_object* v_00_u03b1_5399_, lean_object* v_x_5400_, lean_object* v_when_5401_, lean_object* v___y_5402_, lean_object* v___y_5403_, lean_object* v___y_5404_){
_start:
{
uint8_t v_when_boxed_5405_; lean_object* v_res_5406_; 
v_when_boxed_5405_ = lean_unbox(v_when_5401_);
v_res_5406_ = l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2(v_00_u03b1_5399_, v_x_5400_, v_when_boxed_5405_, v___y_5402_, v___y_5403_);
lean_dec(v___y_5403_);
lean_dec_ref(v___y_5402_);
return v_res_5406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___lam__0(lean_object* v_x_5407_, lean_object* v___y_5408_, lean_object* v___y_5409_){
_start:
{
lean_object* v___x_5411_; lean_object* v___x_5412_; 
v___x_5411_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_5412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5412_, 0, v___x_5411_);
return v___x_5412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___lam__0___boxed(lean_object* v_x_5413_, lean_object* v___y_5414_, lean_object* v___y_5415_, lean_object* v___y_5416_){
_start:
{
lean_object* v_res_5417_; 
v_res_5417_ = l_Lean_Meta_eraseInaccessibleAnnotations___lam__0(v_x_5413_, v___y_5414_, v___y_5415_);
lean_dec(v___y_5415_);
lean_dec_ref(v___y_5414_);
lean_dec_ref(v_x_5413_);
return v_res_5417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___lam__1(lean_object* v_e_5418_, lean_object* v___y_5419_, lean_object* v___y_5420_){
_start:
{
lean_object* v___y_5423_; lean_object* v___x_5426_; 
v___x_5426_ = l_Lean_inaccessible_x3f(v_e_5418_);
if (lean_obj_tag(v___x_5426_) == 1)
{
lean_object* v_val_5427_; 
lean_dec_ref(v_e_5418_);
v_val_5427_ = lean_ctor_get(v___x_5426_, 0);
lean_inc(v_val_5427_);
lean_dec_ref_known(v___x_5426_, 1);
v___y_5423_ = v_val_5427_;
goto v___jp_5422_;
}
else
{
lean_dec(v___x_5426_);
v___y_5423_ = v_e_5418_;
goto v___jp_5422_;
}
v___jp_5422_:
{
lean_object* v___x_5424_; lean_object* v___x_5425_; 
v___x_5424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5424_, 0, v___y_5423_);
v___x_5425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5425_, 0, v___x_5424_);
return v___x_5425_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___lam__1___boxed(lean_object* v_e_5428_, lean_object* v___y_5429_, lean_object* v___y_5430_, lean_object* v___y_5431_){
_start:
{
lean_object* v_res_5432_; 
v_res_5432_ = l_Lean_Meta_eraseInaccessibleAnnotations___lam__1(v_e_5428_, v___y_5429_, v___y_5430_);
lean_dec(v___y_5430_);
lean_dec_ref(v___y_5429_);
return v_res_5432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations(lean_object* v_e_5435_, lean_object* v_a_5436_, lean_object* v_a_5437_){
_start:
{
lean_object* v___f_5439_; lean_object* v___f_5440_; lean_object* v___x_5441_; 
v___f_5439_ = ((lean_object*)(l_Lean_Meta_eraseInaccessibleAnnotations___closed__0));
v___f_5440_ = ((lean_object*)(l_Lean_Meta_eraseInaccessibleAnnotations___closed__1));
v___x_5441_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_5435_, v___f_5439_, v___f_5440_, v_a_5436_, v_a_5437_);
return v___x_5441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___boxed(lean_object* v_e_5442_, lean_object* v_a_5443_, lean_object* v_a_5444_, lean_object* v_a_5445_){
_start:
{
lean_object* v_res_5446_; 
v_res_5446_ = l_Lean_Meta_eraseInaccessibleAnnotations(v_e_5442_, v_a_5443_, v_a_5444_);
lean_dec(v_a_5444_);
lean_dec_ref(v_a_5443_);
return v_res_5446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_erasePatternRefAnnotations___lam__1(lean_object* v_e_5447_, lean_object* v___y_5448_, lean_object* v___y_5449_){
_start:
{
lean_object* v___y_5452_; lean_object* v___x_5455_; 
v___x_5455_ = l_Lean_patternWithRef_x3f(v_e_5447_);
if (lean_obj_tag(v___x_5455_) == 1)
{
lean_object* v_val_5456_; lean_object* v_snd_5457_; 
lean_dec_ref(v_e_5447_);
v_val_5456_ = lean_ctor_get(v___x_5455_, 0);
lean_inc(v_val_5456_);
lean_dec_ref_known(v___x_5455_, 1);
v_snd_5457_ = lean_ctor_get(v_val_5456_, 1);
lean_inc(v_snd_5457_);
lean_dec(v_val_5456_);
v___y_5452_ = v_snd_5457_;
goto v___jp_5451_;
}
else
{
lean_dec(v___x_5455_);
v___y_5452_ = v_e_5447_;
goto v___jp_5451_;
}
v___jp_5451_:
{
lean_object* v___x_5453_; lean_object* v___x_5454_; 
v___x_5453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5453_, 0, v___y_5452_);
v___x_5454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5454_, 0, v___x_5453_);
return v___x_5454_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_erasePatternRefAnnotations___lam__1___boxed(lean_object* v_e_5458_, lean_object* v___y_5459_, lean_object* v___y_5460_, lean_object* v___y_5461_){
_start:
{
lean_object* v_res_5462_; 
v_res_5462_ = l_Lean_Meta_erasePatternRefAnnotations___lam__1(v_e_5458_, v___y_5459_, v___y_5460_);
lean_dec(v___y_5460_);
lean_dec_ref(v___y_5459_);
return v_res_5462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_erasePatternRefAnnotations(lean_object* v_e_5464_, lean_object* v_a_5465_, lean_object* v_a_5466_){
_start:
{
lean_object* v___f_5468_; lean_object* v___f_5469_; lean_object* v___x_5470_; 
v___f_5468_ = ((lean_object*)(l_Lean_Meta_eraseInaccessibleAnnotations___closed__0));
v___f_5469_ = ((lean_object*)(l_Lean_Meta_erasePatternRefAnnotations___closed__0));
v___x_5470_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_5464_, v___f_5468_, v___f_5469_, v_a_5465_, v_a_5466_);
return v___x_5470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_erasePatternRefAnnotations___boxed(lean_object* v_e_5471_, lean_object* v_a_5472_, lean_object* v_a_5473_, lean_object* v_a_5474_){
_start:
{
lean_object* v_res_5475_; 
v_res_5475_ = l_Lean_Meta_erasePatternRefAnnotations(v_e_5471_, v_a_5472_, v_a_5473_);
lean_dec(v_a_5473_);
lean_dec_ref(v_a_5472_);
return v_res_5475_;
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
