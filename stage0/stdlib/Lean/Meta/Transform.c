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
lean_object* v___y_1099_; lean_object* v___y_1109_; lean_object* v___y_1110_; uint8_t v___y_1111_; lean_object* v___y_1112_; lean_object* v___y_1113_; lean_object* v___y_1114_; uint8_t v___y_1115_; lean_object* v___y_1116_; lean_object* v___y_1117_; lean_object* v___y_1118_; lean_object* v___y_1119_; lean_object* v___y_1120_; lean_object* v_toCold_1125_; lean_object* v_options_1126_; lean_object* v_currRecDepth_1127_; lean_object* v_maxRecDepth_1128_; lean_object* v_ref_1129_; lean_object* v_currNamespace_1130_; lean_object* v_openDecls_1131_; lean_object* v_initHeartbeats_1132_; lean_object* v_maxHeartbeats_1133_; lean_object* v_currMacroScope_1134_; uint8_t v_diag_1135_; uint8_t v_suppressElabErrors_1136_; lean_object* v_cancelTk_x3f_1142_; 
v_toCold_1125_ = lean_ctor_get(v___y_1095_, 0);
v_options_1126_ = lean_ctor_get(v___y_1095_, 1);
v_currRecDepth_1127_ = lean_ctor_get(v___y_1095_, 2);
v_maxRecDepth_1128_ = lean_ctor_get(v___y_1095_, 3);
v_ref_1129_ = lean_ctor_get(v___y_1095_, 4);
v_currNamespace_1130_ = lean_ctor_get(v___y_1095_, 5);
v_openDecls_1131_ = lean_ctor_get(v___y_1095_, 6);
v_initHeartbeats_1132_ = lean_ctor_get(v___y_1095_, 7);
v_maxHeartbeats_1133_ = lean_ctor_get(v___y_1095_, 8);
v_currMacroScope_1134_ = lean_ctor_get(v___y_1095_, 9);
v_diag_1135_ = lean_ctor_get_uint8(v___y_1095_, sizeof(void*)*10);
v_suppressElabErrors_1136_ = lean_ctor_get_uint8(v___y_1095_, sizeof(void*)*10 + 1);
v_cancelTk_x3f_1142_ = lean_ctor_get(v_toCold_1125_, 3);
if (lean_obj_tag(v_cancelTk_x3f_1142_) == 1)
{
lean_object* v_val_1143_; uint8_t v___x_1144_; 
v_val_1143_ = lean_ctor_get(v_cancelTk_x3f_1142_, 0);
v___x_1144_ = l_IO_CancelToken_isSet(v_val_1143_);
if (v___x_1144_ == 0)
{
goto v___jp_1137_;
}
else
{
lean_object* v___x_1145_; lean_object* v_a_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1153_; 
lean_dec_ref(v_x_1093_);
v___x_1145_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___redArg();
v_a_1146_ = lean_ctor_get(v___x_1145_, 0);
v_isSharedCheck_1153_ = !lean_is_exclusive(v___x_1145_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1148_ = v___x_1145_;
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_a_1146_);
lean_dec(v___x_1145_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1151_; 
if (v_isShared_1149_ == 0)
{
v___x_1151_ = v___x_1148_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v_a_1146_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
}
}
}
}
else
{
goto v___jp_1137_;
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
lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___x_1121_ = lean_unsigned_to_nat(1u);
v___x_1122_ = lean_nat_add(v___y_1117_, v___x_1121_);
lean_inc(v___y_1119_);
lean_inc(v___y_1110_);
lean_inc(v___y_1116_);
lean_inc(v___y_1120_);
lean_inc(v___y_1109_);
lean_inc(v___y_1113_);
lean_inc_ref(v___y_1114_);
lean_inc_ref(v___y_1112_);
v___x_1123_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_1123_, 0, v___y_1112_);
lean_ctor_set(v___x_1123_, 1, v___y_1114_);
lean_ctor_set(v___x_1123_, 2, v___x_1122_);
lean_ctor_set(v___x_1123_, 3, v___y_1113_);
lean_ctor_set(v___x_1123_, 4, v___y_1118_);
lean_ctor_set(v___x_1123_, 5, v___y_1109_);
lean_ctor_set(v___x_1123_, 6, v___y_1120_);
lean_ctor_set(v___x_1123_, 7, v___y_1116_);
lean_ctor_set(v___x_1123_, 8, v___y_1110_);
lean_ctor_set(v___x_1123_, 9, v___y_1119_);
lean_ctor_set_uint8(v___x_1123_, sizeof(void*)*10, v___y_1111_);
lean_ctor_set_uint8(v___x_1123_, sizeof(void*)*10 + 1, v___y_1115_);
lean_inc(v___y_1096_);
lean_inc(v___y_1094_);
v___x_1124_ = lean_apply_4(v_x_1093_, v___y_1094_, v___x_1123_, v___y_1096_, lean_box(0));
v___y_1099_ = v___x_1124_;
goto v___jp_1098_;
}
v___jp_1137_:
{
lean_object* v___x_1138_; uint8_t v___x_1139_; 
v___x_1138_ = lean_unsigned_to_nat(0u);
v___x_1139_ = lean_nat_dec_eq(v_maxRecDepth_1128_, v___x_1138_);
if (v___x_1139_ == 0)
{
uint8_t v___x_1140_; 
v___x_1140_ = lean_nat_dec_eq(v_currRecDepth_1127_, v_maxRecDepth_1128_);
if (v___x_1140_ == 0)
{
lean_inc(v_ref_1129_);
v___y_1109_ = v_currNamespace_1130_;
v___y_1110_ = v_maxHeartbeats_1133_;
v___y_1111_ = v_diag_1135_;
v___y_1112_ = v_toCold_1125_;
v___y_1113_ = v_maxRecDepth_1128_;
v___y_1114_ = v_options_1126_;
v___y_1115_ = v_suppressElabErrors_1136_;
v___y_1116_ = v_initHeartbeats_1132_;
v___y_1117_ = v_currRecDepth_1127_;
v___y_1118_ = v_ref_1129_;
v___y_1119_ = v_currMacroScope_1134_;
v___y_1120_ = v_openDecls_1131_;
goto v___jp_1108_;
}
else
{
lean_object* v___x_1141_; 
lean_dec_ref(v_x_1093_);
lean_inc(v_ref_1129_);
v___x_1141_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_1129_);
v___y_1099_ = v___x_1141_;
goto v___jp_1098_;
}
}
else
{
lean_inc(v_ref_1129_);
v___y_1109_ = v_currNamespace_1130_;
v___y_1110_ = v_maxHeartbeats_1133_;
v___y_1111_ = v_diag_1135_;
v___y_1112_ = v_toCold_1125_;
v___y_1113_ = v_maxRecDepth_1128_;
v___y_1114_ = v_options_1126_;
v___y_1115_ = v_suppressElabErrors_1136_;
v___y_1116_ = v_initHeartbeats_1132_;
v___y_1117_ = v_currRecDepth_1127_;
v___y_1118_ = v_ref_1129_;
v___y_1119_ = v_currMacroScope_1134_;
v___y_1120_ = v_openDecls_1131_;
goto v___jp_1108_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___redArg___boxed(lean_object* v_x_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_){
_start:
{
lean_object* v_res_1159_; 
v_res_1159_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___redArg(v_x_1154_, v___y_1155_, v___y_1156_, v___y_1157_);
lean_dec(v___y_1157_);
lean_dec_ref(v___y_1156_);
lean_dec(v___y_1155_);
return v_res_1159_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_1160_, lean_object* v_x_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_){
_start:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; 
v___x_1165_ = lean_apply_1(v_x_1161_, lean_box(0));
v___x_1166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1166_, 0, v___x_1165_);
return v___x_1166_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_1167_, lean_object* v_x_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_){
_start:
{
lean_object* v_res_1172_; 
v_res_1172_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__0(v_00_u03b1_1167_, v_x_1168_, v___y_1169_, v___y_1170_);
lean_dec(v___y_1170_);
lean_dec_ref(v___y_1169_);
return v_res_1172_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___redArg(lean_object* v_a_1173_, lean_object* v_x_1174_){
_start:
{
if (lean_obj_tag(v_x_1174_) == 0)
{
uint8_t v___x_1175_; 
v___x_1175_ = 0;
return v___x_1175_;
}
else
{
lean_object* v_key_1176_; lean_object* v_tail_1177_; uint8_t v___x_1178_; 
v_key_1176_ = lean_ctor_get(v_x_1174_, 0);
v_tail_1177_ = lean_ctor_get(v_x_1174_, 2);
v___x_1178_ = l_Lean_ExprStructEq_beq(v_key_1176_, v_a_1173_);
if (v___x_1178_ == 0)
{
v_x_1174_ = v_tail_1177_;
goto _start;
}
else
{
return v___x_1178_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___redArg___boxed(lean_object* v_a_1180_, lean_object* v_x_1181_){
_start:
{
uint8_t v_res_1182_; lean_object* v_r_1183_; 
v_res_1182_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___redArg(v_a_1180_, v_x_1181_);
lean_dec(v_x_1181_);
lean_dec_ref(v_a_1180_);
v_r_1183_ = lean_box(v_res_1182_);
return v_r_1183_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(lean_object* v_x_1184_, lean_object* v_x_1185_){
_start:
{
if (lean_obj_tag(v_x_1185_) == 0)
{
return v_x_1184_;
}
else
{
lean_object* v_key_1186_; lean_object* v_value_1187_; lean_object* v_tail_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1211_; 
v_key_1186_ = lean_ctor_get(v_x_1185_, 0);
v_value_1187_ = lean_ctor_get(v_x_1185_, 1);
v_tail_1188_ = lean_ctor_get(v_x_1185_, 2);
v_isSharedCheck_1211_ = !lean_is_exclusive(v_x_1185_);
if (v_isSharedCheck_1211_ == 0)
{
v___x_1190_ = v_x_1185_;
v_isShared_1191_ = v_isSharedCheck_1211_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_tail_1188_);
lean_inc(v_value_1187_);
lean_inc(v_key_1186_);
lean_dec(v_x_1185_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1211_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v___x_1192_; uint64_t v___x_1193_; uint64_t v___x_1194_; uint64_t v___x_1195_; uint64_t v_fold_1196_; uint64_t v___x_1197_; uint64_t v___x_1198_; uint64_t v___x_1199_; size_t v___x_1200_; size_t v___x_1201_; size_t v___x_1202_; size_t v___x_1203_; size_t v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1207_; 
v___x_1192_ = lean_array_get_size(v_x_1184_);
v___x_1193_ = l_Lean_ExprStructEq_hash(v_key_1186_);
v___x_1194_ = 32ULL;
v___x_1195_ = lean_uint64_shift_right(v___x_1193_, v___x_1194_);
v_fold_1196_ = lean_uint64_xor(v___x_1193_, v___x_1195_);
v___x_1197_ = 16ULL;
v___x_1198_ = lean_uint64_shift_right(v_fold_1196_, v___x_1197_);
v___x_1199_ = lean_uint64_xor(v_fold_1196_, v___x_1198_);
v___x_1200_ = lean_uint64_to_usize(v___x_1199_);
v___x_1201_ = lean_usize_of_nat(v___x_1192_);
v___x_1202_ = ((size_t)1ULL);
v___x_1203_ = lean_usize_sub(v___x_1201_, v___x_1202_);
v___x_1204_ = lean_usize_land(v___x_1200_, v___x_1203_);
v___x_1205_ = lean_array_uget_borrowed(v_x_1184_, v___x_1204_);
lean_inc(v___x_1205_);
if (v_isShared_1191_ == 0)
{
lean_ctor_set(v___x_1190_, 2, v___x_1205_);
v___x_1207_ = v___x_1190_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v_key_1186_);
lean_ctor_set(v_reuseFailAlloc_1210_, 1, v_value_1187_);
lean_ctor_set(v_reuseFailAlloc_1210_, 2, v___x_1205_);
v___x_1207_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
lean_object* v___x_1208_; 
v___x_1208_ = lean_array_uset(v_x_1184_, v___x_1204_, v___x_1207_);
v_x_1184_ = v___x_1208_;
v_x_1185_ = v_tail_1188_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(lean_object* v_i_1212_, lean_object* v_source_1213_, lean_object* v_target_1214_){
_start:
{
lean_object* v___x_1215_; uint8_t v___x_1216_; 
v___x_1215_ = lean_array_get_size(v_source_1213_);
v___x_1216_ = lean_nat_dec_lt(v_i_1212_, v___x_1215_);
if (v___x_1216_ == 0)
{
lean_dec_ref(v_source_1213_);
lean_dec(v_i_1212_);
return v_target_1214_;
}
else
{
lean_object* v_es_1217_; lean_object* v___x_1218_; lean_object* v_source_1219_; lean_object* v_target_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; 
v_es_1217_ = lean_array_fget(v_source_1213_, v_i_1212_);
v___x_1218_ = lean_box(0);
v_source_1219_ = lean_array_fset(v_source_1213_, v_i_1212_, v___x_1218_);
v_target_1220_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_target_1214_, v_es_1217_);
v___x_1221_ = lean_unsigned_to_nat(1u);
v___x_1222_ = lean_nat_add(v_i_1212_, v___x_1221_);
lean_dec(v_i_1212_);
v_i_1212_ = v___x_1222_;
v_source_1213_ = v_source_1219_;
v_target_1214_ = v_target_1220_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11___redArg(lean_object* v_data_1224_){
_start:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v_nbuckets_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1225_ = lean_array_get_size(v_data_1224_);
v___x_1226_ = lean_unsigned_to_nat(2u);
v_nbuckets_1227_ = lean_nat_mul(v___x_1225_, v___x_1226_);
v___x_1228_ = lean_unsigned_to_nat(0u);
v___x_1229_ = lean_box(0);
v___x_1230_ = lean_mk_array(v_nbuckets_1227_, v___x_1229_);
v___x_1231_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v___x_1228_, v_data_1224_, v___x_1230_);
return v___x_1231_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__12___redArg(lean_object* v_a_1232_, lean_object* v_b_1233_, lean_object* v_x_1234_){
_start:
{
if (lean_obj_tag(v_x_1234_) == 0)
{
lean_dec(v_b_1233_);
lean_dec_ref(v_a_1232_);
return v_x_1234_;
}
else
{
lean_object* v_key_1235_; lean_object* v_value_1236_; lean_object* v_tail_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1249_; 
v_key_1235_ = lean_ctor_get(v_x_1234_, 0);
v_value_1236_ = lean_ctor_get(v_x_1234_, 1);
v_tail_1237_ = lean_ctor_get(v_x_1234_, 2);
v_isSharedCheck_1249_ = !lean_is_exclusive(v_x_1234_);
if (v_isSharedCheck_1249_ == 0)
{
v___x_1239_ = v_x_1234_;
v_isShared_1240_ = v_isSharedCheck_1249_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_tail_1237_);
lean_inc(v_value_1236_);
lean_inc(v_key_1235_);
lean_dec(v_x_1234_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1249_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
uint8_t v___x_1241_; 
v___x_1241_ = l_Lean_ExprStructEq_beq(v_key_1235_, v_a_1232_);
if (v___x_1241_ == 0)
{
lean_object* v___x_1242_; lean_object* v___x_1244_; 
v___x_1242_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__12___redArg(v_a_1232_, v_b_1233_, v_tail_1237_);
if (v_isShared_1240_ == 0)
{
lean_ctor_set(v___x_1239_, 2, v___x_1242_);
v___x_1244_ = v___x_1239_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v_key_1235_);
lean_ctor_set(v_reuseFailAlloc_1245_, 1, v_value_1236_);
lean_ctor_set(v_reuseFailAlloc_1245_, 2, v___x_1242_);
v___x_1244_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
return v___x_1244_;
}
}
else
{
lean_object* v___x_1247_; 
lean_dec(v_value_1236_);
lean_dec(v_key_1235_);
if (v_isShared_1240_ == 0)
{
lean_ctor_set(v___x_1239_, 1, v_b_1233_);
lean_ctor_set(v___x_1239_, 0, v_a_1232_);
v___x_1247_ = v___x_1239_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v_a_1232_);
lean_ctor_set(v_reuseFailAlloc_1248_, 1, v_b_1233_);
lean_ctor_set(v_reuseFailAlloc_1248_, 2, v_tail_1237_);
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
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6___redArg(lean_object* v_m_1250_, lean_object* v_a_1251_, lean_object* v_b_1252_){
_start:
{
lean_object* v_size_1253_; lean_object* v_buckets_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1297_; 
v_size_1253_ = lean_ctor_get(v_m_1250_, 0);
v_buckets_1254_ = lean_ctor_get(v_m_1250_, 1);
v_isSharedCheck_1297_ = !lean_is_exclusive(v_m_1250_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1256_ = v_m_1250_;
v_isShared_1257_ = v_isSharedCheck_1297_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_buckets_1254_);
lean_inc(v_size_1253_);
lean_dec(v_m_1250_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1297_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v___x_1258_; uint64_t v___x_1259_; uint64_t v___x_1260_; uint64_t v___x_1261_; uint64_t v_fold_1262_; uint64_t v___x_1263_; uint64_t v___x_1264_; uint64_t v___x_1265_; size_t v___x_1266_; size_t v___x_1267_; size_t v___x_1268_; size_t v___x_1269_; size_t v___x_1270_; lean_object* v_bkt_1271_; uint8_t v___x_1272_; 
v___x_1258_ = lean_array_get_size(v_buckets_1254_);
v___x_1259_ = l_Lean_ExprStructEq_hash(v_a_1251_);
v___x_1260_ = 32ULL;
v___x_1261_ = lean_uint64_shift_right(v___x_1259_, v___x_1260_);
v_fold_1262_ = lean_uint64_xor(v___x_1259_, v___x_1261_);
v___x_1263_ = 16ULL;
v___x_1264_ = lean_uint64_shift_right(v_fold_1262_, v___x_1263_);
v___x_1265_ = lean_uint64_xor(v_fold_1262_, v___x_1264_);
v___x_1266_ = lean_uint64_to_usize(v___x_1265_);
v___x_1267_ = lean_usize_of_nat(v___x_1258_);
v___x_1268_ = ((size_t)1ULL);
v___x_1269_ = lean_usize_sub(v___x_1267_, v___x_1268_);
v___x_1270_ = lean_usize_land(v___x_1266_, v___x_1269_);
v_bkt_1271_ = lean_array_uget_borrowed(v_buckets_1254_, v___x_1270_);
v___x_1272_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___redArg(v_a_1251_, v_bkt_1271_);
if (v___x_1272_ == 0)
{
lean_object* v___x_1273_; lean_object* v_size_x27_1274_; lean_object* v___x_1275_; lean_object* v_buckets_x27_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; uint8_t v___x_1282_; 
v___x_1273_ = lean_unsigned_to_nat(1u);
v_size_x27_1274_ = lean_nat_add(v_size_1253_, v___x_1273_);
lean_dec(v_size_1253_);
lean_inc(v_bkt_1271_);
v___x_1275_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1275_, 0, v_a_1251_);
lean_ctor_set(v___x_1275_, 1, v_b_1252_);
lean_ctor_set(v___x_1275_, 2, v_bkt_1271_);
v_buckets_x27_1276_ = lean_array_uset(v_buckets_1254_, v___x_1270_, v___x_1275_);
v___x_1277_ = lean_unsigned_to_nat(4u);
v___x_1278_ = lean_nat_mul(v_size_x27_1274_, v___x_1277_);
v___x_1279_ = lean_unsigned_to_nat(3u);
v___x_1280_ = lean_nat_div(v___x_1278_, v___x_1279_);
lean_dec(v___x_1278_);
v___x_1281_ = lean_array_get_size(v_buckets_x27_1276_);
v___x_1282_ = lean_nat_dec_le(v___x_1280_, v___x_1281_);
lean_dec(v___x_1280_);
if (v___x_1282_ == 0)
{
lean_object* v_val_1283_; lean_object* v___x_1285_; 
v_val_1283_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11___redArg(v_buckets_x27_1276_);
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 1, v_val_1283_);
lean_ctor_set(v___x_1256_, 0, v_size_x27_1274_);
v___x_1285_ = v___x_1256_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v_size_x27_1274_);
lean_ctor_set(v_reuseFailAlloc_1286_, 1, v_val_1283_);
v___x_1285_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
return v___x_1285_;
}
}
else
{
lean_object* v___x_1288_; 
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 1, v_buckets_x27_1276_);
lean_ctor_set(v___x_1256_, 0, v_size_x27_1274_);
v___x_1288_ = v___x_1256_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v_size_x27_1274_);
lean_ctor_set(v_reuseFailAlloc_1289_, 1, v_buckets_x27_1276_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
return v___x_1288_;
}
}
}
else
{
lean_object* v___x_1290_; lean_object* v_buckets_x27_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1295_; 
lean_inc(v_bkt_1271_);
v___x_1290_ = lean_box(0);
v_buckets_x27_1291_ = lean_array_uset(v_buckets_1254_, v___x_1270_, v___x_1290_);
v___x_1292_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__12___redArg(v_a_1251_, v_b_1252_, v_bkt_1271_);
v___x_1293_ = lean_array_uset(v_buckets_x27_1291_, v___x_1270_, v___x_1292_);
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 1, v___x_1293_);
v___x_1295_ = v___x_1256_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v_size_1253_);
lean_ctor_set(v_reuseFailAlloc_1296_, 1, v___x_1293_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__2(lean_object* v_a_1298_, lean_object* v_e_1299_, lean_object* v_a_1300_){
_start:
{
lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; 
v___x_1302_ = lean_st_ref_take(v_a_1298_);
v___x_1303_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6___redArg(v___x_1302_, v_e_1299_, v_a_1300_);
v___x_1304_ = lean_st_ref_put(v_a_1298_, v___x_1303_);
v___x_1305_ = lean_box(0);
return v___x_1305_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__2___boxed(lean_object* v_a_1306_, lean_object* v_e_1307_, lean_object* v_a_1308_, lean_object* v___y_1309_){
_start:
{
lean_object* v_res_1310_; 
v_res_1310_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__2(v_a_1306_, v_e_1307_, v_a_1308_);
lean_dec(v_a_1306_);
return v_res_1310_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___redArg(lean_object* v_a_1311_, lean_object* v_x_1312_){
_start:
{
if (lean_obj_tag(v_x_1312_) == 0)
{
lean_object* v___x_1313_; 
v___x_1313_ = lean_box(0);
return v___x_1313_;
}
else
{
lean_object* v_key_1314_; lean_object* v_value_1315_; lean_object* v_tail_1316_; uint8_t v___x_1317_; 
v_key_1314_ = lean_ctor_get(v_x_1312_, 0);
v_value_1315_ = lean_ctor_get(v_x_1312_, 1);
v_tail_1316_ = lean_ctor_get(v_x_1312_, 2);
v___x_1317_ = l_Lean_ExprStructEq_beq(v_key_1314_, v_a_1311_);
if (v___x_1317_ == 0)
{
v_x_1312_ = v_tail_1316_;
goto _start;
}
else
{
lean_object* v___x_1319_; 
lean_inc(v_value_1315_);
v___x_1319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1319_, 0, v_value_1315_);
return v___x_1319_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___redArg___boxed(lean_object* v_a_1320_, lean_object* v_x_1321_){
_start:
{
lean_object* v_res_1322_; 
v_res_1322_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___redArg(v_a_1320_, v_x_1321_);
lean_dec(v_x_1321_);
lean_dec_ref(v_a_1320_);
return v_res_1322_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg(lean_object* v_m_1323_, lean_object* v_a_1324_){
_start:
{
lean_object* v_buckets_1325_; lean_object* v___x_1326_; uint64_t v___x_1327_; uint64_t v___x_1328_; uint64_t v___x_1329_; uint64_t v_fold_1330_; uint64_t v___x_1331_; uint64_t v___x_1332_; uint64_t v___x_1333_; size_t v___x_1334_; size_t v___x_1335_; size_t v___x_1336_; size_t v___x_1337_; size_t v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; 
v_buckets_1325_ = lean_ctor_get(v_m_1323_, 1);
v___x_1326_ = lean_array_get_size(v_buckets_1325_);
v___x_1327_ = l_Lean_ExprStructEq_hash(v_a_1324_);
v___x_1328_ = 32ULL;
v___x_1329_ = lean_uint64_shift_right(v___x_1327_, v___x_1328_);
v_fold_1330_ = lean_uint64_xor(v___x_1327_, v___x_1329_);
v___x_1331_ = 16ULL;
v___x_1332_ = lean_uint64_shift_right(v_fold_1330_, v___x_1331_);
v___x_1333_ = lean_uint64_xor(v_fold_1330_, v___x_1332_);
v___x_1334_ = lean_uint64_to_usize(v___x_1333_);
v___x_1335_ = lean_usize_of_nat(v___x_1326_);
v___x_1336_ = ((size_t)1ULL);
v___x_1337_ = lean_usize_sub(v___x_1335_, v___x_1336_);
v___x_1338_ = lean_usize_land(v___x_1334_, v___x_1337_);
v___x_1339_ = lean_array_uget_borrowed(v_buckets_1325_, v___x_1338_);
v___x_1340_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___redArg(v_a_1324_, v___x_1339_);
return v___x_1340_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_m_1341_, lean_object* v_a_1342_){
_start:
{
lean_object* v_res_1343_; 
v_res_1343_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg(v_m_1341_, v_a_1342_);
lean_dec_ref(v_a_1342_);
lean_dec_ref(v_m_1341_);
return v_res_1343_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1(lean_object* v_pre_1344_, lean_object* v_post_1345_, size_t v_sz_1346_, size_t v_i_1347_, lean_object* v_bs_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_){
_start:
{
uint8_t v___x_1353_; 
v___x_1353_ = lean_usize_dec_lt(v_i_1347_, v_sz_1346_);
if (v___x_1353_ == 0)
{
lean_object* v___x_1354_; 
lean_dec_ref(v_post_1345_);
lean_dec_ref(v_pre_1344_);
v___x_1354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1354_, 0, v_bs_1348_);
return v___x_1354_;
}
else
{
lean_object* v_v_1355_; lean_object* v___x_1356_; 
v_v_1355_ = lean_array_uget_borrowed(v_bs_1348_, v_i_1347_);
lean_inc(v_v_1355_);
lean_inc_ref(v_post_1345_);
lean_inc_ref(v_pre_1344_);
v___x_1356_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1344_, v_post_1345_, v_v_1355_, v___y_1349_, v___y_1350_, v___y_1351_);
if (lean_obj_tag(v___x_1356_) == 0)
{
lean_object* v_a_1357_; lean_object* v___x_1358_; lean_object* v_bs_x27_1359_; size_t v___x_1360_; size_t v___x_1361_; lean_object* v___x_1362_; 
v_a_1357_ = lean_ctor_get(v___x_1356_, 0);
lean_inc(v_a_1357_);
lean_dec_ref_known(v___x_1356_, 1);
v___x_1358_ = lean_unsigned_to_nat(0u);
v_bs_x27_1359_ = lean_array_uset(v_bs_1348_, v_i_1347_, v___x_1358_);
v___x_1360_ = ((size_t)1ULL);
v___x_1361_ = lean_usize_add(v_i_1347_, v___x_1360_);
v___x_1362_ = lean_array_uset(v_bs_x27_1359_, v_i_1347_, v_a_1357_);
v_i_1347_ = v___x_1361_;
v_bs_1348_ = v___x_1362_;
goto _start;
}
else
{
lean_object* v_a_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1371_; 
lean_dec_ref(v_bs_1348_);
lean_dec_ref(v_post_1345_);
lean_dec_ref(v_pre_1344_);
v_a_1364_ = lean_ctor_get(v___x_1356_, 0);
v_isSharedCheck_1371_ = !lean_is_exclusive(v___x_1356_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1366_ = v___x_1356_;
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_a_1364_);
lean_dec(v___x_1356_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v___x_1369_; 
if (v_isShared_1367_ == 0)
{
v___x_1369_ = v___x_1366_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v_a_1364_);
v___x_1369_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
return v___x_1369_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__4(lean_object* v_pre_1372_, lean_object* v_post_1373_, lean_object* v_x_1374_, lean_object* v_x_1375_, lean_object* v_x_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_){
_start:
{
if (lean_obj_tag(v_x_1374_) == 5)
{
lean_object* v_fn_1381_; lean_object* v_arg_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; 
v_fn_1381_ = lean_ctor_get(v_x_1374_, 0);
lean_inc_ref(v_fn_1381_);
v_arg_1382_ = lean_ctor_get(v_x_1374_, 1);
lean_inc_ref(v_arg_1382_);
lean_dec_ref_known(v_x_1374_, 2);
v___x_1383_ = lean_array_set(v_x_1375_, v_x_1376_, v_arg_1382_);
v___x_1384_ = lean_unsigned_to_nat(1u);
v___x_1385_ = lean_nat_sub(v_x_1376_, v___x_1384_);
lean_dec(v_x_1376_);
v_x_1374_ = v_fn_1381_;
v_x_1375_ = v___x_1383_;
v_x_1376_ = v___x_1385_;
goto _start;
}
else
{
lean_object* v___x_1387_; 
lean_dec(v_x_1376_);
lean_inc_ref(v_post_1373_);
lean_inc_ref(v_pre_1372_);
v___x_1387_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1372_, v_post_1373_, v_x_1374_, v___y_1377_, v___y_1378_, v___y_1379_);
if (lean_obj_tag(v___x_1387_) == 0)
{
lean_object* v_a_1388_; size_t v_sz_1389_; size_t v___x_1390_; lean_object* v___x_1391_; 
v_a_1388_ = lean_ctor_get(v___x_1387_, 0);
lean_inc(v_a_1388_);
lean_dec_ref_known(v___x_1387_, 1);
v_sz_1389_ = lean_array_size(v_x_1375_);
v___x_1390_ = ((size_t)0ULL);
lean_inc_ref(v_post_1373_);
lean_inc_ref(v_pre_1372_);
v___x_1391_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1(v_pre_1372_, v_post_1373_, v_sz_1389_, v___x_1390_, v_x_1375_, v___y_1377_, v___y_1378_, v___y_1379_);
if (lean_obj_tag(v___x_1391_) == 0)
{
lean_object* v_a_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; 
v_a_1392_ = lean_ctor_get(v___x_1391_, 0);
lean_inc(v_a_1392_);
lean_dec_ref_known(v___x_1391_, 1);
v___x_1393_ = l_Lean_mkAppN(v_a_1388_, v_a_1392_);
lean_dec(v_a_1392_);
v___x_1394_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1372_, v_post_1373_, v___x_1393_, v___y_1377_, v___y_1378_, v___y_1379_);
return v___x_1394_;
}
else
{
lean_object* v_a_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1402_; 
lean_dec(v_a_1388_);
lean_dec_ref(v_post_1373_);
lean_dec_ref(v_pre_1372_);
v_a_1395_ = lean_ctor_get(v___x_1391_, 0);
v_isSharedCheck_1402_ = !lean_is_exclusive(v___x_1391_);
if (v_isSharedCheck_1402_ == 0)
{
v___x_1397_ = v___x_1391_;
v_isShared_1398_ = v_isSharedCheck_1402_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_a_1395_);
lean_dec(v___x_1391_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1402_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
lean_object* v___x_1400_; 
if (v_isShared_1398_ == 0)
{
v___x_1400_ = v___x_1397_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v_a_1395_);
v___x_1400_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
return v___x_1400_;
}
}
}
}
else
{
lean_dec_ref(v_x_1375_);
lean_dec_ref(v_post_1373_);
lean_dec_ref(v_pre_1372_);
return v___x_1387_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__1(lean_object* v___x_1403_, lean_object* v_pre_1404_, lean_object* v_e_1405_, lean_object* v_post_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_){
_start:
{
lean_object* v___x_1411_; 
v___x_1411_ = l_Lean_Core_checkSystem(v___x_1403_, v___y_1408_, v___y_1409_);
if (lean_obj_tag(v___x_1411_) == 0)
{
lean_object* v___x_1412_; 
lean_dec_ref_known(v___x_1411_, 1);
lean_inc_ref(v_pre_1404_);
lean_inc(v___y_1409_);
lean_inc_ref(v___y_1408_);
lean_inc_ref(v_e_1405_);
v___x_1412_ = lean_apply_4(v_pre_1404_, v_e_1405_, v___y_1408_, v___y_1409_, lean_box(0));
if (lean_obj_tag(v___x_1412_) == 0)
{
lean_object* v_a_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1528_; 
v_a_1413_ = lean_ctor_get(v___x_1412_, 0);
v_isSharedCheck_1528_ = !lean_is_exclusive(v___x_1412_);
if (v_isSharedCheck_1528_ == 0)
{
v___x_1415_ = v___x_1412_;
v_isShared_1416_ = v_isSharedCheck_1528_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_a_1413_);
lean_dec(v___x_1412_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1528_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___y_1418_; 
switch(lean_obj_tag(v_a_1413_))
{
case 0:
{
lean_object* v_e_1518_; lean_object* v___x_1520_; 
lean_dec_ref(v_post_1406_);
lean_dec_ref(v_e_1405_);
lean_dec_ref(v_pre_1404_);
v_e_1518_ = lean_ctor_get(v_a_1413_, 0);
lean_inc_ref(v_e_1518_);
lean_dec_ref_known(v_a_1413_, 1);
if (v_isShared_1416_ == 0)
{
lean_ctor_set(v___x_1415_, 0, v_e_1518_);
v___x_1520_ = v___x_1415_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v_e_1518_);
v___x_1520_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
return v___x_1520_;
}
}
case 1:
{
lean_object* v_e_1522_; lean_object* v___x_1523_; 
lean_del_object(v___x_1415_);
lean_dec_ref(v_e_1405_);
v_e_1522_ = lean_ctor_get(v_a_1413_, 0);
lean_inc_ref(v_e_1522_);
lean_dec_ref_known(v_a_1413_, 1);
lean_inc_ref(v_post_1406_);
lean_inc_ref(v_pre_1404_);
v___x_1523_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1404_, v_post_1406_, v_e_1522_, v___y_1407_, v___y_1408_, v___y_1409_);
if (lean_obj_tag(v___x_1523_) == 0)
{
lean_object* v_a_1524_; lean_object* v___x_1525_; 
v_a_1524_ = lean_ctor_get(v___x_1523_, 0);
lean_inc(v_a_1524_);
lean_dec_ref_known(v___x_1523_, 1);
v___x_1525_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1404_, v_post_1406_, v_a_1524_, v___y_1407_, v___y_1408_, v___y_1409_);
return v___x_1525_;
}
else
{
lean_dec_ref(v_post_1406_);
lean_dec_ref(v_pre_1404_);
return v___x_1523_;
}
}
default: 
{
lean_object* v_e_x3f_1526_; 
lean_del_object(v___x_1415_);
v_e_x3f_1526_ = lean_ctor_get(v_a_1413_, 0);
lean_inc(v_e_x3f_1526_);
lean_dec_ref_known(v_a_1413_, 1);
if (lean_obj_tag(v_e_x3f_1526_) == 0)
{
v___y_1418_ = v_e_1405_;
goto v___jp_1417_;
}
else
{
lean_object* v_val_1527_; 
lean_dec_ref(v_e_1405_);
v_val_1527_ = lean_ctor_get(v_e_x3f_1526_, 0);
lean_inc(v_val_1527_);
lean_dec_ref_known(v_e_x3f_1526_, 1);
v___y_1418_ = v_val_1527_;
goto v___jp_1417_;
}
}
}
v___jp_1417_:
{
switch(lean_obj_tag(v___y_1418_))
{
case 7:
{
lean_object* v_binderName_1419_; lean_object* v_binderType_1420_; lean_object* v_body_1421_; uint8_t v_binderInfo_1422_; lean_object* v___x_1423_; 
v_binderName_1419_ = lean_ctor_get(v___y_1418_, 0);
v_binderType_1420_ = lean_ctor_get(v___y_1418_, 1);
v_body_1421_ = lean_ctor_get(v___y_1418_, 2);
v_binderInfo_1422_ = lean_ctor_get_uint8(v___y_1418_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1420_);
lean_inc_ref(v_post_1406_);
lean_inc_ref(v_pre_1404_);
v___x_1423_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1404_, v_post_1406_, v_binderType_1420_, v___y_1407_, v___y_1408_, v___y_1409_);
if (lean_obj_tag(v___x_1423_) == 0)
{
lean_object* v_a_1424_; lean_object* v___x_1425_; 
v_a_1424_ = lean_ctor_get(v___x_1423_, 0);
lean_inc(v_a_1424_);
lean_dec_ref_known(v___x_1423_, 1);
lean_inc_ref(v_body_1421_);
lean_inc_ref(v_post_1406_);
lean_inc_ref(v_pre_1404_);
v___x_1425_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1404_, v_post_1406_, v_body_1421_, v___y_1407_, v___y_1408_, v___y_1409_);
if (lean_obj_tag(v___x_1425_) == 0)
{
lean_object* v_a_1426_; size_t v___x_1427_; size_t v___x_1428_; uint8_t v___x_1429_; 
v_a_1426_ = lean_ctor_get(v___x_1425_, 0);
lean_inc(v_a_1426_);
lean_dec_ref_known(v___x_1425_, 1);
v___x_1427_ = lean_ptr_addr(v_binderType_1420_);
v___x_1428_ = lean_ptr_addr(v_a_1424_);
v___x_1429_ = lean_usize_dec_eq(v___x_1427_, v___x_1428_);
if (v___x_1429_ == 0)
{
lean_object* v___x_1430_; lean_object* v___x_1431_; 
lean_inc(v_binderName_1419_);
lean_dec_ref_known(v___y_1418_, 3);
v___x_1430_ = l_Lean_Expr_forallE___override(v_binderName_1419_, v_a_1424_, v_a_1426_, v_binderInfo_1422_);
v___x_1431_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1404_, v_post_1406_, v___x_1430_, v___y_1407_, v___y_1408_, v___y_1409_);
return v___x_1431_;
}
else
{
size_t v___x_1432_; size_t v___x_1433_; uint8_t v___x_1434_; 
v___x_1432_ = lean_ptr_addr(v_body_1421_);
v___x_1433_ = lean_ptr_addr(v_a_1426_);
v___x_1434_ = lean_usize_dec_eq(v___x_1432_, v___x_1433_);
if (v___x_1434_ == 0)
{
lean_object* v___x_1435_; lean_object* v___x_1436_; 
lean_inc(v_binderName_1419_);
lean_dec_ref_known(v___y_1418_, 3);
v___x_1435_ = l_Lean_Expr_forallE___override(v_binderName_1419_, v_a_1424_, v_a_1426_, v_binderInfo_1422_);
v___x_1436_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1404_, v_post_1406_, v___x_1435_, v___y_1407_, v___y_1408_, v___y_1409_);
return v___x_1436_;
}
else
{
uint8_t v___x_1437_; 
v___x_1437_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1422_, v_binderInfo_1422_);
if (v___x_1437_ == 0)
{
lean_object* v___x_1438_; lean_object* v___x_1439_; 
lean_inc(v_binderName_1419_);
lean_dec_ref_known(v___y_1418_, 3);
v___x_1438_ = l_Lean_Expr_forallE___override(v_binderName_1419_, v_a_1424_, v_a_1426_, v_binderInfo_1422_);
v___x_1439_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1404_, v_post_1406_, v___x_1438_, v___y_1407_, v___y_1408_, v___y_1409_);
return v___x_1439_;
}
else
{
lean_object* v___x_1440_; 
lean_dec(v_a_1426_);
lean_dec(v_a_1424_);
v___x_1440_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1404_, v_post_1406_, v___y_1418_, v___y_1407_, v___y_1408_, v___y_1409_);
return v___x_1440_;
}
}
}
}
else
{
lean_dec(v_a_1424_);
lean_dec_ref_known(v___y_1418_, 3);
lean_dec_ref(v_post_1406_);
lean_dec_ref(v_pre_1404_);
return v___x_1425_;
}
}
else
{
lean_dec_ref_known(v___y_1418_, 3);
lean_dec_ref(v_post_1406_);
lean_dec_ref(v_pre_1404_);
return v___x_1423_;
}
}
case 6:
{
lean_object* v_binderName_1441_; lean_object* v_binderType_1442_; lean_object* v_body_1443_; uint8_t v_binderInfo_1444_; lean_object* v___x_1445_; 
v_binderName_1441_ = lean_ctor_get(v___y_1418_, 0);
v_binderType_1442_ = lean_ctor_get(v___y_1418_, 1);
v_body_1443_ = lean_ctor_get(v___y_1418_, 2);
v_binderInfo_1444_ = lean_ctor_get_uint8(v___y_1418_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1442_);
lean_inc_ref(v_post_1406_);
lean_inc_ref(v_pre_1404_);
v___x_1445_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1404_, v_post_1406_, v_binderType_1442_, v___y_1407_, v___y_1408_, v___y_1409_);
if (lean_obj_tag(v___x_1445_) == 0)
{
lean_object* v_a_1446_; lean_object* v___x_1447_; 
v_a_1446_ = lean_ctor_get(v___x_1445_, 0);
lean_inc(v_a_1446_);
lean_dec_ref_known(v___x_1445_, 1);
lean_inc_ref(v_body_1443_);
lean_inc_ref(v_post_1406_);
lean_inc_ref(v_pre_1404_);
v___x_1447_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1404_, v_post_1406_, v_body_1443_, v___y_1407_, v___y_1408_, v___y_1409_);
if (lean_obj_tag(v___x_1447_) == 0)
{
lean_object* v_a_1448_; size_t v___x_1449_; size_t v___x_1450_; uint8_t v___x_1451_; 
v_a_1448_ = lean_ctor_get(v___x_1447_, 0);
lean_inc(v_a_1448_);
lean_dec_ref_known(v___x_1447_, 1);
v___x_1449_ = lean_ptr_addr(v_binderType_1442_);
v___x_1450_ = lean_ptr_addr(v_a_1446_);
v___x_1451_ = lean_usize_dec_eq(v___x_1449_, v___x_1450_);
if (v___x_1451_ == 0)
{
lean_object* v___x_1452_; lean_object* v___x_1453_; 
lean_inc(v_binderName_1441_);
lean_dec_ref_known(v___y_1418_, 3);
v___x_1452_ = l_Lean_Expr_lam___override(v_binderName_1441_, v_a_1446_, v_a_1448_, v_binderInfo_1444_);
v___x_1453_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1404_, v_post_1406_, v___x_1452_, v___y_1407_, v___y_1408_, v___y_1409_);
return v___x_1453_;
}
else
{
size_t v___x_1454_; size_t v___x_1455_; uint8_t v___x_1456_; 
v___x_1454_ = lean_ptr_addr(v_body_1443_);
v___x_1455_ = lean_ptr_addr(v_a_1448_);
v___x_1456_ = lean_usize_dec_eq(v___x_1454_, v___x_1455_);
if (v___x_1456_ == 0)
{
lean_object* v___x_1457_; lean_object* v___x_1458_; 
lean_inc(v_binderName_1441_);
lean_dec_ref_known(v___y_1418_, 3);
v___x_1457_ = l_Lean_Expr_lam___override(v_binderName_1441_, v_a_1446_, v_a_1448_, v_binderInfo_1444_);
v___x_1458_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1404_, v_post_1406_, v___x_1457_, v___y_1407_, v___y_1408_, v___y_1409_);
return v___x_1458_;
}
else
{
uint8_t v___x_1459_; 
v___x_1459_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1444_, v_binderInfo_1444_);
if (v___x_1459_ == 0)
{
lean_object* v___x_1460_; lean_object* v___x_1461_; 
lean_inc(v_binderName_1441_);
lean_dec_ref_known(v___y_1418_, 3);
v___x_1460_ = l_Lean_Expr_lam___override(v_binderName_1441_, v_a_1446_, v_a_1448_, v_binderInfo_1444_);
v___x_1461_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1404_, v_post_1406_, v___x_1460_, v___y_1407_, v___y_1408_, v___y_1409_);
return v___x_1461_;
}
else
{
lean_object* v___x_1462_; 
lean_dec(v_a_1448_);
lean_dec(v_a_1446_);
v___x_1462_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1404_, v_post_1406_, v___y_1418_, v___y_1407_, v___y_1408_, v___y_1409_);
return v___x_1462_;
}
}
}
}
else
{
lean_dec(v_a_1446_);
lean_dec_ref_known(v___y_1418_, 3);
lean_dec_ref(v_post_1406_);
lean_dec_ref(v_pre_1404_);
return v___x_1447_;
}
}
else
{
lean_dec_ref_known(v___y_1418_, 3);
lean_dec_ref(v_post_1406_);
lean_dec_ref(v_pre_1404_);
return v___x_1445_;
}
}
case 8:
{
lean_object* v_declName_1463_; lean_object* v_type_1464_; lean_object* v_value_1465_; lean_object* v_body_1466_; uint8_t v_nondep_1467_; lean_object* v___x_1468_; 
v_declName_1463_ = lean_ctor_get(v___y_1418_, 0);
v_type_1464_ = lean_ctor_get(v___y_1418_, 1);
v_value_1465_ = lean_ctor_get(v___y_1418_, 2);
v_body_1466_ = lean_ctor_get(v___y_1418_, 3);
v_nondep_1467_ = lean_ctor_get_uint8(v___y_1418_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_1464_);
lean_inc_ref(v_post_1406_);
lean_inc_ref(v_pre_1404_);
v___x_1468_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1404_, v_post_1406_, v_type_1464_, v___y_1407_, v___y_1408_, v___y_1409_);
if (lean_obj_tag(v___x_1468_) == 0)
{
lean_object* v_a_1469_; lean_object* v___x_1470_; 
v_a_1469_ = lean_ctor_get(v___x_1468_, 0);
lean_inc(v_a_1469_);
lean_dec_ref_known(v___x_1468_, 1);
lean_inc_ref(v_value_1465_);
lean_inc_ref(v_post_1406_);
lean_inc_ref(v_pre_1404_);
v___x_1470_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1404_, v_post_1406_, v_value_1465_, v___y_1407_, v___y_1408_, v___y_1409_);
if (lean_obj_tag(v___x_1470_) == 0)
{
lean_object* v_a_1471_; lean_object* v___x_1472_; 
v_a_1471_ = lean_ctor_get(v___x_1470_, 0);
lean_inc(v_a_1471_);
lean_dec_ref_known(v___x_1470_, 1);
lean_inc_ref(v_body_1466_);
lean_inc_ref(v_post_1406_);
lean_inc_ref(v_pre_1404_);
v___x_1472_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1404_, v_post_1406_, v_body_1466_, v___y_1407_, v___y_1408_, v___y_1409_);
if (lean_obj_tag(v___x_1472_) == 0)
{
lean_object* v_a_1473_; size_t v___x_1474_; size_t v___x_1475_; uint8_t v___x_1476_; 
v_a_1473_ = lean_ctor_get(v___x_1472_, 0);
lean_inc(v_a_1473_);
lean_dec_ref_known(v___x_1472_, 1);
v___x_1474_ = lean_ptr_addr(v_type_1464_);
v___x_1475_ = lean_ptr_addr(v_a_1469_);
v___x_1476_ = lean_usize_dec_eq(v___x_1474_, v___x_1475_);
if (v___x_1476_ == 0)
{
lean_object* v___x_1477_; lean_object* v___x_1478_; 
lean_inc(v_declName_1463_);
lean_dec_ref_known(v___y_1418_, 4);
v___x_1477_ = l_Lean_Expr_letE___override(v_declName_1463_, v_a_1469_, v_a_1471_, v_a_1473_, v_nondep_1467_);
v___x_1478_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1404_, v_post_1406_, v___x_1477_, v___y_1407_, v___y_1408_, v___y_1409_);
return v___x_1478_;
}
else
{
size_t v___x_1479_; size_t v___x_1480_; uint8_t v___x_1481_; 
v___x_1479_ = lean_ptr_addr(v_value_1465_);
v___x_1480_ = lean_ptr_addr(v_a_1471_);
v___x_1481_ = lean_usize_dec_eq(v___x_1479_, v___x_1480_);
if (v___x_1481_ == 0)
{
lean_object* v___x_1482_; lean_object* v___x_1483_; 
lean_inc(v_declName_1463_);
lean_dec_ref_known(v___y_1418_, 4);
v___x_1482_ = l_Lean_Expr_letE___override(v_declName_1463_, v_a_1469_, v_a_1471_, v_a_1473_, v_nondep_1467_);
v___x_1483_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1404_, v_post_1406_, v___x_1482_, v___y_1407_, v___y_1408_, v___y_1409_);
return v___x_1483_;
}
else
{
size_t v___x_1484_; size_t v___x_1485_; uint8_t v___x_1486_; 
v___x_1484_ = lean_ptr_addr(v_body_1466_);
v___x_1485_ = lean_ptr_addr(v_a_1473_);
v___x_1486_ = lean_usize_dec_eq(v___x_1484_, v___x_1485_);
if (v___x_1486_ == 0)
{
lean_object* v___x_1487_; lean_object* v___x_1488_; 
lean_inc(v_declName_1463_);
lean_dec_ref_known(v___y_1418_, 4);
v___x_1487_ = l_Lean_Expr_letE___override(v_declName_1463_, v_a_1469_, v_a_1471_, v_a_1473_, v_nondep_1467_);
v___x_1488_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1404_, v_post_1406_, v___x_1487_, v___y_1407_, v___y_1408_, v___y_1409_);
return v___x_1488_;
}
else
{
lean_object* v___x_1489_; 
lean_dec(v_a_1473_);
lean_dec(v_a_1471_);
lean_dec(v_a_1469_);
v___x_1489_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1404_, v_post_1406_, v___y_1418_, v___y_1407_, v___y_1408_, v___y_1409_);
return v___x_1489_;
}
}
}
}
else
{
lean_dec(v_a_1471_);
lean_dec(v_a_1469_);
lean_dec_ref_known(v___y_1418_, 4);
lean_dec_ref(v_post_1406_);
lean_dec_ref(v_pre_1404_);
return v___x_1472_;
}
}
else
{
lean_dec(v_a_1469_);
lean_dec_ref_known(v___y_1418_, 4);
lean_dec_ref(v_post_1406_);
lean_dec_ref(v_pre_1404_);
return v___x_1470_;
}
}
else
{
lean_dec_ref_known(v___y_1418_, 4);
lean_dec_ref(v_post_1406_);
lean_dec_ref(v_pre_1404_);
return v___x_1468_;
}
}
case 5:
{
lean_object* v_dummy_1490_; lean_object* v_nargs_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; 
v_dummy_1490_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_1491_ = l_Lean_Expr_getAppNumArgs(v___y_1418_);
lean_inc(v_nargs_1491_);
v___x_1492_ = lean_mk_array(v_nargs_1491_, v_dummy_1490_);
v___x_1493_ = lean_unsigned_to_nat(1u);
v___x_1494_ = lean_nat_sub(v_nargs_1491_, v___x_1493_);
lean_dec(v_nargs_1491_);
v___x_1495_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__4(v_pre_1404_, v_post_1406_, v___y_1418_, v___x_1492_, v___x_1494_, v___y_1407_, v___y_1408_, v___y_1409_);
return v___x_1495_;
}
case 10:
{
lean_object* v_data_1496_; lean_object* v_expr_1497_; lean_object* v___x_1498_; 
v_data_1496_ = lean_ctor_get(v___y_1418_, 0);
v_expr_1497_ = lean_ctor_get(v___y_1418_, 1);
lean_inc_ref(v_expr_1497_);
lean_inc_ref(v_post_1406_);
lean_inc_ref(v_pre_1404_);
v___x_1498_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1404_, v_post_1406_, v_expr_1497_, v___y_1407_, v___y_1408_, v___y_1409_);
if (lean_obj_tag(v___x_1498_) == 0)
{
lean_object* v_a_1499_; size_t v___x_1500_; size_t v___x_1501_; uint8_t v___x_1502_; 
v_a_1499_ = lean_ctor_get(v___x_1498_, 0);
lean_inc(v_a_1499_);
lean_dec_ref_known(v___x_1498_, 1);
v___x_1500_ = lean_ptr_addr(v_expr_1497_);
v___x_1501_ = lean_ptr_addr(v_a_1499_);
v___x_1502_ = lean_usize_dec_eq(v___x_1500_, v___x_1501_);
if (v___x_1502_ == 0)
{
lean_object* v___x_1503_; lean_object* v___x_1504_; 
lean_inc(v_data_1496_);
lean_dec_ref_known(v___y_1418_, 2);
v___x_1503_ = l_Lean_Expr_mdata___override(v_data_1496_, v_a_1499_);
v___x_1504_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1404_, v_post_1406_, v___x_1503_, v___y_1407_, v___y_1408_, v___y_1409_);
return v___x_1504_;
}
else
{
lean_object* v___x_1505_; 
lean_dec(v_a_1499_);
v___x_1505_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1404_, v_post_1406_, v___y_1418_, v___y_1407_, v___y_1408_, v___y_1409_);
return v___x_1505_;
}
}
else
{
lean_dec_ref_known(v___y_1418_, 2);
lean_dec_ref(v_post_1406_);
lean_dec_ref(v_pre_1404_);
return v___x_1498_;
}
}
case 11:
{
lean_object* v_typeName_1506_; lean_object* v_idx_1507_; lean_object* v_struct_1508_; lean_object* v___x_1509_; 
v_typeName_1506_ = lean_ctor_get(v___y_1418_, 0);
v_idx_1507_ = lean_ctor_get(v___y_1418_, 1);
v_struct_1508_ = lean_ctor_get(v___y_1418_, 2);
lean_inc_ref(v_struct_1508_);
lean_inc_ref(v_post_1406_);
lean_inc_ref(v_pre_1404_);
v___x_1509_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1404_, v_post_1406_, v_struct_1508_, v___y_1407_, v___y_1408_, v___y_1409_);
if (lean_obj_tag(v___x_1509_) == 0)
{
lean_object* v_a_1510_; size_t v___x_1511_; size_t v___x_1512_; uint8_t v___x_1513_; 
v_a_1510_ = lean_ctor_get(v___x_1509_, 0);
lean_inc(v_a_1510_);
lean_dec_ref_known(v___x_1509_, 1);
v___x_1511_ = lean_ptr_addr(v_struct_1508_);
v___x_1512_ = lean_ptr_addr(v_a_1510_);
v___x_1513_ = lean_usize_dec_eq(v___x_1511_, v___x_1512_);
if (v___x_1513_ == 0)
{
lean_object* v___x_1514_; lean_object* v___x_1515_; 
lean_inc(v_idx_1507_);
lean_inc(v_typeName_1506_);
lean_dec_ref_known(v___y_1418_, 3);
v___x_1514_ = l_Lean_Expr_proj___override(v_typeName_1506_, v_idx_1507_, v_a_1510_);
v___x_1515_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1404_, v_post_1406_, v___x_1514_, v___y_1407_, v___y_1408_, v___y_1409_);
return v___x_1515_;
}
else
{
lean_object* v___x_1516_; 
lean_dec(v_a_1510_);
v___x_1516_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1404_, v_post_1406_, v___y_1418_, v___y_1407_, v___y_1408_, v___y_1409_);
return v___x_1516_;
}
}
else
{
lean_dec_ref_known(v___y_1418_, 3);
lean_dec_ref(v_post_1406_);
lean_dec_ref(v_pre_1404_);
return v___x_1509_;
}
}
default: 
{
lean_object* v___x_1517_; 
v___x_1517_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1404_, v_post_1406_, v___y_1418_, v___y_1407_, v___y_1408_, v___y_1409_);
return v___x_1517_;
}
}
}
}
}
else
{
lean_object* v_a_1529_; lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1536_; 
lean_dec_ref(v_post_1406_);
lean_dec_ref(v_e_1405_);
lean_dec_ref(v_pre_1404_);
v_a_1529_ = lean_ctor_get(v___x_1412_, 0);
v_isSharedCheck_1536_ = !lean_is_exclusive(v___x_1412_);
if (v_isSharedCheck_1536_ == 0)
{
v___x_1531_ = v___x_1412_;
v_isShared_1532_ = v_isSharedCheck_1536_;
goto v_resetjp_1530_;
}
else
{
lean_inc(v_a_1529_);
lean_dec(v___x_1412_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1536_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
lean_object* v___x_1534_; 
if (v_isShared_1532_ == 0)
{
v___x_1534_ = v___x_1531_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v_a_1529_);
v___x_1534_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
return v___x_1534_;
}
}
}
}
else
{
lean_object* v_a_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1544_; 
lean_dec_ref(v_post_1406_);
lean_dec_ref(v_e_1405_);
lean_dec_ref(v_pre_1404_);
v_a_1537_ = lean_ctor_get(v___x_1411_, 0);
v_isSharedCheck_1544_ = !lean_is_exclusive(v___x_1411_);
if (v_isSharedCheck_1544_ == 0)
{
v___x_1539_ = v___x_1411_;
v_isShared_1540_ = v_isSharedCheck_1544_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_a_1537_);
lean_dec(v___x_1411_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1544_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
lean_object* v___x_1542_; 
if (v_isShared_1540_ == 0)
{
v___x_1542_ = v___x_1539_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v_a_1537_);
v___x_1542_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
return v___x_1542_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__1___boxed(lean_object* v___x_1545_, lean_object* v_pre_1546_, lean_object* v_e_1547_, lean_object* v_post_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_){
_start:
{
lean_object* v_res_1553_; 
v_res_1553_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__1(v___x_1545_, v_pre_1546_, v_e_1547_, v_post_1548_, v___y_1549_, v___y_1550_, v___y_1551_);
lean_dec(v___y_1551_);
lean_dec_ref(v___y_1550_);
lean_dec(v___y_1549_);
return v_res_1553_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(lean_object* v_pre_1554_, lean_object* v_post_1555_, lean_object* v_e_1556_, lean_object* v_a_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_){
_start:
{
lean_object* v___x_1561_; lean_object* v___x_1562_; 
lean_inc(v_a_1557_);
v___x_1561_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1561_, 0, lean_box(0));
lean_closure_set(v___x_1561_, 1, lean_box(0));
lean_closure_set(v___x_1561_, 2, v_a_1557_);
v___x_1562_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__0(lean_box(0), v___x_1561_, v___y_1558_, v___y_1559_);
if (lean_obj_tag(v___x_1562_) == 0)
{
lean_object* v_a_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1594_; 
v_a_1563_ = lean_ctor_get(v___x_1562_, 0);
v_isSharedCheck_1594_ = !lean_is_exclusive(v___x_1562_);
if (v_isSharedCheck_1594_ == 0)
{
v___x_1565_ = v___x_1562_;
v_isShared_1566_ = v_isSharedCheck_1594_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_a_1563_);
lean_dec(v___x_1562_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1594_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
lean_object* v___x_1567_; 
v___x_1567_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg(v_a_1563_, v_e_1556_);
lean_dec(v_a_1563_);
if (lean_obj_tag(v___x_1567_) == 0)
{
lean_object* v___x_1568_; lean_object* v___f_1569_; lean_object* v___x_1570_; 
lean_del_object(v___x_1565_);
v___x_1568_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__19___closed__0));
lean_inc_ref(v_e_1556_);
v___f_1569_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__1___boxed), 8, 4);
lean_closure_set(v___f_1569_, 0, v___x_1568_);
lean_closure_set(v___f_1569_, 1, v_pre_1554_);
lean_closure_set(v___f_1569_, 2, v_e_1556_);
lean_closure_set(v___f_1569_, 3, v_post_1555_);
v___x_1570_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___redArg(v___f_1569_, v_a_1557_, v___y_1558_, v___y_1559_);
if (lean_obj_tag(v___x_1570_) == 0)
{
lean_object* v_a_1571_; lean_object* v___f_1572_; lean_object* v___x_1573_; 
v_a_1571_ = lean_ctor_get(v___x_1570_, 0);
lean_inc_n(v_a_1571_, 2);
lean_dec_ref_known(v___x_1570_, 1);
lean_inc(v_a_1557_);
v___f_1572_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1572_, 0, v_a_1557_);
lean_closure_set(v___f_1572_, 1, v_e_1556_);
lean_closure_set(v___f_1572_, 2, v_a_1571_);
v___x_1573_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__0(lean_box(0), v___f_1572_, v___y_1558_, v___y_1559_);
if (lean_obj_tag(v___x_1573_) == 0)
{
lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1580_; 
v_isSharedCheck_1580_ = !lean_is_exclusive(v___x_1573_);
if (v_isSharedCheck_1580_ == 0)
{
lean_object* v_unused_1581_; 
v_unused_1581_ = lean_ctor_get(v___x_1573_, 0);
lean_dec(v_unused_1581_);
v___x_1575_ = v___x_1573_;
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
else
{
lean_dec(v___x_1573_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
lean_object* v___x_1578_; 
if (v_isShared_1576_ == 0)
{
lean_ctor_set(v___x_1575_, 0, v_a_1571_);
v___x_1578_ = v___x_1575_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v_a_1571_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
return v___x_1578_;
}
}
}
else
{
lean_object* v_a_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1589_; 
lean_dec(v_a_1571_);
v_a_1582_ = lean_ctor_get(v___x_1573_, 0);
v_isSharedCheck_1589_ = !lean_is_exclusive(v___x_1573_);
if (v_isSharedCheck_1589_ == 0)
{
v___x_1584_ = v___x_1573_;
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_a_1582_);
lean_dec(v___x_1573_);
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
else
{
lean_dec_ref(v_e_1556_);
return v___x_1570_;
}
}
else
{
lean_object* v_val_1590_; lean_object* v___x_1592_; 
lean_dec_ref(v_e_1556_);
lean_dec_ref(v_post_1555_);
lean_dec_ref(v_pre_1554_);
v_val_1590_ = lean_ctor_get(v___x_1567_, 0);
lean_inc(v_val_1590_);
lean_dec_ref_known(v___x_1567_, 1);
if (v_isShared_1566_ == 0)
{
lean_ctor_set(v___x_1565_, 0, v_val_1590_);
v___x_1592_ = v___x_1565_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v_val_1590_);
v___x_1592_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
return v___x_1592_;
}
}
}
}
else
{
lean_object* v_a_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1602_; 
lean_dec_ref(v_e_1556_);
lean_dec_ref(v_post_1555_);
lean_dec_ref(v_pre_1554_);
v_a_1595_ = lean_ctor_get(v___x_1562_, 0);
v_isSharedCheck_1602_ = !lean_is_exclusive(v___x_1562_);
if (v_isSharedCheck_1602_ == 0)
{
v___x_1597_ = v___x_1562_;
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_a_1595_);
lean_dec(v___x_1562_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v___x_1600_; 
if (v_isShared_1598_ == 0)
{
v___x_1600_ = v___x_1597_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v_a_1595_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
return v___x_1600_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(lean_object* v_pre_1603_, lean_object* v_post_1604_, lean_object* v_e_1605_, lean_object* v_a_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_){
_start:
{
lean_object* v___x_1610_; 
lean_inc_ref(v_post_1604_);
lean_inc(v___y_1608_);
lean_inc_ref(v___y_1607_);
lean_inc_ref(v_e_1605_);
v___x_1610_ = lean_apply_4(v_post_1604_, v_e_1605_, v___y_1607_, v___y_1608_, lean_box(0));
if (lean_obj_tag(v___x_1610_) == 0)
{
lean_object* v_a_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1629_; 
v_a_1611_ = lean_ctor_get(v___x_1610_, 0);
v_isSharedCheck_1629_ = !lean_is_exclusive(v___x_1610_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1613_ = v___x_1610_;
v_isShared_1614_ = v_isSharedCheck_1629_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_a_1611_);
lean_dec(v___x_1610_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1629_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
switch(lean_obj_tag(v_a_1611_))
{
case 0:
{
lean_object* v_e_1615_; lean_object* v___x_1617_; 
lean_dec_ref(v_e_1605_);
lean_dec_ref(v_post_1604_);
lean_dec_ref(v_pre_1603_);
v_e_1615_ = lean_ctor_get(v_a_1611_, 0);
lean_inc_ref(v_e_1615_);
lean_dec_ref_known(v_a_1611_, 1);
if (v_isShared_1614_ == 0)
{
lean_ctor_set(v___x_1613_, 0, v_e_1615_);
v___x_1617_ = v___x_1613_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v_e_1615_);
v___x_1617_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
return v___x_1617_;
}
}
case 1:
{
lean_object* v_e_1619_; lean_object* v___x_1620_; 
lean_del_object(v___x_1613_);
lean_dec_ref(v_e_1605_);
v_e_1619_ = lean_ctor_get(v_a_1611_, 0);
lean_inc_ref(v_e_1619_);
lean_dec_ref_known(v_a_1611_, 1);
v___x_1620_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1603_, v_post_1604_, v_e_1619_, v_a_1606_, v___y_1607_, v___y_1608_);
return v___x_1620_;
}
default: 
{
lean_object* v_e_x3f_1621_; 
lean_dec_ref(v_post_1604_);
lean_dec_ref(v_pre_1603_);
v_e_x3f_1621_ = lean_ctor_get(v_a_1611_, 0);
lean_inc(v_e_x3f_1621_);
lean_dec_ref_known(v_a_1611_, 1);
if (lean_obj_tag(v_e_x3f_1621_) == 0)
{
lean_object* v___x_1623_; 
if (v_isShared_1614_ == 0)
{
lean_ctor_set(v___x_1613_, 0, v_e_1605_);
v___x_1623_ = v___x_1613_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v_e_1605_);
v___x_1623_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
return v___x_1623_;
}
}
else
{
lean_object* v_val_1625_; lean_object* v___x_1627_; 
lean_dec_ref(v_e_1605_);
v_val_1625_ = lean_ctor_get(v_e_x3f_1621_, 0);
lean_inc(v_val_1625_);
lean_dec_ref_known(v_e_x3f_1621_, 1);
if (v_isShared_1614_ == 0)
{
lean_ctor_set(v___x_1613_, 0, v_val_1625_);
v___x_1627_ = v___x_1613_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_val_1625_);
v___x_1627_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
return v___x_1627_;
}
}
}
}
}
}
else
{
lean_object* v_a_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1637_; 
lean_dec_ref(v_e_1605_);
lean_dec_ref(v_post_1604_);
lean_dec_ref(v_pre_1603_);
v_a_1630_ = lean_ctor_get(v___x_1610_, 0);
v_isSharedCheck_1637_ = !lean_is_exclusive(v___x_1610_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1632_ = v___x_1610_;
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_a_1630_);
lean_dec(v___x_1610_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v___x_1635_; 
if (v_isShared_1633_ == 0)
{
v___x_1635_ = v___x_1632_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_a_1630_);
v___x_1635_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
return v___x_1635_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_1638_, lean_object* v_post_1639_, lean_object* v_e_1640_, lean_object* v_a_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_){
_start:
{
lean_object* v_res_1645_; 
v_res_1645_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1638_, v_post_1639_, v_e_1640_, v_a_1641_, v___y_1642_, v___y_1643_);
lean_dec(v___y_1643_);
lean_dec_ref(v___y_1642_);
lean_dec(v_a_1641_);
return v_res_1645_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_1646_, lean_object* v_post_1647_, lean_object* v_sz_1648_, lean_object* v_i_1649_, lean_object* v_bs_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_){
_start:
{
size_t v_sz_boxed_1655_; size_t v_i_boxed_1656_; lean_object* v_res_1657_; 
v_sz_boxed_1655_ = lean_unbox_usize(v_sz_1648_);
lean_dec(v_sz_1648_);
v_i_boxed_1656_ = lean_unbox_usize(v_i_1649_);
lean_dec(v_i_1649_);
v_res_1657_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1(v_pre_1646_, v_post_1647_, v_sz_boxed_1655_, v_i_boxed_1656_, v_bs_1650_, v___y_1651_, v___y_1652_, v___y_1653_);
lean_dec(v___y_1653_);
lean_dec_ref(v___y_1652_);
lean_dec(v___y_1651_);
return v_res_1657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__4___boxed(lean_object* v_pre_1658_, lean_object* v_post_1659_, lean_object* v_x_1660_, lean_object* v_x_1661_, lean_object* v_x_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_){
_start:
{
lean_object* v_res_1667_; 
v_res_1667_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__4(v_pre_1658_, v_post_1659_, v_x_1660_, v_x_1661_, v_x_1662_, v___y_1663_, v___y_1664_, v___y_1665_);
lean_dec(v___y_1665_);
lean_dec_ref(v___y_1664_);
lean_dec(v___y_1663_);
return v_res_1667_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___boxed(lean_object* v_pre_1668_, lean_object* v_post_1669_, lean_object* v_e_1670_, lean_object* v_a_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_){
_start:
{
lean_object* v_res_1675_; 
v_res_1675_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1668_, v_post_1669_, v_e_1670_, v_a_1671_, v___y_1672_, v___y_1673_);
lean_dec(v___y_1673_);
lean_dec_ref(v___y_1672_);
lean_dec(v_a_1671_);
return v_res_1675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___lam__0(lean_object* v_00_u03b1_1676_, lean_object* v_x_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_){
_start:
{
lean_object* v___x_1681_; lean_object* v___x_1682_; 
v___x_1681_ = lean_apply_1(v_x_1677_, lean_box(0));
v___x_1682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1682_, 0, v___x_1681_);
return v___x_1682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___lam__0___boxed(lean_object* v_00_u03b1_1683_, lean_object* v_x_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_){
_start:
{
lean_object* v_res_1688_; 
v_res_1688_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___lam__0(v_00_u03b1_1683_, v_x_1684_, v___y_1685_, v___y_1686_);
lean_dec(v___y_1686_);
lean_dec_ref(v___y_1685_);
return v_res_1688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(lean_object* v_input_1689_, lean_object* v_pre_1690_, lean_object* v_post_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_){
_start:
{
lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v_a_1697_; lean_object* v___x_1698_; 
v___x_1695_ = lean_obj_once(&l_Lean_Core_transform___redArg___closed__2, &l_Lean_Core_transform___redArg___closed__2_once, _init_l_Lean_Core_transform___redArg___closed__2);
v___x_1696_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___lam__0(lean_box(0), v___x_1695_, v___y_1692_, v___y_1693_);
v_a_1697_ = lean_ctor_get(v___x_1696_, 0);
lean_inc(v_a_1697_);
lean_dec_ref(v___x_1696_);
v___x_1698_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1690_, v_post_1691_, v_input_1689_, v_a_1697_, v___y_1692_, v___y_1693_);
if (lean_obj_tag(v___x_1698_) == 0)
{
lean_object* v_a_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1708_; 
v_a_1699_ = lean_ctor_get(v___x_1698_, 0);
lean_inc(v_a_1699_);
lean_dec_ref_known(v___x_1698_, 1);
v___x_1700_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1700_, 0, lean_box(0));
lean_closure_set(v___x_1700_, 1, lean_box(0));
lean_closure_set(v___x_1700_, 2, v_a_1697_);
v___x_1701_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___lam__0(lean_box(0), v___x_1700_, v___y_1692_, v___y_1693_);
v_isSharedCheck_1708_ = !lean_is_exclusive(v___x_1701_);
if (v_isSharedCheck_1708_ == 0)
{
lean_object* v_unused_1709_; 
v_unused_1709_ = lean_ctor_get(v___x_1701_, 0);
lean_dec(v_unused_1709_);
v___x_1703_ = v___x_1701_;
v_isShared_1704_ = v_isSharedCheck_1708_;
goto v_resetjp_1702_;
}
else
{
lean_dec(v___x_1701_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1708_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
lean_object* v___x_1706_; 
if (v_isShared_1704_ == 0)
{
lean_ctor_set(v___x_1703_, 0, v_a_1699_);
v___x_1706_ = v___x_1703_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v_a_1699_);
v___x_1706_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
return v___x_1706_;
}
}
}
else
{
lean_dec(v_a_1697_);
return v___x_1698_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___boxed(lean_object* v_input_1710_, lean_object* v_pre_1711_, lean_object* v_post_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_){
_start:
{
lean_object* v_res_1716_; 
v_res_1716_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_input_1710_, v_pre_1711_, v_post_1712_, v___y_1713_, v___y_1714_);
lean_dec(v___y_1714_);
lean_dec_ref(v___y_1713_);
return v_res_1716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_betaReduce(lean_object* v_e_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_){
_start:
{
lean_object* v___f_1723_; lean_object* v___f_1724_; lean_object* v___x_1725_; 
v___f_1723_ = ((lean_object*)(l_Lean_Core_betaReduce___closed__0));
v___f_1724_ = ((lean_object*)(l_Lean_Core_betaReduce___closed__1));
v___x_1725_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_1719_, v___f_1723_, v___f_1724_, v_a_1720_, v_a_1721_);
return v___x_1725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_betaReduce___boxed(lean_object* v_e_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_){
_start:
{
lean_object* v_res_1730_; 
v_res_1730_ = l_Lean_Core_betaReduce(v_e_1726_, v_a_1727_, v_a_1728_);
lean_dec(v_a_1728_);
lean_dec_ref(v_a_1727_);
return v_res_1730_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_1731_, lean_object* v_m_1732_, lean_object* v_a_1733_){
_start:
{
lean_object* v___x_1734_; 
v___x_1734_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg(v_m_1732_, v_a_1733_);
return v___x_1734_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_1735_, lean_object* v_m_1736_, lean_object* v_a_1737_){
_start:
{
lean_object* v_res_1738_; 
v_res_1738_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3(v_00_u03b2_1735_, v_m_1736_, v_a_1737_);
lean_dec_ref(v_a_1737_);
lean_dec_ref(v_m_1736_);
return v_res_1738_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_1739_, lean_object* v_ref_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_){
_start:
{
lean_object* v___x_1744_; 
v___x_1744_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_1740_);
return v___x_1744_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1745_, lean_object* v_ref_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_){
_start:
{
lean_object* v_res_1750_; 
v_res_1750_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_1745_, v_ref_1746_, v___y_1747_, v___y_1748_);
lean_dec(v___y_1748_);
lean_dec_ref(v___y_1747_);
return v_res_1750_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8(lean_object* v_00_u03b1_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_){
_start:
{
lean_object* v___x_1755_; 
v___x_1755_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___redArg();
return v___x_1755_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___boxed(lean_object* v_00_u03b1_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_){
_start:
{
lean_object* v_res_1760_; 
v_res_1760_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8(v_00_u03b1_1756_, v___y_1757_, v___y_1758_);
lean_dec(v___y_1758_);
lean_dec_ref(v___y_1757_);
return v_res_1760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5(lean_object* v_00_u03b1_1761_, lean_object* v_x_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_){
_start:
{
lean_object* v___x_1767_; 
v___x_1767_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___redArg(v_x_1762_, v___y_1763_, v___y_1764_, v___y_1765_);
return v___x_1767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b1_1768_, lean_object* v_x_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_){
_start:
{
lean_object* v_res_1774_; 
v_res_1774_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5(v_00_u03b1_1768_, v_x_1769_, v___y_1770_, v___y_1771_, v___y_1772_);
lean_dec(v___y_1772_);
lean_dec_ref(v___y_1771_);
lean_dec(v___y_1770_);
return v_res_1774_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6(lean_object* v_00_u03b2_1775_, lean_object* v_m_1776_, lean_object* v_a_1777_, lean_object* v_b_1778_){
_start:
{
lean_object* v___x_1779_; 
v___x_1779_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6___redArg(v_m_1776_, v_a_1777_, v_b_1778_);
return v___x_1779_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4(lean_object* v_00_u03b2_1780_, lean_object* v_a_1781_, lean_object* v_x_1782_){
_start:
{
lean_object* v___x_1783_; 
v___x_1783_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___redArg(v_a_1781_, v_x_1782_);
return v___x_1783_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___boxed(lean_object* v_00_u03b2_1784_, lean_object* v_a_1785_, lean_object* v_x_1786_){
_start:
{
lean_object* v_res_1787_; 
v_res_1787_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4(v_00_u03b2_1784_, v_a_1785_, v_x_1786_);
lean_dec(v_x_1786_);
lean_dec_ref(v_a_1785_);
return v_res_1787_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10(lean_object* v_00_u03b2_1788_, lean_object* v_a_1789_, lean_object* v_x_1790_){
_start:
{
uint8_t v___x_1791_; 
v___x_1791_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___redArg(v_a_1789_, v_x_1790_);
return v___x_1791_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___boxed(lean_object* v_00_u03b2_1792_, lean_object* v_a_1793_, lean_object* v_x_1794_){
_start:
{
uint8_t v_res_1795_; lean_object* v_r_1796_; 
v_res_1795_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10(v_00_u03b2_1792_, v_a_1793_, v_x_1794_);
lean_dec(v_x_1794_);
lean_dec_ref(v_a_1793_);
v_r_1796_ = lean_box(v_res_1795_);
return v_r_1796_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11(lean_object* v_00_u03b2_1797_, lean_object* v_data_1798_){
_start:
{
lean_object* v___x_1799_; 
v___x_1799_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11___redArg(v_data_1798_);
return v___x_1799_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__12(lean_object* v_00_u03b2_1800_, lean_object* v_a_1801_, lean_object* v_b_1802_, lean_object* v_x_1803_){
_start:
{
lean_object* v___x_1804_; 
v___x_1804_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__12___redArg(v_a_1801_, v_b_1802_, v_x_1803_);
return v___x_1804_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12(lean_object* v_00_u03b2_1805_, lean_object* v_i_1806_, lean_object* v_source_1807_, lean_object* v_target_1808_){
_start:
{
lean_object* v___x_1809_; 
v___x_1809_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v_i_1806_, v_source_1807_, v_target_1808_);
return v___x_1809_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13(lean_object* v_00_u03b2_1810_, lean_object* v_x_1811_, lean_object* v_x_1812_){
_start:
{
lean_object* v___x_1813_; 
v___x_1813_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_x_1811_, v_x_1812_);
return v___x_1813_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__0(lean_object* v_toApplicative_1814_, lean_object* v_a_1815_){
_start:
{
lean_object* v_toPure_1816_; lean_object* v___x_1817_; 
v_toPure_1816_ = lean_ctor_get(v_toApplicative_1814_, 1);
lean_inc(v_toPure_1816_);
lean_dec_ref(v_toApplicative_1814_);
v___x_1817_ = lean_apply_2(v_toPure_1816_, lean_box(0), v_a_1815_);
return v___x_1817_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__13(lean_object* v___x_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_){
_start:
{
lean_object* v___x_1824_; 
v___x_1824_ = l_Lean_Core_checkSystem(v___x_1818_, v___y_1821_, v___y_1822_);
return v___x_1824_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__13___boxed(lean_object* v___x_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_){
_start:
{
lean_object* v_res_1831_; 
v_res_1831_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__13(v___x_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_);
lean_dec(v___y_1829_);
lean_dec_ref(v___y_1828_);
lean_dec(v___y_1827_);
lean_dec_ref(v___y_1826_);
return v_res_1831_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14(lean_object* v_inst_1834_, lean_object* v_x_1835_, lean_object* v___x_1836_, lean_object* v___x_1837_, lean_object* v_inst_1838_, lean_object* v___f_1839_, lean_object* v___x_1840_, lean_object* v___x_1841_, lean_object* v_a_1842_, lean_object* v_toBind_1843_, lean_object* v___f_1844_, lean_object* v_toApplicative_1845_, lean_object* v_a_1846_){
_start:
{
if (lean_obj_tag(v_a_1846_) == 0)
{
lean_object* v___f_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_3407__overap_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; 
lean_dec_ref(v_toApplicative_1845_);
v___f_1847_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14___closed__0));
v___x_1848_ = lean_apply_2(v_inst_1834_, lean_box(0), v___f_1847_);
lean_inc_ref(v___x_1837_);
lean_inc_ref(v___x_1836_);
v___x_1849_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonadLift___aux__1___boxed), 10, 9);
lean_closure_set(v___x_1849_, 0, lean_box(0));
lean_closure_set(v___x_1849_, 1, lean_box(0));
lean_closure_set(v___x_1849_, 2, lean_box(0));
lean_closure_set(v___x_1849_, 3, lean_box(0));
lean_closure_set(v___x_1849_, 4, v_x_1835_);
lean_closure_set(v___x_1849_, 5, v___x_1836_);
lean_closure_set(v___x_1849_, 6, v___x_1837_);
lean_closure_set(v___x_1849_, 7, lean_box(0));
lean_closure_set(v___x_1849_, 8, v___x_1848_);
v___x_1850_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonad___aux__13___boxed), 13, 12);
lean_closure_set(v___x_1850_, 0, lean_box(0));
lean_closure_set(v___x_1850_, 1, lean_box(0));
lean_closure_set(v___x_1850_, 2, lean_box(0));
lean_closure_set(v___x_1850_, 3, lean_box(0));
lean_closure_set(v___x_1850_, 4, v_x_1835_);
lean_closure_set(v___x_1850_, 5, v___x_1836_);
lean_closure_set(v___x_1850_, 6, v___x_1837_);
lean_closure_set(v___x_1850_, 7, v_inst_1838_);
lean_closure_set(v___x_1850_, 8, lean_box(0));
lean_closure_set(v___x_1850_, 9, lean_box(0));
lean_closure_set(v___x_1850_, 10, v___x_1849_);
lean_closure_set(v___x_1850_, 11, v___f_1839_);
v___x_3407__overap_1851_ = l_Lean_Meta_withIncRecDepth___redArg(v___x_1840_, v___x_1841_, v___x_1850_);
lean_inc(v_a_1842_);
v___x_1852_ = lean_apply_1(v___x_3407__overap_1851_, v_a_1842_);
v___x_1853_ = lean_apply_4(v_toBind_1843_, lean_box(0), lean_box(0), v___x_1852_, v___f_1844_);
return v___x_1853_;
}
else
{
lean_object* v_val_1854_; lean_object* v_toPure_1855_; lean_object* v___x_1856_; 
lean_dec(v___f_1844_);
lean_dec(v_toBind_1843_);
lean_dec_ref(v___x_1841_);
lean_dec_ref(v___x_1840_);
lean_dec(v___f_1839_);
lean_dec_ref(v_inst_1838_);
lean_dec_ref(v___x_1837_);
lean_dec_ref(v___x_1836_);
lean_dec(v_inst_1834_);
v_val_1854_ = lean_ctor_get(v_a_1846_, 0);
lean_inc(v_val_1854_);
lean_dec_ref_known(v_a_1846_, 1);
v_toPure_1855_ = lean_ctor_get(v_toApplicative_1845_, 1);
lean_inc(v_toPure_1855_);
lean_dec_ref(v_toApplicative_1845_);
v___x_1856_ = lean_apply_2(v_toPure_1855_, lean_box(0), v_val_1854_);
return v___x_1856_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14___boxed(lean_object* v_inst_1857_, lean_object* v_x_1858_, lean_object* v___x_1859_, lean_object* v___x_1860_, lean_object* v_inst_1861_, lean_object* v___f_1862_, lean_object* v___x_1863_, lean_object* v___x_1864_, lean_object* v_a_1865_, lean_object* v_toBind_1866_, lean_object* v___f_1867_, lean_object* v_toApplicative_1868_, lean_object* v_a_1869_){
_start:
{
lean_object* v_res_1870_; 
v_res_1870_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14(v_inst_1857_, v_x_1858_, v___x_1859_, v___x_1860_, v_inst_1861_, v___f_1862_, v___x_1863_, v___x_1864_, v_a_1865_, v_toBind_1866_, v___f_1867_, v_toApplicative_1868_, v_a_1869_);
lean_dec(v_a_1865_);
return v_res_1870_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__1(lean_object* v___x_1871_, lean_object* v___x_1872_, lean_object* v_declName_1873_, lean_object* v_a_1874_, lean_object* v___f_1875_, uint8_t v_nondep_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_){
_start:
{
uint8_t v___x_1879_; lean_object* v___x_3426__overap_1880_; lean_object* v___x_1881_; 
v___x_1879_ = 0;
v___x_3426__overap_1880_ = l_Lean_Meta_withLetDecl___redArg(v___x_1871_, v___x_1872_, v_declName_1873_, v_a_1874_, v_a_1878_, v___f_1875_, v_nondep_1876_, v___x_1879_);
lean_inc(v_a_1877_);
v___x_1881_ = lean_apply_1(v___x_3426__overap_1880_, v_a_1877_);
return v___x_1881_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__1___boxed(lean_object* v___x_1882_, lean_object* v___x_1883_, lean_object* v_declName_1884_, lean_object* v_a_1885_, lean_object* v___f_1886_, lean_object* v_nondep_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_){
_start:
{
uint8_t v_nondep_3605__boxed_1890_; lean_object* v_res_1891_; 
v_nondep_3605__boxed_1890_ = lean_unbox(v_nondep_1887_);
v_res_1891_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__1(v___x_1882_, v___x_1883_, v_declName_1884_, v_a_1885_, v___f_1886_, v_nondep_3605__boxed_1890_, v_a_1888_, v_a_1889_);
lean_dec(v_a_1888_);
return v_res_1891_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__4(lean_object* v_fvars_1892_, uint8_t v_usedLetOnly_1893_, lean_object* v_inst_1894_, lean_object* v_toBind_1895_, lean_object* v___f_1896_, lean_object* v_a_1897_){
_start:
{
uint8_t v___x_1898_; uint8_t v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; 
v___x_1898_ = 0;
v___x_1899_ = 1;
v___x_1900_ = lean_box(v_usedLetOnly_1893_);
v___x_1901_ = lean_box(v___x_1898_);
v___x_1902_ = lean_box(v___x_1899_);
v___x_1903_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLetFVars___boxed), 10, 5);
lean_closure_set(v___x_1903_, 0, v_fvars_1892_);
lean_closure_set(v___x_1903_, 1, v_a_1897_);
lean_closure_set(v___x_1903_, 2, v___x_1900_);
lean_closure_set(v___x_1903_, 3, v___x_1901_);
lean_closure_set(v___x_1903_, 4, v___x_1902_);
v___x_1904_ = lean_apply_2(v_inst_1894_, lean_box(0), v___x_1903_);
v___x_1905_ = lean_apply_4(v_toBind_1895_, lean_box(0), lean_box(0), v___x_1904_, v___f_1896_);
return v___x_1905_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__4___boxed(lean_object* v_fvars_1906_, lean_object* v_usedLetOnly_1907_, lean_object* v_inst_1908_, lean_object* v_toBind_1909_, lean_object* v___f_1910_, lean_object* v_a_1911_){
_start:
{
uint8_t v_usedLetOnly_boxed_1912_; lean_object* v_res_1913_; 
v_usedLetOnly_boxed_1912_ = lean_unbox(v_usedLetOnly_1907_);
v_res_1913_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__4(v_fvars_1906_, v_usedLetOnly_boxed_1912_, v_inst_1908_, v_toBind_1909_, v___f_1910_, v_a_1911_);
return v_res_1913_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__3(lean_object* v_fvars_1914_, uint8_t v_usedLetOnly_1915_, lean_object* v_inst_1916_, lean_object* v_toBind_1917_, lean_object* v___f_1918_, lean_object* v_a_1919_){
_start:
{
uint8_t v___x_1920_; uint8_t v___x_1921_; uint8_t v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; 
v___x_1920_ = 0;
v___x_1921_ = 1;
v___x_1922_ = 1;
v___x_1923_ = lean_box(v___x_1920_);
v___x_1924_ = lean_box(v_usedLetOnly_1915_);
v___x_1925_ = lean_box(v___x_1920_);
v___x_1926_ = lean_box(v___x_1921_);
v___x_1927_ = lean_box(v___x_1922_);
v___x_1928_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(v___x_1928_, 0, v_fvars_1914_);
lean_closure_set(v___x_1928_, 1, v_a_1919_);
lean_closure_set(v___x_1928_, 2, v___x_1923_);
lean_closure_set(v___x_1928_, 3, v___x_1924_);
lean_closure_set(v___x_1928_, 4, v___x_1925_);
lean_closure_set(v___x_1928_, 5, v___x_1926_);
lean_closure_set(v___x_1928_, 6, v___x_1927_);
v___x_1929_ = lean_apply_2(v_inst_1916_, lean_box(0), v___x_1928_);
v___x_1930_ = lean_apply_4(v_toBind_1917_, lean_box(0), lean_box(0), v___x_1929_, v___f_1918_);
return v___x_1930_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__3___boxed(lean_object* v_fvars_1931_, lean_object* v_usedLetOnly_1932_, lean_object* v_inst_1933_, lean_object* v_toBind_1934_, lean_object* v___f_1935_, lean_object* v_a_1936_){
_start:
{
uint8_t v_usedLetOnly_boxed_1937_; lean_object* v_res_1938_; 
v_usedLetOnly_boxed_1937_ = lean_unbox(v_usedLetOnly_1932_);
v_res_1938_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__3(v_fvars_1931_, v_usedLetOnly_boxed_1937_, v_inst_1933_, v_toBind_1934_, v___f_1935_, v_a_1936_);
return v_res_1938_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1(lean_object* v___x_1939_, lean_object* v___x_1940_, lean_object* v_binderName_1941_, uint8_t v_binderInfo_1942_, lean_object* v___f_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_){
_start:
{
uint8_t v___x_1946_; lean_object* v___x_3484__overap_1947_; lean_object* v___x_1948_; 
v___x_1946_ = 0;
v___x_3484__overap_1947_ = l_Lean_Meta_withLocalDecl___redArg(v___x_1939_, v___x_1940_, v_binderName_1941_, v_binderInfo_1942_, v_a_1945_, v___f_1943_, v___x_1946_);
lean_inc(v_a_1944_);
v___x_1948_ = lean_apply_1(v___x_3484__overap_1947_, v_a_1944_);
return v___x_1948_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1___boxed(lean_object* v___x_1949_, lean_object* v___x_1950_, lean_object* v_binderName_1951_, lean_object* v_binderInfo_1952_, lean_object* v___f_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_){
_start:
{
uint8_t v_binderInfo_3673__boxed_1956_; lean_object* v_res_1957_; 
v_binderInfo_3673__boxed_1956_ = lean_unbox(v_binderInfo_1952_);
v_res_1957_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1(v___x_1949_, v___x_1950_, v_binderName_1951_, v_binderInfo_3673__boxed_1956_, v___f_1953_, v_a_1954_, v_a_1955_);
lean_dec(v_a_1954_);
return v_res_1957_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__3(lean_object* v_fvars_1958_, uint8_t v_usedLetOnly_1959_, lean_object* v_inst_1960_, lean_object* v_toBind_1961_, lean_object* v___f_1962_, lean_object* v_a_1963_){
_start:
{
uint8_t v___x_1964_; uint8_t v___x_1965_; uint8_t v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; 
v___x_1964_ = 0;
v___x_1965_ = 1;
v___x_1966_ = 1;
v___x_1967_ = lean_box(v___x_1964_);
v___x_1968_ = lean_box(v_usedLetOnly_1959_);
v___x_1969_ = lean_box(v___x_1965_);
v___x_1970_ = lean_box(v___x_1966_);
v___x_1971_ = lean_alloc_closure((void*)(l_Lean_Meta_mkForallFVars___boxed), 11, 6);
lean_closure_set(v___x_1971_, 0, v_fvars_1958_);
lean_closure_set(v___x_1971_, 1, v_a_1963_);
lean_closure_set(v___x_1971_, 2, v___x_1967_);
lean_closure_set(v___x_1971_, 3, v___x_1968_);
lean_closure_set(v___x_1971_, 4, v___x_1969_);
lean_closure_set(v___x_1971_, 5, v___x_1970_);
v___x_1972_ = lean_apply_2(v_inst_1960_, lean_box(0), v___x_1971_);
v___x_1973_ = lean_apply_4(v_toBind_1961_, lean_box(0), lean_box(0), v___x_1972_, v___f_1962_);
return v___x_1973_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__3___boxed(lean_object* v_fvars_1974_, lean_object* v_usedLetOnly_1975_, lean_object* v_inst_1976_, lean_object* v_toBind_1977_, lean_object* v___f_1978_, lean_object* v_a_1979_){
_start:
{
uint8_t v_usedLetOnly_boxed_1980_; lean_object* v_res_1981_; 
v_usedLetOnly_boxed_1980_ = lean_unbox(v_usedLetOnly_1975_);
v_res_1981_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__3(v_fvars_1974_, v_usedLetOnly_boxed_1980_, v_inst_1976_, v_toBind_1977_, v___f_1978_, v_a_1979_);
return v_res_1981_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__7(lean_object* v___f_1982_, lean_object* v___y_1983_, lean_object* v_a_1984_){
_start:
{
lean_object* v___x_1985_; 
lean_inc(v___y_1983_);
v___x_1985_ = lean_apply_2(v___f_1982_, v_a_1984_, v___y_1983_);
return v___x_1985_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__7___boxed(lean_object* v___f_1986_, lean_object* v___y_1987_, lean_object* v_a_1988_){
_start:
{
lean_object* v_res_1989_; 
v_res_1989_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__7(v___f_1986_, v___y_1987_, v_a_1988_);
lean_dec(v___y_1987_);
return v_res_1989_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1(lean_object* v_toApplicative_1990_, lean_object* v_acc_1991_, lean_object* v_next_1992_, lean_object* v_a_1993_){
_start:
{
lean_object* v_toPure_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; 
v_toPure_1994_ = lean_ctor_get(v_toApplicative_1990_, 1);
lean_inc(v_toPure_1994_);
lean_dec_ref(v_toApplicative_1990_);
v___x_1995_ = lean_array_fset(v_acc_1991_, v_next_1992_, v_a_1993_);
v___x_1996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1996_, 0, v___x_1995_);
v___x_1997_ = lean_apply_2(v_toPure_1994_, lean_box(0), v___x_1996_);
return v___x_1997_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1___boxed(lean_object* v_toApplicative_1998_, lean_object* v_acc_1999_, lean_object* v_next_2000_, lean_object* v_a_2001_){
_start:
{
lean_object* v_res_2002_; 
v_res_2002_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1(v_toApplicative_1998_, v_acc_1999_, v_next_2000_, v_a_2001_);
lean_dec(v_next_2000_);
return v_res_2002_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__2(lean_object* v_toApplicative_2003_, lean_object* v_next_2004_, lean_object* v_G_2005_, lean_object* v___y_2006_, lean_object* v_a_2007_){
_start:
{
if (lean_obj_tag(v_a_2007_) == 0)
{
lean_object* v_a_2008_; lean_object* v_toPure_2009_; lean_object* v___x_2010_; 
lean_dec(v_G_2005_);
v_a_2008_ = lean_ctor_get(v_a_2007_, 0);
lean_inc(v_a_2008_);
lean_dec_ref_known(v_a_2007_, 1);
v_toPure_2009_ = lean_ctor_get(v_toApplicative_2003_, 1);
lean_inc(v_toPure_2009_);
lean_dec_ref(v_toApplicative_2003_);
v___x_2010_ = lean_apply_2(v_toPure_2009_, lean_box(0), v_a_2008_);
return v___x_2010_;
}
else
{
lean_object* v_a_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; 
lean_dec_ref(v_toApplicative_2003_);
v_a_2011_ = lean_ctor_get(v_a_2007_, 0);
lean_inc(v_a_2011_);
lean_dec_ref_known(v_a_2007_, 1);
v___x_2012_ = lean_unsigned_to_nat(1u);
v___x_2013_ = lean_nat_add(v_next_2004_, v___x_2012_);
lean_inc(v___y_2006_);
v___x_2014_ = lean_apply_5(v_G_2005_, v___x_2013_, v_a_2011_, lean_box(0), lean_box(0), v___y_2006_);
return v___x_2014_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__2___boxed(lean_object* v_toApplicative_2015_, lean_object* v_next_2016_, lean_object* v_G_2017_, lean_object* v___y_2018_, lean_object* v_a_2019_){
_start:
{
lean_object* v_res_2020_; 
v_res_2020_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__2(v_toApplicative_2015_, v_next_2016_, v_G_2017_, v___y_2018_, v_a_2019_);
lean_dec(v___y_2018_);
lean_dec(v_next_2016_);
return v_res_2020_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5(lean_object* v_f_2021_, lean_object* v_inst_2022_, lean_object* v_inst_2023_, lean_object* v_inst_2024_, lean_object* v_pre_2025_, lean_object* v_post_2026_, uint8_t v_usedLetOnly_2027_, uint8_t v_skipConstInApp_2028_, uint8_t v_skipInstances_2029_, lean_object* v_x_2030_, lean_object* v_x_2031_, lean_object* v___y_2032_, lean_object* v_a_2033_){
_start:
{
lean_object* v___x_2034_; lean_object* v___x_2035_; 
v___x_2034_ = l_Lean_mkAppN(v_f_2021_, v_a_2033_);
v___x_2035_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2022_, v_inst_2023_, v_inst_2024_, v_pre_2025_, v_post_2026_, v_usedLetOnly_2027_, v_skipConstInApp_2028_, v_skipInstances_2029_, v_x_2030_, v_x_2031_, v___x_2034_, v___y_2032_);
return v___x_2035_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5___boxed(lean_object* v_f_2036_, lean_object* v_inst_2037_, lean_object* v_inst_2038_, lean_object* v_inst_2039_, lean_object* v_pre_2040_, lean_object* v_post_2041_, lean_object* v_usedLetOnly_2042_, lean_object* v_skipConstInApp_2043_, lean_object* v_skipInstances_2044_, lean_object* v_x_2045_, lean_object* v_x_2046_, lean_object* v___y_2047_, lean_object* v_a_2048_){
_start:
{
uint8_t v_usedLetOnly_boxed_2049_; uint8_t v_skipConstInApp_boxed_2050_; uint8_t v_skipInstances_boxed_2051_; lean_object* v_res_2052_; 
v_usedLetOnly_boxed_2049_ = lean_unbox(v_usedLetOnly_2042_);
v_skipConstInApp_boxed_2050_ = lean_unbox(v_skipConstInApp_2043_);
v_skipInstances_boxed_2051_ = lean_unbox(v_skipInstances_2044_);
v_res_2052_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5(v_f_2036_, v_inst_2037_, v_inst_2038_, v_inst_2039_, v_pre_2040_, v_post_2041_, v_usedLetOnly_boxed_2049_, v_skipConstInApp_boxed_2050_, v_skipInstances_boxed_2051_, v_x_2045_, v_x_2046_, v___y_2047_, v_a_2048_);
lean_dec_ref(v_a_2048_);
lean_dec(v___y_2047_);
return v_res_2052_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___boxed(lean_object* v_inst_2053_, lean_object* v_inst_2054_, lean_object* v_inst_2055_, lean_object* v_pre_2056_, lean_object* v_post_2057_, lean_object* v_usedLetOnly_2058_, lean_object* v_skipConstInApp_2059_, lean_object* v_skipInstances_2060_, lean_object* v_x_2061_, lean_object* v_x_2062_, lean_object* v_e_2063_, lean_object* v_a_2064_){
_start:
{
uint8_t v_usedLetOnly_boxed_2065_; uint8_t v_skipConstInApp_boxed_2066_; uint8_t v_skipInstances_boxed_2067_; lean_object* v_res_2068_; 
v_usedLetOnly_boxed_2065_ = lean_unbox(v_usedLetOnly_2058_);
v_skipConstInApp_boxed_2066_ = lean_unbox(v_skipConstInApp_2059_);
v_skipInstances_boxed_2067_ = lean_unbox(v_skipInstances_2060_);
v_res_2068_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2053_, v_inst_2054_, v_inst_2055_, v_pre_2056_, v_post_2057_, v_usedLetOnly_boxed_2065_, v_skipConstInApp_boxed_2066_, v_skipInstances_boxed_2067_, v_x_2061_, v_x_2062_, v_e_2063_, v_a_2064_);
lean_dec(v_a_2064_);
return v_res_2068_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__4(lean_object* v___x_2069_, lean_object* v_toApplicative_2070_, lean_object* v_toBind_2071_, lean_object* v___f_2072_, lean_object* v_paramInfo_2073_, lean_object* v_inst_2074_, lean_object* v_inst_2075_, lean_object* v_inst_2076_, lean_object* v_pre_2077_, lean_object* v_post_2078_, uint8_t v_usedLetOnly_2079_, uint8_t v_skipConstInApp_2080_, uint8_t v_skipInstances_2081_, lean_object* v_x_2082_, lean_object* v_x_2083_, lean_object* v_next_2084_, lean_object* v_acc_2085_, lean_object* v_h_2086_, lean_object* v_G_2087_, lean_object* v___y_2088_){
_start:
{
uint8_t v___x_2089_; 
v___x_2089_ = lean_nat_dec_lt(v_next_2084_, v___x_2069_);
if (v___x_2089_ == 0)
{
lean_object* v_toPure_2090_; lean_object* v___x_2091_; 
lean_dec(v_G_2087_);
lean_dec(v_next_2084_);
lean_dec(v_x_2083_);
lean_dec(v_post_2078_);
lean_dec(v_pre_2077_);
lean_dec_ref(v_inst_2076_);
lean_dec(v_inst_2075_);
lean_dec_ref(v_inst_2074_);
lean_dec(v___f_2072_);
lean_dec(v_toBind_2071_);
v_toPure_2090_ = lean_ctor_get(v_toApplicative_2070_, 1);
lean_inc(v_toPure_2090_);
lean_dec_ref(v_toApplicative_2070_);
v___x_2091_ = lean_apply_2(v_toPure_2090_, lean_box(0), v_acc_2085_);
return v___x_2091_;
}
else
{
lean_object* v___f_2092_; lean_object* v___y_2094_; lean_object* v___x_2097_; lean_object* v___x_2098_; uint8_t v___x_2099_; 
lean_inc(v___y_2088_);
lean_inc(v_next_2084_);
lean_inc_ref(v_toApplicative_2070_);
v___f_2092_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__2___boxed), 5, 4);
lean_closure_set(v___f_2092_, 0, v_toApplicative_2070_);
lean_closure_set(v___f_2092_, 1, v_next_2084_);
lean_closure_set(v___f_2092_, 2, v_G_2087_);
lean_closure_set(v___f_2092_, 3, v___y_2088_);
v___x_2097_ = lean_array_fget_borrowed(v_acc_2085_, v_next_2084_);
v___x_2098_ = lean_array_get_size(v_paramInfo_2073_);
v___x_2099_ = lean_nat_dec_lt(v_next_2084_, v___x_2098_);
if (v___x_2099_ == 0)
{
lean_object* v___f_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; 
lean_inc(v___x_2097_);
v___f_2100_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2100_, 0, v_toApplicative_2070_);
lean_closure_set(v___f_2100_, 1, v_acc_2085_);
lean_closure_set(v___f_2100_, 2, v_next_2084_);
v___x_2101_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2074_, v_inst_2075_, v_inst_2076_, v_pre_2077_, v_post_2078_, v_usedLetOnly_2079_, v_skipConstInApp_2080_, v_skipInstances_2081_, v_x_2082_, v_x_2083_, v___x_2097_, v___y_2088_);
lean_inc(v_toBind_2071_);
v___x_2102_ = lean_apply_4(v_toBind_2071_, lean_box(0), lean_box(0), v___x_2101_, v___f_2100_);
v___y_2094_ = v___x_2102_;
goto v___jp_2093_;
}
else
{
lean_object* v___x_2103_; uint8_t v_isInstance_2104_; 
v___x_2103_ = lean_array_fget_borrowed(v_paramInfo_2073_, v_next_2084_);
v_isInstance_2104_ = lean_ctor_get_uint8(v___x_2103_, sizeof(void*)*1 + 4);
if (v_isInstance_2104_ == 0)
{
lean_object* v___f_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; 
lean_inc(v___x_2097_);
v___f_2105_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2105_, 0, v_toApplicative_2070_);
lean_closure_set(v___f_2105_, 1, v_acc_2085_);
lean_closure_set(v___f_2105_, 2, v_next_2084_);
v___x_2106_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2074_, v_inst_2075_, v_inst_2076_, v_pre_2077_, v_post_2078_, v_usedLetOnly_2079_, v_skipConstInApp_2080_, v_skipInstances_2081_, v_x_2082_, v_x_2083_, v___x_2097_, v___y_2088_);
lean_inc(v_toBind_2071_);
v___x_2107_ = lean_apply_4(v_toBind_2071_, lean_box(0), lean_box(0), v___x_2106_, v___f_2105_);
v___y_2094_ = v___x_2107_;
goto v___jp_2093_;
}
else
{
lean_object* v_toPure_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; 
lean_dec(v_next_2084_);
lean_dec(v_x_2083_);
lean_dec(v_post_2078_);
lean_dec(v_pre_2077_);
lean_dec_ref(v_inst_2076_);
lean_dec(v_inst_2075_);
lean_dec_ref(v_inst_2074_);
v_toPure_2108_ = lean_ctor_get(v_toApplicative_2070_, 1);
lean_inc(v_toPure_2108_);
lean_dec_ref(v_toApplicative_2070_);
v___x_2109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2109_, 0, v_acc_2085_);
v___x_2110_ = lean_apply_2(v_toPure_2108_, lean_box(0), v___x_2109_);
v___y_2094_ = v___x_2110_;
goto v___jp_2093_;
}
}
v___jp_2093_:
{
lean_object* v___x_2095_; lean_object* v___x_2096_; 
lean_inc(v_toBind_2071_);
v___x_2095_ = lean_apply_4(v_toBind_2071_, lean_box(0), lean_box(0), v___y_2094_, v___f_2072_);
v___x_2096_ = lean_apply_4(v_toBind_2071_, lean_box(0), lean_box(0), v___x_2095_, v___f_2092_);
return v___x_2096_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__4___boxed(lean_object** _args){
lean_object* v___x_2111_ = _args[0];
lean_object* v_toApplicative_2112_ = _args[1];
lean_object* v_toBind_2113_ = _args[2];
lean_object* v___f_2114_ = _args[3];
lean_object* v_paramInfo_2115_ = _args[4];
lean_object* v_inst_2116_ = _args[5];
lean_object* v_inst_2117_ = _args[6];
lean_object* v_inst_2118_ = _args[7];
lean_object* v_pre_2119_ = _args[8];
lean_object* v_post_2120_ = _args[9];
lean_object* v_usedLetOnly_2121_ = _args[10];
lean_object* v_skipConstInApp_2122_ = _args[11];
lean_object* v_skipInstances_2123_ = _args[12];
lean_object* v_x_2124_ = _args[13];
lean_object* v_x_2125_ = _args[14];
lean_object* v_next_2126_ = _args[15];
lean_object* v_acc_2127_ = _args[16];
lean_object* v_h_2128_ = _args[17];
lean_object* v_G_2129_ = _args[18];
lean_object* v___y_2130_ = _args[19];
_start:
{
uint8_t v_usedLetOnly_boxed_2131_; uint8_t v_skipConstInApp_boxed_2132_; uint8_t v_skipInstances_boxed_2133_; lean_object* v_res_2134_; 
v_usedLetOnly_boxed_2131_ = lean_unbox(v_usedLetOnly_2121_);
v_skipConstInApp_boxed_2132_ = lean_unbox(v_skipConstInApp_2122_);
v_skipInstances_boxed_2133_ = lean_unbox(v_skipInstances_2123_);
v_res_2134_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__4(v___x_2111_, v_toApplicative_2112_, v_toBind_2113_, v___f_2114_, v_paramInfo_2115_, v_inst_2116_, v_inst_2117_, v_inst_2118_, v_pre_2119_, v_post_2120_, v_usedLetOnly_boxed_2131_, v_skipConstInApp_boxed_2132_, v_skipInstances_boxed_2133_, v_x_2124_, v_x_2125_, v_next_2126_, v_acc_2127_, v_h_2128_, v_G_2129_, v___y_2130_);
lean_dec(v___y_2130_);
lean_dec_ref(v_paramInfo_2115_);
lean_dec(v___x_2111_);
return v_res_2134_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__3(lean_object* v___x_2135_, lean_object* v_toApplicative_2136_, lean_object* v_toBind_2137_, lean_object* v___f_2138_, lean_object* v_inst_2139_, lean_object* v_inst_2140_, lean_object* v_inst_2141_, lean_object* v_pre_2142_, lean_object* v_post_2143_, uint8_t v_usedLetOnly_2144_, uint8_t v_skipConstInApp_2145_, uint8_t v_skipInstances_2146_, lean_object* v_x_2147_, lean_object* v_x_2148_, lean_object* v_args_2149_, lean_object* v___y_2150_, lean_object* v___f_2151_, lean_object* v_a_2152_){
_start:
{
lean_object* v_paramInfo_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___f_2158_; lean_object* v___x_3244__overap_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; 
v_paramInfo_2153_ = lean_ctor_get(v_a_2152_, 0);
lean_inc_ref(v_paramInfo_2153_);
lean_dec_ref(v_a_2152_);
v___x_2154_ = lean_unsigned_to_nat(0u);
v___x_2155_ = lean_box(v_usedLetOnly_2144_);
v___x_2156_ = lean_box(v_skipConstInApp_2145_);
v___x_2157_ = lean_box(v_skipInstances_2146_);
lean_inc(v_toBind_2137_);
v___f_2158_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__4___boxed), 20, 15);
lean_closure_set(v___f_2158_, 0, v___x_2135_);
lean_closure_set(v___f_2158_, 1, v_toApplicative_2136_);
lean_closure_set(v___f_2158_, 2, v_toBind_2137_);
lean_closure_set(v___f_2158_, 3, v___f_2138_);
lean_closure_set(v___f_2158_, 4, v_paramInfo_2153_);
lean_closure_set(v___f_2158_, 5, v_inst_2139_);
lean_closure_set(v___f_2158_, 6, v_inst_2140_);
lean_closure_set(v___f_2158_, 7, v_inst_2141_);
lean_closure_set(v___f_2158_, 8, v_pre_2142_);
lean_closure_set(v___f_2158_, 9, v_post_2143_);
lean_closure_set(v___f_2158_, 10, v___x_2155_);
lean_closure_set(v___f_2158_, 11, v___x_2156_);
lean_closure_set(v___f_2158_, 12, v___x_2157_);
lean_closure_set(v___f_2158_, 13, v_x_2147_);
lean_closure_set(v___f_2158_, 14, v_x_2148_);
v___x_3244__overap_2159_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_2158_, v___x_2154_, v_args_2149_, lean_box(0));
lean_inc(v___y_2150_);
v___x_2160_ = lean_apply_1(v___x_3244__overap_2159_, v___y_2150_);
v___x_2161_ = lean_apply_4(v_toBind_2137_, lean_box(0), lean_box(0), v___x_2160_, v___f_2151_);
return v___x_2161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__3___boxed(lean_object** _args){
lean_object* v___x_2162_ = _args[0];
lean_object* v_toApplicative_2163_ = _args[1];
lean_object* v_toBind_2164_ = _args[2];
lean_object* v___f_2165_ = _args[3];
lean_object* v_inst_2166_ = _args[4];
lean_object* v_inst_2167_ = _args[5];
lean_object* v_inst_2168_ = _args[6];
lean_object* v_pre_2169_ = _args[7];
lean_object* v_post_2170_ = _args[8];
lean_object* v_usedLetOnly_2171_ = _args[9];
lean_object* v_skipConstInApp_2172_ = _args[10];
lean_object* v_skipInstances_2173_ = _args[11];
lean_object* v_x_2174_ = _args[12];
lean_object* v_x_2175_ = _args[13];
lean_object* v_args_2176_ = _args[14];
lean_object* v___y_2177_ = _args[15];
lean_object* v___f_2178_ = _args[16];
lean_object* v_a_2179_ = _args[17];
_start:
{
uint8_t v_usedLetOnly_boxed_2180_; uint8_t v_skipConstInApp_boxed_2181_; uint8_t v_skipInstances_boxed_2182_; lean_object* v_res_2183_; 
v_usedLetOnly_boxed_2180_ = lean_unbox(v_usedLetOnly_2171_);
v_skipConstInApp_boxed_2181_ = lean_unbox(v_skipConstInApp_2172_);
v_skipInstances_boxed_2182_ = lean_unbox(v_skipInstances_2173_);
v_res_2183_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__3(v___x_2162_, v_toApplicative_2163_, v_toBind_2164_, v___f_2165_, v_inst_2166_, v_inst_2167_, v_inst_2168_, v_pre_2169_, v_post_2170_, v_usedLetOnly_boxed_2180_, v_skipConstInApp_boxed_2181_, v_skipInstances_boxed_2182_, v_x_2174_, v_x_2175_, v_args_2176_, v___y_2177_, v___f_2178_, v_a_2179_);
lean_dec(v___y_2177_);
return v_res_2183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__6(uint8_t v_skipInstances_2184_, lean_object* v_inst_2185_, lean_object* v_inst_2186_, lean_object* v_inst_2187_, lean_object* v_pre_2188_, lean_object* v_post_2189_, uint8_t v_usedLetOnly_2190_, uint8_t v_skipConstInApp_2191_, lean_object* v_x_2192_, lean_object* v_x_2193_, lean_object* v_args_2194_, lean_object* v___x_2195_, lean_object* v_toBind_2196_, lean_object* v_toApplicative_2197_, lean_object* v___f_2198_, lean_object* v_f_2199_, lean_object* v___y_2200_){
_start:
{
if (v_skipInstances_2184_ == 0)
{
lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___f_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; size_t v_sz_2209_; size_t v___x_2210_; lean_object* v___x_3257__overap_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; 
lean_dec(v___f_2198_);
lean_dec_ref(v_toApplicative_2197_);
v___x_2201_ = lean_box(v_usedLetOnly_2190_);
v___x_2202_ = lean_box(v_skipConstInApp_2191_);
v___x_2203_ = lean_box(v_skipInstances_2184_);
lean_inc_n(v___y_2200_, 2);
lean_inc(v_x_2193_);
lean_inc(v_post_2189_);
lean_inc(v_pre_2188_);
lean_inc_ref(v_inst_2187_);
lean_inc(v_inst_2186_);
lean_inc_ref(v_inst_2185_);
v___f_2204_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5___boxed), 13, 12);
lean_closure_set(v___f_2204_, 0, v_f_2199_);
lean_closure_set(v___f_2204_, 1, v_inst_2185_);
lean_closure_set(v___f_2204_, 2, v_inst_2186_);
lean_closure_set(v___f_2204_, 3, v_inst_2187_);
lean_closure_set(v___f_2204_, 4, v_pre_2188_);
lean_closure_set(v___f_2204_, 5, v_post_2189_);
lean_closure_set(v___f_2204_, 6, v___x_2201_);
lean_closure_set(v___f_2204_, 7, v___x_2202_);
lean_closure_set(v___f_2204_, 8, v___x_2203_);
lean_closure_set(v___f_2204_, 9, v_x_2192_);
lean_closure_set(v___f_2204_, 10, v_x_2193_);
lean_closure_set(v___f_2204_, 11, v___y_2200_);
v___x_2205_ = lean_box(v_usedLetOnly_2190_);
v___x_2206_ = lean_box(v_skipConstInApp_2191_);
v___x_2207_ = lean_box(v_skipInstances_2184_);
v___x_2208_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___boxed), 12, 10);
lean_closure_set(v___x_2208_, 0, v_inst_2185_);
lean_closure_set(v___x_2208_, 1, v_inst_2186_);
lean_closure_set(v___x_2208_, 2, v_inst_2187_);
lean_closure_set(v___x_2208_, 3, v_pre_2188_);
lean_closure_set(v___x_2208_, 4, v_post_2189_);
lean_closure_set(v___x_2208_, 5, v___x_2205_);
lean_closure_set(v___x_2208_, 6, v___x_2206_);
lean_closure_set(v___x_2208_, 7, v___x_2207_);
lean_closure_set(v___x_2208_, 8, v_x_2192_);
lean_closure_set(v___x_2208_, 9, v_x_2193_);
v_sz_2209_ = lean_array_size(v_args_2194_);
v___x_2210_ = ((size_t)0ULL);
v___x_3257__overap_2211_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2195_, v___x_2208_, v_sz_2209_, v___x_2210_, v_args_2194_);
v___x_2212_ = lean_apply_1(v___x_3257__overap_2211_, v___y_2200_);
v___x_2213_ = lean_apply_4(v_toBind_2196_, lean_box(0), lean_box(0), v___x_2212_, v___f_2204_);
return v___x_2213_;
}
else
{
lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___f_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___f_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; 
lean_dec_ref(v___x_2195_);
v___x_2214_ = lean_box(v_usedLetOnly_2190_);
v___x_2215_ = lean_box(v_skipConstInApp_2191_);
v___x_2216_ = lean_box(v_skipInstances_2184_);
lean_inc_n(v___y_2200_, 2);
lean_inc(v_x_2193_);
lean_inc(v_post_2189_);
lean_inc(v_pre_2188_);
lean_inc_ref(v_inst_2187_);
lean_inc_n(v_inst_2186_, 2);
lean_inc_ref(v_inst_2185_);
lean_inc_ref(v_f_2199_);
v___f_2217_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5___boxed), 13, 12);
lean_closure_set(v___f_2217_, 0, v_f_2199_);
lean_closure_set(v___f_2217_, 1, v_inst_2185_);
lean_closure_set(v___f_2217_, 2, v_inst_2186_);
lean_closure_set(v___f_2217_, 3, v_inst_2187_);
lean_closure_set(v___f_2217_, 4, v_pre_2188_);
lean_closure_set(v___f_2217_, 5, v_post_2189_);
lean_closure_set(v___f_2217_, 6, v___x_2214_);
lean_closure_set(v___f_2217_, 7, v___x_2215_);
lean_closure_set(v___f_2217_, 8, v___x_2216_);
lean_closure_set(v___f_2217_, 9, v_x_2192_);
lean_closure_set(v___f_2217_, 10, v_x_2193_);
lean_closure_set(v___f_2217_, 11, v___y_2200_);
v___x_2218_ = lean_array_get_size(v_args_2194_);
v___x_2219_ = lean_box(v_usedLetOnly_2190_);
v___x_2220_ = lean_box(v_skipConstInApp_2191_);
v___x_2221_ = lean_box(v_skipInstances_2184_);
lean_inc(v_toBind_2196_);
v___f_2222_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__3___boxed), 18, 17);
lean_closure_set(v___f_2222_, 0, v___x_2218_);
lean_closure_set(v___f_2222_, 1, v_toApplicative_2197_);
lean_closure_set(v___f_2222_, 2, v_toBind_2196_);
lean_closure_set(v___f_2222_, 3, v___f_2198_);
lean_closure_set(v___f_2222_, 4, v_inst_2185_);
lean_closure_set(v___f_2222_, 5, v_inst_2186_);
lean_closure_set(v___f_2222_, 6, v_inst_2187_);
lean_closure_set(v___f_2222_, 7, v_pre_2188_);
lean_closure_set(v___f_2222_, 8, v_post_2189_);
lean_closure_set(v___f_2222_, 9, v___x_2219_);
lean_closure_set(v___f_2222_, 10, v___x_2220_);
lean_closure_set(v___f_2222_, 11, v___x_2221_);
lean_closure_set(v___f_2222_, 12, v_x_2192_);
lean_closure_set(v___f_2222_, 13, v_x_2193_);
lean_closure_set(v___f_2222_, 14, v_args_2194_);
lean_closure_set(v___f_2222_, 15, v___y_2200_);
lean_closure_set(v___f_2222_, 16, v___f_2217_);
v___x_2223_ = lean_alloc_closure((void*)(l_Lean_Meta_getFunInfoNArgs___boxed), 7, 2);
lean_closure_set(v___x_2223_, 0, v_f_2199_);
lean_closure_set(v___x_2223_, 1, v___x_2218_);
v___x_2224_ = lean_apply_2(v_inst_2186_, lean_box(0), v___x_2223_);
v___x_2225_ = lean_apply_4(v_toBind_2196_, lean_box(0), lean_box(0), v___x_2224_, v___f_2222_);
return v___x_2225_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__6___boxed(lean_object** _args){
lean_object* v_skipInstances_2226_ = _args[0];
lean_object* v_inst_2227_ = _args[1];
lean_object* v_inst_2228_ = _args[2];
lean_object* v_inst_2229_ = _args[3];
lean_object* v_pre_2230_ = _args[4];
lean_object* v_post_2231_ = _args[5];
lean_object* v_usedLetOnly_2232_ = _args[6];
lean_object* v_skipConstInApp_2233_ = _args[7];
lean_object* v_x_2234_ = _args[8];
lean_object* v_x_2235_ = _args[9];
lean_object* v_args_2236_ = _args[10];
lean_object* v___x_2237_ = _args[11];
lean_object* v_toBind_2238_ = _args[12];
lean_object* v_toApplicative_2239_ = _args[13];
lean_object* v___f_2240_ = _args[14];
lean_object* v_f_2241_ = _args[15];
lean_object* v___y_2242_ = _args[16];
_start:
{
uint8_t v_skipInstances_boxed_2243_; uint8_t v_usedLetOnly_boxed_2244_; uint8_t v_skipConstInApp_boxed_2245_; lean_object* v_res_2246_; 
v_skipInstances_boxed_2243_ = lean_unbox(v_skipInstances_2226_);
v_usedLetOnly_boxed_2244_ = lean_unbox(v_usedLetOnly_2232_);
v_skipConstInApp_boxed_2245_ = lean_unbox(v_skipConstInApp_2233_);
v_res_2246_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__6(v_skipInstances_boxed_2243_, v_inst_2227_, v_inst_2228_, v_inst_2229_, v_pre_2230_, v_post_2231_, v_usedLetOnly_boxed_2244_, v_skipConstInApp_boxed_2245_, v_x_2234_, v_x_2235_, v_args_2236_, v___x_2237_, v_toBind_2238_, v_toApplicative_2239_, v___f_2240_, v_f_2241_, v___y_2242_);
lean_dec(v___y_2242_);
return v_res_2246_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__9(uint8_t v_skipInstances_2247_, lean_object* v_inst_2248_, lean_object* v_inst_2249_, lean_object* v_inst_2250_, lean_object* v_pre_2251_, lean_object* v_post_2252_, uint8_t v_usedLetOnly_2253_, uint8_t v_skipConstInApp_2254_, lean_object* v_x_2255_, lean_object* v_x_2256_, lean_object* v___x_2257_, lean_object* v_toBind_2258_, lean_object* v_toApplicative_2259_, lean_object* v___f_2260_, lean_object* v_f_2261_, lean_object* v_args_2262_, lean_object* v___y_2263_){
_start:
{
lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___f_2267_; lean_object* v___f_2268_; 
v___x_2264_ = lean_box(v_skipInstances_2247_);
v___x_2265_ = lean_box(v_usedLetOnly_2253_);
v___x_2266_ = lean_box(v_skipConstInApp_2254_);
lean_inc_ref(v_toApplicative_2259_);
lean_inc(v_toBind_2258_);
lean_inc(v_x_2256_);
lean_inc(v_post_2252_);
lean_inc(v_pre_2251_);
lean_inc_ref(v_inst_2250_);
lean_inc(v_inst_2249_);
lean_inc_ref(v_inst_2248_);
v___f_2267_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__6___boxed), 17, 15);
lean_closure_set(v___f_2267_, 0, v___x_2264_);
lean_closure_set(v___f_2267_, 1, v_inst_2248_);
lean_closure_set(v___f_2267_, 2, v_inst_2249_);
lean_closure_set(v___f_2267_, 3, v_inst_2250_);
lean_closure_set(v___f_2267_, 4, v_pre_2251_);
lean_closure_set(v___f_2267_, 5, v_post_2252_);
lean_closure_set(v___f_2267_, 6, v___x_2265_);
lean_closure_set(v___f_2267_, 7, v___x_2266_);
lean_closure_set(v___f_2267_, 8, v_x_2255_);
lean_closure_set(v___f_2267_, 9, v_x_2256_);
lean_closure_set(v___f_2267_, 10, v_args_2262_);
lean_closure_set(v___f_2267_, 11, v___x_2257_);
lean_closure_set(v___f_2267_, 12, v_toBind_2258_);
lean_closure_set(v___f_2267_, 13, v_toApplicative_2259_);
lean_closure_set(v___f_2267_, 14, v___f_2260_);
lean_inc(v___y_2263_);
v___f_2268_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__7___boxed), 3, 2);
lean_closure_set(v___f_2268_, 0, v___f_2267_);
lean_closure_set(v___f_2268_, 1, v___y_2263_);
if (v_skipConstInApp_2254_ == 0)
{
lean_dec_ref(v_toApplicative_2259_);
goto v___jp_2269_;
}
else
{
uint8_t v___x_2272_; 
v___x_2272_ = l_Lean_Expr_isConst(v_f_2261_);
if (v___x_2272_ == 0)
{
lean_dec_ref(v_toApplicative_2259_);
goto v___jp_2269_;
}
else
{
lean_object* v_toPure_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; 
lean_dec(v_x_2256_);
lean_dec(v_post_2252_);
lean_dec(v_pre_2251_);
lean_dec_ref(v_inst_2250_);
lean_dec(v_inst_2249_);
lean_dec_ref(v_inst_2248_);
v_toPure_2273_ = lean_ctor_get(v_toApplicative_2259_, 1);
lean_inc(v_toPure_2273_);
lean_dec_ref(v_toApplicative_2259_);
v___x_2274_ = lean_apply_2(v_toPure_2273_, lean_box(0), v_f_2261_);
v___x_2275_ = lean_apply_4(v_toBind_2258_, lean_box(0), lean_box(0), v___x_2274_, v___f_2268_);
return v___x_2275_;
}
}
v___jp_2269_:
{
lean_object* v___x_2270_; lean_object* v___x_2271_; 
v___x_2270_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2248_, v_inst_2249_, v_inst_2250_, v_pre_2251_, v_post_2252_, v_usedLetOnly_2253_, v_skipConstInApp_2254_, v_skipInstances_2247_, v_x_2255_, v_x_2256_, v_f_2261_, v___y_2263_);
v___x_2271_ = lean_apply_4(v_toBind_2258_, lean_box(0), lean_box(0), v___x_2270_, v___f_2268_);
return v___x_2271_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__9___boxed(lean_object** _args){
lean_object* v_skipInstances_2276_ = _args[0];
lean_object* v_inst_2277_ = _args[1];
lean_object* v_inst_2278_ = _args[2];
lean_object* v_inst_2279_ = _args[3];
lean_object* v_pre_2280_ = _args[4];
lean_object* v_post_2281_ = _args[5];
lean_object* v_usedLetOnly_2282_ = _args[6];
lean_object* v_skipConstInApp_2283_ = _args[7];
lean_object* v_x_2284_ = _args[8];
lean_object* v_x_2285_ = _args[9];
lean_object* v___x_2286_ = _args[10];
lean_object* v_toBind_2287_ = _args[11];
lean_object* v_toApplicative_2288_ = _args[12];
lean_object* v___f_2289_ = _args[13];
lean_object* v_f_2290_ = _args[14];
lean_object* v_args_2291_ = _args[15];
lean_object* v___y_2292_ = _args[16];
_start:
{
uint8_t v_skipInstances_boxed_2293_; uint8_t v_usedLetOnly_boxed_2294_; uint8_t v_skipConstInApp_boxed_2295_; lean_object* v_res_2296_; 
v_skipInstances_boxed_2293_ = lean_unbox(v_skipInstances_2276_);
v_usedLetOnly_boxed_2294_ = lean_unbox(v_usedLetOnly_2282_);
v_skipConstInApp_boxed_2295_ = lean_unbox(v_skipConstInApp_2283_);
v_res_2296_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__9(v_skipInstances_boxed_2293_, v_inst_2277_, v_inst_2278_, v_inst_2279_, v_pre_2280_, v_post_2281_, v_usedLetOnly_boxed_2294_, v_skipConstInApp_boxed_2295_, v_x_2284_, v_x_2285_, v___x_2286_, v_toBind_2287_, v_toApplicative_2288_, v___f_2289_, v_f_2290_, v_args_2291_, v___y_2292_);
lean_dec(v___y_2292_);
return v_res_2296_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__0(lean_object* v_fvars_2299_, lean_object* v_inst_2300_, lean_object* v_inst_2301_, lean_object* v_inst_2302_, lean_object* v_pre_2303_, lean_object* v_post_2304_, uint8_t v_usedLetOnly_2305_, uint8_t v_skipConstInApp_2306_, uint8_t v_skipInstances_2307_, lean_object* v_x_2308_, lean_object* v_x_2309_, lean_object* v_body_2310_, lean_object* v_x_2311_, lean_object* v___y_2312_){
_start:
{
lean_object* v___x_2313_; lean_object* v___x_2314_; 
v___x_2313_ = lean_array_push(v_fvars_2299_, v_x_2311_);
v___x_2314_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(v_inst_2300_, v_inst_2301_, v_inst_2302_, v_pre_2303_, v_post_2304_, v_usedLetOnly_2305_, v_skipConstInApp_2306_, v_skipInstances_2307_, v_x_2308_, v_x_2309_, v___x_2313_, v_body_2310_, v___y_2312_);
return v___x_2314_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__0___boxed(lean_object* v_fvars_2315_, lean_object* v_inst_2316_, lean_object* v_inst_2317_, lean_object* v_inst_2318_, lean_object* v_pre_2319_, lean_object* v_post_2320_, lean_object* v_usedLetOnly_2321_, lean_object* v_skipConstInApp_2322_, lean_object* v_skipInstances_2323_, lean_object* v_x_2324_, lean_object* v_x_2325_, lean_object* v_body_2326_, lean_object* v_x_2327_, lean_object* v___y_2328_){
_start:
{
uint8_t v_usedLetOnly_boxed_2329_; uint8_t v_skipConstInApp_boxed_2330_; uint8_t v_skipInstances_boxed_2331_; lean_object* v_res_2332_; 
v_usedLetOnly_boxed_2329_ = lean_unbox(v_usedLetOnly_2321_);
v_skipConstInApp_boxed_2330_ = lean_unbox(v_skipConstInApp_2322_);
v_skipInstances_boxed_2331_ = lean_unbox(v_skipInstances_2323_);
v_res_2332_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__0(v_fvars_2315_, v_inst_2316_, v_inst_2317_, v_inst_2318_, v_pre_2319_, v_post_2320_, v_usedLetOnly_boxed_2329_, v_skipConstInApp_boxed_2330_, v_skipInstances_boxed_2331_, v_x_2324_, v_x_2325_, v_body_2326_, v_x_2327_, v___y_2328_);
lean_dec(v___y_2328_);
return v_res_2332_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3___boxed(lean_object* v_inst_2333_, lean_object* v_inst_2334_, lean_object* v_inst_2335_, lean_object* v_pre_2336_, lean_object* v_post_2337_, lean_object* v_usedLetOnly_2338_, lean_object* v_skipConstInApp_2339_, lean_object* v_skipInstances_2340_, lean_object* v_x_2341_, lean_object* v_x_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_){
_start:
{
uint8_t v_usedLetOnly_boxed_2345_; uint8_t v_skipConstInApp_boxed_2346_; uint8_t v_skipInstances_boxed_2347_; lean_object* v_res_2348_; 
v_usedLetOnly_boxed_2345_ = lean_unbox(v_usedLetOnly_2338_);
v_skipConstInApp_boxed_2346_ = lean_unbox(v_skipConstInApp_2339_);
v_skipInstances_boxed_2347_ = lean_unbox(v_skipInstances_2340_);
v_res_2348_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3(v_inst_2333_, v_inst_2334_, v_inst_2335_, v_pre_2336_, v_post_2337_, v_usedLetOnly_boxed_2345_, v_skipConstInApp_boxed_2346_, v_skipInstances_boxed_2347_, v_x_2341_, v_x_2342_, v_a_2343_, v_a_2344_);
lean_dec(v_a_2343_);
return v_res_2348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(lean_object* v_inst_2349_, lean_object* v_inst_2350_, lean_object* v_inst_2351_, lean_object* v_pre_2352_, lean_object* v_post_2353_, uint8_t v_usedLetOnly_2354_, uint8_t v_skipConstInApp_2355_, uint8_t v_skipInstances_2356_, lean_object* v_x_2357_, lean_object* v_x_2358_, lean_object* v_fvars_2359_, lean_object* v_e_2360_, lean_object* v_a_2361_){
_start:
{
lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___f_2366_; lean_object* v___f_2367_; lean_object* v___x_2368_; 
v___x_2362_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0));
v___x_2363_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1));
lean_inc_ref(v_inst_2349_);
v___x_2364_ = l_Lean_MonadCacheT_instMonad___redArg(v_x_2357_, v___x_2362_, v___x_2363_, v_inst_2349_);
v___x_2365_ = l_Lean_MonadCacheT_instMonadControl___redArg(v_x_2357_, v___x_2362_, v___x_2363_);
lean_inc_ref_n(v_inst_2351_, 2);
lean_inc_ref(v___x_2365_);
v___f_2366_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_2366_, 0, v___x_2365_);
lean_closure_set(v___f_2366_, 1, v_inst_2351_);
v___f_2367_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_2367_, 0, v___x_2365_);
lean_closure_set(v___f_2367_, 1, v_inst_2351_);
v___x_2368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2368_, 0, v___f_2366_);
lean_ctor_set(v___x_2368_, 1, v___f_2367_);
if (lean_obj_tag(v_e_2360_) == 7)
{
lean_object* v_binderName_2369_; lean_object* v_binderType_2370_; lean_object* v_body_2371_; uint8_t v_binderInfo_2372_; lean_object* v_toBind_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___f_2377_; lean_object* v___x_2378_; lean_object* v___f_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; 
v_binderName_2369_ = lean_ctor_get(v_e_2360_, 0);
lean_inc(v_binderName_2369_);
v_binderType_2370_ = lean_ctor_get(v_e_2360_, 1);
lean_inc_ref(v_binderType_2370_);
v_body_2371_ = lean_ctor_get(v_e_2360_, 2);
lean_inc_ref(v_body_2371_);
v_binderInfo_2372_ = lean_ctor_get_uint8(v_e_2360_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2360_, 3);
v_toBind_2373_ = lean_ctor_get(v_inst_2349_, 1);
lean_inc(v_toBind_2373_);
v___x_2374_ = lean_box(v_usedLetOnly_2354_);
v___x_2375_ = lean_box(v_skipConstInApp_2355_);
v___x_2376_ = lean_box(v_skipInstances_2356_);
lean_inc(v_x_2358_);
lean_inc(v_post_2353_);
lean_inc(v_pre_2352_);
lean_inc_ref(v_inst_2351_);
lean_inc(v_inst_2350_);
lean_inc_ref(v_inst_2349_);
lean_inc_ref(v_fvars_2359_);
v___f_2377_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__0___boxed), 14, 12);
lean_closure_set(v___f_2377_, 0, v_fvars_2359_);
lean_closure_set(v___f_2377_, 1, v_inst_2349_);
lean_closure_set(v___f_2377_, 2, v_inst_2350_);
lean_closure_set(v___f_2377_, 3, v_inst_2351_);
lean_closure_set(v___f_2377_, 4, v_pre_2352_);
lean_closure_set(v___f_2377_, 5, v_post_2353_);
lean_closure_set(v___f_2377_, 6, v___x_2374_);
lean_closure_set(v___f_2377_, 7, v___x_2375_);
lean_closure_set(v___f_2377_, 8, v___x_2376_);
lean_closure_set(v___f_2377_, 9, v_x_2357_);
lean_closure_set(v___f_2377_, 10, v_x_2358_);
lean_closure_set(v___f_2377_, 11, v_body_2371_);
v___x_2378_ = lean_box(v_binderInfo_2372_);
lean_inc(v_a_2361_);
v___f_2379_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_2379_, 0, v___x_2368_);
lean_closure_set(v___f_2379_, 1, v___x_2364_);
lean_closure_set(v___f_2379_, 2, v_binderName_2369_);
lean_closure_set(v___f_2379_, 3, v___x_2378_);
lean_closure_set(v___f_2379_, 4, v___f_2377_);
lean_closure_set(v___f_2379_, 5, v_a_2361_);
v___x_2380_ = lean_expr_instantiate_rev(v_binderType_2370_, v_fvars_2359_);
lean_dec_ref(v_fvars_2359_);
lean_dec_ref(v_binderType_2370_);
v___x_2381_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2349_, v_inst_2350_, v_inst_2351_, v_pre_2352_, v_post_2353_, v_usedLetOnly_2354_, v_skipConstInApp_2355_, v_skipInstances_2356_, v_x_2357_, v_x_2358_, v___x_2380_, v_a_2361_);
v___x_2382_ = lean_apply_4(v_toBind_2373_, lean_box(0), lean_box(0), v___x_2381_, v___f_2379_);
return v___x_2382_;
}
else
{
lean_object* v_toBind_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___f_2387_; lean_object* v___x_2388_; lean_object* v___f_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; 
lean_dec_ref_known(v___x_2368_, 2);
lean_dec_ref(v___x_2364_);
v_toBind_2383_ = lean_ctor_get(v_inst_2349_, 1);
lean_inc_n(v_toBind_2383_, 2);
v___x_2384_ = lean_box(v_usedLetOnly_2354_);
v___x_2385_ = lean_box(v_skipConstInApp_2355_);
v___x_2386_ = lean_box(v_skipInstances_2356_);
lean_inc(v_a_2361_);
lean_inc(v_x_2358_);
lean_inc(v_post_2353_);
lean_inc(v_pre_2352_);
lean_inc_ref(v_inst_2351_);
lean_inc_n(v_inst_2350_, 2);
lean_inc_ref(v_inst_2349_);
v___f_2387_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3___boxed), 12, 11);
lean_closure_set(v___f_2387_, 0, v_inst_2349_);
lean_closure_set(v___f_2387_, 1, v_inst_2350_);
lean_closure_set(v___f_2387_, 2, v_inst_2351_);
lean_closure_set(v___f_2387_, 3, v_pre_2352_);
lean_closure_set(v___f_2387_, 4, v_post_2353_);
lean_closure_set(v___f_2387_, 5, v___x_2384_);
lean_closure_set(v___f_2387_, 6, v___x_2385_);
lean_closure_set(v___f_2387_, 7, v___x_2386_);
lean_closure_set(v___f_2387_, 8, v_x_2357_);
lean_closure_set(v___f_2387_, 9, v_x_2358_);
lean_closure_set(v___f_2387_, 10, v_a_2361_);
v___x_2388_ = lean_box(v_usedLetOnly_2354_);
lean_inc_ref(v_fvars_2359_);
v___f_2389_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__3___boxed), 6, 5);
lean_closure_set(v___f_2389_, 0, v_fvars_2359_);
lean_closure_set(v___f_2389_, 1, v___x_2388_);
lean_closure_set(v___f_2389_, 2, v_inst_2350_);
lean_closure_set(v___f_2389_, 3, v_toBind_2383_);
lean_closure_set(v___f_2389_, 4, v___f_2387_);
v___x_2390_ = lean_expr_instantiate_rev(v_e_2360_, v_fvars_2359_);
lean_dec_ref(v_fvars_2359_);
lean_dec_ref(v_e_2360_);
v___x_2391_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2349_, v_inst_2350_, v_inst_2351_, v_pre_2352_, v_post_2353_, v_usedLetOnly_2354_, v_skipConstInApp_2355_, v_skipInstances_2356_, v_x_2357_, v_x_2358_, v___x_2390_, v_a_2361_);
v___x_2392_ = lean_apply_4(v_toBind_2383_, lean_box(0), lean_box(0), v___x_2391_, v___f_2389_);
return v___x_2392_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__0(lean_object* v_fvars_2393_, lean_object* v_inst_2394_, lean_object* v_inst_2395_, lean_object* v_inst_2396_, lean_object* v_pre_2397_, lean_object* v_post_2398_, uint8_t v_usedLetOnly_2399_, uint8_t v_skipConstInApp_2400_, uint8_t v_skipInstances_2401_, lean_object* v_x_2402_, lean_object* v_x_2403_, lean_object* v_body_2404_, lean_object* v_x_2405_, lean_object* v___y_2406_){
_start:
{
lean_object* v___x_2407_; lean_object* v___x_2408_; 
v___x_2407_ = lean_array_push(v_fvars_2393_, v_x_2405_);
v___x_2408_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(v_inst_2394_, v_inst_2395_, v_inst_2396_, v_pre_2397_, v_post_2398_, v_usedLetOnly_2399_, v_skipConstInApp_2400_, v_skipInstances_2401_, v_x_2402_, v_x_2403_, v___x_2407_, v_body_2404_, v___y_2406_);
return v___x_2408_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__0___boxed(lean_object* v_fvars_2409_, lean_object* v_inst_2410_, lean_object* v_inst_2411_, lean_object* v_inst_2412_, lean_object* v_pre_2413_, lean_object* v_post_2414_, lean_object* v_usedLetOnly_2415_, lean_object* v_skipConstInApp_2416_, lean_object* v_skipInstances_2417_, lean_object* v_x_2418_, lean_object* v_x_2419_, lean_object* v_body_2420_, lean_object* v_x_2421_, lean_object* v___y_2422_){
_start:
{
uint8_t v_usedLetOnly_boxed_2423_; uint8_t v_skipConstInApp_boxed_2424_; uint8_t v_skipInstances_boxed_2425_; lean_object* v_res_2426_; 
v_usedLetOnly_boxed_2423_ = lean_unbox(v_usedLetOnly_2415_);
v_skipConstInApp_boxed_2424_ = lean_unbox(v_skipConstInApp_2416_);
v_skipInstances_boxed_2425_ = lean_unbox(v_skipInstances_2417_);
v_res_2426_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__0(v_fvars_2409_, v_inst_2410_, v_inst_2411_, v_inst_2412_, v_pre_2413_, v_post_2414_, v_usedLetOnly_boxed_2423_, v_skipConstInApp_boxed_2424_, v_skipInstances_boxed_2425_, v_x_2418_, v_x_2419_, v_body_2420_, v_x_2421_, v___y_2422_);
lean_dec(v___y_2422_);
return v_res_2426_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(lean_object* v_inst_2427_, lean_object* v_inst_2428_, lean_object* v_inst_2429_, lean_object* v_pre_2430_, lean_object* v_post_2431_, uint8_t v_usedLetOnly_2432_, uint8_t v_skipConstInApp_2433_, uint8_t v_skipInstances_2434_, lean_object* v_x_2435_, lean_object* v_x_2436_, lean_object* v_fvars_2437_, lean_object* v_e_2438_, lean_object* v_a_2439_){
_start:
{
lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___f_2444_; lean_object* v___f_2445_; lean_object* v___x_2446_; 
v___x_2440_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0));
v___x_2441_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1));
lean_inc_ref(v_inst_2427_);
v___x_2442_ = l_Lean_MonadCacheT_instMonad___redArg(v_x_2435_, v___x_2440_, v___x_2441_, v_inst_2427_);
v___x_2443_ = l_Lean_MonadCacheT_instMonadControl___redArg(v_x_2435_, v___x_2440_, v___x_2441_);
lean_inc_ref_n(v_inst_2429_, 2);
lean_inc_ref(v___x_2443_);
v___f_2444_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_2444_, 0, v___x_2443_);
lean_closure_set(v___f_2444_, 1, v_inst_2429_);
v___f_2445_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_2445_, 0, v___x_2443_);
lean_closure_set(v___f_2445_, 1, v_inst_2429_);
v___x_2446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2446_, 0, v___f_2444_);
lean_ctor_set(v___x_2446_, 1, v___f_2445_);
if (lean_obj_tag(v_e_2438_) == 6)
{
lean_object* v_binderName_2447_; lean_object* v_binderType_2448_; lean_object* v_body_2449_; uint8_t v_binderInfo_2450_; lean_object* v_toBind_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___f_2455_; lean_object* v___x_2456_; lean_object* v___f_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; 
v_binderName_2447_ = lean_ctor_get(v_e_2438_, 0);
lean_inc(v_binderName_2447_);
v_binderType_2448_ = lean_ctor_get(v_e_2438_, 1);
lean_inc_ref(v_binderType_2448_);
v_body_2449_ = lean_ctor_get(v_e_2438_, 2);
lean_inc_ref(v_body_2449_);
v_binderInfo_2450_ = lean_ctor_get_uint8(v_e_2438_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2438_, 3);
v_toBind_2451_ = lean_ctor_get(v_inst_2427_, 1);
lean_inc(v_toBind_2451_);
v___x_2452_ = lean_box(v_usedLetOnly_2432_);
v___x_2453_ = lean_box(v_skipConstInApp_2433_);
v___x_2454_ = lean_box(v_skipInstances_2434_);
lean_inc(v_x_2436_);
lean_inc(v_post_2431_);
lean_inc(v_pre_2430_);
lean_inc_ref(v_inst_2429_);
lean_inc(v_inst_2428_);
lean_inc_ref(v_inst_2427_);
lean_inc_ref(v_fvars_2437_);
v___f_2455_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__0___boxed), 14, 12);
lean_closure_set(v___f_2455_, 0, v_fvars_2437_);
lean_closure_set(v___f_2455_, 1, v_inst_2427_);
lean_closure_set(v___f_2455_, 2, v_inst_2428_);
lean_closure_set(v___f_2455_, 3, v_inst_2429_);
lean_closure_set(v___f_2455_, 4, v_pre_2430_);
lean_closure_set(v___f_2455_, 5, v_post_2431_);
lean_closure_set(v___f_2455_, 6, v___x_2452_);
lean_closure_set(v___f_2455_, 7, v___x_2453_);
lean_closure_set(v___f_2455_, 8, v___x_2454_);
lean_closure_set(v___f_2455_, 9, v_x_2435_);
lean_closure_set(v___f_2455_, 10, v_x_2436_);
lean_closure_set(v___f_2455_, 11, v_body_2449_);
v___x_2456_ = lean_box(v_binderInfo_2450_);
lean_inc(v_a_2439_);
v___f_2457_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_2457_, 0, v___x_2446_);
lean_closure_set(v___f_2457_, 1, v___x_2442_);
lean_closure_set(v___f_2457_, 2, v_binderName_2447_);
lean_closure_set(v___f_2457_, 3, v___x_2456_);
lean_closure_set(v___f_2457_, 4, v___f_2455_);
lean_closure_set(v___f_2457_, 5, v_a_2439_);
v___x_2458_ = lean_expr_instantiate_rev(v_binderType_2448_, v_fvars_2437_);
lean_dec_ref(v_fvars_2437_);
lean_dec_ref(v_binderType_2448_);
v___x_2459_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2427_, v_inst_2428_, v_inst_2429_, v_pre_2430_, v_post_2431_, v_usedLetOnly_2432_, v_skipConstInApp_2433_, v_skipInstances_2434_, v_x_2435_, v_x_2436_, v___x_2458_, v_a_2439_);
v___x_2460_ = lean_apply_4(v_toBind_2451_, lean_box(0), lean_box(0), v___x_2459_, v___f_2457_);
return v___x_2460_;
}
else
{
lean_object* v_toBind_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___f_2465_; lean_object* v___x_2466_; lean_object* v___f_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; 
lean_dec_ref_known(v___x_2446_, 2);
lean_dec_ref(v___x_2442_);
v_toBind_2461_ = lean_ctor_get(v_inst_2427_, 1);
lean_inc_n(v_toBind_2461_, 2);
v___x_2462_ = lean_box(v_usedLetOnly_2432_);
v___x_2463_ = lean_box(v_skipConstInApp_2433_);
v___x_2464_ = lean_box(v_skipInstances_2434_);
lean_inc(v_a_2439_);
lean_inc(v_x_2436_);
lean_inc(v_post_2431_);
lean_inc(v_pre_2430_);
lean_inc_ref(v_inst_2429_);
lean_inc_n(v_inst_2428_, 2);
lean_inc_ref(v_inst_2427_);
v___f_2465_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3___boxed), 12, 11);
lean_closure_set(v___f_2465_, 0, v_inst_2427_);
lean_closure_set(v___f_2465_, 1, v_inst_2428_);
lean_closure_set(v___f_2465_, 2, v_inst_2429_);
lean_closure_set(v___f_2465_, 3, v_pre_2430_);
lean_closure_set(v___f_2465_, 4, v_post_2431_);
lean_closure_set(v___f_2465_, 5, v___x_2462_);
lean_closure_set(v___f_2465_, 6, v___x_2463_);
lean_closure_set(v___f_2465_, 7, v___x_2464_);
lean_closure_set(v___f_2465_, 8, v_x_2435_);
lean_closure_set(v___f_2465_, 9, v_x_2436_);
lean_closure_set(v___f_2465_, 10, v_a_2439_);
v___x_2466_ = lean_box(v_usedLetOnly_2432_);
lean_inc_ref(v_fvars_2437_);
v___f_2467_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__3___boxed), 6, 5);
lean_closure_set(v___f_2467_, 0, v_fvars_2437_);
lean_closure_set(v___f_2467_, 1, v___x_2466_);
lean_closure_set(v___f_2467_, 2, v_inst_2428_);
lean_closure_set(v___f_2467_, 3, v_toBind_2461_);
lean_closure_set(v___f_2467_, 4, v___f_2465_);
v___x_2468_ = lean_expr_instantiate_rev(v_e_2438_, v_fvars_2437_);
lean_dec_ref(v_fvars_2437_);
lean_dec_ref(v_e_2438_);
v___x_2469_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2427_, v_inst_2428_, v_inst_2429_, v_pre_2430_, v_post_2431_, v_usedLetOnly_2432_, v_skipConstInApp_2433_, v_skipInstances_2434_, v_x_2435_, v_x_2436_, v___x_2468_, v_a_2439_);
v___x_2470_ = lean_apply_4(v_toBind_2461_, lean_box(0), lean_box(0), v___x_2469_, v___f_2467_);
return v___x_2470_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__0(lean_object* v_fvars_2471_, lean_object* v_inst_2472_, lean_object* v_inst_2473_, lean_object* v_inst_2474_, lean_object* v_pre_2475_, lean_object* v_post_2476_, uint8_t v_usedLetOnly_2477_, uint8_t v_skipConstInApp_2478_, uint8_t v_skipInstances_2479_, lean_object* v_x_2480_, lean_object* v_x_2481_, lean_object* v_body_2482_, lean_object* v_x_2483_, lean_object* v___y_2484_){
_start:
{
lean_object* v___x_2485_; lean_object* v___x_2486_; 
v___x_2485_ = lean_array_push(v_fvars_2471_, v_x_2483_);
v___x_2486_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(v_inst_2472_, v_inst_2473_, v_inst_2474_, v_pre_2475_, v_post_2476_, v_usedLetOnly_2477_, v_skipConstInApp_2478_, v_skipInstances_2479_, v_x_2480_, v_x_2481_, v___x_2485_, v_body_2482_, v___y_2484_);
return v___x_2486_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__0___boxed(lean_object* v_fvars_2487_, lean_object* v_inst_2488_, lean_object* v_inst_2489_, lean_object* v_inst_2490_, lean_object* v_pre_2491_, lean_object* v_post_2492_, lean_object* v_usedLetOnly_2493_, lean_object* v_skipConstInApp_2494_, lean_object* v_skipInstances_2495_, lean_object* v_x_2496_, lean_object* v_x_2497_, lean_object* v_body_2498_, lean_object* v_x_2499_, lean_object* v___y_2500_){
_start:
{
uint8_t v_usedLetOnly_boxed_2501_; uint8_t v_skipConstInApp_boxed_2502_; uint8_t v_skipInstances_boxed_2503_; lean_object* v_res_2504_; 
v_usedLetOnly_boxed_2501_ = lean_unbox(v_usedLetOnly_2493_);
v_skipConstInApp_boxed_2502_ = lean_unbox(v_skipConstInApp_2494_);
v_skipInstances_boxed_2503_ = lean_unbox(v_skipInstances_2495_);
v_res_2504_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__0(v_fvars_2487_, v_inst_2488_, v_inst_2489_, v_inst_2490_, v_pre_2491_, v_post_2492_, v_usedLetOnly_boxed_2501_, v_skipConstInApp_boxed_2502_, v_skipInstances_boxed_2503_, v_x_2496_, v_x_2497_, v_body_2498_, v_x_2499_, v___y_2500_);
lean_dec(v___y_2500_);
return v_res_2504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__2(lean_object* v___x_2505_, lean_object* v___x_2506_, lean_object* v_declName_2507_, lean_object* v___f_2508_, uint8_t v_nondep_2509_, lean_object* v_a_2510_, lean_object* v_value_2511_, lean_object* v_fvars_2512_, lean_object* v_inst_2513_, lean_object* v_inst_2514_, lean_object* v_inst_2515_, lean_object* v_pre_2516_, lean_object* v_post_2517_, uint8_t v_usedLetOnly_2518_, uint8_t v_skipConstInApp_2519_, uint8_t v_skipInstances_2520_, lean_object* v_x_2521_, lean_object* v_x_2522_, lean_object* v_toBind_2523_, lean_object* v_a_2524_){
_start:
{
lean_object* v___x_2525_; lean_object* v___f_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; 
v___x_2525_ = lean_box(v_nondep_2509_);
lean_inc(v_a_2510_);
v___f_2526_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_2526_, 0, v___x_2505_);
lean_closure_set(v___f_2526_, 1, v___x_2506_);
lean_closure_set(v___f_2526_, 2, v_declName_2507_);
lean_closure_set(v___f_2526_, 3, v_a_2524_);
lean_closure_set(v___f_2526_, 4, v___f_2508_);
lean_closure_set(v___f_2526_, 5, v___x_2525_);
lean_closure_set(v___f_2526_, 6, v_a_2510_);
v___x_2527_ = lean_expr_instantiate_rev(v_value_2511_, v_fvars_2512_);
v___x_2528_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2513_, v_inst_2514_, v_inst_2515_, v_pre_2516_, v_post_2517_, v_usedLetOnly_2518_, v_skipConstInApp_2519_, v_skipInstances_2520_, v_x_2521_, v_x_2522_, v___x_2527_, v_a_2510_);
v___x_2529_ = lean_apply_4(v_toBind_2523_, lean_box(0), lean_box(0), v___x_2528_, v___f_2526_);
return v___x_2529_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__2___boxed(lean_object** _args){
lean_object* v___x_2530_ = _args[0];
lean_object* v___x_2531_ = _args[1];
lean_object* v_declName_2532_ = _args[2];
lean_object* v___f_2533_ = _args[3];
lean_object* v_nondep_2534_ = _args[4];
lean_object* v_a_2535_ = _args[5];
lean_object* v_value_2536_ = _args[6];
lean_object* v_fvars_2537_ = _args[7];
lean_object* v_inst_2538_ = _args[8];
lean_object* v_inst_2539_ = _args[9];
lean_object* v_inst_2540_ = _args[10];
lean_object* v_pre_2541_ = _args[11];
lean_object* v_post_2542_ = _args[12];
lean_object* v_usedLetOnly_2543_ = _args[13];
lean_object* v_skipConstInApp_2544_ = _args[14];
lean_object* v_skipInstances_2545_ = _args[15];
lean_object* v_x_2546_ = _args[16];
lean_object* v_x_2547_ = _args[17];
lean_object* v_toBind_2548_ = _args[18];
lean_object* v_a_2549_ = _args[19];
_start:
{
uint8_t v_nondep_3815__boxed_2550_; uint8_t v_usedLetOnly_boxed_2551_; uint8_t v_skipConstInApp_boxed_2552_; uint8_t v_skipInstances_boxed_2553_; lean_object* v_res_2554_; 
v_nondep_3815__boxed_2550_ = lean_unbox(v_nondep_2534_);
v_usedLetOnly_boxed_2551_ = lean_unbox(v_usedLetOnly_2543_);
v_skipConstInApp_boxed_2552_ = lean_unbox(v_skipConstInApp_2544_);
v_skipInstances_boxed_2553_ = lean_unbox(v_skipInstances_2545_);
v_res_2554_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__2(v___x_2530_, v___x_2531_, v_declName_2532_, v___f_2533_, v_nondep_3815__boxed_2550_, v_a_2535_, v_value_2536_, v_fvars_2537_, v_inst_2538_, v_inst_2539_, v_inst_2540_, v_pre_2541_, v_post_2542_, v_usedLetOnly_boxed_2551_, v_skipConstInApp_boxed_2552_, v_skipInstances_boxed_2553_, v_x_2546_, v_x_2547_, v_toBind_2548_, v_a_2549_);
lean_dec_ref(v_fvars_2537_);
lean_dec_ref(v_value_2536_);
lean_dec(v_a_2535_);
return v_res_2554_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(lean_object* v_inst_2555_, lean_object* v_inst_2556_, lean_object* v_inst_2557_, lean_object* v_pre_2558_, lean_object* v_post_2559_, uint8_t v_usedLetOnly_2560_, uint8_t v_skipConstInApp_2561_, uint8_t v_skipInstances_2562_, lean_object* v_x_2563_, lean_object* v_x_2564_, lean_object* v_fvars_2565_, lean_object* v_e_2566_, lean_object* v_a_2567_){
_start:
{
lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___f_2572_; lean_object* v___f_2573_; lean_object* v___x_2574_; 
v___x_2568_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0));
v___x_2569_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1));
lean_inc_ref(v_inst_2555_);
v___x_2570_ = l_Lean_MonadCacheT_instMonad___redArg(v_x_2563_, v___x_2568_, v___x_2569_, v_inst_2555_);
v___x_2571_ = l_Lean_MonadCacheT_instMonadControl___redArg(v_x_2563_, v___x_2568_, v___x_2569_);
lean_inc_ref_n(v_inst_2557_, 2);
lean_inc_ref(v___x_2571_);
v___f_2572_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_2572_, 0, v___x_2571_);
lean_closure_set(v___f_2572_, 1, v_inst_2557_);
v___f_2573_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_2573_, 0, v___x_2571_);
lean_closure_set(v___f_2573_, 1, v_inst_2557_);
v___x_2574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2574_, 0, v___f_2572_);
lean_ctor_set(v___x_2574_, 1, v___f_2573_);
if (lean_obj_tag(v_e_2566_) == 8)
{
lean_object* v_declName_2575_; lean_object* v_type_2576_; lean_object* v_value_2577_; lean_object* v_body_2578_; uint8_t v_nondep_2579_; lean_object* v_toBind_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___f_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___f_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; 
v_declName_2575_ = lean_ctor_get(v_e_2566_, 0);
lean_inc(v_declName_2575_);
v_type_2576_ = lean_ctor_get(v_e_2566_, 1);
lean_inc_ref(v_type_2576_);
v_value_2577_ = lean_ctor_get(v_e_2566_, 2);
lean_inc_ref(v_value_2577_);
v_body_2578_ = lean_ctor_get(v_e_2566_, 3);
lean_inc_ref(v_body_2578_);
v_nondep_2579_ = lean_ctor_get_uint8(v_e_2566_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_2566_, 4);
v_toBind_2580_ = lean_ctor_get(v_inst_2555_, 1);
lean_inc_n(v_toBind_2580_, 2);
v___x_2581_ = lean_box(v_usedLetOnly_2560_);
v___x_2582_ = lean_box(v_skipConstInApp_2561_);
v___x_2583_ = lean_box(v_skipInstances_2562_);
lean_inc_n(v_x_2564_, 2);
lean_inc_n(v_post_2559_, 2);
lean_inc_n(v_pre_2558_, 2);
lean_inc_ref_n(v_inst_2557_, 2);
lean_inc_n(v_inst_2556_, 2);
lean_inc_ref_n(v_inst_2555_, 2);
lean_inc_ref_n(v_fvars_2565_, 2);
v___f_2584_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__0___boxed), 14, 12);
lean_closure_set(v___f_2584_, 0, v_fvars_2565_);
lean_closure_set(v___f_2584_, 1, v_inst_2555_);
lean_closure_set(v___f_2584_, 2, v_inst_2556_);
lean_closure_set(v___f_2584_, 3, v_inst_2557_);
lean_closure_set(v___f_2584_, 4, v_pre_2558_);
lean_closure_set(v___f_2584_, 5, v_post_2559_);
lean_closure_set(v___f_2584_, 6, v___x_2581_);
lean_closure_set(v___f_2584_, 7, v___x_2582_);
lean_closure_set(v___f_2584_, 8, v___x_2583_);
lean_closure_set(v___f_2584_, 9, v_x_2563_);
lean_closure_set(v___f_2584_, 10, v_x_2564_);
lean_closure_set(v___f_2584_, 11, v_body_2578_);
v___x_2585_ = lean_box(v_nondep_2579_);
v___x_2586_ = lean_box(v_usedLetOnly_2560_);
v___x_2587_ = lean_box(v_skipConstInApp_2561_);
v___x_2588_ = lean_box(v_skipInstances_2562_);
lean_inc(v_a_2567_);
v___f_2589_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__2___boxed), 20, 19);
lean_closure_set(v___f_2589_, 0, v___x_2574_);
lean_closure_set(v___f_2589_, 1, v___x_2570_);
lean_closure_set(v___f_2589_, 2, v_declName_2575_);
lean_closure_set(v___f_2589_, 3, v___f_2584_);
lean_closure_set(v___f_2589_, 4, v___x_2585_);
lean_closure_set(v___f_2589_, 5, v_a_2567_);
lean_closure_set(v___f_2589_, 6, v_value_2577_);
lean_closure_set(v___f_2589_, 7, v_fvars_2565_);
lean_closure_set(v___f_2589_, 8, v_inst_2555_);
lean_closure_set(v___f_2589_, 9, v_inst_2556_);
lean_closure_set(v___f_2589_, 10, v_inst_2557_);
lean_closure_set(v___f_2589_, 11, v_pre_2558_);
lean_closure_set(v___f_2589_, 12, v_post_2559_);
lean_closure_set(v___f_2589_, 13, v___x_2586_);
lean_closure_set(v___f_2589_, 14, v___x_2587_);
lean_closure_set(v___f_2589_, 15, v___x_2588_);
lean_closure_set(v___f_2589_, 16, v_x_2563_);
lean_closure_set(v___f_2589_, 17, v_x_2564_);
lean_closure_set(v___f_2589_, 18, v_toBind_2580_);
v___x_2590_ = lean_expr_instantiate_rev(v_type_2576_, v_fvars_2565_);
lean_dec_ref(v_fvars_2565_);
lean_dec_ref(v_type_2576_);
v___x_2591_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2555_, v_inst_2556_, v_inst_2557_, v_pre_2558_, v_post_2559_, v_usedLetOnly_2560_, v_skipConstInApp_2561_, v_skipInstances_2562_, v_x_2563_, v_x_2564_, v___x_2590_, v_a_2567_);
v___x_2592_ = lean_apply_4(v_toBind_2580_, lean_box(0), lean_box(0), v___x_2591_, v___f_2589_);
return v___x_2592_;
}
else
{
lean_object* v_toBind_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___f_2597_; lean_object* v___x_2598_; lean_object* v___f_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; 
lean_dec_ref_known(v___x_2574_, 2);
lean_dec_ref(v___x_2570_);
v_toBind_2593_ = lean_ctor_get(v_inst_2555_, 1);
lean_inc_n(v_toBind_2593_, 2);
v___x_2594_ = lean_box(v_usedLetOnly_2560_);
v___x_2595_ = lean_box(v_skipConstInApp_2561_);
v___x_2596_ = lean_box(v_skipInstances_2562_);
lean_inc(v_a_2567_);
lean_inc(v_x_2564_);
lean_inc(v_post_2559_);
lean_inc(v_pre_2558_);
lean_inc_ref(v_inst_2557_);
lean_inc_n(v_inst_2556_, 2);
lean_inc_ref(v_inst_2555_);
v___f_2597_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3___boxed), 12, 11);
lean_closure_set(v___f_2597_, 0, v_inst_2555_);
lean_closure_set(v___f_2597_, 1, v_inst_2556_);
lean_closure_set(v___f_2597_, 2, v_inst_2557_);
lean_closure_set(v___f_2597_, 3, v_pre_2558_);
lean_closure_set(v___f_2597_, 4, v_post_2559_);
lean_closure_set(v___f_2597_, 5, v___x_2594_);
lean_closure_set(v___f_2597_, 6, v___x_2595_);
lean_closure_set(v___f_2597_, 7, v___x_2596_);
lean_closure_set(v___f_2597_, 8, v_x_2563_);
lean_closure_set(v___f_2597_, 9, v_x_2564_);
lean_closure_set(v___f_2597_, 10, v_a_2567_);
v___x_2598_ = lean_box(v_usedLetOnly_2560_);
lean_inc_ref(v_fvars_2565_);
v___f_2599_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__4___boxed), 6, 5);
lean_closure_set(v___f_2599_, 0, v_fvars_2565_);
lean_closure_set(v___f_2599_, 1, v___x_2598_);
lean_closure_set(v___f_2599_, 2, v_inst_2556_);
lean_closure_set(v___f_2599_, 3, v_toBind_2593_);
lean_closure_set(v___f_2599_, 4, v___f_2597_);
v___x_2600_ = lean_expr_instantiate_rev(v_e_2566_, v_fvars_2565_);
lean_dec_ref(v_fvars_2565_);
lean_dec_ref(v_e_2566_);
v___x_2601_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2555_, v_inst_2556_, v_inst_2557_, v_pre_2558_, v_post_2559_, v_usedLetOnly_2560_, v_skipConstInApp_2561_, v_skipInstances_2562_, v_x_2563_, v_x_2564_, v___x_2600_, v_a_2567_);
v___x_2602_ = lean_apply_4(v_toBind_2593_, lean_box(0), lean_box(0), v___x_2601_, v___f_2599_);
return v___x_2602_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__8(lean_object* v_expr_2603_, lean_object* v_data_2604_, lean_object* v_inst_2605_, lean_object* v_inst_2606_, lean_object* v_inst_2607_, lean_object* v_pre_2608_, lean_object* v_post_2609_, uint8_t v_usedLetOnly_2610_, uint8_t v_skipConstInApp_2611_, uint8_t v_skipInstances_2612_, lean_object* v_x_2613_, lean_object* v_x_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v_a_2617_){
_start:
{
size_t v___x_2618_; size_t v___x_2619_; uint8_t v___x_2620_; 
v___x_2618_ = lean_ptr_addr(v_expr_2603_);
v___x_2619_ = lean_ptr_addr(v_a_2617_);
v___x_2620_ = lean_usize_dec_eq(v___x_2618_, v___x_2619_);
if (v___x_2620_ == 0)
{
lean_object* v___x_2621_; lean_object* v___x_2622_; 
lean_dec_ref(v___y_2616_);
v___x_2621_ = l_Lean_Expr_mdata___override(v_data_2604_, v_a_2617_);
v___x_2622_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2605_, v_inst_2606_, v_inst_2607_, v_pre_2608_, v_post_2609_, v_usedLetOnly_2610_, v_skipConstInApp_2611_, v_skipInstances_2612_, v_x_2613_, v_x_2614_, v___x_2621_, v___y_2615_);
return v___x_2622_;
}
else
{
lean_object* v___x_2623_; 
lean_dec_ref(v_a_2617_);
lean_dec(v_data_2604_);
v___x_2623_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2605_, v_inst_2606_, v_inst_2607_, v_pre_2608_, v_post_2609_, v_usedLetOnly_2610_, v_skipConstInApp_2611_, v_skipInstances_2612_, v_x_2613_, v_x_2614_, v___y_2616_, v___y_2615_);
return v___x_2623_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__8___boxed(lean_object* v_expr_2624_, lean_object* v_data_2625_, lean_object* v_inst_2626_, lean_object* v_inst_2627_, lean_object* v_inst_2628_, lean_object* v_pre_2629_, lean_object* v_post_2630_, lean_object* v_usedLetOnly_2631_, lean_object* v_skipConstInApp_2632_, lean_object* v_skipInstances_2633_, lean_object* v_x_2634_, lean_object* v_x_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v_a_2638_){
_start:
{
uint8_t v_usedLetOnly_boxed_2639_; uint8_t v_skipConstInApp_boxed_2640_; uint8_t v_skipInstances_boxed_2641_; lean_object* v_res_2642_; 
v_usedLetOnly_boxed_2639_ = lean_unbox(v_usedLetOnly_2631_);
v_skipConstInApp_boxed_2640_ = lean_unbox(v_skipConstInApp_2632_);
v_skipInstances_boxed_2641_ = lean_unbox(v_skipInstances_2633_);
v_res_2642_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__8(v_expr_2624_, v_data_2625_, v_inst_2626_, v_inst_2627_, v_inst_2628_, v_pre_2629_, v_post_2630_, v_usedLetOnly_boxed_2639_, v_skipConstInApp_boxed_2640_, v_skipInstances_boxed_2641_, v_x_2634_, v_x_2635_, v___y_2636_, v___y_2637_, v_a_2638_);
lean_dec(v___y_2636_);
lean_dec_ref(v_expr_2624_);
return v_res_2642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__10(lean_object* v_struct_2643_, lean_object* v_typeName_2644_, lean_object* v_idx_2645_, lean_object* v_inst_2646_, lean_object* v_inst_2647_, lean_object* v_inst_2648_, lean_object* v_pre_2649_, lean_object* v_post_2650_, uint8_t v_usedLetOnly_2651_, uint8_t v_skipConstInApp_2652_, uint8_t v_skipInstances_2653_, lean_object* v_x_2654_, lean_object* v_x_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v_a_2658_){
_start:
{
size_t v___x_2659_; size_t v___x_2660_; uint8_t v___x_2661_; 
v___x_2659_ = lean_ptr_addr(v_struct_2643_);
v___x_2660_ = lean_ptr_addr(v_a_2658_);
v___x_2661_ = lean_usize_dec_eq(v___x_2659_, v___x_2660_);
if (v___x_2661_ == 0)
{
lean_object* v___x_2662_; lean_object* v___x_2663_; 
lean_dec_ref(v___y_2657_);
v___x_2662_ = l_Lean_Expr_proj___override(v_typeName_2644_, v_idx_2645_, v_a_2658_);
v___x_2663_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2646_, v_inst_2647_, v_inst_2648_, v_pre_2649_, v_post_2650_, v_usedLetOnly_2651_, v_skipConstInApp_2652_, v_skipInstances_2653_, v_x_2654_, v_x_2655_, v___x_2662_, v___y_2656_);
return v___x_2663_;
}
else
{
lean_object* v___x_2664_; 
lean_dec_ref(v_a_2658_);
lean_dec(v_idx_2645_);
lean_dec(v_typeName_2644_);
v___x_2664_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2646_, v_inst_2647_, v_inst_2648_, v_pre_2649_, v_post_2650_, v_usedLetOnly_2651_, v_skipConstInApp_2652_, v_skipInstances_2653_, v_x_2654_, v_x_2655_, v___y_2657_, v___y_2656_);
return v___x_2664_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__10___boxed(lean_object* v_struct_2665_, lean_object* v_typeName_2666_, lean_object* v_idx_2667_, lean_object* v_inst_2668_, lean_object* v_inst_2669_, lean_object* v_inst_2670_, lean_object* v_pre_2671_, lean_object* v_post_2672_, lean_object* v_usedLetOnly_2673_, lean_object* v_skipConstInApp_2674_, lean_object* v_skipInstances_2675_, lean_object* v_x_2676_, lean_object* v_x_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v_a_2680_){
_start:
{
uint8_t v_usedLetOnly_boxed_2681_; uint8_t v_skipConstInApp_boxed_2682_; uint8_t v_skipInstances_boxed_2683_; lean_object* v_res_2684_; 
v_usedLetOnly_boxed_2681_ = lean_unbox(v_usedLetOnly_2673_);
v_skipConstInApp_boxed_2682_ = lean_unbox(v_skipConstInApp_2674_);
v_skipInstances_boxed_2683_ = lean_unbox(v_skipInstances_2675_);
v_res_2684_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__10(v_struct_2665_, v_typeName_2666_, v_idx_2667_, v_inst_2668_, v_inst_2669_, v_inst_2670_, v_pre_2671_, v_post_2672_, v_usedLetOnly_boxed_2681_, v_skipConstInApp_boxed_2682_, v_skipInstances_boxed_2683_, v_x_2676_, v_x_2677_, v___y_2678_, v___y_2679_, v_a_2680_);
lean_dec(v___y_2678_);
lean_dec_ref(v_struct_2665_);
return v_res_2684_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11(lean_object* v_toApplicative_2685_, lean_object* v_inst_2686_, lean_object* v_inst_2687_, lean_object* v_inst_2688_, lean_object* v_pre_2689_, lean_object* v_post_2690_, uint8_t v_usedLetOnly_2691_, uint8_t v_skipConstInApp_2692_, uint8_t v_skipInstances_2693_, lean_object* v_x_2694_, lean_object* v_x_2695_, lean_object* v___y_2696_, lean_object* v___f_2697_, lean_object* v_toBind_2698_, lean_object* v_e_2699_, lean_object* v_a_2700_){
_start:
{
lean_object* v___y_2702_; 
switch(lean_obj_tag(v_a_2700_))
{
case 0:
{
lean_object* v_e_2734_; lean_object* v_toPure_2735_; lean_object* v___x_2736_; 
lean_dec_ref(v_e_2699_);
lean_dec(v_toBind_2698_);
lean_dec(v___f_2697_);
lean_dec(v_x_2695_);
lean_dec(v_post_2690_);
lean_dec(v_pre_2689_);
lean_dec_ref(v_inst_2688_);
lean_dec(v_inst_2687_);
lean_dec_ref(v_inst_2686_);
v_e_2734_ = lean_ctor_get(v_a_2700_, 0);
lean_inc_ref(v_e_2734_);
lean_dec_ref_known(v_a_2700_, 1);
v_toPure_2735_ = lean_ctor_get(v_toApplicative_2685_, 1);
lean_inc(v_toPure_2735_);
lean_dec_ref(v_toApplicative_2685_);
v___x_2736_ = lean_apply_2(v_toPure_2735_, lean_box(0), v_e_2734_);
return v___x_2736_;
}
case 1:
{
lean_object* v_e_2737_; lean_object* v___x_2738_; 
lean_dec_ref(v_e_2699_);
lean_dec(v_toBind_2698_);
lean_dec(v___f_2697_);
lean_dec_ref(v_toApplicative_2685_);
v_e_2737_ = lean_ctor_get(v_a_2700_, 0);
lean_inc_ref(v_e_2737_);
lean_dec_ref_known(v_a_2700_, 1);
v___x_2738_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2686_, v_inst_2687_, v_inst_2688_, v_pre_2689_, v_post_2690_, v_usedLetOnly_2691_, v_skipConstInApp_2692_, v_skipInstances_2693_, v_x_2694_, v_x_2695_, v_e_2737_, v___y_2696_);
return v___x_2738_;
}
default: 
{
lean_object* v_e_x3f_2739_; 
lean_dec_ref(v_toApplicative_2685_);
v_e_x3f_2739_ = lean_ctor_get(v_a_2700_, 0);
lean_inc(v_e_x3f_2739_);
lean_dec_ref_known(v_a_2700_, 1);
if (lean_obj_tag(v_e_x3f_2739_) == 0)
{
v___y_2702_ = v_e_2699_;
goto v___jp_2701_;
}
else
{
lean_object* v_val_2740_; 
lean_dec_ref(v_e_2699_);
v_val_2740_ = lean_ctor_get(v_e_x3f_2739_, 0);
lean_inc(v_val_2740_);
lean_dec_ref_known(v_e_x3f_2739_, 1);
v___y_2702_ = v_val_2740_;
goto v___jp_2701_;
}
}
}
v___jp_2701_:
{
switch(lean_obj_tag(v___y_2702_))
{
case 7:
{
lean_object* v___x_2703_; lean_object* v___x_2704_; 
lean_dec(v_toBind_2698_);
lean_dec(v___f_2697_);
v___x_2703_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_2704_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(v_inst_2686_, v_inst_2687_, v_inst_2688_, v_pre_2689_, v_post_2690_, v_usedLetOnly_2691_, v_skipConstInApp_2692_, v_skipInstances_2693_, v_x_2694_, v_x_2695_, v___x_2703_, v___y_2702_, v___y_2696_);
return v___x_2704_;
}
case 6:
{
lean_object* v___x_2705_; lean_object* v___x_2706_; 
lean_dec(v_toBind_2698_);
lean_dec(v___f_2697_);
v___x_2705_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_2706_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(v_inst_2686_, v_inst_2687_, v_inst_2688_, v_pre_2689_, v_post_2690_, v_usedLetOnly_2691_, v_skipConstInApp_2692_, v_skipInstances_2693_, v_x_2694_, v_x_2695_, v___x_2705_, v___y_2702_, v___y_2696_);
return v___x_2706_;
}
case 8:
{
lean_object* v___x_2707_; lean_object* v___x_2708_; 
lean_dec(v_toBind_2698_);
lean_dec(v___f_2697_);
v___x_2707_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_2708_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(v_inst_2686_, v_inst_2687_, v_inst_2688_, v_pre_2689_, v_post_2690_, v_usedLetOnly_2691_, v_skipConstInApp_2692_, v_skipInstances_2693_, v_x_2694_, v_x_2695_, v___x_2707_, v___y_2702_, v___y_2696_);
return v___x_2708_;
}
case 5:
{
lean_object* v_dummy_2709_; lean_object* v_nargs_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_3361__overap_2714_; lean_object* v___x_2715_; 
lean_dec(v_toBind_2698_);
lean_dec(v_x_2695_);
lean_dec(v_post_2690_);
lean_dec(v_pre_2689_);
lean_dec_ref(v_inst_2688_);
lean_dec(v_inst_2687_);
lean_dec_ref(v_inst_2686_);
v_dummy_2709_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_2710_ = l_Lean_Expr_getAppNumArgs(v___y_2702_);
lean_inc(v_nargs_2710_);
v___x_2711_ = lean_mk_array(v_nargs_2710_, v_dummy_2709_);
v___x_2712_ = lean_unsigned_to_nat(1u);
v___x_2713_ = lean_nat_sub(v_nargs_2710_, v___x_2712_);
lean_dec(v_nargs_2710_);
v___x_3361__overap_2714_ = l_Lean_Expr_withAppAux___redArg(v___f_2697_, v___y_2702_, v___x_2711_, v___x_2713_);
lean_inc(v___y_2696_);
v___x_2715_ = lean_apply_1(v___x_3361__overap_2714_, v___y_2696_);
return v___x_2715_;
}
case 10:
{
lean_object* v_data_2716_; lean_object* v_expr_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___f_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; 
lean_dec(v___f_2697_);
v_data_2716_ = lean_ctor_get(v___y_2702_, 0);
lean_inc(v_data_2716_);
v_expr_2717_ = lean_ctor_get(v___y_2702_, 1);
lean_inc_ref_n(v_expr_2717_, 2);
v___x_2718_ = lean_box(v_usedLetOnly_2691_);
v___x_2719_ = lean_box(v_skipConstInApp_2692_);
v___x_2720_ = lean_box(v_skipInstances_2693_);
lean_inc(v___y_2696_);
lean_inc(v_x_2695_);
lean_inc(v_post_2690_);
lean_inc(v_pre_2689_);
lean_inc_ref(v_inst_2688_);
lean_inc(v_inst_2687_);
lean_inc_ref(v_inst_2686_);
v___f_2721_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__8___boxed), 15, 14);
lean_closure_set(v___f_2721_, 0, v_expr_2717_);
lean_closure_set(v___f_2721_, 1, v_data_2716_);
lean_closure_set(v___f_2721_, 2, v_inst_2686_);
lean_closure_set(v___f_2721_, 3, v_inst_2687_);
lean_closure_set(v___f_2721_, 4, v_inst_2688_);
lean_closure_set(v___f_2721_, 5, v_pre_2689_);
lean_closure_set(v___f_2721_, 6, v_post_2690_);
lean_closure_set(v___f_2721_, 7, v___x_2718_);
lean_closure_set(v___f_2721_, 8, v___x_2719_);
lean_closure_set(v___f_2721_, 9, v___x_2720_);
lean_closure_set(v___f_2721_, 10, v_x_2694_);
lean_closure_set(v___f_2721_, 11, v_x_2695_);
lean_closure_set(v___f_2721_, 12, v___y_2696_);
lean_closure_set(v___f_2721_, 13, v___y_2702_);
v___x_2722_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2686_, v_inst_2687_, v_inst_2688_, v_pre_2689_, v_post_2690_, v_usedLetOnly_2691_, v_skipConstInApp_2692_, v_skipInstances_2693_, v_x_2694_, v_x_2695_, v_expr_2717_, v___y_2696_);
v___x_2723_ = lean_apply_4(v_toBind_2698_, lean_box(0), lean_box(0), v___x_2722_, v___f_2721_);
return v___x_2723_;
}
case 11:
{
lean_object* v_typeName_2724_; lean_object* v_idx_2725_; lean_object* v_struct_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___f_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; 
lean_dec(v___f_2697_);
v_typeName_2724_ = lean_ctor_get(v___y_2702_, 0);
lean_inc(v_typeName_2724_);
v_idx_2725_ = lean_ctor_get(v___y_2702_, 1);
lean_inc(v_idx_2725_);
v_struct_2726_ = lean_ctor_get(v___y_2702_, 2);
lean_inc_ref_n(v_struct_2726_, 2);
v___x_2727_ = lean_box(v_usedLetOnly_2691_);
v___x_2728_ = lean_box(v_skipConstInApp_2692_);
v___x_2729_ = lean_box(v_skipInstances_2693_);
lean_inc(v___y_2696_);
lean_inc(v_x_2695_);
lean_inc(v_post_2690_);
lean_inc(v_pre_2689_);
lean_inc_ref(v_inst_2688_);
lean_inc(v_inst_2687_);
lean_inc_ref(v_inst_2686_);
v___f_2730_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__10___boxed), 16, 15);
lean_closure_set(v___f_2730_, 0, v_struct_2726_);
lean_closure_set(v___f_2730_, 1, v_typeName_2724_);
lean_closure_set(v___f_2730_, 2, v_idx_2725_);
lean_closure_set(v___f_2730_, 3, v_inst_2686_);
lean_closure_set(v___f_2730_, 4, v_inst_2687_);
lean_closure_set(v___f_2730_, 5, v_inst_2688_);
lean_closure_set(v___f_2730_, 6, v_pre_2689_);
lean_closure_set(v___f_2730_, 7, v_post_2690_);
lean_closure_set(v___f_2730_, 8, v___x_2727_);
lean_closure_set(v___f_2730_, 9, v___x_2728_);
lean_closure_set(v___f_2730_, 10, v___x_2729_);
lean_closure_set(v___f_2730_, 11, v_x_2694_);
lean_closure_set(v___f_2730_, 12, v_x_2695_);
lean_closure_set(v___f_2730_, 13, v___y_2696_);
lean_closure_set(v___f_2730_, 14, v___y_2702_);
v___x_2731_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2686_, v_inst_2687_, v_inst_2688_, v_pre_2689_, v_post_2690_, v_usedLetOnly_2691_, v_skipConstInApp_2692_, v_skipInstances_2693_, v_x_2694_, v_x_2695_, v_struct_2726_, v___y_2696_);
v___x_2732_ = lean_apply_4(v_toBind_2698_, lean_box(0), lean_box(0), v___x_2731_, v___f_2730_);
return v___x_2732_;
}
default: 
{
lean_object* v___x_2733_; 
lean_dec(v_toBind_2698_);
lean_dec(v___f_2697_);
v___x_2733_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2686_, v_inst_2687_, v_inst_2688_, v_pre_2689_, v_post_2690_, v_usedLetOnly_2691_, v_skipConstInApp_2692_, v_skipInstances_2693_, v_x_2694_, v_x_2695_, v___y_2702_, v___y_2696_);
return v___x_2733_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___boxed(lean_object* v_toApplicative_2741_, lean_object* v_inst_2742_, lean_object* v_inst_2743_, lean_object* v_inst_2744_, lean_object* v_pre_2745_, lean_object* v_post_2746_, lean_object* v_usedLetOnly_2747_, lean_object* v_skipConstInApp_2748_, lean_object* v_skipInstances_2749_, lean_object* v_x_2750_, lean_object* v_x_2751_, lean_object* v___y_2752_, lean_object* v___f_2753_, lean_object* v_toBind_2754_, lean_object* v_e_2755_, lean_object* v_a_2756_){
_start:
{
uint8_t v_usedLetOnly_boxed_2757_; uint8_t v_skipConstInApp_boxed_2758_; uint8_t v_skipInstances_boxed_2759_; lean_object* v_res_2760_; 
v_usedLetOnly_boxed_2757_ = lean_unbox(v_usedLetOnly_2747_);
v_skipConstInApp_boxed_2758_ = lean_unbox(v_skipConstInApp_2748_);
v_skipInstances_boxed_2759_ = lean_unbox(v_skipInstances_2749_);
v_res_2760_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11(v_toApplicative_2741_, v_inst_2742_, v_inst_2743_, v_inst_2744_, v_pre_2745_, v_post_2746_, v_usedLetOnly_boxed_2757_, v_skipConstInApp_boxed_2758_, v_skipInstances_boxed_2759_, v_x_2750_, v_x_2751_, v___y_2752_, v___f_2753_, v_toBind_2754_, v_e_2755_, v_a_2756_);
lean_dec(v___y_2752_);
return v_res_2760_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12(lean_object* v_toApplicative_2761_, lean_object* v_inst_2762_, lean_object* v_inst_2763_, lean_object* v_inst_2764_, lean_object* v_pre_2765_, lean_object* v_post_2766_, uint8_t v_usedLetOnly_2767_, uint8_t v_skipConstInApp_2768_, uint8_t v_skipInstances_2769_, lean_object* v_x_2770_, lean_object* v_x_2771_, lean_object* v___f_2772_, lean_object* v_toBind_2773_, lean_object* v_e_2774_, lean_object* v_____r_2775_, lean_object* v___y_2776_){
_start:
{
lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___f_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; 
v___x_2777_ = lean_box(v_usedLetOnly_2767_);
v___x_2778_ = lean_box(v_skipConstInApp_2768_);
v___x_2779_ = lean_box(v_skipInstances_2769_);
lean_inc_ref(v_e_2774_);
lean_inc(v_toBind_2773_);
lean_inc(v___y_2776_);
lean_inc(v_pre_2765_);
v___f_2780_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___boxed), 16, 15);
lean_closure_set(v___f_2780_, 0, v_toApplicative_2761_);
lean_closure_set(v___f_2780_, 1, v_inst_2762_);
lean_closure_set(v___f_2780_, 2, v_inst_2763_);
lean_closure_set(v___f_2780_, 3, v_inst_2764_);
lean_closure_set(v___f_2780_, 4, v_pre_2765_);
lean_closure_set(v___f_2780_, 5, v_post_2766_);
lean_closure_set(v___f_2780_, 6, v___x_2777_);
lean_closure_set(v___f_2780_, 7, v___x_2778_);
lean_closure_set(v___f_2780_, 8, v___x_2779_);
lean_closure_set(v___f_2780_, 9, v_x_2770_);
lean_closure_set(v___f_2780_, 10, v_x_2771_);
lean_closure_set(v___f_2780_, 11, v___y_2776_);
lean_closure_set(v___f_2780_, 12, v___f_2772_);
lean_closure_set(v___f_2780_, 13, v_toBind_2773_);
lean_closure_set(v___f_2780_, 14, v_e_2774_);
v___x_2781_ = lean_apply_1(v_pre_2765_, v_e_2774_);
v___x_2782_ = lean_apply_4(v_toBind_2773_, lean_box(0), lean_box(0), v___x_2781_, v___f_2780_);
return v___x_2782_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12___boxed(lean_object* v_toApplicative_2783_, lean_object* v_inst_2784_, lean_object* v_inst_2785_, lean_object* v_inst_2786_, lean_object* v_pre_2787_, lean_object* v_post_2788_, lean_object* v_usedLetOnly_2789_, lean_object* v_skipConstInApp_2790_, lean_object* v_skipInstances_2791_, lean_object* v_x_2792_, lean_object* v_x_2793_, lean_object* v___f_2794_, lean_object* v_toBind_2795_, lean_object* v_e_2796_, lean_object* v_____r_2797_, lean_object* v___y_2798_){
_start:
{
uint8_t v_usedLetOnly_boxed_2799_; uint8_t v_skipConstInApp_boxed_2800_; uint8_t v_skipInstances_boxed_2801_; lean_object* v_res_2802_; 
v_usedLetOnly_boxed_2799_ = lean_unbox(v_usedLetOnly_2789_);
v_skipConstInApp_boxed_2800_ = lean_unbox(v_skipConstInApp_2790_);
v_skipInstances_boxed_2801_ = lean_unbox(v_skipInstances_2791_);
v_res_2802_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12(v_toApplicative_2783_, v_inst_2784_, v_inst_2785_, v_inst_2786_, v_pre_2787_, v_post_2788_, v_usedLetOnly_boxed_2799_, v_skipConstInApp_boxed_2800_, v_skipInstances_boxed_2801_, v_x_2792_, v_x_2793_, v___f_2794_, v_toBind_2795_, v_e_2796_, v_____r_2797_, v___y_2798_);
lean_dec(v___y_2798_);
return v_res_2802_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(lean_object* v_inst_2803_, lean_object* v_inst_2804_, lean_object* v_inst_2805_, lean_object* v_pre_2806_, lean_object* v_post_2807_, uint8_t v_usedLetOnly_2808_, uint8_t v_skipConstInApp_2809_, uint8_t v_skipInstances_2810_, lean_object* v_x_2811_, lean_object* v_x_2812_, lean_object* v_e_2813_, lean_object* v_a_2814_){
_start:
{
lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___f_2819_; lean_object* v___f_2820_; lean_object* v___x_2821_; lean_object* v_toApplicative_2822_; lean_object* v_toBind_2823_; lean_object* v___f_2824_; lean_object* v___f_2825_; lean_object* v___f_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___f_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___f_2834_; lean_object* v___f_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; 
v___x_2815_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0));
v___x_2816_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1));
lean_inc_ref_n(v_inst_2803_, 3);
v___x_2817_ = l_Lean_MonadCacheT_instMonad___redArg(v_x_2811_, v___x_2815_, v___x_2816_, v_inst_2803_);
v___x_2818_ = l_Lean_MonadCacheT_instMonadControl___redArg(v_x_2811_, v___x_2815_, v___x_2816_);
lean_inc_ref_n(v_inst_2805_, 3);
lean_inc_ref(v___x_2818_);
v___f_2819_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_2819_, 0, v___x_2818_);
lean_closure_set(v___f_2819_, 1, v_inst_2805_);
v___f_2820_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_2820_, 0, v___x_2818_);
lean_closure_set(v___f_2820_, 1, v_inst_2805_);
v___x_2821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2821_, 0, v___f_2819_);
lean_ctor_set(v___x_2821_, 1, v___f_2820_);
v_toApplicative_2822_ = lean_ctor_get(v_inst_2803_, 0);
lean_inc_ref_n(v_toApplicative_2822_, 6);
v_toBind_2823_ = lean_ctor_get(v_inst_2803_, 1);
lean_inc_n(v_toBind_2823_, 6);
v___f_2824_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2824_, 0, v_toApplicative_2822_);
lean_inc_n(v_x_2812_, 3);
lean_inc_n(v_a_2814_, 3);
lean_inc_ref_n(v_e_2813_, 2);
v___f_2825_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_2825_, 0, v_toApplicative_2822_);
lean_closure_set(v___f_2825_, 1, v___x_2815_);
lean_closure_set(v___f_2825_, 2, v___x_2816_);
lean_closure_set(v___f_2825_, 3, v_e_2813_);
lean_closure_set(v___f_2825_, 4, v_a_2814_);
lean_closure_set(v___f_2825_, 5, v_x_2812_);
lean_closure_set(v___f_2825_, 6, v_toBind_2823_);
v___f_2826_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__3___boxed), 5, 4);
lean_closure_set(v___f_2826_, 0, v_toApplicative_2822_);
lean_closure_set(v___f_2826_, 1, v___x_2815_);
lean_closure_set(v___f_2826_, 2, v___x_2816_);
lean_closure_set(v___f_2826_, 3, v_e_2813_);
v___x_2827_ = lean_box(v_skipInstances_2810_);
v___x_2828_ = lean_box(v_usedLetOnly_2808_);
v___x_2829_ = lean_box(v_skipConstInApp_2809_);
lean_inc_ref(v___x_2817_);
lean_inc(v_post_2807_);
lean_inc(v_pre_2806_);
lean_inc_n(v_inst_2804_, 2);
v___f_2830_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__9___boxed), 17, 14);
lean_closure_set(v___f_2830_, 0, v___x_2827_);
lean_closure_set(v___f_2830_, 1, v_inst_2803_);
lean_closure_set(v___f_2830_, 2, v_inst_2804_);
lean_closure_set(v___f_2830_, 3, v_inst_2805_);
lean_closure_set(v___f_2830_, 4, v_pre_2806_);
lean_closure_set(v___f_2830_, 5, v_post_2807_);
lean_closure_set(v___f_2830_, 6, v___x_2828_);
lean_closure_set(v___f_2830_, 7, v___x_2829_);
lean_closure_set(v___f_2830_, 8, v_x_2811_);
lean_closure_set(v___f_2830_, 9, v_x_2812_);
lean_closure_set(v___f_2830_, 10, v___x_2817_);
lean_closure_set(v___f_2830_, 11, v_toBind_2823_);
lean_closure_set(v___f_2830_, 12, v_toApplicative_2822_);
lean_closure_set(v___f_2830_, 13, v___f_2824_);
v___x_2831_ = lean_box(v_usedLetOnly_2808_);
v___x_2832_ = lean_box(v_skipConstInApp_2809_);
v___x_2833_ = lean_box(v_skipInstances_2810_);
v___f_2834_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12___boxed), 16, 14);
lean_closure_set(v___f_2834_, 0, v_toApplicative_2822_);
lean_closure_set(v___f_2834_, 1, v_inst_2803_);
lean_closure_set(v___f_2834_, 2, v_inst_2804_);
lean_closure_set(v___f_2834_, 3, v_inst_2805_);
lean_closure_set(v___f_2834_, 4, v_pre_2806_);
lean_closure_set(v___f_2834_, 5, v_post_2807_);
lean_closure_set(v___f_2834_, 6, v___x_2831_);
lean_closure_set(v___f_2834_, 7, v___x_2832_);
lean_closure_set(v___f_2834_, 8, v___x_2833_);
lean_closure_set(v___f_2834_, 9, v_x_2811_);
lean_closure_set(v___f_2834_, 10, v_x_2812_);
lean_closure_set(v___f_2834_, 11, v___f_2830_);
lean_closure_set(v___f_2834_, 12, v_toBind_2823_);
lean_closure_set(v___f_2834_, 13, v_e_2813_);
v___f_2835_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14___boxed), 13, 12);
lean_closure_set(v___f_2835_, 0, v_inst_2804_);
lean_closure_set(v___f_2835_, 1, v_x_2811_);
lean_closure_set(v___f_2835_, 2, v___x_2815_);
lean_closure_set(v___f_2835_, 3, v___x_2816_);
lean_closure_set(v___f_2835_, 4, v_inst_2803_);
lean_closure_set(v___f_2835_, 5, v___f_2834_);
lean_closure_set(v___f_2835_, 6, v___x_2821_);
lean_closure_set(v___f_2835_, 7, v___x_2817_);
lean_closure_set(v___f_2835_, 8, v_a_2814_);
lean_closure_set(v___f_2835_, 9, v_toBind_2823_);
lean_closure_set(v___f_2835_, 10, v___f_2825_);
lean_closure_set(v___f_2835_, 11, v_toApplicative_2822_);
v___x_2836_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2836_, 0, lean_box(0));
lean_closure_set(v___x_2836_, 1, lean_box(0));
lean_closure_set(v___x_2836_, 2, v_a_2814_);
v___x_2837_ = lean_apply_2(v_x_2812_, lean_box(0), v___x_2836_);
v___x_2838_ = lean_apply_4(v_toBind_2823_, lean_box(0), lean_box(0), v___x_2837_, v___f_2826_);
v___x_2839_ = lean_apply_4(v_toBind_2823_, lean_box(0), lean_box(0), v___x_2838_, v___f_2835_);
return v___x_2839_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___lam__0(lean_object* v_toApplicative_2840_, lean_object* v_inst_2841_, lean_object* v_inst_2842_, lean_object* v_inst_2843_, lean_object* v_pre_2844_, lean_object* v_post_2845_, uint8_t v_usedLetOnly_2846_, uint8_t v_skipConstInApp_2847_, uint8_t v_skipInstances_2848_, lean_object* v_x_2849_, lean_object* v_x_2850_, lean_object* v_a_2851_, lean_object* v_e_2852_, lean_object* v_a_2853_){
_start:
{
lean_object* v___y_2855_; 
switch(lean_obj_tag(v_a_2853_))
{
case 0:
{
lean_object* v_e_2858_; lean_object* v_toPure_2859_; lean_object* v___x_2860_; 
lean_dec_ref(v_e_2852_);
lean_dec(v_x_2850_);
lean_dec(v_post_2845_);
lean_dec(v_pre_2844_);
lean_dec_ref(v_inst_2843_);
lean_dec(v_inst_2842_);
lean_dec_ref(v_inst_2841_);
v_e_2858_ = lean_ctor_get(v_a_2853_, 0);
lean_inc_ref(v_e_2858_);
lean_dec_ref_known(v_a_2853_, 1);
v_toPure_2859_ = lean_ctor_get(v_toApplicative_2840_, 1);
lean_inc(v_toPure_2859_);
lean_dec_ref(v_toApplicative_2840_);
v___x_2860_ = lean_apply_2(v_toPure_2859_, lean_box(0), v_e_2858_);
return v___x_2860_;
}
case 1:
{
lean_object* v_e_2861_; lean_object* v___x_2862_; 
lean_dec_ref(v_e_2852_);
lean_dec_ref(v_toApplicative_2840_);
v_e_2861_ = lean_ctor_get(v_a_2853_, 0);
lean_inc_ref(v_e_2861_);
lean_dec_ref_known(v_a_2853_, 1);
v___x_2862_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2841_, v_inst_2842_, v_inst_2843_, v_pre_2844_, v_post_2845_, v_usedLetOnly_2846_, v_skipConstInApp_2847_, v_skipInstances_2848_, v_x_2849_, v_x_2850_, v_e_2861_, v_a_2851_);
return v___x_2862_;
}
default: 
{
lean_object* v_e_x3f_2863_; 
lean_dec(v_x_2850_);
lean_dec(v_post_2845_);
lean_dec(v_pre_2844_);
lean_dec_ref(v_inst_2843_);
lean_dec(v_inst_2842_);
lean_dec_ref(v_inst_2841_);
v_e_x3f_2863_ = lean_ctor_get(v_a_2853_, 0);
lean_inc(v_e_x3f_2863_);
lean_dec_ref_known(v_a_2853_, 1);
if (lean_obj_tag(v_e_x3f_2863_) == 0)
{
v___y_2855_ = v_e_2852_;
goto v___jp_2854_;
}
else
{
lean_object* v_val_2864_; 
lean_dec_ref(v_e_2852_);
v_val_2864_ = lean_ctor_get(v_e_x3f_2863_, 0);
lean_inc(v_val_2864_);
lean_dec_ref_known(v_e_x3f_2863_, 1);
v___y_2855_ = v_val_2864_;
goto v___jp_2854_;
}
}
}
v___jp_2854_:
{
lean_object* v_toPure_2856_; lean_object* v___x_2857_; 
v_toPure_2856_ = lean_ctor_get(v_toApplicative_2840_, 1);
lean_inc(v_toPure_2856_);
lean_dec_ref(v_toApplicative_2840_);
v___x_2857_ = lean_apply_2(v_toPure_2856_, lean_box(0), v___y_2855_);
return v___x_2857_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___lam__0___boxed(lean_object* v_toApplicative_2865_, lean_object* v_inst_2866_, lean_object* v_inst_2867_, lean_object* v_inst_2868_, lean_object* v_pre_2869_, lean_object* v_post_2870_, lean_object* v_usedLetOnly_2871_, lean_object* v_skipConstInApp_2872_, lean_object* v_skipInstances_2873_, lean_object* v_x_2874_, lean_object* v_x_2875_, lean_object* v_a_2876_, lean_object* v_e_2877_, lean_object* v_a_2878_){
_start:
{
uint8_t v_usedLetOnly_boxed_2879_; uint8_t v_skipConstInApp_boxed_2880_; uint8_t v_skipInstances_boxed_2881_; lean_object* v_res_2882_; 
v_usedLetOnly_boxed_2879_ = lean_unbox(v_usedLetOnly_2871_);
v_skipConstInApp_boxed_2880_ = lean_unbox(v_skipConstInApp_2872_);
v_skipInstances_boxed_2881_ = lean_unbox(v_skipInstances_2873_);
v_res_2882_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___lam__0(v_toApplicative_2865_, v_inst_2866_, v_inst_2867_, v_inst_2868_, v_pre_2869_, v_post_2870_, v_usedLetOnly_boxed_2879_, v_skipConstInApp_boxed_2880_, v_skipInstances_boxed_2881_, v_x_2874_, v_x_2875_, v_a_2876_, v_e_2877_, v_a_2878_);
lean_dec(v_a_2876_);
return v_res_2882_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(lean_object* v_inst_2883_, lean_object* v_inst_2884_, lean_object* v_inst_2885_, lean_object* v_pre_2886_, lean_object* v_post_2887_, uint8_t v_usedLetOnly_2888_, uint8_t v_skipConstInApp_2889_, uint8_t v_skipInstances_2890_, lean_object* v_x_2891_, lean_object* v_x_2892_, lean_object* v_e_2893_, lean_object* v_a_2894_){
_start:
{
lean_object* v_toApplicative_2895_; lean_object* v_toBind_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___f_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; 
v_toApplicative_2895_ = lean_ctor_get(v_inst_2883_, 0);
lean_inc_ref(v_toApplicative_2895_);
v_toBind_2896_ = lean_ctor_get(v_inst_2883_, 1);
lean_inc(v_toBind_2896_);
v___x_2897_ = lean_box(v_usedLetOnly_2888_);
v___x_2898_ = lean_box(v_skipConstInApp_2889_);
v___x_2899_ = lean_box(v_skipInstances_2890_);
lean_inc_ref(v_e_2893_);
lean_inc(v_a_2894_);
lean_inc(v_post_2887_);
v___f_2900_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___lam__0___boxed), 14, 13);
lean_closure_set(v___f_2900_, 0, v_toApplicative_2895_);
lean_closure_set(v___f_2900_, 1, v_inst_2883_);
lean_closure_set(v___f_2900_, 2, v_inst_2884_);
lean_closure_set(v___f_2900_, 3, v_inst_2885_);
lean_closure_set(v___f_2900_, 4, v_pre_2886_);
lean_closure_set(v___f_2900_, 5, v_post_2887_);
lean_closure_set(v___f_2900_, 6, v___x_2897_);
lean_closure_set(v___f_2900_, 7, v___x_2898_);
lean_closure_set(v___f_2900_, 8, v___x_2899_);
lean_closure_set(v___f_2900_, 9, v_x_2891_);
lean_closure_set(v___f_2900_, 10, v_x_2892_);
lean_closure_set(v___f_2900_, 11, v_a_2894_);
lean_closure_set(v___f_2900_, 12, v_e_2893_);
v___x_2901_ = lean_apply_1(v_post_2887_, v_e_2893_);
v___x_2902_ = lean_apply_4(v_toBind_2896_, lean_box(0), lean_box(0), v___x_2901_, v___f_2900_);
return v___x_2902_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3(lean_object* v_inst_2903_, lean_object* v_inst_2904_, lean_object* v_inst_2905_, lean_object* v_pre_2906_, lean_object* v_post_2907_, uint8_t v_usedLetOnly_2908_, uint8_t v_skipConstInApp_2909_, uint8_t v_skipInstances_2910_, lean_object* v_x_2911_, lean_object* v_x_2912_, lean_object* v_a_2913_, lean_object* v_a_2914_){
_start:
{
lean_object* v___x_2915_; 
v___x_2915_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2903_, v_inst_2904_, v_inst_2905_, v_pre_2906_, v_post_2907_, v_usedLetOnly_2908_, v_skipConstInApp_2909_, v_skipInstances_2910_, v_x_2911_, v_x_2912_, v_a_2914_, v_a_2913_);
return v___x_2915_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___boxed(lean_object* v_inst_2916_, lean_object* v_inst_2917_, lean_object* v_inst_2918_, lean_object* v_pre_2919_, lean_object* v_post_2920_, lean_object* v_usedLetOnly_2921_, lean_object* v_skipConstInApp_2922_, lean_object* v_skipInstances_2923_, lean_object* v_x_2924_, lean_object* v_x_2925_, lean_object* v_e_2926_, lean_object* v_a_2927_){
_start:
{
uint8_t v_usedLetOnly_boxed_2928_; uint8_t v_skipConstInApp_boxed_2929_; uint8_t v_skipInstances_boxed_2930_; lean_object* v_res_2931_; 
v_usedLetOnly_boxed_2928_ = lean_unbox(v_usedLetOnly_2921_);
v_skipConstInApp_boxed_2929_ = lean_unbox(v_skipConstInApp_2922_);
v_skipInstances_boxed_2930_ = lean_unbox(v_skipInstances_2923_);
v_res_2931_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2916_, v_inst_2917_, v_inst_2918_, v_pre_2919_, v_post_2920_, v_usedLetOnly_boxed_2928_, v_skipConstInApp_boxed_2929_, v_skipInstances_boxed_2930_, v_x_2924_, v_x_2925_, v_e_2926_, v_a_2927_);
lean_dec(v_a_2927_);
return v_res_2931_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___boxed(lean_object* v_inst_2932_, lean_object* v_inst_2933_, lean_object* v_inst_2934_, lean_object* v_pre_2935_, lean_object* v_post_2936_, lean_object* v_usedLetOnly_2937_, lean_object* v_skipConstInApp_2938_, lean_object* v_skipInstances_2939_, lean_object* v_x_2940_, lean_object* v_x_2941_, lean_object* v_fvars_2942_, lean_object* v_e_2943_, lean_object* v_a_2944_){
_start:
{
uint8_t v_usedLetOnly_boxed_2945_; uint8_t v_skipConstInApp_boxed_2946_; uint8_t v_skipInstances_boxed_2947_; lean_object* v_res_2948_; 
v_usedLetOnly_boxed_2945_ = lean_unbox(v_usedLetOnly_2937_);
v_skipConstInApp_boxed_2946_ = lean_unbox(v_skipConstInApp_2938_);
v_skipInstances_boxed_2947_ = lean_unbox(v_skipInstances_2939_);
v_res_2948_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(v_inst_2932_, v_inst_2933_, v_inst_2934_, v_pre_2935_, v_post_2936_, v_usedLetOnly_boxed_2945_, v_skipConstInApp_boxed_2946_, v_skipInstances_boxed_2947_, v_x_2940_, v_x_2941_, v_fvars_2942_, v_e_2943_, v_a_2944_);
lean_dec(v_a_2944_);
return v_res_2948_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___boxed(lean_object* v_inst_2949_, lean_object* v_inst_2950_, lean_object* v_inst_2951_, lean_object* v_pre_2952_, lean_object* v_post_2953_, lean_object* v_usedLetOnly_2954_, lean_object* v_skipConstInApp_2955_, lean_object* v_skipInstances_2956_, lean_object* v_x_2957_, lean_object* v_x_2958_, lean_object* v_fvars_2959_, lean_object* v_e_2960_, lean_object* v_a_2961_){
_start:
{
uint8_t v_usedLetOnly_boxed_2962_; uint8_t v_skipConstInApp_boxed_2963_; uint8_t v_skipInstances_boxed_2964_; lean_object* v_res_2965_; 
v_usedLetOnly_boxed_2962_ = lean_unbox(v_usedLetOnly_2954_);
v_skipConstInApp_boxed_2963_ = lean_unbox(v_skipConstInApp_2955_);
v_skipInstances_boxed_2964_ = lean_unbox(v_skipInstances_2956_);
v_res_2965_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(v_inst_2949_, v_inst_2950_, v_inst_2951_, v_pre_2952_, v_post_2953_, v_usedLetOnly_boxed_2962_, v_skipConstInApp_boxed_2963_, v_skipInstances_boxed_2964_, v_x_2957_, v_x_2958_, v_fvars_2959_, v_e_2960_, v_a_2961_);
lean_dec(v_a_2961_);
return v_res_2965_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___boxed(lean_object* v_inst_2966_, lean_object* v_inst_2967_, lean_object* v_inst_2968_, lean_object* v_pre_2969_, lean_object* v_post_2970_, lean_object* v_usedLetOnly_2971_, lean_object* v_skipConstInApp_2972_, lean_object* v_skipInstances_2973_, lean_object* v_x_2974_, lean_object* v_x_2975_, lean_object* v_fvars_2976_, lean_object* v_e_2977_, lean_object* v_a_2978_){
_start:
{
uint8_t v_usedLetOnly_boxed_2979_; uint8_t v_skipConstInApp_boxed_2980_; uint8_t v_skipInstances_boxed_2981_; lean_object* v_res_2982_; 
v_usedLetOnly_boxed_2979_ = lean_unbox(v_usedLetOnly_2971_);
v_skipConstInApp_boxed_2980_ = lean_unbox(v_skipConstInApp_2972_);
v_skipInstances_boxed_2981_ = lean_unbox(v_skipInstances_2973_);
v_res_2982_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(v_inst_2966_, v_inst_2967_, v_inst_2968_, v_pre_2969_, v_post_2970_, v_usedLetOnly_boxed_2979_, v_skipConstInApp_boxed_2980_, v_skipInstances_boxed_2981_, v_x_2974_, v_x_2975_, v_fvars_2976_, v_e_2977_, v_a_2978_);
lean_dec(v_a_2978_);
return v_res_2982_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit(lean_object* v_m_2983_, lean_object* v_inst_2984_, lean_object* v_inst_2985_, lean_object* v_inst_2986_, lean_object* v_pre_2987_, lean_object* v_post_2988_, uint8_t v_usedLetOnly_2989_, uint8_t v_skipConstInApp_2990_, uint8_t v_skipInstances_2991_, lean_object* v_x_2992_, lean_object* v_x_2993_, lean_object* v_e_2994_, lean_object* v_a_2995_){
_start:
{
lean_object* v___x_2996_; 
v___x_2996_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2984_, v_inst_2985_, v_inst_2986_, v_pre_2987_, v_post_2988_, v_usedLetOnly_2989_, v_skipConstInApp_2990_, v_skipInstances_2991_, v_x_2992_, v_x_2993_, v_e_2994_, v_a_2995_);
return v___x_2996_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___boxed(lean_object* v_m_2997_, lean_object* v_inst_2998_, lean_object* v_inst_2999_, lean_object* v_inst_3000_, lean_object* v_pre_3001_, lean_object* v_post_3002_, lean_object* v_usedLetOnly_3003_, lean_object* v_skipConstInApp_3004_, lean_object* v_skipInstances_3005_, lean_object* v_x_3006_, lean_object* v_x_3007_, lean_object* v_e_3008_, lean_object* v_a_3009_){
_start:
{
uint8_t v_usedLetOnly_boxed_3010_; uint8_t v_skipConstInApp_boxed_3011_; uint8_t v_skipInstances_boxed_3012_; lean_object* v_res_3013_; 
v_usedLetOnly_boxed_3010_ = lean_unbox(v_usedLetOnly_3003_);
v_skipConstInApp_boxed_3011_ = lean_unbox(v_skipConstInApp_3004_);
v_skipInstances_boxed_3012_ = lean_unbox(v_skipInstances_3005_);
v_res_3013_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit(v_m_2997_, v_inst_2998_, v_inst_2999_, v_inst_3000_, v_pre_3001_, v_post_3002_, v_usedLetOnly_boxed_3010_, v_skipConstInApp_boxed_3011_, v_skipInstances_boxed_3012_, v_x_3006_, v_x_3007_, v_e_3008_, v_a_3009_);
lean_dec(v_a_3009_);
return v_res_3013_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet(lean_object* v_m_3014_, lean_object* v_inst_3015_, lean_object* v_inst_3016_, lean_object* v_inst_3017_, lean_object* v_pre_3018_, lean_object* v_post_3019_, uint8_t v_usedLetOnly_3020_, uint8_t v_skipConstInApp_3021_, uint8_t v_skipInstances_3022_, lean_object* v_x_3023_, lean_object* v_x_3024_, lean_object* v_fvars_3025_, lean_object* v_e_3026_, lean_object* v_a_3027_){
_start:
{
lean_object* v___x_3028_; 
v___x_3028_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(v_inst_3015_, v_inst_3016_, v_inst_3017_, v_pre_3018_, v_post_3019_, v_usedLetOnly_3020_, v_skipConstInApp_3021_, v_skipInstances_3022_, v_x_3023_, v_x_3024_, v_fvars_3025_, v_e_3026_, v_a_3027_);
return v___x_3028_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___boxed(lean_object* v_m_3029_, lean_object* v_inst_3030_, lean_object* v_inst_3031_, lean_object* v_inst_3032_, lean_object* v_pre_3033_, lean_object* v_post_3034_, lean_object* v_usedLetOnly_3035_, lean_object* v_skipConstInApp_3036_, lean_object* v_skipInstances_3037_, lean_object* v_x_3038_, lean_object* v_x_3039_, lean_object* v_fvars_3040_, lean_object* v_e_3041_, lean_object* v_a_3042_){
_start:
{
uint8_t v_usedLetOnly_boxed_3043_; uint8_t v_skipConstInApp_boxed_3044_; uint8_t v_skipInstances_boxed_3045_; lean_object* v_res_3046_; 
v_usedLetOnly_boxed_3043_ = lean_unbox(v_usedLetOnly_3035_);
v_skipConstInApp_boxed_3044_ = lean_unbox(v_skipConstInApp_3036_);
v_skipInstances_boxed_3045_ = lean_unbox(v_skipInstances_3037_);
v_res_3046_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet(v_m_3029_, v_inst_3030_, v_inst_3031_, v_inst_3032_, v_pre_3033_, v_post_3034_, v_usedLetOnly_boxed_3043_, v_skipConstInApp_boxed_3044_, v_skipInstances_boxed_3045_, v_x_3038_, v_x_3039_, v_fvars_3040_, v_e_3041_, v_a_3042_);
lean_dec(v_a_3042_);
return v_res_3046_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost(lean_object* v_m_3047_, lean_object* v_inst_3048_, lean_object* v_inst_3049_, lean_object* v_inst_3050_, lean_object* v_pre_3051_, lean_object* v_post_3052_, uint8_t v_usedLetOnly_3053_, uint8_t v_skipConstInApp_3054_, uint8_t v_skipInstances_3055_, lean_object* v_x_3056_, lean_object* v_x_3057_, lean_object* v_e_3058_, lean_object* v_a_3059_){
_start:
{
lean_object* v___x_3060_; 
v___x_3060_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_3048_, v_inst_3049_, v_inst_3050_, v_pre_3051_, v_post_3052_, v_usedLetOnly_3053_, v_skipConstInApp_3054_, v_skipInstances_3055_, v_x_3056_, v_x_3057_, v_e_3058_, v_a_3059_);
return v___x_3060_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___boxed(lean_object* v_m_3061_, lean_object* v_inst_3062_, lean_object* v_inst_3063_, lean_object* v_inst_3064_, lean_object* v_pre_3065_, lean_object* v_post_3066_, lean_object* v_usedLetOnly_3067_, lean_object* v_skipConstInApp_3068_, lean_object* v_skipInstances_3069_, lean_object* v_x_3070_, lean_object* v_x_3071_, lean_object* v_e_3072_, lean_object* v_a_3073_){
_start:
{
uint8_t v_usedLetOnly_boxed_3074_; uint8_t v_skipConstInApp_boxed_3075_; uint8_t v_skipInstances_boxed_3076_; lean_object* v_res_3077_; 
v_usedLetOnly_boxed_3074_ = lean_unbox(v_usedLetOnly_3067_);
v_skipConstInApp_boxed_3075_ = lean_unbox(v_skipConstInApp_3068_);
v_skipInstances_boxed_3076_ = lean_unbox(v_skipInstances_3069_);
v_res_3077_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost(v_m_3061_, v_inst_3062_, v_inst_3063_, v_inst_3064_, v_pre_3065_, v_post_3066_, v_usedLetOnly_boxed_3074_, v_skipConstInApp_boxed_3075_, v_skipInstances_boxed_3076_, v_x_3070_, v_x_3071_, v_e_3072_, v_a_3073_);
lean_dec(v_a_3073_);
return v_res_3077_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda(lean_object* v_m_3078_, lean_object* v_inst_3079_, lean_object* v_inst_3080_, lean_object* v_inst_3081_, lean_object* v_pre_3082_, lean_object* v_post_3083_, uint8_t v_usedLetOnly_3084_, uint8_t v_skipConstInApp_3085_, uint8_t v_skipInstances_3086_, lean_object* v_x_3087_, lean_object* v_x_3088_, lean_object* v_fvars_3089_, lean_object* v_e_3090_, lean_object* v_a_3091_){
_start:
{
lean_object* v___x_3092_; 
v___x_3092_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(v_inst_3079_, v_inst_3080_, v_inst_3081_, v_pre_3082_, v_post_3083_, v_usedLetOnly_3084_, v_skipConstInApp_3085_, v_skipInstances_3086_, v_x_3087_, v_x_3088_, v_fvars_3089_, v_e_3090_, v_a_3091_);
return v___x_3092_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___boxed(lean_object* v_m_3093_, lean_object* v_inst_3094_, lean_object* v_inst_3095_, lean_object* v_inst_3096_, lean_object* v_pre_3097_, lean_object* v_post_3098_, lean_object* v_usedLetOnly_3099_, lean_object* v_skipConstInApp_3100_, lean_object* v_skipInstances_3101_, lean_object* v_x_3102_, lean_object* v_x_3103_, lean_object* v_fvars_3104_, lean_object* v_e_3105_, lean_object* v_a_3106_){
_start:
{
uint8_t v_usedLetOnly_boxed_3107_; uint8_t v_skipConstInApp_boxed_3108_; uint8_t v_skipInstances_boxed_3109_; lean_object* v_res_3110_; 
v_usedLetOnly_boxed_3107_ = lean_unbox(v_usedLetOnly_3099_);
v_skipConstInApp_boxed_3108_ = lean_unbox(v_skipConstInApp_3100_);
v_skipInstances_boxed_3109_ = lean_unbox(v_skipInstances_3101_);
v_res_3110_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda(v_m_3093_, v_inst_3094_, v_inst_3095_, v_inst_3096_, v_pre_3097_, v_post_3098_, v_usedLetOnly_boxed_3107_, v_skipConstInApp_boxed_3108_, v_skipInstances_boxed_3109_, v_x_3102_, v_x_3103_, v_fvars_3104_, v_e_3105_, v_a_3106_);
lean_dec(v_a_3106_);
return v_res_3110_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall(lean_object* v_m_3111_, lean_object* v_inst_3112_, lean_object* v_inst_3113_, lean_object* v_inst_3114_, lean_object* v_pre_3115_, lean_object* v_post_3116_, uint8_t v_usedLetOnly_3117_, uint8_t v_skipConstInApp_3118_, uint8_t v_skipInstances_3119_, lean_object* v_x_3120_, lean_object* v_x_3121_, lean_object* v_fvars_3122_, lean_object* v_e_3123_, lean_object* v_a_3124_){
_start:
{
lean_object* v___x_3125_; 
v___x_3125_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(v_inst_3112_, v_inst_3113_, v_inst_3114_, v_pre_3115_, v_post_3116_, v_usedLetOnly_3117_, v_skipConstInApp_3118_, v_skipInstances_3119_, v_x_3120_, v_x_3121_, v_fvars_3122_, v_e_3123_, v_a_3124_);
return v___x_3125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___boxed(lean_object* v_m_3126_, lean_object* v_inst_3127_, lean_object* v_inst_3128_, lean_object* v_inst_3129_, lean_object* v_pre_3130_, lean_object* v_post_3131_, lean_object* v_usedLetOnly_3132_, lean_object* v_skipConstInApp_3133_, lean_object* v_skipInstances_3134_, lean_object* v_x_3135_, lean_object* v_x_3136_, lean_object* v_fvars_3137_, lean_object* v_e_3138_, lean_object* v_a_3139_){
_start:
{
uint8_t v_usedLetOnly_boxed_3140_; uint8_t v_skipConstInApp_boxed_3141_; uint8_t v_skipInstances_boxed_3142_; lean_object* v_res_3143_; 
v_usedLetOnly_boxed_3140_ = lean_unbox(v_usedLetOnly_3132_);
v_skipConstInApp_boxed_3141_ = lean_unbox(v_skipConstInApp_3133_);
v_skipInstances_boxed_3142_ = lean_unbox(v_skipInstances_3134_);
v_res_3143_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall(v_m_3126_, v_inst_3127_, v_inst_3128_, v_inst_3129_, v_pre_3130_, v_post_3131_, v_usedLetOnly_boxed_3140_, v_skipConstInApp_boxed_3141_, v_skipInstances_boxed_3142_, v_x_3135_, v_x_3136_, v_fvars_3137_, v_e_3138_, v_a_3139_);
lean_dec(v_a_3139_);
return v_res_3143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__0(lean_object* v_x_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_){
_start:
{
lean_object* v___x_3150_; lean_object* v___x_3151_; 
v___x_3150_ = lean_apply_1(v_x_3144_, lean_box(0));
v___x_3151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3151_, 0, v___x_3150_);
return v___x_3151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__0___boxed(lean_object* v_x_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_){
_start:
{
lean_object* v_res_3158_; 
v_res_3158_ = l_Lean_Meta_transformWithCache___redArg___lam__0(v_x_3152_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_);
lean_dec(v___y_3156_);
lean_dec_ref(v___y_3155_);
lean_dec(v___y_3154_);
lean_dec_ref(v___y_3153_);
return v_res_3158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__1(lean_object* v_inst_3159_, lean_object* v_00_u03b1_3160_, lean_object* v_x_3161_){
_start:
{
lean_object* v___f_3162_; lean_object* v___x_3163_; 
v___f_3162_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_3162_, 0, v_x_3161_);
v___x_3163_ = lean_apply_2(v_inst_3159_, lean_box(0), v___f_3162_);
return v___x_3163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__4(lean_object* v_toPure_3164_, lean_object* v_x_3165_, lean_object* v_toBind_3166_, lean_object* v_inst_3167_, lean_object* v_inst_3168_, lean_object* v_inst_3169_, lean_object* v_pre_3170_, lean_object* v_post_3171_, uint8_t v_usedLetOnly_3172_, uint8_t v_skipConstInApp_3173_, uint8_t v_skipInstances_3174_, lean_object* v_x_3175_, lean_object* v_input_3176_, lean_object* v_ref_3177_){
_start:
{
lean_object* v___f_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; 
lean_inc(v_toBind_3166_);
lean_inc(v_x_3165_);
lean_inc(v_ref_3177_);
v___f_3178_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__4), 5, 4);
lean_closure_set(v___f_3178_, 0, v_toPure_3164_);
lean_closure_set(v___f_3178_, 1, v_ref_3177_);
lean_closure_set(v___f_3178_, 2, v_x_3165_);
lean_closure_set(v___f_3178_, 3, v_toBind_3166_);
v___x_3179_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_3167_, v_inst_3168_, v_inst_3169_, v_pre_3170_, v_post_3171_, v_usedLetOnly_3172_, v_skipConstInApp_3173_, v_skipInstances_3174_, v_x_3175_, v_x_3165_, v_input_3176_, v_ref_3177_);
lean_dec(v_ref_3177_);
v___x_3180_ = lean_apply_4(v_toBind_3166_, lean_box(0), lean_box(0), v___x_3179_, v___f_3178_);
return v___x_3180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__4___boxed(lean_object* v_toPure_3181_, lean_object* v_x_3182_, lean_object* v_toBind_3183_, lean_object* v_inst_3184_, lean_object* v_inst_3185_, lean_object* v_inst_3186_, lean_object* v_pre_3187_, lean_object* v_post_3188_, lean_object* v_usedLetOnly_3189_, lean_object* v_skipConstInApp_3190_, lean_object* v_skipInstances_3191_, lean_object* v_x_3192_, lean_object* v_input_3193_, lean_object* v_ref_3194_){
_start:
{
uint8_t v_usedLetOnly_boxed_3195_; uint8_t v_skipConstInApp_boxed_3196_; uint8_t v_skipInstances_boxed_3197_; lean_object* v_res_3198_; 
v_usedLetOnly_boxed_3195_ = lean_unbox(v_usedLetOnly_3189_);
v_skipConstInApp_boxed_3196_ = lean_unbox(v_skipConstInApp_3190_);
v_skipInstances_boxed_3197_ = lean_unbox(v_skipInstances_3191_);
v_res_3198_ = l_Lean_Meta_transformWithCache___redArg___lam__4(v_toPure_3181_, v_x_3182_, v_toBind_3183_, v_inst_3184_, v_inst_3185_, v_inst_3186_, v_pre_3187_, v_post_3188_, v_usedLetOnly_boxed_3195_, v_skipConstInApp_boxed_3196_, v_skipInstances_boxed_3197_, v_x_3192_, v_input_3193_, v_ref_3194_);
return v_res_3198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg(lean_object* v_inst_3199_, lean_object* v_inst_3200_, lean_object* v_inst_3201_, lean_object* v_input_3202_, lean_object* v_cache_3203_, lean_object* v_pre_3204_, lean_object* v_post_3205_, uint8_t v_usedLetOnly_3206_, uint8_t v_skipConstInApp_3207_, uint8_t v_skipInstances_3208_){
_start:
{
lean_object* v_x_3209_; lean_object* v_toApplicative_3210_; lean_object* v_toBind_3211_; lean_object* v_toPure_3212_; lean_object* v_x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___f_3219_; lean_object* v___x_3220_; 
v_x_3209_ = lean_box(0);
v_toApplicative_3210_ = lean_ctor_get(v_inst_3199_, 0);
v_toBind_3211_ = lean_ctor_get(v_inst_3199_, 1);
lean_inc_n(v_toBind_3211_, 2);
v_toPure_3212_ = lean_ctor_get(v_toApplicative_3210_, 1);
lean_inc(v_toPure_3212_);
lean_inc_n(v_inst_3200_, 2);
v_x_3213_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__1), 3, 1);
lean_closure_set(v_x_3213_, 0, v_inst_3200_);
v___x_3214_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_3214_, 0, lean_box(0));
lean_closure_set(v___x_3214_, 1, lean_box(0));
lean_closure_set(v___x_3214_, 2, v_cache_3203_);
v___x_3215_ = l_Lean_Meta_transformWithCache___redArg___lam__1(v_inst_3200_, lean_box(0), v___x_3214_);
v___x_3216_ = lean_box(v_usedLetOnly_3206_);
v___x_3217_ = lean_box(v_skipConstInApp_3207_);
v___x_3218_ = lean_box(v_skipInstances_3208_);
v___f_3219_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__4___boxed), 14, 13);
lean_closure_set(v___f_3219_, 0, v_toPure_3212_);
lean_closure_set(v___f_3219_, 1, v_x_3213_);
lean_closure_set(v___f_3219_, 2, v_toBind_3211_);
lean_closure_set(v___f_3219_, 3, v_inst_3199_);
lean_closure_set(v___f_3219_, 4, v_inst_3200_);
lean_closure_set(v___f_3219_, 5, v_inst_3201_);
lean_closure_set(v___f_3219_, 6, v_pre_3204_);
lean_closure_set(v___f_3219_, 7, v_post_3205_);
lean_closure_set(v___f_3219_, 8, v___x_3216_);
lean_closure_set(v___f_3219_, 9, v___x_3217_);
lean_closure_set(v___f_3219_, 10, v___x_3218_);
lean_closure_set(v___f_3219_, 11, v_x_3209_);
lean_closure_set(v___f_3219_, 12, v_input_3202_);
v___x_3220_ = lean_apply_4(v_toBind_3211_, lean_box(0), lean_box(0), v___x_3215_, v___f_3219_);
return v___x_3220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___boxed(lean_object* v_inst_3221_, lean_object* v_inst_3222_, lean_object* v_inst_3223_, lean_object* v_input_3224_, lean_object* v_cache_3225_, lean_object* v_pre_3226_, lean_object* v_post_3227_, lean_object* v_usedLetOnly_3228_, lean_object* v_skipConstInApp_3229_, lean_object* v_skipInstances_3230_){
_start:
{
uint8_t v_usedLetOnly_boxed_3231_; uint8_t v_skipConstInApp_boxed_3232_; uint8_t v_skipInstances_boxed_3233_; lean_object* v_res_3234_; 
v_usedLetOnly_boxed_3231_ = lean_unbox(v_usedLetOnly_3228_);
v_skipConstInApp_boxed_3232_ = lean_unbox(v_skipConstInApp_3229_);
v_skipInstances_boxed_3233_ = lean_unbox(v_skipInstances_3230_);
v_res_3234_ = l_Lean_Meta_transformWithCache___redArg(v_inst_3221_, v_inst_3222_, v_inst_3223_, v_input_3224_, v_cache_3225_, v_pre_3226_, v_post_3227_, v_usedLetOnly_boxed_3231_, v_skipConstInApp_boxed_3232_, v_skipInstances_boxed_3233_);
return v_res_3234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache(lean_object* v_m_3235_, lean_object* v_inst_3236_, lean_object* v_inst_3237_, lean_object* v_inst_3238_, lean_object* v_input_3239_, lean_object* v_cache_3240_, lean_object* v_pre_3241_, lean_object* v_post_3242_, uint8_t v_usedLetOnly_3243_, uint8_t v_skipConstInApp_3244_, uint8_t v_skipInstances_3245_){
_start:
{
lean_object* v_x_3246_; lean_object* v_toApplicative_3247_; lean_object* v_toBind_3248_; lean_object* v_toPure_3249_; lean_object* v_x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___f_3256_; lean_object* v___x_3257_; 
v_x_3246_ = lean_box(0);
v_toApplicative_3247_ = lean_ctor_get(v_inst_3236_, 0);
v_toBind_3248_ = lean_ctor_get(v_inst_3236_, 1);
lean_inc_n(v_toBind_3248_, 2);
v_toPure_3249_ = lean_ctor_get(v_toApplicative_3247_, 1);
lean_inc(v_toPure_3249_);
lean_inc_n(v_inst_3237_, 2);
v_x_3250_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__1), 3, 1);
lean_closure_set(v_x_3250_, 0, v_inst_3237_);
v___x_3251_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_3251_, 0, lean_box(0));
lean_closure_set(v___x_3251_, 1, lean_box(0));
lean_closure_set(v___x_3251_, 2, v_cache_3240_);
v___x_3252_ = l_Lean_Meta_transformWithCache___redArg___lam__1(v_inst_3237_, lean_box(0), v___x_3251_);
v___x_3253_ = lean_box(v_usedLetOnly_3243_);
v___x_3254_ = lean_box(v_skipConstInApp_3244_);
v___x_3255_ = lean_box(v_skipInstances_3245_);
v___f_3256_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__4___boxed), 14, 13);
lean_closure_set(v___f_3256_, 0, v_toPure_3249_);
lean_closure_set(v___f_3256_, 1, v_x_3250_);
lean_closure_set(v___f_3256_, 2, v_toBind_3248_);
lean_closure_set(v___f_3256_, 3, v_inst_3236_);
lean_closure_set(v___f_3256_, 4, v_inst_3237_);
lean_closure_set(v___f_3256_, 5, v_inst_3238_);
lean_closure_set(v___f_3256_, 6, v_pre_3241_);
lean_closure_set(v___f_3256_, 7, v_post_3242_);
lean_closure_set(v___f_3256_, 8, v___x_3253_);
lean_closure_set(v___f_3256_, 9, v___x_3254_);
lean_closure_set(v___f_3256_, 10, v___x_3255_);
lean_closure_set(v___f_3256_, 11, v_x_3246_);
lean_closure_set(v___f_3256_, 12, v_input_3239_);
v___x_3257_ = lean_apply_4(v_toBind_3248_, lean_box(0), lean_box(0), v___x_3252_, v___f_3256_);
return v___x_3257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___boxed(lean_object* v_m_3258_, lean_object* v_inst_3259_, lean_object* v_inst_3260_, lean_object* v_inst_3261_, lean_object* v_input_3262_, lean_object* v_cache_3263_, lean_object* v_pre_3264_, lean_object* v_post_3265_, lean_object* v_usedLetOnly_3266_, lean_object* v_skipConstInApp_3267_, lean_object* v_skipInstances_3268_){
_start:
{
uint8_t v_usedLetOnly_boxed_3269_; uint8_t v_skipConstInApp_boxed_3270_; uint8_t v_skipInstances_boxed_3271_; lean_object* v_res_3272_; 
v_usedLetOnly_boxed_3269_ = lean_unbox(v_usedLetOnly_3266_);
v_skipConstInApp_boxed_3270_ = lean_unbox(v_skipConstInApp_3267_);
v_skipInstances_boxed_3271_ = lean_unbox(v_skipInstances_3268_);
v_res_3272_ = l_Lean_Meta_transformWithCache(v_m_3258_, v_inst_3259_, v_inst_3260_, v_inst_3261_, v_input_3262_, v_cache_3263_, v_pre_3264_, v_post_3265_, v_usedLetOnly_boxed_3269_, v_skipConstInApp_boxed_3270_, v_skipInstances_boxed_3271_);
return v_res_3272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___redArg___lam__5(lean_object* v_toPure_3273_, lean_object* v_x_3274_, lean_object* v_toBind_3275_, lean_object* v_inst_3276_, lean_object* v_inst_3277_, lean_object* v_inst_3278_, lean_object* v_pre_3279_, lean_object* v_post_3280_, uint8_t v_usedLetOnly_3281_, uint8_t v_skipConstInApp_3282_, uint8_t v___x_3283_, lean_object* v_x_3284_, lean_object* v_input_3285_, lean_object* v_ref_3286_){
_start:
{
lean_object* v___f_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; 
lean_inc(v_toBind_3275_);
lean_inc(v_x_3274_);
lean_inc(v_ref_3286_);
v___f_3287_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__4), 5, 4);
lean_closure_set(v___f_3287_, 0, v_toPure_3273_);
lean_closure_set(v___f_3287_, 1, v_ref_3286_);
lean_closure_set(v___f_3287_, 2, v_x_3274_);
lean_closure_set(v___f_3287_, 3, v_toBind_3275_);
v___x_3288_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_3276_, v_inst_3277_, v_inst_3278_, v_pre_3279_, v_post_3280_, v_usedLetOnly_3281_, v_skipConstInApp_3282_, v___x_3283_, v_x_3284_, v_x_3274_, v_input_3285_, v_ref_3286_);
lean_dec(v_ref_3286_);
v___x_3289_ = lean_apply_4(v_toBind_3275_, lean_box(0), lean_box(0), v___x_3288_, v___f_3287_);
return v___x_3289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___redArg___lam__5___boxed(lean_object* v_toPure_3290_, lean_object* v_x_3291_, lean_object* v_toBind_3292_, lean_object* v_inst_3293_, lean_object* v_inst_3294_, lean_object* v_inst_3295_, lean_object* v_pre_3296_, lean_object* v_post_3297_, lean_object* v_usedLetOnly_3298_, lean_object* v_skipConstInApp_3299_, lean_object* v___x_3300_, lean_object* v_x_3301_, lean_object* v_input_3302_, lean_object* v_ref_3303_){
_start:
{
uint8_t v_usedLetOnly_boxed_3304_; uint8_t v_skipConstInApp_boxed_3305_; uint8_t v___x_114__boxed_3306_; lean_object* v_res_3307_; 
v_usedLetOnly_boxed_3304_ = lean_unbox(v_usedLetOnly_3298_);
v_skipConstInApp_boxed_3305_ = lean_unbox(v_skipConstInApp_3299_);
v___x_114__boxed_3306_ = lean_unbox(v___x_3300_);
v_res_3307_ = l_Lean_Meta_transform___redArg___lam__5(v_toPure_3290_, v_x_3291_, v_toBind_3292_, v_inst_3293_, v_inst_3294_, v_inst_3295_, v_pre_3296_, v_post_3297_, v_usedLetOnly_boxed_3304_, v_skipConstInApp_boxed_3305_, v___x_114__boxed_3306_, v_x_3301_, v_input_3302_, v_ref_3303_);
return v_res_3307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___redArg(lean_object* v_inst_3308_, lean_object* v_inst_3309_, lean_object* v_inst_3310_, lean_object* v_input_3311_, lean_object* v_pre_3312_, lean_object* v_post_3313_, uint8_t v_usedLetOnly_3314_, uint8_t v_skipConstInApp_3315_){
_start:
{
lean_object* v_toApplicative_3316_; lean_object* v_toBind_3317_; lean_object* v_x_3318_; lean_object* v_toPure_3319_; lean_object* v_x_3320_; uint8_t v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___f_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___f_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; 
v_toApplicative_3316_ = lean_ctor_get(v_inst_3308_, 0);
v_toBind_3317_ = lean_ctor_get(v_inst_3308_, 1);
lean_inc_n(v_toBind_3317_, 3);
v_x_3318_ = lean_box(0);
v_toPure_3319_ = lean_ctor_get(v_toApplicative_3316_, 1);
lean_inc_n(v_toPure_3319_, 2);
lean_inc_n(v_inst_3309_, 2);
v_x_3320_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__1), 3, 1);
lean_closure_set(v_x_3320_, 0, v_inst_3309_);
v___x_3321_ = 0;
v___x_3322_ = lean_obj_once(&l_Lean_Core_transform___redArg___closed__2, &l_Lean_Core_transform___redArg___closed__2_once, _init_l_Lean_Core_transform___redArg___closed__2);
v___x_3323_ = l_Lean_Meta_transformWithCache___redArg___lam__1(v_inst_3309_, lean_box(0), v___x_3322_);
v___f_3324_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__2), 2, 1);
lean_closure_set(v___f_3324_, 0, v_toPure_3319_);
v___x_3325_ = lean_box(v_usedLetOnly_3314_);
v___x_3326_ = lean_box(v_skipConstInApp_3315_);
v___x_3327_ = lean_box(v___x_3321_);
v___f_3328_ = lean_alloc_closure((void*)(l_Lean_Meta_transform___redArg___lam__5___boxed), 14, 13);
lean_closure_set(v___f_3328_, 0, v_toPure_3319_);
lean_closure_set(v___f_3328_, 1, v_x_3320_);
lean_closure_set(v___f_3328_, 2, v_toBind_3317_);
lean_closure_set(v___f_3328_, 3, v_inst_3308_);
lean_closure_set(v___f_3328_, 4, v_inst_3309_);
lean_closure_set(v___f_3328_, 5, v_inst_3310_);
lean_closure_set(v___f_3328_, 6, v_pre_3312_);
lean_closure_set(v___f_3328_, 7, v_post_3313_);
lean_closure_set(v___f_3328_, 8, v___x_3325_);
lean_closure_set(v___f_3328_, 9, v___x_3326_);
lean_closure_set(v___f_3328_, 10, v___x_3327_);
lean_closure_set(v___f_3328_, 11, v_x_3318_);
lean_closure_set(v___f_3328_, 12, v_input_3311_);
v___x_3329_ = lean_apply_4(v_toBind_3317_, lean_box(0), lean_box(0), v___x_3323_, v___f_3328_);
v___x_3330_ = lean_apply_4(v_toBind_3317_, lean_box(0), lean_box(0), v___x_3329_, v___f_3324_);
return v___x_3330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___redArg___boxed(lean_object* v_inst_3331_, lean_object* v_inst_3332_, lean_object* v_inst_3333_, lean_object* v_input_3334_, lean_object* v_pre_3335_, lean_object* v_post_3336_, lean_object* v_usedLetOnly_3337_, lean_object* v_skipConstInApp_3338_){
_start:
{
uint8_t v_usedLetOnly_boxed_3339_; uint8_t v_skipConstInApp_boxed_3340_; lean_object* v_res_3341_; 
v_usedLetOnly_boxed_3339_ = lean_unbox(v_usedLetOnly_3337_);
v_skipConstInApp_boxed_3340_ = lean_unbox(v_skipConstInApp_3338_);
v_res_3341_ = l_Lean_Meta_transform___redArg(v_inst_3331_, v_inst_3332_, v_inst_3333_, v_input_3334_, v_pre_3335_, v_post_3336_, v_usedLetOnly_boxed_3339_, v_skipConstInApp_boxed_3340_);
return v_res_3341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform(lean_object* v_m_3342_, lean_object* v_inst_3343_, lean_object* v_inst_3344_, lean_object* v_inst_3345_, lean_object* v_input_3346_, lean_object* v_pre_3347_, lean_object* v_post_3348_, uint8_t v_usedLetOnly_3349_, uint8_t v_skipConstInApp_3350_){
_start:
{
lean_object* v___x_3351_; 
v___x_3351_ = l_Lean_Meta_transform___redArg(v_inst_3343_, v_inst_3344_, v_inst_3345_, v_input_3346_, v_pre_3347_, v_post_3348_, v_usedLetOnly_3349_, v_skipConstInApp_3350_);
return v___x_3351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___boxed(lean_object* v_m_3352_, lean_object* v_inst_3353_, lean_object* v_inst_3354_, lean_object* v_inst_3355_, lean_object* v_input_3356_, lean_object* v_pre_3357_, lean_object* v_post_3358_, lean_object* v_usedLetOnly_3359_, lean_object* v_skipConstInApp_3360_){
_start:
{
uint8_t v_usedLetOnly_boxed_3361_; uint8_t v_skipConstInApp_boxed_3362_; lean_object* v_res_3363_; 
v_usedLetOnly_boxed_3361_ = lean_unbox(v_usedLetOnly_3359_);
v_skipConstInApp_boxed_3362_ = lean_unbox(v_skipConstInApp_3360_);
v_res_3363_ = l_Lean_Meta_transform(v_m_3352_, v_inst_3353_, v_inst_3354_, v_inst_3355_, v_input_3356_, v_pre_3357_, v_post_3358_, v_usedLetOnly_boxed_3361_, v_skipConstInApp_boxed_3362_);
return v_res_3363_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(lean_object* v_e_3364_, lean_object* v___y_3365_){
_start:
{
uint8_t v___x_3367_; 
v___x_3367_ = l_Lean_Expr_hasMVar(v_e_3364_);
if (v___x_3367_ == 0)
{
lean_object* v___x_3368_; 
v___x_3368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3368_, 0, v_e_3364_);
return v___x_3368_;
}
else
{
lean_object* v___x_3369_; lean_object* v_mctx_3370_; lean_object* v___x_3371_; lean_object* v_fst_3372_; lean_object* v_snd_3373_; lean_object* v___x_3374_; lean_object* v_cache_3375_; lean_object* v_zetaDeltaFVarIds_3376_; lean_object* v_postponed_3377_; lean_object* v_diag_3378_; lean_object* v___x_3380_; uint8_t v_isShared_3381_; uint8_t v_isSharedCheck_3387_; 
v___x_3369_ = lean_st_ref_get(v___y_3365_);
v_mctx_3370_ = lean_ctor_get(v___x_3369_, 0);
lean_inc_ref(v_mctx_3370_);
lean_dec(v___x_3369_);
v___x_3371_ = l_Lean_instantiateMVarsCore(v_mctx_3370_, v_e_3364_);
v_fst_3372_ = lean_ctor_get(v___x_3371_, 0);
lean_inc(v_fst_3372_);
v_snd_3373_ = lean_ctor_get(v___x_3371_, 1);
lean_inc(v_snd_3373_);
lean_dec_ref(v___x_3371_);
v___x_3374_ = lean_st_ref_take(v___y_3365_);
v_cache_3375_ = lean_ctor_get(v___x_3374_, 1);
v_zetaDeltaFVarIds_3376_ = lean_ctor_get(v___x_3374_, 2);
v_postponed_3377_ = lean_ctor_get(v___x_3374_, 3);
v_diag_3378_ = lean_ctor_get(v___x_3374_, 4);
v_isSharedCheck_3387_ = !lean_is_exclusive(v___x_3374_);
if (v_isSharedCheck_3387_ == 0)
{
lean_object* v_unused_3388_; 
v_unused_3388_ = lean_ctor_get(v___x_3374_, 0);
lean_dec(v_unused_3388_);
v___x_3380_ = v___x_3374_;
v_isShared_3381_ = v_isSharedCheck_3387_;
goto v_resetjp_3379_;
}
else
{
lean_inc(v_diag_3378_);
lean_inc(v_postponed_3377_);
lean_inc(v_zetaDeltaFVarIds_3376_);
lean_inc(v_cache_3375_);
lean_dec(v___x_3374_);
v___x_3380_ = lean_box(0);
v_isShared_3381_ = v_isSharedCheck_3387_;
goto v_resetjp_3379_;
}
v_resetjp_3379_:
{
lean_object* v___x_3383_; 
if (v_isShared_3381_ == 0)
{
lean_ctor_set(v___x_3380_, 0, v_snd_3373_);
v___x_3383_ = v___x_3380_;
goto v_reusejp_3382_;
}
else
{
lean_object* v_reuseFailAlloc_3386_; 
v_reuseFailAlloc_3386_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3386_, 0, v_snd_3373_);
lean_ctor_set(v_reuseFailAlloc_3386_, 1, v_cache_3375_);
lean_ctor_set(v_reuseFailAlloc_3386_, 2, v_zetaDeltaFVarIds_3376_);
lean_ctor_set(v_reuseFailAlloc_3386_, 3, v_postponed_3377_);
lean_ctor_set(v_reuseFailAlloc_3386_, 4, v_diag_3378_);
v___x_3383_ = v_reuseFailAlloc_3386_;
goto v_reusejp_3382_;
}
v_reusejp_3382_:
{
lean_object* v___x_3384_; lean_object* v___x_3385_; 
v___x_3384_ = lean_st_ref_put(v___y_3365_, v___x_3383_);
v___x_3385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3385_, 0, v_fst_3372_);
return v___x_3385_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg___boxed(lean_object* v_e_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_){
_start:
{
lean_object* v_res_3392_; 
v_res_3392_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(v_e_3389_, v___y_3390_);
lean_dec(v___y_3390_);
return v_res_3392_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0(lean_object* v_e_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_){
_start:
{
lean_object* v___x_3399_; 
v___x_3399_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(v_e_3393_, v___y_3395_);
return v___x_3399_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___boxed(lean_object* v_e_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_){
_start:
{
lean_object* v_res_3406_; 
v_res_3406_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0(v_e_3400_, v___y_3401_, v___y_3402_, v___y_3403_, v___y_3404_);
lean_dec(v___y_3404_);
lean_dec_ref(v___y_3403_);
lean_dec(v___y_3402_);
lean_dec_ref(v___y_3401_);
return v_res_3406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__0(uint8_t v_zetaHave_3407_, lean_object* v___x_3408_, uint8_t v_zetaDelta_3409_, lean_object* v_fvarId_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_){
_start:
{
lean_object* v___x_3416_; 
v___x_3416_ = l_Lean_FVarId_findDecl_x3f___redArg(v_fvarId_3410_, v___y_3411_);
if (lean_obj_tag(v___x_3416_) == 0)
{
lean_object* v_a_3417_; lean_object* v___x_3419_; uint8_t v_isShared_3420_; uint8_t v_isSharedCheck_3445_; 
v_a_3417_ = lean_ctor_get(v___x_3416_, 0);
v_isSharedCheck_3445_ = !lean_is_exclusive(v___x_3416_);
if (v_isSharedCheck_3445_ == 0)
{
v___x_3419_ = v___x_3416_;
v_isShared_3420_ = v_isSharedCheck_3445_;
goto v_resetjp_3418_;
}
else
{
lean_inc(v_a_3417_);
lean_dec(v___x_3416_);
v___x_3419_ = lean_box(0);
v_isShared_3420_ = v_isSharedCheck_3445_;
goto v_resetjp_3418_;
}
v_resetjp_3418_:
{
if (lean_obj_tag(v_a_3417_) == 1)
{
lean_object* v_val_3421_; lean_object* v___x_3423_; uint8_t v_isShared_3424_; uint8_t v_isSharedCheck_3440_; 
v_val_3421_ = lean_ctor_get(v_a_3417_, 0);
v_isSharedCheck_3440_ = !lean_is_exclusive(v_a_3417_);
if (v_isSharedCheck_3440_ == 0)
{
v___x_3423_ = v_a_3417_;
v_isShared_3424_ = v_isSharedCheck_3440_;
goto v_resetjp_3422_;
}
else
{
lean_inc(v_val_3421_);
lean_dec(v_a_3417_);
v___x_3423_ = lean_box(0);
v_isShared_3424_ = v_isSharedCheck_3440_;
goto v_resetjp_3422_;
}
v_resetjp_3422_:
{
uint8_t v___y_3426_; 
if (v_zetaDelta_3409_ == 0)
{
lean_object* v___x_3434_; uint8_t v___x_3435_; 
v___x_3434_ = l_Lean_LocalDecl_index(v_val_3421_);
v___x_3435_ = lean_nat_dec_lt(v___x_3434_, v___x_3408_);
lean_dec(v___x_3434_);
if (v___x_3435_ == 0)
{
lean_del_object(v___x_3423_);
goto v___jp_3431_;
}
else
{
lean_object* v___x_3436_; lean_object* v___x_3438_; 
lean_dec(v_val_3421_);
lean_del_object(v___x_3419_);
v___x_3436_ = lean_box(0);
if (v_isShared_3424_ == 0)
{
lean_ctor_set_tag(v___x_3423_, 0);
lean_ctor_set(v___x_3423_, 0, v___x_3436_);
v___x_3438_ = v___x_3423_;
goto v_reusejp_3437_;
}
else
{
lean_object* v_reuseFailAlloc_3439_; 
v_reuseFailAlloc_3439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3439_, 0, v___x_3436_);
v___x_3438_ = v_reuseFailAlloc_3439_;
goto v_reusejp_3437_;
}
v_reusejp_3437_:
{
return v___x_3438_;
}
}
}
else
{
lean_del_object(v___x_3423_);
goto v___jp_3431_;
}
v___jp_3425_:
{
lean_object* v___x_3427_; lean_object* v___x_3429_; 
v___x_3427_ = l_Lean_LocalDecl_value_x3f(v_val_3421_, v___y_3426_);
lean_dec(v_val_3421_);
if (v_isShared_3420_ == 0)
{
lean_ctor_set(v___x_3419_, 0, v___x_3427_);
v___x_3429_ = v___x_3419_;
goto v_reusejp_3428_;
}
else
{
lean_object* v_reuseFailAlloc_3430_; 
v_reuseFailAlloc_3430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3430_, 0, v___x_3427_);
v___x_3429_ = v_reuseFailAlloc_3430_;
goto v_reusejp_3428_;
}
v_reusejp_3428_:
{
return v___x_3429_;
}
}
v___jp_3431_:
{
if (v_zetaHave_3407_ == 0)
{
v___y_3426_ = v_zetaHave_3407_;
goto v___jp_3425_;
}
else
{
lean_object* v___x_3432_; uint8_t v___x_3433_; 
v___x_3432_ = l_Lean_LocalDecl_index(v_val_3421_);
v___x_3433_ = lean_nat_dec_le(v___x_3408_, v___x_3432_);
lean_dec(v___x_3432_);
v___y_3426_ = v___x_3433_;
goto v___jp_3425_;
}
}
}
}
else
{
lean_object* v___x_3441_; lean_object* v___x_3443_; 
lean_dec(v_a_3417_);
v___x_3441_ = lean_box(0);
if (v_isShared_3420_ == 0)
{
lean_ctor_set(v___x_3419_, 0, v___x_3441_);
v___x_3443_ = v___x_3419_;
goto v_reusejp_3442_;
}
else
{
lean_object* v_reuseFailAlloc_3444_; 
v_reuseFailAlloc_3444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3444_, 0, v___x_3441_);
v___x_3443_ = v_reuseFailAlloc_3444_;
goto v_reusejp_3442_;
}
v_reusejp_3442_:
{
return v___x_3443_;
}
}
}
}
else
{
lean_object* v_a_3446_; lean_object* v___x_3448_; uint8_t v_isShared_3449_; uint8_t v_isSharedCheck_3453_; 
v_a_3446_ = lean_ctor_get(v___x_3416_, 0);
v_isSharedCheck_3453_ = !lean_is_exclusive(v___x_3416_);
if (v_isSharedCheck_3453_ == 0)
{
v___x_3448_ = v___x_3416_;
v_isShared_3449_ = v_isSharedCheck_3453_;
goto v_resetjp_3447_;
}
else
{
lean_inc(v_a_3446_);
lean_dec(v___x_3416_);
v___x_3448_ = lean_box(0);
v_isShared_3449_ = v_isSharedCheck_3453_;
goto v_resetjp_3447_;
}
v_resetjp_3447_:
{
lean_object* v___x_3451_; 
if (v_isShared_3449_ == 0)
{
v___x_3451_ = v___x_3448_;
goto v_reusejp_3450_;
}
else
{
lean_object* v_reuseFailAlloc_3452_; 
v_reuseFailAlloc_3452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3452_, 0, v_a_3446_);
v___x_3451_ = v_reuseFailAlloc_3452_;
goto v_reusejp_3450_;
}
v_reusejp_3450_:
{
return v___x_3451_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__0___boxed(lean_object* v_zetaHave_3454_, lean_object* v___x_3455_, lean_object* v_zetaDelta_3456_, lean_object* v_fvarId_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_){
_start:
{
uint8_t v_zetaHave_boxed_3463_; uint8_t v_zetaDelta_boxed_3464_; lean_object* v_res_3465_; 
v_zetaHave_boxed_3463_ = lean_unbox(v_zetaHave_3454_);
v_zetaDelta_boxed_3464_ = lean_unbox(v_zetaDelta_3456_);
v_res_3465_ = l_Lean_Meta_zetaReduce___lam__0(v_zetaHave_boxed_3463_, v___x_3455_, v_zetaDelta_boxed_3464_, v_fvarId_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_);
lean_dec(v___y_3461_);
lean_dec_ref(v___y_3460_);
lean_dec(v___y_3459_);
lean_dec_ref(v___y_3458_);
lean_dec(v___x_3455_);
return v_res_3465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__1(lean_object* v_e_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_){
_start:
{
lean_object* v___x_3472_; lean_object* v___x_3473_; 
v___x_3472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3472_, 0, v_e_3466_);
v___x_3473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3473_, 0, v___x_3472_);
return v___x_3473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__1___boxed(lean_object* v_e_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_){
_start:
{
lean_object* v_res_3480_; 
v_res_3480_ = l_Lean_Meta_zetaReduce___lam__1(v_e_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_);
lean_dec(v___y_3478_);
lean_dec_ref(v___y_3477_);
lean_dec(v___y_3476_);
lean_dec_ref(v___y_3475_);
return v_res_3480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__2(lean_object* v___f_3481_, lean_object* v_e_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_){
_start:
{
if (lean_obj_tag(v_e_3482_) == 1)
{
lean_object* v_fvarId_3488_; lean_object* v___x_3489_; 
v_fvarId_3488_ = lean_ctor_get(v_e_3482_, 0);
lean_inc(v___y_3486_);
lean_inc_ref(v___y_3485_);
lean_inc(v___y_3484_);
lean_inc_ref(v___y_3483_);
lean_inc(v_fvarId_3488_);
v___x_3489_ = lean_apply_6(v___f_3481_, v_fvarId_3488_, v___y_3483_, v___y_3484_, v___y_3485_, v___y_3486_, lean_box(0));
if (lean_obj_tag(v___x_3489_) == 0)
{
lean_object* v_a_3490_; lean_object* v___x_3492_; uint8_t v_isShared_3493_; uint8_t v_isSharedCheck_3515_; 
v_a_3490_ = lean_ctor_get(v___x_3489_, 0);
v_isSharedCheck_3515_ = !lean_is_exclusive(v___x_3489_);
if (v_isSharedCheck_3515_ == 0)
{
v___x_3492_ = v___x_3489_;
v_isShared_3493_ = v_isSharedCheck_3515_;
goto v_resetjp_3491_;
}
else
{
lean_inc(v_a_3490_);
lean_dec(v___x_3489_);
v___x_3492_ = lean_box(0);
v_isShared_3493_ = v_isSharedCheck_3515_;
goto v_resetjp_3491_;
}
v_resetjp_3491_:
{
if (lean_obj_tag(v_a_3490_) == 1)
{
lean_object* v_val_3494_; lean_object* v___x_3496_; uint8_t v_isShared_3497_; uint8_t v_isSharedCheck_3510_; 
lean_del_object(v___x_3492_);
lean_dec_ref_known(v_e_3482_, 1);
v_val_3494_ = lean_ctor_get(v_a_3490_, 0);
v_isSharedCheck_3510_ = !lean_is_exclusive(v_a_3490_);
if (v_isSharedCheck_3510_ == 0)
{
v___x_3496_ = v_a_3490_;
v_isShared_3497_ = v_isSharedCheck_3510_;
goto v_resetjp_3495_;
}
else
{
lean_inc(v_val_3494_);
lean_dec(v_a_3490_);
v___x_3496_ = lean_box(0);
v_isShared_3497_ = v_isSharedCheck_3510_;
goto v_resetjp_3495_;
}
v_resetjp_3495_:
{
lean_object* v___x_3498_; lean_object* v_a_3499_; lean_object* v___x_3501_; uint8_t v_isShared_3502_; uint8_t v_isSharedCheck_3509_; 
v___x_3498_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(v_val_3494_, v___y_3484_);
v_a_3499_ = lean_ctor_get(v___x_3498_, 0);
v_isSharedCheck_3509_ = !lean_is_exclusive(v___x_3498_);
if (v_isSharedCheck_3509_ == 0)
{
v___x_3501_ = v___x_3498_;
v_isShared_3502_ = v_isSharedCheck_3509_;
goto v_resetjp_3500_;
}
else
{
lean_inc(v_a_3499_);
lean_dec(v___x_3498_);
v___x_3501_ = lean_box(0);
v_isShared_3502_ = v_isSharedCheck_3509_;
goto v_resetjp_3500_;
}
v_resetjp_3500_:
{
lean_object* v___x_3504_; 
if (v_isShared_3497_ == 0)
{
lean_ctor_set(v___x_3496_, 0, v_a_3499_);
v___x_3504_ = v___x_3496_;
goto v_reusejp_3503_;
}
else
{
lean_object* v_reuseFailAlloc_3508_; 
v_reuseFailAlloc_3508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3508_, 0, v_a_3499_);
v___x_3504_ = v_reuseFailAlloc_3508_;
goto v_reusejp_3503_;
}
v_reusejp_3503_:
{
lean_object* v___x_3506_; 
if (v_isShared_3502_ == 0)
{
lean_ctor_set(v___x_3501_, 0, v___x_3504_);
v___x_3506_ = v___x_3501_;
goto v_reusejp_3505_;
}
else
{
lean_object* v_reuseFailAlloc_3507_; 
v_reuseFailAlloc_3507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3507_, 0, v___x_3504_);
v___x_3506_ = v_reuseFailAlloc_3507_;
goto v_reusejp_3505_;
}
v_reusejp_3505_:
{
return v___x_3506_;
}
}
}
}
}
else
{
lean_object* v___x_3511_; lean_object* v___x_3513_; 
lean_dec(v_a_3490_);
v___x_3511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3511_, 0, v_e_3482_);
if (v_isShared_3493_ == 0)
{
lean_ctor_set(v___x_3492_, 0, v___x_3511_);
v___x_3513_ = v___x_3492_;
goto v_reusejp_3512_;
}
else
{
lean_object* v_reuseFailAlloc_3514_; 
v_reuseFailAlloc_3514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3514_, 0, v___x_3511_);
v___x_3513_ = v_reuseFailAlloc_3514_;
goto v_reusejp_3512_;
}
v_reusejp_3512_:
{
return v___x_3513_;
}
}
}
}
else
{
lean_object* v_a_3516_; lean_object* v___x_3518_; uint8_t v_isShared_3519_; uint8_t v_isSharedCheck_3523_; 
lean_dec_ref_known(v_e_3482_, 1);
v_a_3516_ = lean_ctor_get(v___x_3489_, 0);
v_isSharedCheck_3523_ = !lean_is_exclusive(v___x_3489_);
if (v_isSharedCheck_3523_ == 0)
{
v___x_3518_ = v___x_3489_;
v_isShared_3519_ = v_isSharedCheck_3523_;
goto v_resetjp_3517_;
}
else
{
lean_inc(v_a_3516_);
lean_dec(v___x_3489_);
v___x_3518_ = lean_box(0);
v_isShared_3519_ = v_isSharedCheck_3523_;
goto v_resetjp_3517_;
}
v_resetjp_3517_:
{
lean_object* v___x_3521_; 
if (v_isShared_3519_ == 0)
{
v___x_3521_ = v___x_3518_;
goto v_reusejp_3520_;
}
else
{
lean_object* v_reuseFailAlloc_3522_; 
v_reuseFailAlloc_3522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3522_, 0, v_a_3516_);
v___x_3521_ = v_reuseFailAlloc_3522_;
goto v_reusejp_3520_;
}
v_reusejp_3520_:
{
return v___x_3521_;
}
}
}
}
else
{
lean_object* v___x_3524_; lean_object* v___x_3525_; 
lean_dec_ref(v_e_3482_);
lean_dec_ref(v___f_3481_);
v___x_3524_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_3525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3525_, 0, v___x_3524_);
return v___x_3525_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__2___boxed(lean_object* v___f_3526_, lean_object* v_e_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_){
_start:
{
lean_object* v_res_3533_; 
v_res_3533_ = l_Lean_Meta_zetaReduce___lam__2(v___f_3526_, v_e_3527_, v___y_3528_, v___y_3529_, v___y_3530_, v___y_3531_);
lean_dec(v___y_3531_);
lean_dec_ref(v___y_3530_);
lean_dec(v___y_3529_);
lean_dec_ref(v___y_3528_);
return v_res_3533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__4(lean_object* v___f_3534_, lean_object* v_e_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_){
_start:
{
lean_object* v___x_3541_; 
v___x_3541_ = l_Lean_Expr_getAppFn(v_e_3535_);
if (lean_obj_tag(v___x_3541_) == 1)
{
lean_object* v_fvarId_3542_; lean_object* v___x_3543_; 
v_fvarId_3542_ = lean_ctor_get(v___x_3541_, 0);
lean_inc(v_fvarId_3542_);
lean_dec_ref_known(v___x_3541_, 1);
lean_inc(v___y_3539_);
lean_inc_ref(v___y_3538_);
lean_inc(v___y_3537_);
lean_inc_ref(v___y_3536_);
v___x_3543_ = lean_apply_6(v___f_3534_, v_fvarId_3542_, v___y_3536_, v___y_3537_, v___y_3538_, v___y_3539_, lean_box(0));
if (lean_obj_tag(v___x_3543_) == 0)
{
lean_object* v_a_3544_; lean_object* v___x_3546_; uint8_t v_isShared_3547_; uint8_t v_isSharedCheck_3576_; 
v_a_3544_ = lean_ctor_get(v___x_3543_, 0);
v_isSharedCheck_3576_ = !lean_is_exclusive(v___x_3543_);
if (v_isSharedCheck_3576_ == 0)
{
v___x_3546_ = v___x_3543_;
v_isShared_3547_ = v_isSharedCheck_3576_;
goto v_resetjp_3545_;
}
else
{
lean_inc(v_a_3544_);
lean_dec(v___x_3543_);
v___x_3546_ = lean_box(0);
v_isShared_3547_ = v_isSharedCheck_3576_;
goto v_resetjp_3545_;
}
v_resetjp_3545_:
{
if (lean_obj_tag(v_a_3544_) == 1)
{
lean_object* v_val_3548_; lean_object* v___x_3550_; uint8_t v_isShared_3551_; uint8_t v_isSharedCheck_3571_; 
lean_del_object(v___x_3546_);
v_val_3548_ = lean_ctor_get(v_a_3544_, 0);
v_isSharedCheck_3571_ = !lean_is_exclusive(v_a_3544_);
if (v_isSharedCheck_3571_ == 0)
{
v___x_3550_ = v_a_3544_;
v_isShared_3551_ = v_isSharedCheck_3571_;
goto v_resetjp_3549_;
}
else
{
lean_inc(v_val_3548_);
lean_dec(v_a_3544_);
v___x_3550_ = lean_box(0);
v_isShared_3551_ = v_isSharedCheck_3571_;
goto v_resetjp_3549_;
}
v_resetjp_3549_:
{
lean_object* v___x_3552_; lean_object* v_a_3553_; lean_object* v___x_3555_; uint8_t v_isShared_3556_; uint8_t v_isSharedCheck_3570_; 
v___x_3552_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(v_val_3548_, v___y_3537_);
v_a_3553_ = lean_ctor_get(v___x_3552_, 0);
v_isSharedCheck_3570_ = !lean_is_exclusive(v___x_3552_);
if (v_isSharedCheck_3570_ == 0)
{
v___x_3555_ = v___x_3552_;
v_isShared_3556_ = v_isSharedCheck_3570_;
goto v_resetjp_3554_;
}
else
{
lean_inc(v_a_3553_);
lean_dec(v___x_3552_);
v___x_3555_ = lean_box(0);
v_isShared_3556_ = v_isSharedCheck_3570_;
goto v_resetjp_3554_;
}
v_resetjp_3554_:
{
lean_object* v_dummy_3557_; lean_object* v_nargs_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3565_; 
v_dummy_3557_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_3558_ = l_Lean_Expr_getAppNumArgs(v_e_3535_);
lean_inc(v_nargs_3558_);
v___x_3559_ = lean_mk_array(v_nargs_3558_, v_dummy_3557_);
v___x_3560_ = lean_unsigned_to_nat(1u);
v___x_3561_ = lean_nat_sub(v_nargs_3558_, v___x_3560_);
lean_dec(v_nargs_3558_);
v___x_3562_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3535_, v___x_3559_, v___x_3561_);
v___x_3563_ = l_Lean_Expr_beta(v_a_3553_, v___x_3562_);
if (v_isShared_3551_ == 0)
{
lean_ctor_set(v___x_3550_, 0, v___x_3563_);
v___x_3565_ = v___x_3550_;
goto v_reusejp_3564_;
}
else
{
lean_object* v_reuseFailAlloc_3569_; 
v_reuseFailAlloc_3569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3569_, 0, v___x_3563_);
v___x_3565_ = v_reuseFailAlloc_3569_;
goto v_reusejp_3564_;
}
v_reusejp_3564_:
{
lean_object* v___x_3567_; 
if (v_isShared_3556_ == 0)
{
lean_ctor_set(v___x_3555_, 0, v___x_3565_);
v___x_3567_ = v___x_3555_;
goto v_reusejp_3566_;
}
else
{
lean_object* v_reuseFailAlloc_3568_; 
v_reuseFailAlloc_3568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3568_, 0, v___x_3565_);
v___x_3567_ = v_reuseFailAlloc_3568_;
goto v_reusejp_3566_;
}
v_reusejp_3566_:
{
return v___x_3567_;
}
}
}
}
}
else
{
lean_object* v___x_3572_; lean_object* v___x_3574_; 
lean_dec(v_a_3544_);
lean_dec_ref(v_e_3535_);
v___x_3572_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
if (v_isShared_3547_ == 0)
{
lean_ctor_set(v___x_3546_, 0, v___x_3572_);
v___x_3574_ = v___x_3546_;
goto v_reusejp_3573_;
}
else
{
lean_object* v_reuseFailAlloc_3575_; 
v_reuseFailAlloc_3575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3575_, 0, v___x_3572_);
v___x_3574_ = v_reuseFailAlloc_3575_;
goto v_reusejp_3573_;
}
v_reusejp_3573_:
{
return v___x_3574_;
}
}
}
}
else
{
lean_object* v_a_3577_; lean_object* v___x_3579_; uint8_t v_isShared_3580_; uint8_t v_isSharedCheck_3584_; 
lean_dec_ref(v_e_3535_);
v_a_3577_ = lean_ctor_get(v___x_3543_, 0);
v_isSharedCheck_3584_ = !lean_is_exclusive(v___x_3543_);
if (v_isSharedCheck_3584_ == 0)
{
v___x_3579_ = v___x_3543_;
v_isShared_3580_ = v_isSharedCheck_3584_;
goto v_resetjp_3578_;
}
else
{
lean_inc(v_a_3577_);
lean_dec(v___x_3543_);
v___x_3579_ = lean_box(0);
v_isShared_3580_ = v_isSharedCheck_3584_;
goto v_resetjp_3578_;
}
v_resetjp_3578_:
{
lean_object* v___x_3582_; 
if (v_isShared_3580_ == 0)
{
v___x_3582_ = v___x_3579_;
goto v_reusejp_3581_;
}
else
{
lean_object* v_reuseFailAlloc_3583_; 
v_reuseFailAlloc_3583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3583_, 0, v_a_3577_);
v___x_3582_ = v_reuseFailAlloc_3583_;
goto v_reusejp_3581_;
}
v_reusejp_3581_:
{
return v___x_3582_;
}
}
}
}
else
{
lean_object* v___x_3585_; lean_object* v___x_3586_; 
lean_dec_ref(v___x_3541_);
lean_dec_ref(v_e_3535_);
lean_dec_ref(v___f_3534_);
v___x_3585_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_3586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3586_, 0, v___x_3585_);
return v___x_3586_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__4___boxed(lean_object* v___f_3587_, lean_object* v_e_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_){
_start:
{
lean_object* v_res_3594_; 
v_res_3594_ = l_Lean_Meta_zetaReduce___lam__4(v___f_3587_, v_e_3588_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_);
lean_dec(v___y_3592_);
lean_dec_ref(v___y_3591_);
lean_dec(v___y_3590_);
lean_dec_ref(v___y_3589_);
return v_res_3594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0(lean_object* v_00_u03b1_3595_, lean_object* v_x_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_){
_start:
{
lean_object* v___x_3602_; lean_object* v___x_3603_; 
v___x_3602_ = lean_apply_1(v_x_3596_, lean_box(0));
v___x_3603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3603_, 0, v___x_3602_);
return v___x_3603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0___boxed(lean_object* v_00_u03b1_3604_, lean_object* v_x_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_){
_start:
{
lean_object* v_res_3611_; 
v_res_3611_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0(v_00_u03b1_3604_, v_x_3605_, v___y_3606_, v___y_3607_, v___y_3608_, v___y_3609_);
lean_dec(v___y_3609_);
lean_dec_ref(v___y_3608_);
lean_dec(v___y_3607_);
lean_dec_ref(v___y_3606_);
return v_res_3611_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__2(lean_object* v___x_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_){
_start:
{
lean_object* v___x_3618_; 
v___x_3618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3618_, 0, v___x_3612_);
return v___x_3618_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__2___boxed(lean_object* v___x_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_){
_start:
{
lean_object* v_res_3625_; 
v_res_3625_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__2(v___x_3619_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_);
lean_dec(v___y_3623_);
lean_dec_ref(v___y_3622_);
lean_dec(v___y_3621_);
lean_dec_ref(v___y_3620_);
return v_res_3625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0(lean_object* v_k_3626_, lean_object* v___y_3627_, lean_object* v_b_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_){
_start:
{
lean_object* v___x_3634_; 
lean_inc(v___y_3632_);
lean_inc_ref(v___y_3631_);
lean_inc(v___y_3630_);
lean_inc_ref(v___y_3629_);
lean_inc(v___y_3627_);
v___x_3634_ = lean_apply_7(v_k_3626_, v_b_3628_, v___y_3627_, v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_, lean_box(0));
return v___x_3634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0___boxed(lean_object* v_k_3635_, lean_object* v___y_3636_, lean_object* v_b_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_){
_start:
{
lean_object* v_res_3643_; 
v_res_3643_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0(v_k_3635_, v___y_3636_, v_b_3637_, v___y_3638_, v___y_3639_, v___y_3640_, v___y_3641_);
lean_dec(v___y_3641_);
lean_dec_ref(v___y_3640_);
lean_dec(v___y_3639_);
lean_dec_ref(v___y_3638_);
lean_dec(v___y_3636_);
return v_res_3643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(lean_object* v_name_3644_, uint8_t v_bi_3645_, lean_object* v_type_3646_, lean_object* v_k_3647_, uint8_t v_kind_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_){
_start:
{
lean_object* v___f_3655_; lean_object* v___x_3656_; 
lean_inc(v___y_3649_);
v___f_3655_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3655_, 0, v_k_3647_);
lean_closure_set(v___f_3655_, 1, v___y_3649_);
v___x_3656_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3644_, v_bi_3645_, v_type_3646_, v___f_3655_, v_kind_3648_, v___y_3650_, v___y_3651_, v___y_3652_, v___y_3653_);
if (lean_obj_tag(v___x_3656_) == 0)
{
return v___x_3656_;
}
else
{
lean_object* v_a_3657_; lean_object* v___x_3659_; uint8_t v_isShared_3660_; uint8_t v_isSharedCheck_3664_; 
v_a_3657_ = lean_ctor_get(v___x_3656_, 0);
v_isSharedCheck_3664_ = !lean_is_exclusive(v___x_3656_);
if (v_isSharedCheck_3664_ == 0)
{
v___x_3659_ = v___x_3656_;
v_isShared_3660_ = v_isSharedCheck_3664_;
goto v_resetjp_3658_;
}
else
{
lean_inc(v_a_3657_);
lean_dec(v___x_3656_);
v___x_3659_ = lean_box(0);
v_isShared_3660_ = v_isSharedCheck_3664_;
goto v_resetjp_3658_;
}
v_resetjp_3658_:
{
lean_object* v___x_3662_; 
if (v_isShared_3660_ == 0)
{
v___x_3662_ = v___x_3659_;
goto v_reusejp_3661_;
}
else
{
lean_object* v_reuseFailAlloc_3663_; 
v_reuseFailAlloc_3663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3663_, 0, v_a_3657_);
v___x_3662_ = v_reuseFailAlloc_3663_;
goto v_reusejp_3661_;
}
v_reusejp_3661_:
{
return v___x_3662_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___boxed(lean_object* v_name_3665_, lean_object* v_bi_3666_, lean_object* v_type_3667_, lean_object* v_k_3668_, lean_object* v_kind_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_){
_start:
{
uint8_t v_bi_boxed_3676_; uint8_t v_kind_boxed_3677_; lean_object* v_res_3678_; 
v_bi_boxed_3676_ = lean_unbox(v_bi_3666_);
v_kind_boxed_3677_ = lean_unbox(v_kind_3669_);
v_res_3678_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_name_3665_, v_bi_boxed_3676_, v_type_3667_, v_k_3668_, v_kind_boxed_3677_, v___y_3670_, v___y_3671_, v___y_3672_, v___y_3673_, v___y_3674_);
lean_dec(v___y_3674_);
lean_dec_ref(v___y_3673_);
lean_dec(v___y_3672_);
lean_dec_ref(v___y_3671_);
lean_dec(v___y_3670_);
return v_res_3678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg(lean_object* v_name_3679_, lean_object* v_type_3680_, lean_object* v_val_3681_, lean_object* v_k_3682_, uint8_t v_nondep_3683_, uint8_t v_kind_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_){
_start:
{
lean_object* v___f_3691_; lean_object* v___x_3692_; 
lean_inc(v___y_3685_);
v___f_3691_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3691_, 0, v_k_3682_);
lean_closure_set(v___f_3691_, 1, v___y_3685_);
v___x_3692_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_3679_, v_type_3680_, v_val_3681_, v___f_3691_, v_nondep_3683_, v_kind_3684_, v___y_3686_, v___y_3687_, v___y_3688_, v___y_3689_);
if (lean_obj_tag(v___x_3692_) == 0)
{
return v___x_3692_;
}
else
{
lean_object* v_a_3693_; lean_object* v___x_3695_; uint8_t v_isShared_3696_; uint8_t v_isSharedCheck_3700_; 
v_a_3693_ = lean_ctor_get(v___x_3692_, 0);
v_isSharedCheck_3700_ = !lean_is_exclusive(v___x_3692_);
if (v_isSharedCheck_3700_ == 0)
{
v___x_3695_ = v___x_3692_;
v_isShared_3696_ = v_isSharedCheck_3700_;
goto v_resetjp_3694_;
}
else
{
lean_inc(v_a_3693_);
lean_dec(v___x_3692_);
v___x_3695_ = lean_box(0);
v_isShared_3696_ = v_isSharedCheck_3700_;
goto v_resetjp_3694_;
}
v_resetjp_3694_:
{
lean_object* v___x_3698_; 
if (v_isShared_3696_ == 0)
{
v___x_3698_ = v___x_3695_;
goto v_reusejp_3697_;
}
else
{
lean_object* v_reuseFailAlloc_3699_; 
v_reuseFailAlloc_3699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3699_, 0, v_a_3693_);
v___x_3698_ = v_reuseFailAlloc_3699_;
goto v_reusejp_3697_;
}
v_reusejp_3697_:
{
return v___x_3698_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg___boxed(lean_object* v_name_3701_, lean_object* v_type_3702_, lean_object* v_val_3703_, lean_object* v_k_3704_, lean_object* v_nondep_3705_, lean_object* v_kind_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_){
_start:
{
uint8_t v_nondep_boxed_3713_; uint8_t v_kind_boxed_3714_; lean_object* v_res_3715_; 
v_nondep_boxed_3713_ = lean_unbox(v_nondep_3705_);
v_kind_boxed_3714_ = lean_unbox(v_kind_3706_);
v_res_3715_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg(v_name_3701_, v_type_3702_, v_val_3703_, v_k_3704_, v_nondep_boxed_3713_, v_kind_boxed_3714_, v___y_3707_, v___y_3708_, v___y_3709_, v___y_3710_, v___y_3711_);
lean_dec(v___y_3711_);
lean_dec_ref(v___y_3710_);
lean_dec(v___y_3709_);
lean_dec_ref(v___y_3708_);
lean_dec(v___y_3707_);
return v_res_3715_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0(lean_object* v_00_u03b1_3716_, lean_object* v_x_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_){
_start:
{
lean_object* v___x_3723_; lean_object* v___x_3724_; 
v___x_3723_ = lean_apply_1(v_x_3717_, lean_box(0));
v___x_3724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3724_, 0, v___x_3723_);
return v___x_3724_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0___boxed(lean_object* v_00_u03b1_3725_, lean_object* v_x_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_){
_start:
{
lean_object* v_res_3732_; 
v_res_3732_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0(v_00_u03b1_3725_, v_x_3726_, v___y_3727_, v___y_3728_, v___y_3729_, v___y_3730_);
lean_dec(v___y_3730_);
lean_dec_ref(v___y_3729_);
lean_dec(v___y_3728_);
lean_dec_ref(v___y_3727_);
return v_res_3732_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg(lean_object* v_ref_3733_){
_start:
{
lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; 
v___x_3735_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5);
v___x_3736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3736_, 0, v_ref_3733_);
lean_ctor_set(v___x_3736_, 1, v___x_3735_);
v___x_3737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3737_, 0, v___x_3736_);
return v___x_3737_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg___boxed(lean_object* v_ref_3738_, lean_object* v___y_3739_){
_start:
{
lean_object* v_res_3740_; 
v_res_3740_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg(v_ref_3738_);
return v_res_3740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg(lean_object* v_x_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_){
_start:
{
lean_object* v___y_3749_; lean_object* v_toCold_3758_; lean_object* v_options_3759_; lean_object* v_currRecDepth_3760_; lean_object* v_maxRecDepth_3761_; lean_object* v_ref_3762_; lean_object* v_currNamespace_3763_; lean_object* v_openDecls_3764_; lean_object* v_initHeartbeats_3765_; lean_object* v_maxHeartbeats_3766_; lean_object* v_currMacroScope_3767_; uint8_t v_diag_3768_; uint8_t v_suppressElabErrors_3769_; lean_object* v___x_3775_; uint8_t v___x_3776_; 
v_toCold_3758_ = lean_ctor_get(v___y_3745_, 0);
v_options_3759_ = lean_ctor_get(v___y_3745_, 1);
v_currRecDepth_3760_ = lean_ctor_get(v___y_3745_, 2);
v_maxRecDepth_3761_ = lean_ctor_get(v___y_3745_, 3);
v_ref_3762_ = lean_ctor_get(v___y_3745_, 4);
v_currNamespace_3763_ = lean_ctor_get(v___y_3745_, 5);
v_openDecls_3764_ = lean_ctor_get(v___y_3745_, 6);
v_initHeartbeats_3765_ = lean_ctor_get(v___y_3745_, 7);
v_maxHeartbeats_3766_ = lean_ctor_get(v___y_3745_, 8);
v_currMacroScope_3767_ = lean_ctor_get(v___y_3745_, 9);
v_diag_3768_ = lean_ctor_get_uint8(v___y_3745_, sizeof(void*)*10);
v_suppressElabErrors_3769_ = lean_ctor_get_uint8(v___y_3745_, sizeof(void*)*10 + 1);
v___x_3775_ = lean_unsigned_to_nat(0u);
v___x_3776_ = lean_nat_dec_eq(v_maxRecDepth_3761_, v___x_3775_);
if (v___x_3776_ == 0)
{
uint8_t v___x_3777_; 
v___x_3777_ = lean_nat_dec_eq(v_currRecDepth_3760_, v_maxRecDepth_3761_);
if (v___x_3777_ == 0)
{
goto v___jp_3770_;
}
else
{
lean_object* v___x_3778_; 
lean_dec_ref(v_x_3741_);
lean_inc(v_ref_3762_);
v___x_3778_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg(v_ref_3762_);
v___y_3749_ = v___x_3778_;
goto v___jp_3748_;
}
}
else
{
goto v___jp_3770_;
}
v___jp_3748_:
{
if (lean_obj_tag(v___y_3749_) == 0)
{
return v___y_3749_;
}
else
{
lean_object* v_a_3750_; lean_object* v___x_3752_; uint8_t v_isShared_3753_; uint8_t v_isSharedCheck_3757_; 
v_a_3750_ = lean_ctor_get(v___y_3749_, 0);
v_isSharedCheck_3757_ = !lean_is_exclusive(v___y_3749_);
if (v_isSharedCheck_3757_ == 0)
{
v___x_3752_ = v___y_3749_;
v_isShared_3753_ = v_isSharedCheck_3757_;
goto v_resetjp_3751_;
}
else
{
lean_inc(v_a_3750_);
lean_dec(v___y_3749_);
v___x_3752_ = lean_box(0);
v_isShared_3753_ = v_isSharedCheck_3757_;
goto v_resetjp_3751_;
}
v_resetjp_3751_:
{
lean_object* v___x_3755_; 
if (v_isShared_3753_ == 0)
{
v___x_3755_ = v___x_3752_;
goto v_reusejp_3754_;
}
else
{
lean_object* v_reuseFailAlloc_3756_; 
v_reuseFailAlloc_3756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3756_, 0, v_a_3750_);
v___x_3755_ = v_reuseFailAlloc_3756_;
goto v_reusejp_3754_;
}
v_reusejp_3754_:
{
return v___x_3755_;
}
}
}
}
v___jp_3770_:
{
lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; 
v___x_3771_ = lean_unsigned_to_nat(1u);
v___x_3772_ = lean_nat_add(v_currRecDepth_3760_, v___x_3771_);
lean_inc(v_currMacroScope_3767_);
lean_inc(v_maxHeartbeats_3766_);
lean_inc(v_initHeartbeats_3765_);
lean_inc(v_openDecls_3764_);
lean_inc(v_currNamespace_3763_);
lean_inc(v_ref_3762_);
lean_inc(v_maxRecDepth_3761_);
lean_inc_ref(v_options_3759_);
lean_inc_ref(v_toCold_3758_);
v___x_3773_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_3773_, 0, v_toCold_3758_);
lean_ctor_set(v___x_3773_, 1, v_options_3759_);
lean_ctor_set(v___x_3773_, 2, v___x_3772_);
lean_ctor_set(v___x_3773_, 3, v_maxRecDepth_3761_);
lean_ctor_set(v___x_3773_, 4, v_ref_3762_);
lean_ctor_set(v___x_3773_, 5, v_currNamespace_3763_);
lean_ctor_set(v___x_3773_, 6, v_openDecls_3764_);
lean_ctor_set(v___x_3773_, 7, v_initHeartbeats_3765_);
lean_ctor_set(v___x_3773_, 8, v_maxHeartbeats_3766_);
lean_ctor_set(v___x_3773_, 9, v_currMacroScope_3767_);
lean_ctor_set_uint8(v___x_3773_, sizeof(void*)*10, v_diag_3768_);
lean_ctor_set_uint8(v___x_3773_, sizeof(void*)*10 + 1, v_suppressElabErrors_3769_);
lean_inc(v___y_3746_);
lean_inc(v___y_3744_);
lean_inc_ref(v___y_3743_);
lean_inc(v___y_3742_);
v___x_3774_ = lean_apply_6(v_x_3741_, v___y_3742_, v___y_3743_, v___y_3744_, v___x_3773_, v___y_3746_, lean_box(0));
v___y_3749_ = v___x_3774_;
goto v___jp_3748_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg___boxed(lean_object* v_x_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_){
_start:
{
lean_object* v_res_3786_; 
v_res_3786_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg(v_x_3779_, v___y_3780_, v___y_3781_, v___y_3782_, v___y_3783_, v___y_3784_);
lean_dec(v___y_3784_);
lean_dec_ref(v___y_3783_);
lean_dec(v___y_3782_);
lean_dec_ref(v___y_3781_);
lean_dec(v___y_3780_);
return v_res_3786_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___lam__0(lean_object* v_fvars_3787_, lean_object* v_pre_3788_, lean_object* v_post_3789_, uint8_t v_usedLetOnly_3790_, uint8_t v_skipConstInApp_3791_, uint8_t v_skipInstances_3792_, lean_object* v_body_3793_, lean_object* v_x_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_){
_start:
{
lean_object* v___x_3801_; lean_object* v___x_3802_; 
v___x_3801_ = lean_array_push(v_fvars_3787_, v_x_3794_);
v___x_3802_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6(v_pre_3788_, v_post_3789_, v_usedLetOnly_3790_, v_skipConstInApp_3791_, v_skipInstances_3792_, v___x_3801_, v_body_3793_, v___y_3795_, v___y_3796_, v___y_3797_, v___y_3798_, v___y_3799_);
return v___x_3802_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___lam__0___boxed(lean_object* v_fvars_3803_, lean_object* v_pre_3804_, lean_object* v_post_3805_, lean_object* v_usedLetOnly_3806_, lean_object* v_skipConstInApp_3807_, lean_object* v_skipInstances_3808_, lean_object* v_body_3809_, lean_object* v_x_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_){
_start:
{
uint8_t v_usedLetOnly_boxed_3817_; uint8_t v_skipConstInApp_boxed_3818_; uint8_t v_skipInstances_boxed_3819_; lean_object* v_res_3820_; 
v_usedLetOnly_boxed_3817_ = lean_unbox(v_usedLetOnly_3806_);
v_skipConstInApp_boxed_3818_ = lean_unbox(v_skipConstInApp_3807_);
v_skipInstances_boxed_3819_ = lean_unbox(v_skipInstances_3808_);
v_res_3820_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___lam__0(v_fvars_3803_, v_pre_3804_, v_post_3805_, v_usedLetOnly_boxed_3817_, v_skipConstInApp_boxed_3818_, v_skipInstances_boxed_3819_, v_body_3809_, v_x_3810_, v___y_3811_, v___y_3812_, v___y_3813_, v___y_3814_, v___y_3815_);
lean_dec(v___y_3815_);
lean_dec_ref(v___y_3814_);
lean_dec(v___y_3813_);
lean_dec_ref(v___y_3812_);
lean_dec(v___y_3811_);
return v_res_3820_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(lean_object* v_pre_3821_, lean_object* v_post_3822_, uint8_t v_usedLetOnly_3823_, uint8_t v_skipConstInApp_3824_, uint8_t v_skipInstances_3825_, lean_object* v_e_3826_, lean_object* v_a_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_){
_start:
{
lean_object* v___x_3833_; 
lean_inc_ref(v_post_3822_);
lean_inc(v___y_3831_);
lean_inc_ref(v___y_3830_);
lean_inc(v___y_3829_);
lean_inc_ref(v___y_3828_);
lean_inc_ref(v_e_3826_);
v___x_3833_ = lean_apply_6(v_post_3822_, v_e_3826_, v___y_3828_, v___y_3829_, v___y_3830_, v___y_3831_, lean_box(0));
if (lean_obj_tag(v___x_3833_) == 0)
{
lean_object* v_a_3834_; lean_object* v___x_3836_; uint8_t v_isShared_3837_; uint8_t v_isSharedCheck_3852_; 
v_a_3834_ = lean_ctor_get(v___x_3833_, 0);
v_isSharedCheck_3852_ = !lean_is_exclusive(v___x_3833_);
if (v_isSharedCheck_3852_ == 0)
{
v___x_3836_ = v___x_3833_;
v_isShared_3837_ = v_isSharedCheck_3852_;
goto v_resetjp_3835_;
}
else
{
lean_inc(v_a_3834_);
lean_dec(v___x_3833_);
v___x_3836_ = lean_box(0);
v_isShared_3837_ = v_isSharedCheck_3852_;
goto v_resetjp_3835_;
}
v_resetjp_3835_:
{
switch(lean_obj_tag(v_a_3834_))
{
case 0:
{
lean_object* v_e_3838_; lean_object* v___x_3840_; 
lean_dec_ref(v_e_3826_);
lean_dec_ref(v_post_3822_);
lean_dec_ref(v_pre_3821_);
v_e_3838_ = lean_ctor_get(v_a_3834_, 0);
lean_inc_ref(v_e_3838_);
lean_dec_ref_known(v_a_3834_, 1);
if (v_isShared_3837_ == 0)
{
lean_ctor_set(v___x_3836_, 0, v_e_3838_);
v___x_3840_ = v___x_3836_;
goto v_reusejp_3839_;
}
else
{
lean_object* v_reuseFailAlloc_3841_; 
v_reuseFailAlloc_3841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3841_, 0, v_e_3838_);
v___x_3840_ = v_reuseFailAlloc_3841_;
goto v_reusejp_3839_;
}
v_reusejp_3839_:
{
return v___x_3840_;
}
}
case 1:
{
lean_object* v_e_3842_; lean_object* v___x_3843_; 
lean_del_object(v___x_3836_);
lean_dec_ref(v_e_3826_);
v_e_3842_ = lean_ctor_get(v_a_3834_, 0);
lean_inc_ref(v_e_3842_);
lean_dec_ref_known(v_a_3834_, 1);
v___x_3843_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3821_, v_post_3822_, v_usedLetOnly_3823_, v_skipConstInApp_3824_, v_skipInstances_3825_, v_e_3842_, v_a_3827_, v___y_3828_, v___y_3829_, v___y_3830_, v___y_3831_);
return v___x_3843_;
}
default: 
{
lean_object* v_e_x3f_3844_; 
lean_dec_ref(v_post_3822_);
lean_dec_ref(v_pre_3821_);
v_e_x3f_3844_ = lean_ctor_get(v_a_3834_, 0);
lean_inc(v_e_x3f_3844_);
lean_dec_ref_known(v_a_3834_, 1);
if (lean_obj_tag(v_e_x3f_3844_) == 0)
{
lean_object* v___x_3846_; 
if (v_isShared_3837_ == 0)
{
lean_ctor_set(v___x_3836_, 0, v_e_3826_);
v___x_3846_ = v___x_3836_;
goto v_reusejp_3845_;
}
else
{
lean_object* v_reuseFailAlloc_3847_; 
v_reuseFailAlloc_3847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3847_, 0, v_e_3826_);
v___x_3846_ = v_reuseFailAlloc_3847_;
goto v_reusejp_3845_;
}
v_reusejp_3845_:
{
return v___x_3846_;
}
}
else
{
lean_object* v_val_3848_; lean_object* v___x_3850_; 
lean_dec_ref(v_e_3826_);
v_val_3848_ = lean_ctor_get(v_e_x3f_3844_, 0);
lean_inc(v_val_3848_);
lean_dec_ref_known(v_e_x3f_3844_, 1);
if (v_isShared_3837_ == 0)
{
lean_ctor_set(v___x_3836_, 0, v_val_3848_);
v___x_3850_ = v___x_3836_;
goto v_reusejp_3849_;
}
else
{
lean_object* v_reuseFailAlloc_3851_; 
v_reuseFailAlloc_3851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3851_, 0, v_val_3848_);
v___x_3850_ = v_reuseFailAlloc_3851_;
goto v_reusejp_3849_;
}
v_reusejp_3849_:
{
return v___x_3850_;
}
}
}
}
}
}
else
{
lean_object* v_a_3853_; lean_object* v___x_3855_; uint8_t v_isShared_3856_; uint8_t v_isSharedCheck_3860_; 
lean_dec_ref(v_e_3826_);
lean_dec_ref(v_post_3822_);
lean_dec_ref(v_pre_3821_);
v_a_3853_ = lean_ctor_get(v___x_3833_, 0);
v_isSharedCheck_3860_ = !lean_is_exclusive(v___x_3833_);
if (v_isSharedCheck_3860_ == 0)
{
v___x_3855_ = v___x_3833_;
v_isShared_3856_ = v_isSharedCheck_3860_;
goto v_resetjp_3854_;
}
else
{
lean_inc(v_a_3853_);
lean_dec(v___x_3833_);
v___x_3855_ = lean_box(0);
v_isShared_3856_ = v_isSharedCheck_3860_;
goto v_resetjp_3854_;
}
v_resetjp_3854_:
{
lean_object* v___x_3858_; 
if (v_isShared_3856_ == 0)
{
v___x_3858_ = v___x_3855_;
goto v_reusejp_3857_;
}
else
{
lean_object* v_reuseFailAlloc_3859_; 
v_reuseFailAlloc_3859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3859_, 0, v_a_3853_);
v___x_3858_ = v_reuseFailAlloc_3859_;
goto v_reusejp_3857_;
}
v_reusejp_3857_:
{
return v___x_3858_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6(lean_object* v_pre_3861_, lean_object* v_post_3862_, uint8_t v_usedLetOnly_3863_, uint8_t v_skipConstInApp_3864_, uint8_t v_skipInstances_3865_, lean_object* v_fvars_3866_, lean_object* v_e_3867_, lean_object* v_a_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_){
_start:
{
if (lean_obj_tag(v_e_3867_) == 6)
{
lean_object* v_binderName_3874_; lean_object* v_binderType_3875_; lean_object* v_body_3876_; uint8_t v_binderInfo_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; 
v_binderName_3874_ = lean_ctor_get(v_e_3867_, 0);
lean_inc(v_binderName_3874_);
v_binderType_3875_ = lean_ctor_get(v_e_3867_, 1);
lean_inc_ref(v_binderType_3875_);
v_body_3876_ = lean_ctor_get(v_e_3867_, 2);
lean_inc_ref(v_body_3876_);
v_binderInfo_3877_ = lean_ctor_get_uint8(v_e_3867_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_3867_, 3);
v___x_3878_ = lean_expr_instantiate_rev(v_binderType_3875_, v_fvars_3866_);
lean_dec_ref(v_binderType_3875_);
lean_inc_ref(v_post_3862_);
lean_inc_ref(v_pre_3861_);
v___x_3879_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3861_, v_post_3862_, v_usedLetOnly_3863_, v_skipConstInApp_3864_, v_skipInstances_3865_, v___x_3878_, v_a_3868_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_);
if (lean_obj_tag(v___x_3879_) == 0)
{
lean_object* v_a_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___f_3884_; uint8_t v___x_3885_; lean_object* v___x_3886_; 
v_a_3880_ = lean_ctor_get(v___x_3879_, 0);
lean_inc(v_a_3880_);
lean_dec_ref_known(v___x_3879_, 1);
v___x_3881_ = lean_box(v_usedLetOnly_3863_);
v___x_3882_ = lean_box(v_skipConstInApp_3864_);
v___x_3883_ = lean_box(v_skipInstances_3865_);
v___f_3884_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___lam__0___boxed), 14, 7);
lean_closure_set(v___f_3884_, 0, v_fvars_3866_);
lean_closure_set(v___f_3884_, 1, v_pre_3861_);
lean_closure_set(v___f_3884_, 2, v_post_3862_);
lean_closure_set(v___f_3884_, 3, v___x_3881_);
lean_closure_set(v___f_3884_, 4, v___x_3882_);
lean_closure_set(v___f_3884_, 5, v___x_3883_);
lean_closure_set(v___f_3884_, 6, v_body_3876_);
v___x_3885_ = 0;
v___x_3886_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_binderName_3874_, v_binderInfo_3877_, v_a_3880_, v___f_3884_, v___x_3885_, v_a_3868_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_);
return v___x_3886_;
}
else
{
lean_dec_ref(v_body_3876_);
lean_dec(v_binderName_3874_);
lean_dec_ref(v_fvars_3866_);
lean_dec_ref(v_post_3862_);
lean_dec_ref(v_pre_3861_);
return v___x_3879_;
}
}
else
{
lean_object* v___x_3887_; lean_object* v___x_3888_; 
v___x_3887_ = lean_expr_instantiate_rev(v_e_3867_, v_fvars_3866_);
lean_dec_ref(v_e_3867_);
lean_inc_ref(v_post_3862_);
lean_inc_ref(v_pre_3861_);
v___x_3888_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3861_, v_post_3862_, v_usedLetOnly_3863_, v_skipConstInApp_3864_, v_skipInstances_3865_, v___x_3887_, v_a_3868_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_);
if (lean_obj_tag(v___x_3888_) == 0)
{
lean_object* v_a_3889_; uint8_t v___x_3890_; uint8_t v___x_3891_; uint8_t v___x_3892_; lean_object* v___x_3893_; 
v_a_3889_ = lean_ctor_get(v___x_3888_, 0);
lean_inc(v_a_3889_);
lean_dec_ref_known(v___x_3888_, 1);
v___x_3890_ = 0;
v___x_3891_ = 1;
v___x_3892_ = 1;
v___x_3893_ = l_Lean_Meta_mkLambdaFVars(v_fvars_3866_, v_a_3889_, v___x_3890_, v_usedLetOnly_3863_, v___x_3890_, v___x_3891_, v___x_3892_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_);
lean_dec_ref(v_fvars_3866_);
if (lean_obj_tag(v___x_3893_) == 0)
{
lean_object* v_a_3894_; lean_object* v___x_3895_; 
v_a_3894_ = lean_ctor_get(v___x_3893_, 0);
lean_inc(v_a_3894_);
lean_dec_ref_known(v___x_3893_, 1);
v___x_3895_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_3861_, v_post_3862_, v_usedLetOnly_3863_, v_skipConstInApp_3864_, v_skipInstances_3865_, v_a_3894_, v_a_3868_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_);
return v___x_3895_;
}
else
{
lean_dec_ref(v_post_3862_);
lean_dec_ref(v_pre_3861_);
return v___x_3893_;
}
}
else
{
lean_dec_ref(v_fvars_3866_);
lean_dec_ref(v_post_3862_);
lean_dec_ref(v_pre_3861_);
return v___x_3888_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___lam__0(lean_object* v_fvars_3896_, lean_object* v_pre_3897_, lean_object* v_post_3898_, uint8_t v_usedLetOnly_3899_, uint8_t v_skipConstInApp_3900_, uint8_t v_skipInstances_3901_, lean_object* v_body_3902_, lean_object* v_x_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_){
_start:
{
lean_object* v___x_3910_; lean_object* v___x_3911_; 
v___x_3910_ = lean_array_push(v_fvars_3896_, v_x_3903_);
v___x_3911_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7(v_pre_3897_, v_post_3898_, v_usedLetOnly_3899_, v_skipConstInApp_3900_, v_skipInstances_3901_, v___x_3910_, v_body_3902_, v___y_3904_, v___y_3905_, v___y_3906_, v___y_3907_, v___y_3908_);
return v___x_3911_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___lam__0___boxed(lean_object* v_fvars_3912_, lean_object* v_pre_3913_, lean_object* v_post_3914_, lean_object* v_usedLetOnly_3915_, lean_object* v_skipConstInApp_3916_, lean_object* v_skipInstances_3917_, lean_object* v_body_3918_, lean_object* v_x_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_){
_start:
{
uint8_t v_usedLetOnly_boxed_3926_; uint8_t v_skipConstInApp_boxed_3927_; uint8_t v_skipInstances_boxed_3928_; lean_object* v_res_3929_; 
v_usedLetOnly_boxed_3926_ = lean_unbox(v_usedLetOnly_3915_);
v_skipConstInApp_boxed_3927_ = lean_unbox(v_skipConstInApp_3916_);
v_skipInstances_boxed_3928_ = lean_unbox(v_skipInstances_3917_);
v_res_3929_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___lam__0(v_fvars_3912_, v_pre_3913_, v_post_3914_, v_usedLetOnly_boxed_3926_, v_skipConstInApp_boxed_3927_, v_skipInstances_boxed_3928_, v_body_3918_, v_x_3919_, v___y_3920_, v___y_3921_, v___y_3922_, v___y_3923_, v___y_3924_);
lean_dec(v___y_3924_);
lean_dec_ref(v___y_3923_);
lean_dec(v___y_3922_);
lean_dec_ref(v___y_3921_);
lean_dec(v___y_3920_);
return v_res_3929_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7(lean_object* v_pre_3930_, lean_object* v_post_3931_, uint8_t v_usedLetOnly_3932_, uint8_t v_skipConstInApp_3933_, uint8_t v_skipInstances_3934_, lean_object* v_fvars_3935_, lean_object* v_e_3936_, lean_object* v_a_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_){
_start:
{
if (lean_obj_tag(v_e_3936_) == 8)
{
lean_object* v_declName_3943_; lean_object* v_type_3944_; lean_object* v_value_3945_; lean_object* v_body_3946_; uint8_t v_nondep_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; 
v_declName_3943_ = lean_ctor_get(v_e_3936_, 0);
lean_inc(v_declName_3943_);
v_type_3944_ = lean_ctor_get(v_e_3936_, 1);
lean_inc_ref(v_type_3944_);
v_value_3945_ = lean_ctor_get(v_e_3936_, 2);
lean_inc_ref(v_value_3945_);
v_body_3946_ = lean_ctor_get(v_e_3936_, 3);
lean_inc_ref(v_body_3946_);
v_nondep_3947_ = lean_ctor_get_uint8(v_e_3936_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_3936_, 4);
v___x_3948_ = lean_expr_instantiate_rev(v_type_3944_, v_fvars_3935_);
lean_dec_ref(v_type_3944_);
lean_inc_ref(v_post_3931_);
lean_inc_ref(v_pre_3930_);
v___x_3949_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3930_, v_post_3931_, v_usedLetOnly_3932_, v_skipConstInApp_3933_, v_skipInstances_3934_, v___x_3948_, v_a_3937_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_);
if (lean_obj_tag(v___x_3949_) == 0)
{
lean_object* v_a_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; 
v_a_3950_ = lean_ctor_get(v___x_3949_, 0);
lean_inc(v_a_3950_);
lean_dec_ref_known(v___x_3949_, 1);
v___x_3951_ = lean_expr_instantiate_rev(v_value_3945_, v_fvars_3935_);
lean_dec_ref(v_value_3945_);
lean_inc_ref(v_post_3931_);
lean_inc_ref(v_pre_3930_);
v___x_3952_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3930_, v_post_3931_, v_usedLetOnly_3932_, v_skipConstInApp_3933_, v_skipInstances_3934_, v___x_3951_, v_a_3937_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_);
if (lean_obj_tag(v___x_3952_) == 0)
{
lean_object* v_a_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___f_3957_; uint8_t v___x_3958_; lean_object* v___x_3959_; 
v_a_3953_ = lean_ctor_get(v___x_3952_, 0);
lean_inc(v_a_3953_);
lean_dec_ref_known(v___x_3952_, 1);
v___x_3954_ = lean_box(v_usedLetOnly_3932_);
v___x_3955_ = lean_box(v_skipConstInApp_3933_);
v___x_3956_ = lean_box(v_skipInstances_3934_);
v___f_3957_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___lam__0___boxed), 14, 7);
lean_closure_set(v___f_3957_, 0, v_fvars_3935_);
lean_closure_set(v___f_3957_, 1, v_pre_3930_);
lean_closure_set(v___f_3957_, 2, v_post_3931_);
lean_closure_set(v___f_3957_, 3, v___x_3954_);
lean_closure_set(v___f_3957_, 4, v___x_3955_);
lean_closure_set(v___f_3957_, 5, v___x_3956_);
lean_closure_set(v___f_3957_, 6, v_body_3946_);
v___x_3958_ = 0;
v___x_3959_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg(v_declName_3943_, v_a_3950_, v_a_3953_, v___f_3957_, v_nondep_3947_, v___x_3958_, v_a_3937_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_);
return v___x_3959_;
}
else
{
lean_dec(v_a_3950_);
lean_dec_ref(v_body_3946_);
lean_dec(v_declName_3943_);
lean_dec_ref(v_fvars_3935_);
lean_dec_ref(v_post_3931_);
lean_dec_ref(v_pre_3930_);
return v___x_3952_;
}
}
else
{
lean_dec_ref(v_body_3946_);
lean_dec_ref(v_value_3945_);
lean_dec(v_declName_3943_);
lean_dec_ref(v_fvars_3935_);
lean_dec_ref(v_post_3931_);
lean_dec_ref(v_pre_3930_);
return v___x_3949_;
}
}
else
{
lean_object* v___x_3960_; lean_object* v___x_3961_; 
v___x_3960_ = lean_expr_instantiate_rev(v_e_3936_, v_fvars_3935_);
lean_dec_ref(v_e_3936_);
lean_inc_ref(v_post_3931_);
lean_inc_ref(v_pre_3930_);
v___x_3961_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3930_, v_post_3931_, v_usedLetOnly_3932_, v_skipConstInApp_3933_, v_skipInstances_3934_, v___x_3960_, v_a_3937_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_);
if (lean_obj_tag(v___x_3961_) == 0)
{
lean_object* v_a_3962_; uint8_t v___x_3963_; uint8_t v___x_3964_; lean_object* v___x_3965_; 
v_a_3962_ = lean_ctor_get(v___x_3961_, 0);
lean_inc(v_a_3962_);
lean_dec_ref_known(v___x_3961_, 1);
v___x_3963_ = 0;
v___x_3964_ = 1;
v___x_3965_ = l_Lean_Meta_mkLetFVars(v_fvars_3935_, v_a_3962_, v_usedLetOnly_3932_, v___x_3963_, v___x_3964_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_);
lean_dec_ref(v_fvars_3935_);
if (lean_obj_tag(v___x_3965_) == 0)
{
lean_object* v_a_3966_; lean_object* v___x_3967_; 
v_a_3966_ = lean_ctor_get(v___x_3965_, 0);
lean_inc(v_a_3966_);
lean_dec_ref_known(v___x_3965_, 1);
v___x_3967_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_3930_, v_post_3931_, v_usedLetOnly_3932_, v_skipConstInApp_3933_, v_skipInstances_3934_, v_a_3966_, v_a_3937_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_);
return v___x_3967_;
}
else
{
lean_dec_ref(v_post_3931_);
lean_dec_ref(v_pre_3930_);
return v___x_3965_;
}
}
else
{
lean_dec_ref(v_fvars_3935_);
lean_dec_ref(v_post_3931_);
lean_dec_ref(v_pre_3930_);
return v___x_3961_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__2(lean_object* v_pre_3968_, lean_object* v_post_3969_, uint8_t v_usedLetOnly_3970_, uint8_t v_skipConstInApp_3971_, uint8_t v_skipInstances_3972_, size_t v_sz_3973_, size_t v_i_3974_, lean_object* v_bs_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_){
_start:
{
uint8_t v___x_3982_; 
v___x_3982_ = lean_usize_dec_lt(v_i_3974_, v_sz_3973_);
if (v___x_3982_ == 0)
{
lean_object* v___x_3983_; 
lean_dec_ref(v_post_3969_);
lean_dec_ref(v_pre_3968_);
v___x_3983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3983_, 0, v_bs_3975_);
return v___x_3983_;
}
else
{
lean_object* v_v_3984_; lean_object* v___x_3985_; 
v_v_3984_ = lean_array_uget_borrowed(v_bs_3975_, v_i_3974_);
lean_inc(v_v_3984_);
lean_inc_ref(v_post_3969_);
lean_inc_ref(v_pre_3968_);
v___x_3985_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3968_, v_post_3969_, v_usedLetOnly_3970_, v_skipConstInApp_3971_, v_skipInstances_3972_, v_v_3984_, v___y_3976_, v___y_3977_, v___y_3978_, v___y_3979_, v___y_3980_);
if (lean_obj_tag(v___x_3985_) == 0)
{
lean_object* v_a_3986_; lean_object* v___x_3987_; lean_object* v_bs_x27_3988_; size_t v___x_3989_; size_t v___x_3990_; lean_object* v___x_3991_; 
v_a_3986_ = lean_ctor_get(v___x_3985_, 0);
lean_inc(v_a_3986_);
lean_dec_ref_known(v___x_3985_, 1);
v___x_3987_ = lean_unsigned_to_nat(0u);
v_bs_x27_3988_ = lean_array_uset(v_bs_3975_, v_i_3974_, v___x_3987_);
v___x_3989_ = ((size_t)1ULL);
v___x_3990_ = lean_usize_add(v_i_3974_, v___x_3989_);
v___x_3991_ = lean_array_uset(v_bs_x27_3988_, v_i_3974_, v_a_3986_);
v_i_3974_ = v___x_3990_;
v_bs_3975_ = v___x_3991_;
goto _start;
}
else
{
lean_object* v_a_3993_; lean_object* v___x_3995_; uint8_t v_isShared_3996_; uint8_t v_isSharedCheck_4000_; 
lean_dec_ref(v_bs_3975_);
lean_dec_ref(v_post_3969_);
lean_dec_ref(v_pre_3968_);
v_a_3993_ = lean_ctor_get(v___x_3985_, 0);
v_isSharedCheck_4000_ = !lean_is_exclusive(v___x_3985_);
if (v_isSharedCheck_4000_ == 0)
{
v___x_3995_ = v___x_3985_;
v_isShared_3996_ = v_isSharedCheck_4000_;
goto v_resetjp_3994_;
}
else
{
lean_inc(v_a_3993_);
lean_dec(v___x_3985_);
v___x_3995_ = lean_box(0);
v_isShared_3996_ = v_isSharedCheck_4000_;
goto v_resetjp_3994_;
}
v_resetjp_3994_:
{
lean_object* v___x_3998_; 
if (v_isShared_3996_ == 0)
{
v___x_3998_ = v___x_3995_;
goto v_reusejp_3997_;
}
else
{
lean_object* v_reuseFailAlloc_3999_; 
v_reuseFailAlloc_3999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3999_, 0, v_a_3993_);
v___x_3998_ = v_reuseFailAlloc_3999_;
goto v_reusejp_3997_;
}
v_reusejp_3997_:
{
return v___x_3998_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0(lean_object* v_pre_4001_, lean_object* v_post_4002_, uint8_t v_usedLetOnly_4003_, uint8_t v_skipConstInApp_4004_, uint8_t v_skipInstances_4005_, lean_object* v___x_4006_, lean_object* v___y_4007_, lean_object* v_b_4008_, lean_object* v_a_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_){
_start:
{
lean_object* v___x_4015_; 
v___x_4015_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4001_, v_post_4002_, v_usedLetOnly_4003_, v_skipConstInApp_4004_, v_skipInstances_4005_, v___x_4006_, v___y_4007_, v___y_4010_, v___y_4011_, v___y_4012_, v___y_4013_);
if (lean_obj_tag(v___x_4015_) == 0)
{
lean_object* v_a_4016_; lean_object* v___x_4018_; uint8_t v_isShared_4019_; uint8_t v_isSharedCheck_4025_; 
v_a_4016_ = lean_ctor_get(v___x_4015_, 0);
v_isSharedCheck_4025_ = !lean_is_exclusive(v___x_4015_);
if (v_isSharedCheck_4025_ == 0)
{
v___x_4018_ = v___x_4015_;
v_isShared_4019_ = v_isSharedCheck_4025_;
goto v_resetjp_4017_;
}
else
{
lean_inc(v_a_4016_);
lean_dec(v___x_4015_);
v___x_4018_ = lean_box(0);
v_isShared_4019_ = v_isSharedCheck_4025_;
goto v_resetjp_4017_;
}
v_resetjp_4017_:
{
lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4023_; 
v___x_4020_ = lean_array_fset(v_b_4008_, v_a_4009_, v_a_4016_);
v___x_4021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4021_, 0, v___x_4020_);
if (v_isShared_4019_ == 0)
{
lean_ctor_set(v___x_4018_, 0, v___x_4021_);
v___x_4023_ = v___x_4018_;
goto v_reusejp_4022_;
}
else
{
lean_object* v_reuseFailAlloc_4024_; 
v_reuseFailAlloc_4024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4024_, 0, v___x_4021_);
v___x_4023_ = v_reuseFailAlloc_4024_;
goto v_reusejp_4022_;
}
v_reusejp_4022_:
{
return v___x_4023_;
}
}
}
else
{
lean_object* v_a_4026_; lean_object* v___x_4028_; uint8_t v_isShared_4029_; uint8_t v_isSharedCheck_4033_; 
lean_dec_ref(v_b_4008_);
v_a_4026_ = lean_ctor_get(v___x_4015_, 0);
v_isSharedCheck_4033_ = !lean_is_exclusive(v___x_4015_);
if (v_isSharedCheck_4033_ == 0)
{
v___x_4028_ = v___x_4015_;
v_isShared_4029_ = v_isSharedCheck_4033_;
goto v_resetjp_4027_;
}
else
{
lean_inc(v_a_4026_);
lean_dec(v___x_4015_);
v___x_4028_ = lean_box(0);
v_isShared_4029_ = v_isSharedCheck_4033_;
goto v_resetjp_4027_;
}
v_resetjp_4027_:
{
lean_object* v___x_4031_; 
if (v_isShared_4029_ == 0)
{
v___x_4031_ = v___x_4028_;
goto v_reusejp_4030_;
}
else
{
lean_object* v_reuseFailAlloc_4032_; 
v_reuseFailAlloc_4032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4032_, 0, v_a_4026_);
v___x_4031_ = v_reuseFailAlloc_4032_;
goto v_reusejp_4030_;
}
v_reusejp_4030_:
{
return v___x_4031_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed(lean_object* v_pre_4034_, lean_object* v_post_4035_, lean_object* v_usedLetOnly_4036_, lean_object* v_skipConstInApp_4037_, lean_object* v_skipInstances_4038_, lean_object* v___x_4039_, lean_object* v___y_4040_, lean_object* v_b_4041_, lean_object* v_a_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_){
_start:
{
uint8_t v_usedLetOnly_boxed_4048_; uint8_t v_skipConstInApp_boxed_4049_; uint8_t v_skipInstances_boxed_4050_; lean_object* v_res_4051_; 
v_usedLetOnly_boxed_4048_ = lean_unbox(v_usedLetOnly_4036_);
v_skipConstInApp_boxed_4049_ = lean_unbox(v_skipConstInApp_4037_);
v_skipInstances_boxed_4050_ = lean_unbox(v_skipInstances_4038_);
v_res_4051_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0(v_pre_4034_, v_post_4035_, v_usedLetOnly_boxed_4048_, v_skipConstInApp_boxed_4049_, v_skipInstances_boxed_4050_, v___x_4039_, v___y_4040_, v_b_4041_, v_a_4042_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_);
lean_dec(v___y_4046_);
lean_dec_ref(v___y_4045_);
lean_dec(v___y_4044_);
lean_dec_ref(v___y_4043_);
lean_dec(v_a_4042_);
lean_dec(v___y_4040_);
return v_res_4051_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg(lean_object* v_upperBound_4052_, lean_object* v___x_4053_, lean_object* v_pre_4054_, lean_object* v_post_4055_, uint8_t v_usedLetOnly_4056_, uint8_t v_skipConstInApp_4057_, uint8_t v_skipInstances_4058_, lean_object* v_a_4059_, lean_object* v_b_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_){
_start:
{
lean_object* v___y_4068_; uint8_t v___x_4091_; 
v___x_4091_ = lean_nat_dec_lt(v_a_4059_, v_upperBound_4052_);
if (v___x_4091_ == 0)
{
lean_object* v___x_4092_; 
lean_dec(v_a_4059_);
lean_dec_ref(v_post_4055_);
lean_dec_ref(v_pre_4054_);
v___x_4092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4092_, 0, v_b_4060_);
return v___x_4092_;
}
else
{
lean_object* v___x_4093_; lean_object* v___x_4094_; uint8_t v___x_4095_; 
v___x_4093_ = lean_array_fget_borrowed(v_b_4060_, v_a_4059_);
v___x_4094_ = lean_array_get_size(v___x_4053_);
v___x_4095_ = lean_nat_dec_lt(v_a_4059_, v___x_4094_);
if (v___x_4095_ == 0)
{
lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___f_4099_; 
lean_inc(v___x_4093_);
v___x_4096_ = lean_box(v_usedLetOnly_4056_);
v___x_4097_ = lean_box(v_skipConstInApp_4057_);
v___x_4098_ = lean_box(v_skipInstances_4058_);
lean_inc(v_a_4059_);
lean_inc(v___y_4061_);
lean_inc_ref(v_post_4055_);
lean_inc_ref(v_pre_4054_);
v___f_4099_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_4099_, 0, v_pre_4054_);
lean_closure_set(v___f_4099_, 1, v_post_4055_);
lean_closure_set(v___f_4099_, 2, v___x_4096_);
lean_closure_set(v___f_4099_, 3, v___x_4097_);
lean_closure_set(v___f_4099_, 4, v___x_4098_);
lean_closure_set(v___f_4099_, 5, v___x_4093_);
lean_closure_set(v___f_4099_, 6, v___y_4061_);
lean_closure_set(v___f_4099_, 7, v_b_4060_);
lean_closure_set(v___f_4099_, 8, v_a_4059_);
v___y_4068_ = v___f_4099_;
goto v___jp_4067_;
}
else
{
lean_object* v___x_4100_; uint8_t v_isInstance_4101_; 
v___x_4100_ = lean_array_fget_borrowed(v___x_4053_, v_a_4059_);
v_isInstance_4101_ = lean_ctor_get_uint8(v___x_4100_, sizeof(void*)*1 + 4);
if (v_isInstance_4101_ == 0)
{
lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___f_4105_; 
lean_inc(v___x_4093_);
v___x_4102_ = lean_box(v_usedLetOnly_4056_);
v___x_4103_ = lean_box(v_skipConstInApp_4057_);
v___x_4104_ = lean_box(v_skipInstances_4058_);
lean_inc(v_a_4059_);
lean_inc(v___y_4061_);
lean_inc_ref(v_post_4055_);
lean_inc_ref(v_pre_4054_);
v___f_4105_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_4105_, 0, v_pre_4054_);
lean_closure_set(v___f_4105_, 1, v_post_4055_);
lean_closure_set(v___f_4105_, 2, v___x_4102_);
lean_closure_set(v___f_4105_, 3, v___x_4103_);
lean_closure_set(v___f_4105_, 4, v___x_4104_);
lean_closure_set(v___f_4105_, 5, v___x_4093_);
lean_closure_set(v___f_4105_, 6, v___y_4061_);
lean_closure_set(v___f_4105_, 7, v_b_4060_);
lean_closure_set(v___f_4105_, 8, v_a_4059_);
v___y_4068_ = v___f_4105_;
goto v___jp_4067_;
}
else
{
lean_object* v___x_4106_; lean_object* v___f_4107_; 
v___x_4106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4106_, 0, v_b_4060_);
v___f_4107_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_4107_, 0, v___x_4106_);
v___y_4068_ = v___f_4107_;
goto v___jp_4067_;
}
}
}
v___jp_4067_:
{
lean_object* v___x_4069_; 
lean_inc(v___y_4065_);
lean_inc_ref(v___y_4064_);
lean_inc(v___y_4063_);
lean_inc_ref(v___y_4062_);
v___x_4069_ = lean_apply_5(v___y_4068_, v___y_4062_, v___y_4063_, v___y_4064_, v___y_4065_, lean_box(0));
if (lean_obj_tag(v___x_4069_) == 0)
{
lean_object* v_a_4070_; lean_object* v___x_4072_; uint8_t v_isShared_4073_; uint8_t v_isSharedCheck_4082_; 
v_a_4070_ = lean_ctor_get(v___x_4069_, 0);
v_isSharedCheck_4082_ = !lean_is_exclusive(v___x_4069_);
if (v_isSharedCheck_4082_ == 0)
{
v___x_4072_ = v___x_4069_;
v_isShared_4073_ = v_isSharedCheck_4082_;
goto v_resetjp_4071_;
}
else
{
lean_inc(v_a_4070_);
lean_dec(v___x_4069_);
v___x_4072_ = lean_box(0);
v_isShared_4073_ = v_isSharedCheck_4082_;
goto v_resetjp_4071_;
}
v_resetjp_4071_:
{
if (lean_obj_tag(v_a_4070_) == 0)
{
lean_object* v_a_4074_; lean_object* v___x_4076_; 
lean_dec(v_a_4059_);
lean_dec_ref(v_post_4055_);
lean_dec_ref(v_pre_4054_);
v_a_4074_ = lean_ctor_get(v_a_4070_, 0);
lean_inc(v_a_4074_);
lean_dec_ref_known(v_a_4070_, 1);
if (v_isShared_4073_ == 0)
{
lean_ctor_set(v___x_4072_, 0, v_a_4074_);
v___x_4076_ = v___x_4072_;
goto v_reusejp_4075_;
}
else
{
lean_object* v_reuseFailAlloc_4077_; 
v_reuseFailAlloc_4077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4077_, 0, v_a_4074_);
v___x_4076_ = v_reuseFailAlloc_4077_;
goto v_reusejp_4075_;
}
v_reusejp_4075_:
{
return v___x_4076_;
}
}
else
{
lean_object* v_a_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; 
lean_del_object(v___x_4072_);
v_a_4078_ = lean_ctor_get(v_a_4070_, 0);
lean_inc(v_a_4078_);
lean_dec_ref_known(v_a_4070_, 1);
v___x_4079_ = lean_unsigned_to_nat(1u);
v___x_4080_ = lean_nat_add(v_a_4059_, v___x_4079_);
lean_dec(v_a_4059_);
v_a_4059_ = v___x_4080_;
v_b_4060_ = v_a_4078_;
goto _start;
}
}
}
else
{
lean_object* v_a_4083_; lean_object* v___x_4085_; uint8_t v_isShared_4086_; uint8_t v_isSharedCheck_4090_; 
lean_dec(v_a_4059_);
lean_dec_ref(v_post_4055_);
lean_dec_ref(v_pre_4054_);
v_a_4083_ = lean_ctor_get(v___x_4069_, 0);
v_isSharedCheck_4090_ = !lean_is_exclusive(v___x_4069_);
if (v_isSharedCheck_4090_ == 0)
{
v___x_4085_ = v___x_4069_;
v_isShared_4086_ = v_isSharedCheck_4090_;
goto v_resetjp_4084_;
}
else
{
lean_inc(v_a_4083_);
lean_dec(v___x_4069_);
v___x_4085_ = lean_box(0);
v_isShared_4086_ = v_isSharedCheck_4090_;
goto v_resetjp_4084_;
}
v_resetjp_4084_:
{
lean_object* v___x_4088_; 
if (v_isShared_4086_ == 0)
{
v___x_4088_ = v___x_4085_;
goto v_reusejp_4087_;
}
else
{
lean_object* v_reuseFailAlloc_4089_; 
v_reuseFailAlloc_4089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4089_, 0, v_a_4083_);
v___x_4088_ = v_reuseFailAlloc_4089_;
goto v_reusejp_4087_;
}
v_reusejp_4087_:
{
return v___x_4088_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__8(uint8_t v_skipInstances_4108_, lean_object* v_pre_4109_, lean_object* v_post_4110_, uint8_t v_usedLetOnly_4111_, uint8_t v_skipConstInApp_4112_, lean_object* v_x_4113_, lean_object* v_x_4114_, lean_object* v_x_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_){
_start:
{
lean_object* v_f_4123_; lean_object* v___y_4124_; lean_object* v___y_4125_; lean_object* v___y_4126_; lean_object* v___y_4127_; lean_object* v___y_4128_; 
if (lean_obj_tag(v_x_4113_) == 5)
{
lean_object* v_fn_4171_; lean_object* v_arg_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; 
v_fn_4171_ = lean_ctor_get(v_x_4113_, 0);
lean_inc_ref(v_fn_4171_);
v_arg_4172_ = lean_ctor_get(v_x_4113_, 1);
lean_inc_ref(v_arg_4172_);
lean_dec_ref_known(v_x_4113_, 2);
v___x_4173_ = lean_array_set(v_x_4114_, v_x_4115_, v_arg_4172_);
v___x_4174_ = lean_unsigned_to_nat(1u);
v___x_4175_ = lean_nat_sub(v_x_4115_, v___x_4174_);
lean_dec(v_x_4115_);
v_x_4113_ = v_fn_4171_;
v_x_4114_ = v___x_4173_;
v_x_4115_ = v___x_4175_;
goto _start;
}
else
{
lean_dec(v_x_4115_);
if (v_skipConstInApp_4112_ == 0)
{
goto v___jp_4168_;
}
else
{
uint8_t v___x_4177_; 
v___x_4177_ = l_Lean_Expr_isConst(v_x_4113_);
if (v___x_4177_ == 0)
{
goto v___jp_4168_;
}
else
{
v_f_4123_ = v_x_4113_;
v___y_4124_ = v___y_4116_;
v___y_4125_ = v___y_4117_;
v___y_4126_ = v___y_4118_;
v___y_4127_ = v___y_4119_;
v___y_4128_ = v___y_4120_;
goto v___jp_4122_;
}
}
}
v___jp_4122_:
{
if (v_skipInstances_4108_ == 0)
{
size_t v_sz_4129_; size_t v___x_4130_; lean_object* v___x_4131_; 
v_sz_4129_ = lean_array_size(v_x_4114_);
v___x_4130_ = ((size_t)0ULL);
lean_inc_ref(v_post_4110_);
lean_inc_ref(v_pre_4109_);
v___x_4131_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__2(v_pre_4109_, v_post_4110_, v_usedLetOnly_4111_, v_skipConstInApp_4112_, v_skipInstances_4108_, v_sz_4129_, v___x_4130_, v_x_4114_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_);
if (lean_obj_tag(v___x_4131_) == 0)
{
lean_object* v_a_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; 
v_a_4132_ = lean_ctor_get(v___x_4131_, 0);
lean_inc(v_a_4132_);
lean_dec_ref_known(v___x_4131_, 1);
v___x_4133_ = l_Lean_mkAppN(v_f_4123_, v_a_4132_);
lean_dec(v_a_4132_);
v___x_4134_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4109_, v_post_4110_, v_usedLetOnly_4111_, v_skipConstInApp_4112_, v_skipInstances_4108_, v___x_4133_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_);
return v___x_4134_;
}
else
{
lean_object* v_a_4135_; lean_object* v___x_4137_; uint8_t v_isShared_4138_; uint8_t v_isSharedCheck_4142_; 
lean_dec_ref(v_f_4123_);
lean_dec_ref(v_post_4110_);
lean_dec_ref(v_pre_4109_);
v_a_4135_ = lean_ctor_get(v___x_4131_, 0);
v_isSharedCheck_4142_ = !lean_is_exclusive(v___x_4131_);
if (v_isSharedCheck_4142_ == 0)
{
v___x_4137_ = v___x_4131_;
v_isShared_4138_ = v_isSharedCheck_4142_;
goto v_resetjp_4136_;
}
else
{
lean_inc(v_a_4135_);
lean_dec(v___x_4131_);
v___x_4137_ = lean_box(0);
v_isShared_4138_ = v_isSharedCheck_4142_;
goto v_resetjp_4136_;
}
v_resetjp_4136_:
{
lean_object* v___x_4140_; 
if (v_isShared_4138_ == 0)
{
v___x_4140_ = v___x_4137_;
goto v_reusejp_4139_;
}
else
{
lean_object* v_reuseFailAlloc_4141_; 
v_reuseFailAlloc_4141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4141_, 0, v_a_4135_);
v___x_4140_ = v_reuseFailAlloc_4141_;
goto v_reusejp_4139_;
}
v_reusejp_4139_:
{
return v___x_4140_;
}
}
}
}
else
{
lean_object* v___x_4143_; lean_object* v___x_4144_; 
v___x_4143_ = lean_array_get_size(v_x_4114_);
lean_inc_ref(v_f_4123_);
v___x_4144_ = l_Lean_Meta_getFunInfoNArgs(v_f_4123_, v___x_4143_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_);
if (lean_obj_tag(v___x_4144_) == 0)
{
lean_object* v_a_4145_; lean_object* v_paramInfo_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; 
v_a_4145_ = lean_ctor_get(v___x_4144_, 0);
lean_inc(v_a_4145_);
lean_dec_ref_known(v___x_4144_, 1);
v_paramInfo_4146_ = lean_ctor_get(v_a_4145_, 0);
lean_inc_ref(v_paramInfo_4146_);
lean_dec(v_a_4145_);
v___x_4147_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_4110_);
lean_inc_ref(v_pre_4109_);
v___x_4148_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg(v___x_4143_, v_paramInfo_4146_, v_pre_4109_, v_post_4110_, v_usedLetOnly_4111_, v_skipConstInApp_4112_, v_skipInstances_4108_, v___x_4147_, v_x_4114_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_);
lean_dec_ref(v_paramInfo_4146_);
if (lean_obj_tag(v___x_4148_) == 0)
{
lean_object* v_a_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; 
v_a_4149_ = lean_ctor_get(v___x_4148_, 0);
lean_inc(v_a_4149_);
lean_dec_ref_known(v___x_4148_, 1);
v___x_4150_ = l_Lean_mkAppN(v_f_4123_, v_a_4149_);
lean_dec(v_a_4149_);
v___x_4151_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4109_, v_post_4110_, v_usedLetOnly_4111_, v_skipConstInApp_4112_, v_skipInstances_4108_, v___x_4150_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_);
return v___x_4151_;
}
else
{
lean_object* v_a_4152_; lean_object* v___x_4154_; uint8_t v_isShared_4155_; uint8_t v_isSharedCheck_4159_; 
lean_dec_ref(v_f_4123_);
lean_dec_ref(v_post_4110_);
lean_dec_ref(v_pre_4109_);
v_a_4152_ = lean_ctor_get(v___x_4148_, 0);
v_isSharedCheck_4159_ = !lean_is_exclusive(v___x_4148_);
if (v_isSharedCheck_4159_ == 0)
{
v___x_4154_ = v___x_4148_;
v_isShared_4155_ = v_isSharedCheck_4159_;
goto v_resetjp_4153_;
}
else
{
lean_inc(v_a_4152_);
lean_dec(v___x_4148_);
v___x_4154_ = lean_box(0);
v_isShared_4155_ = v_isSharedCheck_4159_;
goto v_resetjp_4153_;
}
v_resetjp_4153_:
{
lean_object* v___x_4157_; 
if (v_isShared_4155_ == 0)
{
v___x_4157_ = v___x_4154_;
goto v_reusejp_4156_;
}
else
{
lean_object* v_reuseFailAlloc_4158_; 
v_reuseFailAlloc_4158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4158_, 0, v_a_4152_);
v___x_4157_ = v_reuseFailAlloc_4158_;
goto v_reusejp_4156_;
}
v_reusejp_4156_:
{
return v___x_4157_;
}
}
}
}
else
{
lean_object* v_a_4160_; lean_object* v___x_4162_; uint8_t v_isShared_4163_; uint8_t v_isSharedCheck_4167_; 
lean_dec_ref(v_f_4123_);
lean_dec_ref(v_x_4114_);
lean_dec_ref(v_post_4110_);
lean_dec_ref(v_pre_4109_);
v_a_4160_ = lean_ctor_get(v___x_4144_, 0);
v_isSharedCheck_4167_ = !lean_is_exclusive(v___x_4144_);
if (v_isSharedCheck_4167_ == 0)
{
v___x_4162_ = v___x_4144_;
v_isShared_4163_ = v_isSharedCheck_4167_;
goto v_resetjp_4161_;
}
else
{
lean_inc(v_a_4160_);
lean_dec(v___x_4144_);
v___x_4162_ = lean_box(0);
v_isShared_4163_ = v_isSharedCheck_4167_;
goto v_resetjp_4161_;
}
v_resetjp_4161_:
{
lean_object* v___x_4165_; 
if (v_isShared_4163_ == 0)
{
v___x_4165_ = v___x_4162_;
goto v_reusejp_4164_;
}
else
{
lean_object* v_reuseFailAlloc_4166_; 
v_reuseFailAlloc_4166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4166_, 0, v_a_4160_);
v___x_4165_ = v_reuseFailAlloc_4166_;
goto v_reusejp_4164_;
}
v_reusejp_4164_:
{
return v___x_4165_;
}
}
}
}
}
v___jp_4168_:
{
lean_object* v___x_4169_; 
lean_inc_ref(v_post_4110_);
lean_inc_ref(v_pre_4109_);
v___x_4169_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4109_, v_post_4110_, v_usedLetOnly_4111_, v_skipConstInApp_4112_, v_skipInstances_4108_, v_x_4113_, v___y_4116_, v___y_4117_, v___y_4118_, v___y_4119_, v___y_4120_);
if (lean_obj_tag(v___x_4169_) == 0)
{
lean_object* v_a_4170_; 
v_a_4170_ = lean_ctor_get(v___x_4169_, 0);
lean_inc(v_a_4170_);
lean_dec_ref_known(v___x_4169_, 1);
v_f_4123_ = v_a_4170_;
v___y_4124_ = v___y_4116_;
v___y_4125_ = v___y_4117_;
v___y_4126_ = v___y_4118_;
v___y_4127_ = v___y_4119_;
v___y_4128_ = v___y_4120_;
goto v___jp_4122_;
}
else
{
lean_dec_ref(v_x_4114_);
lean_dec_ref(v_post_4110_);
lean_dec_ref(v_pre_4109_);
return v___x_4169_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1(lean_object* v___x_4178_, lean_object* v_pre_4179_, lean_object* v_e_4180_, lean_object* v_post_4181_, uint8_t v_usedLetOnly_4182_, uint8_t v_skipConstInApp_4183_, uint8_t v_skipInstances_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_){
_start:
{
lean_object* v___x_4191_; 
v___x_4191_ = l_Lean_Core_checkSystem(v___x_4178_, v___y_4188_, v___y_4189_);
if (lean_obj_tag(v___x_4191_) == 0)
{
lean_object* v___x_4192_; 
lean_dec_ref_known(v___x_4191_, 1);
lean_inc_ref(v_pre_4179_);
lean_inc(v___y_4189_);
lean_inc_ref(v___y_4188_);
lean_inc(v___y_4187_);
lean_inc_ref(v___y_4186_);
lean_inc_ref(v_e_4180_);
v___x_4192_ = lean_apply_6(v_pre_4179_, v_e_4180_, v___y_4186_, v___y_4187_, v___y_4188_, v___y_4189_, lean_box(0));
if (lean_obj_tag(v___x_4192_) == 0)
{
lean_object* v_a_4193_; lean_object* v___x_4195_; uint8_t v_isShared_4196_; uint8_t v_isSharedCheck_4241_; 
v_a_4193_ = lean_ctor_get(v___x_4192_, 0);
v_isSharedCheck_4241_ = !lean_is_exclusive(v___x_4192_);
if (v_isSharedCheck_4241_ == 0)
{
v___x_4195_ = v___x_4192_;
v_isShared_4196_ = v_isSharedCheck_4241_;
goto v_resetjp_4194_;
}
else
{
lean_inc(v_a_4193_);
lean_dec(v___x_4192_);
v___x_4195_ = lean_box(0);
v_isShared_4196_ = v_isSharedCheck_4241_;
goto v_resetjp_4194_;
}
v_resetjp_4194_:
{
lean_object* v___y_4198_; 
switch(lean_obj_tag(v_a_4193_))
{
case 0:
{
lean_object* v_e_4233_; lean_object* v___x_4235_; 
lean_dec_ref(v_post_4181_);
lean_dec_ref(v_e_4180_);
lean_dec_ref(v_pre_4179_);
v_e_4233_ = lean_ctor_get(v_a_4193_, 0);
lean_inc_ref(v_e_4233_);
lean_dec_ref_known(v_a_4193_, 1);
if (v_isShared_4196_ == 0)
{
lean_ctor_set(v___x_4195_, 0, v_e_4233_);
v___x_4235_ = v___x_4195_;
goto v_reusejp_4234_;
}
else
{
lean_object* v_reuseFailAlloc_4236_; 
v_reuseFailAlloc_4236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4236_, 0, v_e_4233_);
v___x_4235_ = v_reuseFailAlloc_4236_;
goto v_reusejp_4234_;
}
v_reusejp_4234_:
{
return v___x_4235_;
}
}
case 1:
{
lean_object* v_e_4237_; lean_object* v___x_4238_; 
lean_del_object(v___x_4195_);
lean_dec_ref(v_e_4180_);
v_e_4237_ = lean_ctor_get(v_a_4193_, 0);
lean_inc_ref(v_e_4237_);
lean_dec_ref_known(v_a_4193_, 1);
v___x_4238_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4179_, v_post_4181_, v_usedLetOnly_4182_, v_skipConstInApp_4183_, v_skipInstances_4184_, v_e_4237_, v___y_4185_, v___y_4186_, v___y_4187_, v___y_4188_, v___y_4189_);
return v___x_4238_;
}
default: 
{
lean_object* v_e_x3f_4239_; 
lean_del_object(v___x_4195_);
v_e_x3f_4239_ = lean_ctor_get(v_a_4193_, 0);
lean_inc(v_e_x3f_4239_);
lean_dec_ref_known(v_a_4193_, 1);
if (lean_obj_tag(v_e_x3f_4239_) == 0)
{
v___y_4198_ = v_e_4180_;
goto v___jp_4197_;
}
else
{
lean_object* v_val_4240_; 
lean_dec_ref(v_e_4180_);
v_val_4240_ = lean_ctor_get(v_e_x3f_4239_, 0);
lean_inc(v_val_4240_);
lean_dec_ref_known(v_e_x3f_4239_, 1);
v___y_4198_ = v_val_4240_;
goto v___jp_4197_;
}
}
}
v___jp_4197_:
{
switch(lean_obj_tag(v___y_4198_))
{
case 7:
{
lean_object* v___x_4199_; lean_object* v___x_4200_; 
v___x_4199_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_4200_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5(v_pre_4179_, v_post_4181_, v_usedLetOnly_4182_, v_skipConstInApp_4183_, v_skipInstances_4184_, v___x_4199_, v___y_4198_, v___y_4185_, v___y_4186_, v___y_4187_, v___y_4188_, v___y_4189_);
return v___x_4200_;
}
case 6:
{
lean_object* v___x_4201_; lean_object* v___x_4202_; 
v___x_4201_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_4202_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6(v_pre_4179_, v_post_4181_, v_usedLetOnly_4182_, v_skipConstInApp_4183_, v_skipInstances_4184_, v___x_4201_, v___y_4198_, v___y_4185_, v___y_4186_, v___y_4187_, v___y_4188_, v___y_4189_);
return v___x_4202_;
}
case 8:
{
lean_object* v___x_4203_; lean_object* v___x_4204_; 
v___x_4203_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_4204_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7(v_pre_4179_, v_post_4181_, v_usedLetOnly_4182_, v_skipConstInApp_4183_, v_skipInstances_4184_, v___x_4203_, v___y_4198_, v___y_4185_, v___y_4186_, v___y_4187_, v___y_4188_, v___y_4189_);
return v___x_4204_;
}
case 5:
{
lean_object* v_dummy_4205_; lean_object* v_nargs_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; 
v_dummy_4205_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_4206_ = l_Lean_Expr_getAppNumArgs(v___y_4198_);
lean_inc(v_nargs_4206_);
v___x_4207_ = lean_mk_array(v_nargs_4206_, v_dummy_4205_);
v___x_4208_ = lean_unsigned_to_nat(1u);
v___x_4209_ = lean_nat_sub(v_nargs_4206_, v___x_4208_);
lean_dec(v_nargs_4206_);
v___x_4210_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__8(v_skipInstances_4184_, v_pre_4179_, v_post_4181_, v_usedLetOnly_4182_, v_skipConstInApp_4183_, v___y_4198_, v___x_4207_, v___x_4209_, v___y_4185_, v___y_4186_, v___y_4187_, v___y_4188_, v___y_4189_);
return v___x_4210_;
}
case 10:
{
lean_object* v_data_4211_; lean_object* v_expr_4212_; lean_object* v___x_4213_; 
v_data_4211_ = lean_ctor_get(v___y_4198_, 0);
v_expr_4212_ = lean_ctor_get(v___y_4198_, 1);
lean_inc_ref(v_expr_4212_);
lean_inc_ref(v_post_4181_);
lean_inc_ref(v_pre_4179_);
v___x_4213_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4179_, v_post_4181_, v_usedLetOnly_4182_, v_skipConstInApp_4183_, v_skipInstances_4184_, v_expr_4212_, v___y_4185_, v___y_4186_, v___y_4187_, v___y_4188_, v___y_4189_);
if (lean_obj_tag(v___x_4213_) == 0)
{
lean_object* v_a_4214_; size_t v___x_4215_; size_t v___x_4216_; uint8_t v___x_4217_; 
v_a_4214_ = lean_ctor_get(v___x_4213_, 0);
lean_inc(v_a_4214_);
lean_dec_ref_known(v___x_4213_, 1);
v___x_4215_ = lean_ptr_addr(v_expr_4212_);
v___x_4216_ = lean_ptr_addr(v_a_4214_);
v___x_4217_ = lean_usize_dec_eq(v___x_4215_, v___x_4216_);
if (v___x_4217_ == 0)
{
lean_object* v___x_4218_; lean_object* v___x_4219_; 
lean_inc(v_data_4211_);
lean_dec_ref_known(v___y_4198_, 2);
v___x_4218_ = l_Lean_Expr_mdata___override(v_data_4211_, v_a_4214_);
v___x_4219_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4179_, v_post_4181_, v_usedLetOnly_4182_, v_skipConstInApp_4183_, v_skipInstances_4184_, v___x_4218_, v___y_4185_, v___y_4186_, v___y_4187_, v___y_4188_, v___y_4189_);
return v___x_4219_;
}
else
{
lean_object* v___x_4220_; 
lean_dec(v_a_4214_);
v___x_4220_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4179_, v_post_4181_, v_usedLetOnly_4182_, v_skipConstInApp_4183_, v_skipInstances_4184_, v___y_4198_, v___y_4185_, v___y_4186_, v___y_4187_, v___y_4188_, v___y_4189_);
return v___x_4220_;
}
}
else
{
lean_dec_ref_known(v___y_4198_, 2);
lean_dec_ref(v_post_4181_);
lean_dec_ref(v_pre_4179_);
return v___x_4213_;
}
}
case 11:
{
lean_object* v_typeName_4221_; lean_object* v_idx_4222_; lean_object* v_struct_4223_; lean_object* v___x_4224_; 
v_typeName_4221_ = lean_ctor_get(v___y_4198_, 0);
v_idx_4222_ = lean_ctor_get(v___y_4198_, 1);
v_struct_4223_ = lean_ctor_get(v___y_4198_, 2);
lean_inc_ref(v_struct_4223_);
lean_inc_ref(v_post_4181_);
lean_inc_ref(v_pre_4179_);
v___x_4224_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4179_, v_post_4181_, v_usedLetOnly_4182_, v_skipConstInApp_4183_, v_skipInstances_4184_, v_struct_4223_, v___y_4185_, v___y_4186_, v___y_4187_, v___y_4188_, v___y_4189_);
if (lean_obj_tag(v___x_4224_) == 0)
{
lean_object* v_a_4225_; size_t v___x_4226_; size_t v___x_4227_; uint8_t v___x_4228_; 
v_a_4225_ = lean_ctor_get(v___x_4224_, 0);
lean_inc(v_a_4225_);
lean_dec_ref_known(v___x_4224_, 1);
v___x_4226_ = lean_ptr_addr(v_struct_4223_);
v___x_4227_ = lean_ptr_addr(v_a_4225_);
v___x_4228_ = lean_usize_dec_eq(v___x_4226_, v___x_4227_);
if (v___x_4228_ == 0)
{
lean_object* v___x_4229_; lean_object* v___x_4230_; 
lean_inc(v_idx_4222_);
lean_inc(v_typeName_4221_);
lean_dec_ref_known(v___y_4198_, 3);
v___x_4229_ = l_Lean_Expr_proj___override(v_typeName_4221_, v_idx_4222_, v_a_4225_);
v___x_4230_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4179_, v_post_4181_, v_usedLetOnly_4182_, v_skipConstInApp_4183_, v_skipInstances_4184_, v___x_4229_, v___y_4185_, v___y_4186_, v___y_4187_, v___y_4188_, v___y_4189_);
return v___x_4230_;
}
else
{
lean_object* v___x_4231_; 
lean_dec(v_a_4225_);
v___x_4231_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4179_, v_post_4181_, v_usedLetOnly_4182_, v_skipConstInApp_4183_, v_skipInstances_4184_, v___y_4198_, v___y_4185_, v___y_4186_, v___y_4187_, v___y_4188_, v___y_4189_);
return v___x_4231_;
}
}
else
{
lean_dec_ref_known(v___y_4198_, 3);
lean_dec_ref(v_post_4181_);
lean_dec_ref(v_pre_4179_);
return v___x_4224_;
}
}
default: 
{
lean_object* v___x_4232_; 
v___x_4232_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4179_, v_post_4181_, v_usedLetOnly_4182_, v_skipConstInApp_4183_, v_skipInstances_4184_, v___y_4198_, v___y_4185_, v___y_4186_, v___y_4187_, v___y_4188_, v___y_4189_);
return v___x_4232_;
}
}
}
}
}
else
{
lean_object* v_a_4242_; lean_object* v___x_4244_; uint8_t v_isShared_4245_; uint8_t v_isSharedCheck_4249_; 
lean_dec_ref(v_post_4181_);
lean_dec_ref(v_e_4180_);
lean_dec_ref(v_pre_4179_);
v_a_4242_ = lean_ctor_get(v___x_4192_, 0);
v_isSharedCheck_4249_ = !lean_is_exclusive(v___x_4192_);
if (v_isSharedCheck_4249_ == 0)
{
v___x_4244_ = v___x_4192_;
v_isShared_4245_ = v_isSharedCheck_4249_;
goto v_resetjp_4243_;
}
else
{
lean_inc(v_a_4242_);
lean_dec(v___x_4192_);
v___x_4244_ = lean_box(0);
v_isShared_4245_ = v_isSharedCheck_4249_;
goto v_resetjp_4243_;
}
v_resetjp_4243_:
{
lean_object* v___x_4247_; 
if (v_isShared_4245_ == 0)
{
v___x_4247_ = v___x_4244_;
goto v_reusejp_4246_;
}
else
{
lean_object* v_reuseFailAlloc_4248_; 
v_reuseFailAlloc_4248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4248_, 0, v_a_4242_);
v___x_4247_ = v_reuseFailAlloc_4248_;
goto v_reusejp_4246_;
}
v_reusejp_4246_:
{
return v___x_4247_;
}
}
}
}
else
{
lean_object* v_a_4250_; lean_object* v___x_4252_; uint8_t v_isShared_4253_; uint8_t v_isSharedCheck_4257_; 
lean_dec_ref(v_post_4181_);
lean_dec_ref(v_e_4180_);
lean_dec_ref(v_pre_4179_);
v_a_4250_ = lean_ctor_get(v___x_4191_, 0);
v_isSharedCheck_4257_ = !lean_is_exclusive(v___x_4191_);
if (v_isSharedCheck_4257_ == 0)
{
v___x_4252_ = v___x_4191_;
v_isShared_4253_ = v_isSharedCheck_4257_;
goto v_resetjp_4251_;
}
else
{
lean_inc(v_a_4250_);
lean_dec(v___x_4191_);
v___x_4252_ = lean_box(0);
v_isShared_4253_ = v_isSharedCheck_4257_;
goto v_resetjp_4251_;
}
v_resetjp_4251_:
{
lean_object* v___x_4255_; 
if (v_isShared_4253_ == 0)
{
v___x_4255_ = v___x_4252_;
goto v_reusejp_4254_;
}
else
{
lean_object* v_reuseFailAlloc_4256_; 
v_reuseFailAlloc_4256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4256_, 0, v_a_4250_);
v___x_4255_ = v_reuseFailAlloc_4256_;
goto v_reusejp_4254_;
}
v_reusejp_4254_:
{
return v___x_4255_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1___boxed(lean_object* v___x_4258_, lean_object* v_pre_4259_, lean_object* v_e_4260_, lean_object* v_post_4261_, lean_object* v_usedLetOnly_4262_, lean_object* v_skipConstInApp_4263_, lean_object* v_skipInstances_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_){
_start:
{
uint8_t v_usedLetOnly_boxed_4271_; uint8_t v_skipConstInApp_boxed_4272_; uint8_t v_skipInstances_boxed_4273_; lean_object* v_res_4274_; 
v_usedLetOnly_boxed_4271_ = lean_unbox(v_usedLetOnly_4262_);
v_skipConstInApp_boxed_4272_ = lean_unbox(v_skipConstInApp_4263_);
v_skipInstances_boxed_4273_ = lean_unbox(v_skipInstances_4264_);
v_res_4274_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1(v___x_4258_, v_pre_4259_, v_e_4260_, v_post_4261_, v_usedLetOnly_boxed_4271_, v_skipConstInApp_boxed_4272_, v_skipInstances_boxed_4273_, v___y_4265_, v___y_4266_, v___y_4267_, v___y_4268_, v___y_4269_);
lean_dec(v___y_4269_);
lean_dec_ref(v___y_4268_);
lean_dec(v___y_4267_);
lean_dec_ref(v___y_4266_);
lean_dec(v___y_4265_);
return v_res_4274_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(lean_object* v_pre_4275_, lean_object* v_post_4276_, uint8_t v_usedLetOnly_4277_, uint8_t v_skipConstInApp_4278_, uint8_t v_skipInstances_4279_, lean_object* v_e_4280_, lean_object* v_a_4281_, lean_object* v___y_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_){
_start:
{
lean_object* v___x_4287_; lean_object* v___x_4288_; 
lean_inc(v_a_4281_);
v___x_4287_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_4287_, 0, lean_box(0));
lean_closure_set(v___x_4287_, 1, lean_box(0));
lean_closure_set(v___x_4287_, 2, v_a_4281_);
v___x_4288_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0(lean_box(0), v___x_4287_, v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_);
if (lean_obj_tag(v___x_4288_) == 0)
{
lean_object* v_a_4289_; lean_object* v___x_4291_; uint8_t v_isShared_4292_; uint8_t v_isSharedCheck_4323_; 
v_a_4289_ = lean_ctor_get(v___x_4288_, 0);
v_isSharedCheck_4323_ = !lean_is_exclusive(v___x_4288_);
if (v_isSharedCheck_4323_ == 0)
{
v___x_4291_ = v___x_4288_;
v_isShared_4292_ = v_isSharedCheck_4323_;
goto v_resetjp_4290_;
}
else
{
lean_inc(v_a_4289_);
lean_dec(v___x_4288_);
v___x_4291_ = lean_box(0);
v_isShared_4292_ = v_isSharedCheck_4323_;
goto v_resetjp_4290_;
}
v_resetjp_4290_:
{
lean_object* v___x_4293_; 
v___x_4293_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg(v_a_4289_, v_e_4280_);
lean_dec(v_a_4289_);
if (lean_obj_tag(v___x_4293_) == 0)
{
lean_object* v___x_4294_; lean_object* v___x_4295_; lean_object* v___x_4296_; lean_object* v___x_4297_; lean_object* v___f_4298_; lean_object* v___x_4299_; 
lean_del_object(v___x_4291_);
v___x_4294_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__19___closed__0));
v___x_4295_ = lean_box(v_usedLetOnly_4277_);
v___x_4296_ = lean_box(v_skipConstInApp_4278_);
v___x_4297_ = lean_box(v_skipInstances_4279_);
lean_inc_ref(v_e_4280_);
v___f_4298_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1___boxed), 13, 7);
lean_closure_set(v___f_4298_, 0, v___x_4294_);
lean_closure_set(v___f_4298_, 1, v_pre_4275_);
lean_closure_set(v___f_4298_, 2, v_e_4280_);
lean_closure_set(v___f_4298_, 3, v_post_4276_);
lean_closure_set(v___f_4298_, 4, v___x_4295_);
lean_closure_set(v___f_4298_, 5, v___x_4296_);
lean_closure_set(v___f_4298_, 6, v___x_4297_);
v___x_4299_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg(v___f_4298_, v_a_4281_, v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_);
if (lean_obj_tag(v___x_4299_) == 0)
{
lean_object* v_a_4300_; lean_object* v___f_4301_; lean_object* v___x_4302_; 
v_a_4300_ = lean_ctor_get(v___x_4299_, 0);
lean_inc_n(v_a_4300_, 2);
lean_dec_ref_known(v___x_4299_, 1);
lean_inc(v_a_4281_);
v___f_4301_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_4301_, 0, v_a_4281_);
lean_closure_set(v___f_4301_, 1, v_e_4280_);
lean_closure_set(v___f_4301_, 2, v_a_4300_);
v___x_4302_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0(lean_box(0), v___f_4301_, v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_);
if (lean_obj_tag(v___x_4302_) == 0)
{
lean_object* v___x_4304_; uint8_t v_isShared_4305_; uint8_t v_isSharedCheck_4309_; 
v_isSharedCheck_4309_ = !lean_is_exclusive(v___x_4302_);
if (v_isSharedCheck_4309_ == 0)
{
lean_object* v_unused_4310_; 
v_unused_4310_ = lean_ctor_get(v___x_4302_, 0);
lean_dec(v_unused_4310_);
v___x_4304_ = v___x_4302_;
v_isShared_4305_ = v_isSharedCheck_4309_;
goto v_resetjp_4303_;
}
else
{
lean_dec(v___x_4302_);
v___x_4304_ = lean_box(0);
v_isShared_4305_ = v_isSharedCheck_4309_;
goto v_resetjp_4303_;
}
v_resetjp_4303_:
{
lean_object* v___x_4307_; 
if (v_isShared_4305_ == 0)
{
lean_ctor_set(v___x_4304_, 0, v_a_4300_);
v___x_4307_ = v___x_4304_;
goto v_reusejp_4306_;
}
else
{
lean_object* v_reuseFailAlloc_4308_; 
v_reuseFailAlloc_4308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4308_, 0, v_a_4300_);
v___x_4307_ = v_reuseFailAlloc_4308_;
goto v_reusejp_4306_;
}
v_reusejp_4306_:
{
return v___x_4307_;
}
}
}
else
{
lean_object* v_a_4311_; lean_object* v___x_4313_; uint8_t v_isShared_4314_; uint8_t v_isSharedCheck_4318_; 
lean_dec(v_a_4300_);
v_a_4311_ = lean_ctor_get(v___x_4302_, 0);
v_isSharedCheck_4318_ = !lean_is_exclusive(v___x_4302_);
if (v_isSharedCheck_4318_ == 0)
{
v___x_4313_ = v___x_4302_;
v_isShared_4314_ = v_isSharedCheck_4318_;
goto v_resetjp_4312_;
}
else
{
lean_inc(v_a_4311_);
lean_dec(v___x_4302_);
v___x_4313_ = lean_box(0);
v_isShared_4314_ = v_isSharedCheck_4318_;
goto v_resetjp_4312_;
}
v_resetjp_4312_:
{
lean_object* v___x_4316_; 
if (v_isShared_4314_ == 0)
{
v___x_4316_ = v___x_4313_;
goto v_reusejp_4315_;
}
else
{
lean_object* v_reuseFailAlloc_4317_; 
v_reuseFailAlloc_4317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4317_, 0, v_a_4311_);
v___x_4316_ = v_reuseFailAlloc_4317_;
goto v_reusejp_4315_;
}
v_reusejp_4315_:
{
return v___x_4316_;
}
}
}
}
else
{
lean_dec_ref(v_e_4280_);
return v___x_4299_;
}
}
else
{
lean_object* v_val_4319_; lean_object* v___x_4321_; 
lean_dec_ref(v_e_4280_);
lean_dec_ref(v_post_4276_);
lean_dec_ref(v_pre_4275_);
v_val_4319_ = lean_ctor_get(v___x_4293_, 0);
lean_inc(v_val_4319_);
lean_dec_ref_known(v___x_4293_, 1);
if (v_isShared_4292_ == 0)
{
lean_ctor_set(v___x_4291_, 0, v_val_4319_);
v___x_4321_ = v___x_4291_;
goto v_reusejp_4320_;
}
else
{
lean_object* v_reuseFailAlloc_4322_; 
v_reuseFailAlloc_4322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4322_, 0, v_val_4319_);
v___x_4321_ = v_reuseFailAlloc_4322_;
goto v_reusejp_4320_;
}
v_reusejp_4320_:
{
return v___x_4321_;
}
}
}
}
else
{
lean_object* v_a_4324_; lean_object* v___x_4326_; uint8_t v_isShared_4327_; uint8_t v_isSharedCheck_4331_; 
lean_dec_ref(v_e_4280_);
lean_dec_ref(v_post_4276_);
lean_dec_ref(v_pre_4275_);
v_a_4324_ = lean_ctor_get(v___x_4288_, 0);
v_isSharedCheck_4331_ = !lean_is_exclusive(v___x_4288_);
if (v_isSharedCheck_4331_ == 0)
{
v___x_4326_ = v___x_4288_;
v_isShared_4327_ = v_isSharedCheck_4331_;
goto v_resetjp_4325_;
}
else
{
lean_inc(v_a_4324_);
lean_dec(v___x_4288_);
v___x_4326_ = lean_box(0);
v_isShared_4327_ = v_isSharedCheck_4331_;
goto v_resetjp_4325_;
}
v_resetjp_4325_:
{
lean_object* v___x_4329_; 
if (v_isShared_4327_ == 0)
{
v___x_4329_ = v___x_4326_;
goto v_reusejp_4328_;
}
else
{
lean_object* v_reuseFailAlloc_4330_; 
v_reuseFailAlloc_4330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4330_, 0, v_a_4324_);
v___x_4329_ = v_reuseFailAlloc_4330_;
goto v_reusejp_4328_;
}
v_reusejp_4328_:
{
return v___x_4329_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___lam__0___boxed(lean_object* v_fvars_4332_, lean_object* v_pre_4333_, lean_object* v_post_4334_, lean_object* v_usedLetOnly_4335_, lean_object* v_skipConstInApp_4336_, lean_object* v_skipInstances_4337_, lean_object* v_body_4338_, lean_object* v_x_4339_, lean_object* v___y_4340_, lean_object* v___y_4341_, lean_object* v___y_4342_, lean_object* v___y_4343_, lean_object* v___y_4344_, lean_object* v___y_4345_){
_start:
{
uint8_t v_usedLetOnly_boxed_4346_; uint8_t v_skipConstInApp_boxed_4347_; uint8_t v_skipInstances_boxed_4348_; lean_object* v_res_4349_; 
v_usedLetOnly_boxed_4346_ = lean_unbox(v_usedLetOnly_4335_);
v_skipConstInApp_boxed_4347_ = lean_unbox(v_skipConstInApp_4336_);
v_skipInstances_boxed_4348_ = lean_unbox(v_skipInstances_4337_);
v_res_4349_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___lam__0(v_fvars_4332_, v_pre_4333_, v_post_4334_, v_usedLetOnly_boxed_4346_, v_skipConstInApp_boxed_4347_, v_skipInstances_boxed_4348_, v_body_4338_, v_x_4339_, v___y_4340_, v___y_4341_, v___y_4342_, v___y_4343_, v___y_4344_);
lean_dec(v___y_4344_);
lean_dec_ref(v___y_4343_);
lean_dec(v___y_4342_);
lean_dec_ref(v___y_4341_);
lean_dec(v___y_4340_);
return v_res_4349_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5(lean_object* v_pre_4350_, lean_object* v_post_4351_, uint8_t v_usedLetOnly_4352_, uint8_t v_skipConstInApp_4353_, uint8_t v_skipInstances_4354_, lean_object* v_fvars_4355_, lean_object* v_e_4356_, lean_object* v_a_4357_, lean_object* v___y_4358_, lean_object* v___y_4359_, lean_object* v___y_4360_, lean_object* v___y_4361_){
_start:
{
if (lean_obj_tag(v_e_4356_) == 7)
{
lean_object* v_binderName_4363_; lean_object* v_binderType_4364_; lean_object* v_body_4365_; uint8_t v_binderInfo_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; 
v_binderName_4363_ = lean_ctor_get(v_e_4356_, 0);
lean_inc(v_binderName_4363_);
v_binderType_4364_ = lean_ctor_get(v_e_4356_, 1);
lean_inc_ref(v_binderType_4364_);
v_body_4365_ = lean_ctor_get(v_e_4356_, 2);
lean_inc_ref(v_body_4365_);
v_binderInfo_4366_ = lean_ctor_get_uint8(v_e_4356_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_4356_, 3);
v___x_4367_ = lean_expr_instantiate_rev(v_binderType_4364_, v_fvars_4355_);
lean_dec_ref(v_binderType_4364_);
lean_inc_ref(v_post_4351_);
lean_inc_ref(v_pre_4350_);
v___x_4368_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4350_, v_post_4351_, v_usedLetOnly_4352_, v_skipConstInApp_4353_, v_skipInstances_4354_, v___x_4367_, v_a_4357_, v___y_4358_, v___y_4359_, v___y_4360_, v___y_4361_);
if (lean_obj_tag(v___x_4368_) == 0)
{
lean_object* v_a_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___f_4373_; uint8_t v___x_4374_; lean_object* v___x_4375_; 
v_a_4369_ = lean_ctor_get(v___x_4368_, 0);
lean_inc(v_a_4369_);
lean_dec_ref_known(v___x_4368_, 1);
v___x_4370_ = lean_box(v_usedLetOnly_4352_);
v___x_4371_ = lean_box(v_skipConstInApp_4353_);
v___x_4372_ = lean_box(v_skipInstances_4354_);
v___f_4373_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___lam__0___boxed), 14, 7);
lean_closure_set(v___f_4373_, 0, v_fvars_4355_);
lean_closure_set(v___f_4373_, 1, v_pre_4350_);
lean_closure_set(v___f_4373_, 2, v_post_4351_);
lean_closure_set(v___f_4373_, 3, v___x_4370_);
lean_closure_set(v___f_4373_, 4, v___x_4371_);
lean_closure_set(v___f_4373_, 5, v___x_4372_);
lean_closure_set(v___f_4373_, 6, v_body_4365_);
v___x_4374_ = 0;
v___x_4375_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_binderName_4363_, v_binderInfo_4366_, v_a_4369_, v___f_4373_, v___x_4374_, v_a_4357_, v___y_4358_, v___y_4359_, v___y_4360_, v___y_4361_);
return v___x_4375_;
}
else
{
lean_dec_ref(v_body_4365_);
lean_dec(v_binderName_4363_);
lean_dec_ref(v_fvars_4355_);
lean_dec_ref(v_post_4351_);
lean_dec_ref(v_pre_4350_);
return v___x_4368_;
}
}
else
{
lean_object* v___x_4376_; lean_object* v___x_4377_; 
v___x_4376_ = lean_expr_instantiate_rev(v_e_4356_, v_fvars_4355_);
lean_dec_ref(v_e_4356_);
lean_inc_ref(v_post_4351_);
lean_inc_ref(v_pre_4350_);
v___x_4377_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4350_, v_post_4351_, v_usedLetOnly_4352_, v_skipConstInApp_4353_, v_skipInstances_4354_, v___x_4376_, v_a_4357_, v___y_4358_, v___y_4359_, v___y_4360_, v___y_4361_);
if (lean_obj_tag(v___x_4377_) == 0)
{
lean_object* v_a_4378_; uint8_t v___x_4379_; uint8_t v___x_4380_; uint8_t v___x_4381_; lean_object* v___x_4382_; 
v_a_4378_ = lean_ctor_get(v___x_4377_, 0);
lean_inc(v_a_4378_);
lean_dec_ref_known(v___x_4377_, 1);
v___x_4379_ = 0;
v___x_4380_ = 1;
v___x_4381_ = 1;
v___x_4382_ = l_Lean_Meta_mkForallFVars(v_fvars_4355_, v_a_4378_, v___x_4379_, v_usedLetOnly_4352_, v___x_4380_, v___x_4381_, v___y_4358_, v___y_4359_, v___y_4360_, v___y_4361_);
lean_dec_ref(v_fvars_4355_);
if (lean_obj_tag(v___x_4382_) == 0)
{
lean_object* v_a_4383_; lean_object* v___x_4384_; 
v_a_4383_ = lean_ctor_get(v___x_4382_, 0);
lean_inc(v_a_4383_);
lean_dec_ref_known(v___x_4382_, 1);
v___x_4384_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4350_, v_post_4351_, v_usedLetOnly_4352_, v_skipConstInApp_4353_, v_skipInstances_4354_, v_a_4383_, v_a_4357_, v___y_4358_, v___y_4359_, v___y_4360_, v___y_4361_);
return v___x_4384_;
}
else
{
lean_dec_ref(v_post_4351_);
lean_dec_ref(v_pre_4350_);
return v___x_4382_;
}
}
else
{
lean_dec_ref(v_fvars_4355_);
lean_dec_ref(v_post_4351_);
lean_dec_ref(v_pre_4350_);
return v___x_4377_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___lam__0(lean_object* v_fvars_4385_, lean_object* v_pre_4386_, lean_object* v_post_4387_, uint8_t v_usedLetOnly_4388_, uint8_t v_skipConstInApp_4389_, uint8_t v_skipInstances_4390_, lean_object* v_body_4391_, lean_object* v_x_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_, lean_object* v___y_4397_){
_start:
{
lean_object* v___x_4399_; lean_object* v___x_4400_; 
v___x_4399_ = lean_array_push(v_fvars_4385_, v_x_4392_);
v___x_4400_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5(v_pre_4386_, v_post_4387_, v_usedLetOnly_4388_, v_skipConstInApp_4389_, v_skipInstances_4390_, v___x_4399_, v_body_4391_, v___y_4393_, v___y_4394_, v___y_4395_, v___y_4396_, v___y_4397_);
return v___x_4400_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3___boxed(lean_object* v_pre_4401_, lean_object* v_post_4402_, lean_object* v_usedLetOnly_4403_, lean_object* v_skipConstInApp_4404_, lean_object* v_skipInstances_4405_, lean_object* v_e_4406_, lean_object* v_a_4407_, lean_object* v___y_4408_, lean_object* v___y_4409_, lean_object* v___y_4410_, lean_object* v___y_4411_, lean_object* v___y_4412_){
_start:
{
uint8_t v_usedLetOnly_boxed_4413_; uint8_t v_skipConstInApp_boxed_4414_; uint8_t v_skipInstances_boxed_4415_; lean_object* v_res_4416_; 
v_usedLetOnly_boxed_4413_ = lean_unbox(v_usedLetOnly_4403_);
v_skipConstInApp_boxed_4414_ = lean_unbox(v_skipConstInApp_4404_);
v_skipInstances_boxed_4415_ = lean_unbox(v_skipInstances_4405_);
v_res_4416_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4401_, v_post_4402_, v_usedLetOnly_boxed_4413_, v_skipConstInApp_boxed_4414_, v_skipInstances_boxed_4415_, v_e_4406_, v_a_4407_, v___y_4408_, v___y_4409_, v___y_4410_, v___y_4411_);
lean_dec(v___y_4411_);
lean_dec_ref(v___y_4410_);
lean_dec(v___y_4409_);
lean_dec_ref(v___y_4408_);
lean_dec(v_a_4407_);
return v_res_4416_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__2___boxed(lean_object* v_pre_4417_, lean_object* v_post_4418_, lean_object* v_usedLetOnly_4419_, lean_object* v_skipConstInApp_4420_, lean_object* v_skipInstances_4421_, lean_object* v_sz_4422_, lean_object* v_i_4423_, lean_object* v_bs_4424_, lean_object* v___y_4425_, lean_object* v___y_4426_, lean_object* v___y_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_){
_start:
{
uint8_t v_usedLetOnly_boxed_4431_; uint8_t v_skipConstInApp_boxed_4432_; uint8_t v_skipInstances_boxed_4433_; size_t v_sz_boxed_4434_; size_t v_i_boxed_4435_; lean_object* v_res_4436_; 
v_usedLetOnly_boxed_4431_ = lean_unbox(v_usedLetOnly_4419_);
v_skipConstInApp_boxed_4432_ = lean_unbox(v_skipConstInApp_4420_);
v_skipInstances_boxed_4433_ = lean_unbox(v_skipInstances_4421_);
v_sz_boxed_4434_ = lean_unbox_usize(v_sz_4422_);
lean_dec(v_sz_4422_);
v_i_boxed_4435_ = lean_unbox_usize(v_i_4423_);
lean_dec(v_i_4423_);
v_res_4436_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__2(v_pre_4417_, v_post_4418_, v_usedLetOnly_boxed_4431_, v_skipConstInApp_boxed_4432_, v_skipInstances_boxed_4433_, v_sz_boxed_4434_, v_i_boxed_4435_, v_bs_4424_, v___y_4425_, v___y_4426_, v___y_4427_, v___y_4428_, v___y_4429_);
lean_dec(v___y_4429_);
lean_dec_ref(v___y_4428_);
lean_dec(v___y_4427_);
lean_dec_ref(v___y_4426_);
lean_dec(v___y_4425_);
return v_res_4436_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___boxed(lean_object* v_pre_4437_, lean_object* v_post_4438_, lean_object* v_usedLetOnly_4439_, lean_object* v_skipConstInApp_4440_, lean_object* v_skipInstances_4441_, lean_object* v_e_4442_, lean_object* v_a_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_){
_start:
{
uint8_t v_usedLetOnly_boxed_4449_; uint8_t v_skipConstInApp_boxed_4450_; uint8_t v_skipInstances_boxed_4451_; lean_object* v_res_4452_; 
v_usedLetOnly_boxed_4449_ = lean_unbox(v_usedLetOnly_4439_);
v_skipConstInApp_boxed_4450_ = lean_unbox(v_skipConstInApp_4440_);
v_skipInstances_boxed_4451_ = lean_unbox(v_skipInstances_4441_);
v_res_4452_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4437_, v_post_4438_, v_usedLetOnly_boxed_4449_, v_skipConstInApp_boxed_4450_, v_skipInstances_boxed_4451_, v_e_4442_, v_a_4443_, v___y_4444_, v___y_4445_, v___y_4446_, v___y_4447_);
lean_dec(v___y_4447_);
lean_dec_ref(v___y_4446_);
lean_dec(v___y_4445_);
lean_dec_ref(v___y_4444_);
lean_dec(v_a_4443_);
return v_res_4452_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___boxed(lean_object* v_pre_4453_, lean_object* v_post_4454_, lean_object* v_usedLetOnly_4455_, lean_object* v_skipConstInApp_4456_, lean_object* v_skipInstances_4457_, lean_object* v_fvars_4458_, lean_object* v_e_4459_, lean_object* v_a_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_, lean_object* v___y_4463_, lean_object* v___y_4464_, lean_object* v___y_4465_){
_start:
{
uint8_t v_usedLetOnly_boxed_4466_; uint8_t v_skipConstInApp_boxed_4467_; uint8_t v_skipInstances_boxed_4468_; lean_object* v_res_4469_; 
v_usedLetOnly_boxed_4466_ = lean_unbox(v_usedLetOnly_4455_);
v_skipConstInApp_boxed_4467_ = lean_unbox(v_skipConstInApp_4456_);
v_skipInstances_boxed_4468_ = lean_unbox(v_skipInstances_4457_);
v_res_4469_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5(v_pre_4453_, v_post_4454_, v_usedLetOnly_boxed_4466_, v_skipConstInApp_boxed_4467_, v_skipInstances_boxed_4468_, v_fvars_4458_, v_e_4459_, v_a_4460_, v___y_4461_, v___y_4462_, v___y_4463_, v___y_4464_);
lean_dec(v___y_4464_);
lean_dec_ref(v___y_4463_);
lean_dec(v___y_4462_);
lean_dec_ref(v___y_4461_);
lean_dec(v_a_4460_);
return v_res_4469_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___boxed(lean_object* v_pre_4470_, lean_object* v_post_4471_, lean_object* v_usedLetOnly_4472_, lean_object* v_skipConstInApp_4473_, lean_object* v_skipInstances_4474_, lean_object* v_fvars_4475_, lean_object* v_e_4476_, lean_object* v_a_4477_, lean_object* v___y_4478_, lean_object* v___y_4479_, lean_object* v___y_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_){
_start:
{
uint8_t v_usedLetOnly_boxed_4483_; uint8_t v_skipConstInApp_boxed_4484_; uint8_t v_skipInstances_boxed_4485_; lean_object* v_res_4486_; 
v_usedLetOnly_boxed_4483_ = lean_unbox(v_usedLetOnly_4472_);
v_skipConstInApp_boxed_4484_ = lean_unbox(v_skipConstInApp_4473_);
v_skipInstances_boxed_4485_ = lean_unbox(v_skipInstances_4474_);
v_res_4486_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6(v_pre_4470_, v_post_4471_, v_usedLetOnly_boxed_4483_, v_skipConstInApp_boxed_4484_, v_skipInstances_boxed_4485_, v_fvars_4475_, v_e_4476_, v_a_4477_, v___y_4478_, v___y_4479_, v___y_4480_, v___y_4481_);
lean_dec(v___y_4481_);
lean_dec_ref(v___y_4480_);
lean_dec(v___y_4479_);
lean_dec_ref(v___y_4478_);
lean_dec(v_a_4477_);
return v_res_4486_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___boxed(lean_object* v_pre_4487_, lean_object* v_post_4488_, lean_object* v_usedLetOnly_4489_, lean_object* v_skipConstInApp_4490_, lean_object* v_skipInstances_4491_, lean_object* v_fvars_4492_, lean_object* v_e_4493_, lean_object* v_a_4494_, lean_object* v___y_4495_, lean_object* v___y_4496_, lean_object* v___y_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_){
_start:
{
uint8_t v_usedLetOnly_boxed_4500_; uint8_t v_skipConstInApp_boxed_4501_; uint8_t v_skipInstances_boxed_4502_; lean_object* v_res_4503_; 
v_usedLetOnly_boxed_4500_ = lean_unbox(v_usedLetOnly_4489_);
v_skipConstInApp_boxed_4501_ = lean_unbox(v_skipConstInApp_4490_);
v_skipInstances_boxed_4502_ = lean_unbox(v_skipInstances_4491_);
v_res_4503_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7(v_pre_4487_, v_post_4488_, v_usedLetOnly_boxed_4500_, v_skipConstInApp_boxed_4501_, v_skipInstances_boxed_4502_, v_fvars_4492_, v_e_4493_, v_a_4494_, v___y_4495_, v___y_4496_, v___y_4497_, v___y_4498_);
lean_dec(v___y_4498_);
lean_dec_ref(v___y_4497_);
lean_dec(v___y_4496_);
lean_dec_ref(v___y_4495_);
lean_dec(v_a_4494_);
return v_res_4503_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_upperBound_4504_, lean_object* v___x_4505_, lean_object* v_pre_4506_, lean_object* v_post_4507_, lean_object* v_usedLetOnly_4508_, lean_object* v_skipConstInApp_4509_, lean_object* v_skipInstances_4510_, lean_object* v_a_4511_, lean_object* v_b_4512_, lean_object* v___y_4513_, lean_object* v___y_4514_, lean_object* v___y_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_){
_start:
{
uint8_t v_usedLetOnly_boxed_4519_; uint8_t v_skipConstInApp_boxed_4520_; uint8_t v_skipInstances_boxed_4521_; lean_object* v_res_4522_; 
v_usedLetOnly_boxed_4519_ = lean_unbox(v_usedLetOnly_4508_);
v_skipConstInApp_boxed_4520_ = lean_unbox(v_skipConstInApp_4509_);
v_skipInstances_boxed_4521_ = lean_unbox(v_skipInstances_4510_);
v_res_4522_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg(v_upperBound_4504_, v___x_4505_, v_pre_4506_, v_post_4507_, v_usedLetOnly_boxed_4519_, v_skipConstInApp_boxed_4520_, v_skipInstances_boxed_4521_, v_a_4511_, v_b_4512_, v___y_4513_, v___y_4514_, v___y_4515_, v___y_4516_, v___y_4517_);
lean_dec(v___y_4517_);
lean_dec_ref(v___y_4516_);
lean_dec(v___y_4515_);
lean_dec_ref(v___y_4514_);
lean_dec(v___y_4513_);
lean_dec_ref(v___x_4505_);
lean_dec(v_upperBound_4504_);
return v_res_4522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__8___boxed(lean_object* v_skipInstances_4523_, lean_object* v_pre_4524_, lean_object* v_post_4525_, lean_object* v_usedLetOnly_4526_, lean_object* v_skipConstInApp_4527_, lean_object* v_x_4528_, lean_object* v_x_4529_, lean_object* v_x_4530_, lean_object* v___y_4531_, lean_object* v___y_4532_, lean_object* v___y_4533_, lean_object* v___y_4534_, lean_object* v___y_4535_, lean_object* v___y_4536_){
_start:
{
uint8_t v_skipInstances_boxed_4537_; uint8_t v_usedLetOnly_boxed_4538_; uint8_t v_skipConstInApp_boxed_4539_; lean_object* v_res_4540_; 
v_skipInstances_boxed_4537_ = lean_unbox(v_skipInstances_4523_);
v_usedLetOnly_boxed_4538_ = lean_unbox(v_usedLetOnly_4526_);
v_skipConstInApp_boxed_4539_ = lean_unbox(v_skipConstInApp_4527_);
v_res_4540_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__8(v_skipInstances_boxed_4537_, v_pre_4524_, v_post_4525_, v_usedLetOnly_boxed_4538_, v_skipConstInApp_boxed_4539_, v_x_4528_, v_x_4529_, v_x_4530_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_, v___y_4535_);
lean_dec(v___y_4535_);
lean_dec_ref(v___y_4534_);
lean_dec(v___y_4533_);
lean_dec_ref(v___y_4532_);
lean_dec(v___y_4531_);
return v_res_4540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(lean_object* v_input_4541_, lean_object* v_pre_4542_, lean_object* v_post_4543_, uint8_t v_usedLetOnly_4544_, uint8_t v_skipConstInApp_4545_, lean_object* v___y_4546_, lean_object* v___y_4547_, lean_object* v___y_4548_, lean_object* v___y_4549_){
_start:
{
lean_object* v___x_4551_; lean_object* v___x_4552_; lean_object* v_a_4553_; uint8_t v___x_4554_; lean_object* v___x_4555_; 
v___x_4551_ = lean_obj_once(&l_Lean_Core_transform___redArg___closed__2, &l_Lean_Core_transform___redArg___closed__2_once, _init_l_Lean_Core_transform___redArg___closed__2);
v___x_4552_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0(lean_box(0), v___x_4551_, v___y_4546_, v___y_4547_, v___y_4548_, v___y_4549_);
v_a_4553_ = lean_ctor_get(v___x_4552_, 0);
lean_inc(v_a_4553_);
lean_dec_ref(v___x_4552_);
v___x_4554_ = 0;
v___x_4555_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4542_, v_post_4543_, v_usedLetOnly_4544_, v_skipConstInApp_4545_, v___x_4554_, v_input_4541_, v_a_4553_, v___y_4546_, v___y_4547_, v___y_4548_, v___y_4549_);
if (lean_obj_tag(v___x_4555_) == 0)
{
lean_object* v_a_4556_; lean_object* v___x_4557_; lean_object* v___x_4558_; lean_object* v___x_4560_; uint8_t v_isShared_4561_; uint8_t v_isSharedCheck_4565_; 
v_a_4556_ = lean_ctor_get(v___x_4555_, 0);
lean_inc(v_a_4556_);
lean_dec_ref_known(v___x_4555_, 1);
v___x_4557_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_4557_, 0, lean_box(0));
lean_closure_set(v___x_4557_, 1, lean_box(0));
lean_closure_set(v___x_4557_, 2, v_a_4553_);
v___x_4558_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0(lean_box(0), v___x_4557_, v___y_4546_, v___y_4547_, v___y_4548_, v___y_4549_);
v_isSharedCheck_4565_ = !lean_is_exclusive(v___x_4558_);
if (v_isSharedCheck_4565_ == 0)
{
lean_object* v_unused_4566_; 
v_unused_4566_ = lean_ctor_get(v___x_4558_, 0);
lean_dec(v_unused_4566_);
v___x_4560_ = v___x_4558_;
v_isShared_4561_ = v_isSharedCheck_4565_;
goto v_resetjp_4559_;
}
else
{
lean_dec(v___x_4558_);
v___x_4560_ = lean_box(0);
v_isShared_4561_ = v_isSharedCheck_4565_;
goto v_resetjp_4559_;
}
v_resetjp_4559_:
{
lean_object* v___x_4563_; 
if (v_isShared_4561_ == 0)
{
lean_ctor_set(v___x_4560_, 0, v_a_4556_);
v___x_4563_ = v___x_4560_;
goto v_reusejp_4562_;
}
else
{
lean_object* v_reuseFailAlloc_4564_; 
v_reuseFailAlloc_4564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4564_, 0, v_a_4556_);
v___x_4563_ = v_reuseFailAlloc_4564_;
goto v_reusejp_4562_;
}
v_reusejp_4562_:
{
return v___x_4563_;
}
}
}
else
{
lean_dec(v_a_4553_);
return v___x_4555_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___boxed(lean_object* v_input_4567_, lean_object* v_pre_4568_, lean_object* v_post_4569_, lean_object* v_usedLetOnly_4570_, lean_object* v_skipConstInApp_4571_, lean_object* v___y_4572_, lean_object* v___y_4573_, lean_object* v___y_4574_, lean_object* v___y_4575_, lean_object* v___y_4576_){
_start:
{
uint8_t v_usedLetOnly_boxed_4577_; uint8_t v_skipConstInApp_boxed_4578_; lean_object* v_res_4579_; 
v_usedLetOnly_boxed_4577_ = lean_unbox(v_usedLetOnly_4570_);
v_skipConstInApp_boxed_4578_ = lean_unbox(v_skipConstInApp_4571_);
v_res_4579_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(v_input_4567_, v_pre_4568_, v_post_4569_, v_usedLetOnly_boxed_4577_, v_skipConstInApp_boxed_4578_, v___y_4572_, v___y_4573_, v___y_4574_, v___y_4575_);
lean_dec(v___y_4575_);
lean_dec_ref(v___y_4574_);
lean_dec(v___y_4573_);
lean_dec_ref(v___y_4572_);
return v_res_4579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce(lean_object* v_e_4581_, uint8_t v_zetaDelta_4582_, uint8_t v_zetaHave_4583_, uint8_t v_beta_4584_, lean_object* v_a_4585_, lean_object* v_a_4586_, lean_object* v_a_4587_, lean_object* v_a_4588_){
_start:
{
lean_object* v_lctx_4590_; lean_object* v___x_4591_; lean_object* v___x_4592_; lean_object* v___x_4593_; lean_object* v___f_4594_; uint8_t v___x_4595_; 
v_lctx_4590_ = lean_ctor_get(v_a_4585_, 2);
lean_inc_ref(v_lctx_4590_);
v___x_4591_ = lean_local_ctx_num_indices(v_lctx_4590_);
v___x_4592_ = lean_box(v_zetaHave_4583_);
v___x_4593_ = lean_box(v_zetaDelta_4582_);
v___f_4594_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaReduce___lam__0___boxed), 9, 3);
lean_closure_set(v___f_4594_, 0, v___x_4592_);
lean_closure_set(v___f_4594_, 1, v___x_4591_);
lean_closure_set(v___f_4594_, 2, v___x_4593_);
v___x_4595_ = 1;
if (v_beta_4584_ == 0)
{
lean_object* v___f_4596_; lean_object* v___f_4597_; lean_object* v___x_4598_; 
v___f_4596_ = ((lean_object*)(l_Lean_Meta_zetaReduce___closed__0));
v___f_4597_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaReduce___lam__2___boxed), 7, 1);
lean_closure_set(v___f_4597_, 0, v___f_4594_);
v___x_4598_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(v_e_4581_, v___f_4597_, v___f_4596_, v___x_4595_, v_beta_4584_, v_a_4585_, v_a_4586_, v_a_4587_, v_a_4588_);
return v___x_4598_;
}
else
{
lean_object* v___f_4599_; lean_object* v___f_4600_; uint8_t v___x_4601_; lean_object* v___x_4602_; 
v___f_4599_ = ((lean_object*)(l_Lean_Meta_zetaReduce___closed__0));
v___f_4600_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaReduce___lam__4___boxed), 7, 1);
lean_closure_set(v___f_4600_, 0, v___f_4594_);
v___x_4601_ = 0;
v___x_4602_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(v_e_4581_, v___f_4600_, v___f_4599_, v___x_4595_, v___x_4601_, v_a_4585_, v_a_4586_, v_a_4587_, v_a_4588_);
return v___x_4602_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___boxed(lean_object* v_e_4603_, lean_object* v_zetaDelta_4604_, lean_object* v_zetaHave_4605_, lean_object* v_beta_4606_, lean_object* v_a_4607_, lean_object* v_a_4608_, lean_object* v_a_4609_, lean_object* v_a_4610_, lean_object* v_a_4611_){
_start:
{
uint8_t v_zetaDelta_boxed_4612_; uint8_t v_zetaHave_boxed_4613_; uint8_t v_beta_boxed_4614_; lean_object* v_res_4615_; 
v_zetaDelta_boxed_4612_ = lean_unbox(v_zetaDelta_4604_);
v_zetaHave_boxed_4613_ = lean_unbox(v_zetaHave_4605_);
v_beta_boxed_4614_ = lean_unbox(v_beta_4606_);
v_res_4615_ = l_Lean_Meta_zetaReduce(v_e_4603_, v_zetaDelta_boxed_4612_, v_zetaHave_boxed_4613_, v_beta_boxed_4614_, v_a_4607_, v_a_4608_, v_a_4609_, v_a_4610_);
lean_dec(v_a_4610_);
lean_dec_ref(v_a_4609_);
lean_dec(v_a_4608_);
lean_dec_ref(v_a_4607_);
return v_res_4615_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4(lean_object* v_upperBound_4616_, lean_object* v___x_4617_, lean_object* v_pre_4618_, lean_object* v_post_4619_, uint8_t v_usedLetOnly_4620_, uint8_t v_skipConstInApp_4621_, uint8_t v_skipInstances_4622_, lean_object* v___x_4623_, lean_object* v_inst_4624_, lean_object* v_R_4625_, lean_object* v_a_4626_, lean_object* v_b_4627_, lean_object* v_c_4628_, lean_object* v___y_4629_, lean_object* v___y_4630_, lean_object* v___y_4631_, lean_object* v___y_4632_, lean_object* v___y_4633_){
_start:
{
lean_object* v___x_4635_; 
v___x_4635_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg(v_upperBound_4616_, v___x_4617_, v_pre_4618_, v_post_4619_, v_usedLetOnly_4620_, v_skipConstInApp_4621_, v_skipInstances_4622_, v_a_4626_, v_b_4627_, v___y_4629_, v___y_4630_, v___y_4631_, v___y_4632_, v___y_4633_);
return v___x_4635_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___boxed(lean_object** _args){
lean_object* v_upperBound_4636_ = _args[0];
lean_object* v___x_4637_ = _args[1];
lean_object* v_pre_4638_ = _args[2];
lean_object* v_post_4639_ = _args[3];
lean_object* v_usedLetOnly_4640_ = _args[4];
lean_object* v_skipConstInApp_4641_ = _args[5];
lean_object* v_skipInstances_4642_ = _args[6];
lean_object* v___x_4643_ = _args[7];
lean_object* v_inst_4644_ = _args[8];
lean_object* v_R_4645_ = _args[9];
lean_object* v_a_4646_ = _args[10];
lean_object* v_b_4647_ = _args[11];
lean_object* v_c_4648_ = _args[12];
lean_object* v___y_4649_ = _args[13];
lean_object* v___y_4650_ = _args[14];
lean_object* v___y_4651_ = _args[15];
lean_object* v___y_4652_ = _args[16];
lean_object* v___y_4653_ = _args[17];
lean_object* v___y_4654_ = _args[18];
_start:
{
uint8_t v_usedLetOnly_boxed_4655_; uint8_t v_skipConstInApp_boxed_4656_; uint8_t v_skipInstances_boxed_4657_; lean_object* v_res_4658_; 
v_usedLetOnly_boxed_4655_ = lean_unbox(v_usedLetOnly_4640_);
v_skipConstInApp_boxed_4656_ = lean_unbox(v_skipConstInApp_4641_);
v_skipInstances_boxed_4657_ = lean_unbox(v_skipInstances_4642_);
v_res_4658_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4(v_upperBound_4636_, v___x_4637_, v_pre_4638_, v_post_4639_, v_usedLetOnly_boxed_4655_, v_skipConstInApp_boxed_4656_, v_skipInstances_boxed_4657_, v___x_4643_, v_inst_4644_, v_R_4645_, v_a_4646_, v_b_4647_, v_c_4648_, v___y_4649_, v___y_4650_, v___y_4651_, v___y_4652_, v___y_4653_);
lean_dec(v___y_4653_);
lean_dec_ref(v___y_4652_);
lean_dec(v___y_4651_);
lean_dec_ref(v___y_4650_);
lean_dec(v___y_4649_);
lean_dec(v___x_4643_);
lean_dec_ref(v___x_4637_);
lean_dec(v_upperBound_4636_);
return v_res_4658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6(lean_object* v_00_u03b1_4659_, lean_object* v_name_4660_, uint8_t v_bi_4661_, lean_object* v_type_4662_, lean_object* v_k_4663_, uint8_t v_kind_4664_, lean_object* v___y_4665_, lean_object* v___y_4666_, lean_object* v___y_4667_, lean_object* v___y_4668_, lean_object* v___y_4669_){
_start:
{
lean_object* v___x_4671_; 
v___x_4671_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_name_4660_, v_bi_4661_, v_type_4662_, v_k_4663_, v_kind_4664_, v___y_4665_, v___y_4666_, v___y_4667_, v___y_4668_, v___y_4669_);
return v___x_4671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___boxed(lean_object* v_00_u03b1_4672_, lean_object* v_name_4673_, lean_object* v_bi_4674_, lean_object* v_type_4675_, lean_object* v_k_4676_, lean_object* v_kind_4677_, lean_object* v___y_4678_, lean_object* v___y_4679_, lean_object* v___y_4680_, lean_object* v___y_4681_, lean_object* v___y_4682_, lean_object* v___y_4683_){
_start:
{
uint8_t v_bi_boxed_4684_; uint8_t v_kind_boxed_4685_; lean_object* v_res_4686_; 
v_bi_boxed_4684_ = lean_unbox(v_bi_4674_);
v_kind_boxed_4685_ = lean_unbox(v_kind_4677_);
v_res_4686_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6(v_00_u03b1_4672_, v_name_4673_, v_bi_boxed_4684_, v_type_4675_, v_k_4676_, v_kind_boxed_4685_, v___y_4678_, v___y_4679_, v___y_4680_, v___y_4681_, v___y_4682_);
lean_dec(v___y_4682_);
lean_dec_ref(v___y_4681_);
lean_dec(v___y_4680_);
lean_dec_ref(v___y_4679_);
lean_dec(v___y_4678_);
return v_res_4686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9(lean_object* v_00_u03b1_4687_, lean_object* v_name_4688_, lean_object* v_type_4689_, lean_object* v_val_4690_, lean_object* v_k_4691_, uint8_t v_nondep_4692_, uint8_t v_kind_4693_, lean_object* v___y_4694_, lean_object* v___y_4695_, lean_object* v___y_4696_, lean_object* v___y_4697_, lean_object* v___y_4698_){
_start:
{
lean_object* v___x_4700_; 
v___x_4700_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg(v_name_4688_, v_type_4689_, v_val_4690_, v_k_4691_, v_nondep_4692_, v_kind_4693_, v___y_4694_, v___y_4695_, v___y_4696_, v___y_4697_, v___y_4698_);
return v___x_4700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___boxed(lean_object* v_00_u03b1_4701_, lean_object* v_name_4702_, lean_object* v_type_4703_, lean_object* v_val_4704_, lean_object* v_k_4705_, lean_object* v_nondep_4706_, lean_object* v_kind_4707_, lean_object* v___y_4708_, lean_object* v___y_4709_, lean_object* v___y_4710_, lean_object* v___y_4711_, lean_object* v___y_4712_, lean_object* v___y_4713_){
_start:
{
uint8_t v_nondep_boxed_4714_; uint8_t v_kind_boxed_4715_; lean_object* v_res_4716_; 
v_nondep_boxed_4714_ = lean_unbox(v_nondep_4706_);
v_kind_boxed_4715_ = lean_unbox(v_kind_4707_);
v_res_4716_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9(v_00_u03b1_4701_, v_name_4702_, v_type_4703_, v_val_4704_, v_k_4705_, v_nondep_boxed_4714_, v_kind_boxed_4715_, v___y_4708_, v___y_4709_, v___y_4710_, v___y_4711_, v___y_4712_);
lean_dec(v___y_4712_);
lean_dec_ref(v___y_4711_);
lean_dec(v___y_4710_);
lean_dec_ref(v___y_4709_);
lean_dec(v___y_4708_);
return v_res_4716_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12(lean_object* v_00_u03b1_4717_, lean_object* v_ref_4718_, lean_object* v___y_4719_, lean_object* v___y_4720_, lean_object* v___y_4721_, lean_object* v___y_4722_){
_start:
{
lean_object* v___x_4724_; 
v___x_4724_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg(v_ref_4718_);
return v___x_4724_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___boxed(lean_object* v_00_u03b1_4725_, lean_object* v_ref_4726_, lean_object* v___y_4727_, lean_object* v___y_4728_, lean_object* v___y_4729_, lean_object* v___y_4730_, lean_object* v___y_4731_){
_start:
{
lean_object* v_res_4732_; 
v_res_4732_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12(v_00_u03b1_4725_, v_ref_4726_, v___y_4727_, v___y_4728_, v___y_4729_, v___y_4730_);
lean_dec(v___y_4730_);
lean_dec_ref(v___y_4729_);
lean_dec(v___y_4728_);
lean_dec_ref(v___y_4727_);
return v_res_4732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9(lean_object* v_00_u03b1_4733_, lean_object* v_x_4734_, lean_object* v___y_4735_, lean_object* v___y_4736_, lean_object* v___y_4737_, lean_object* v___y_4738_, lean_object* v___y_4739_){
_start:
{
lean_object* v___x_4741_; 
v___x_4741_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg(v_x_4734_, v___y_4735_, v___y_4736_, v___y_4737_, v___y_4738_, v___y_4739_);
return v___x_4741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___boxed(lean_object* v_00_u03b1_4742_, lean_object* v_x_4743_, lean_object* v___y_4744_, lean_object* v___y_4745_, lean_object* v___y_4746_, lean_object* v___y_4747_, lean_object* v___y_4748_, lean_object* v___y_4749_){
_start:
{
lean_object* v_res_4750_; 
v_res_4750_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9(v_00_u03b1_4742_, v_x_4743_, v___y_4744_, v___y_4745_, v___y_4746_, v___y_4747_, v___y_4748_);
lean_dec(v___y_4748_);
lean_dec_ref(v___y_4747_);
lean_dec(v___y_4746_);
lean_dec_ref(v___y_4745_);
lean_dec(v___y_4744_);
return v_res_4750_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0_spec__0(lean_object* v_a_4751_, lean_object* v_as_4752_, size_t v_i_4753_, size_t v_stop_4754_){
_start:
{
uint8_t v___x_4755_; 
v___x_4755_ = lean_usize_dec_eq(v_i_4753_, v_stop_4754_);
if (v___x_4755_ == 0)
{
lean_object* v___x_4756_; uint8_t v___x_4757_; 
v___x_4756_ = lean_array_uget_borrowed(v_as_4752_, v_i_4753_);
v___x_4757_ = l_Lean_instBEqFVarId_beq(v_a_4751_, v___x_4756_);
if (v___x_4757_ == 0)
{
size_t v___x_4758_; size_t v___x_4759_; 
v___x_4758_ = ((size_t)1ULL);
v___x_4759_ = lean_usize_add(v_i_4753_, v___x_4758_);
v_i_4753_ = v___x_4759_;
goto _start;
}
else
{
return v___x_4757_;
}
}
else
{
uint8_t v___x_4761_; 
v___x_4761_ = 0;
return v___x_4761_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0_spec__0___boxed(lean_object* v_a_4762_, lean_object* v_as_4763_, lean_object* v_i_4764_, lean_object* v_stop_4765_){
_start:
{
size_t v_i_boxed_4766_; size_t v_stop_boxed_4767_; uint8_t v_res_4768_; lean_object* v_r_4769_; 
v_i_boxed_4766_ = lean_unbox_usize(v_i_4764_);
lean_dec(v_i_4764_);
v_stop_boxed_4767_ = lean_unbox_usize(v_stop_4765_);
lean_dec(v_stop_4765_);
v_res_4768_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0_spec__0(v_a_4762_, v_as_4763_, v_i_boxed_4766_, v_stop_boxed_4767_);
lean_dec_ref(v_as_4763_);
lean_dec(v_a_4762_);
v_r_4769_ = lean_box(v_res_4768_);
return v_r_4769_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0(lean_object* v_as_4770_, lean_object* v_a_4771_){
_start:
{
lean_object* v___x_4772_; lean_object* v___x_4773_; uint8_t v___x_4774_; 
v___x_4772_ = lean_unsigned_to_nat(0u);
v___x_4773_ = lean_array_get_size(v_as_4770_);
v___x_4774_ = lean_nat_dec_lt(v___x_4772_, v___x_4773_);
if (v___x_4774_ == 0)
{
return v___x_4774_;
}
else
{
if (v___x_4774_ == 0)
{
return v___x_4774_;
}
else
{
size_t v___x_4775_; size_t v___x_4776_; uint8_t v___x_4777_; 
v___x_4775_ = ((size_t)0ULL);
v___x_4776_ = lean_usize_of_nat(v___x_4773_);
v___x_4777_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0_spec__0(v_a_4771_, v_as_4770_, v___x_4775_, v___x_4776_);
return v___x_4777_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0___boxed(lean_object* v_as_4778_, lean_object* v_a_4779_){
_start:
{
uint8_t v_res_4780_; lean_object* v_r_4781_; 
v_res_4780_ = l_Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0(v_as_4778_, v_a_4779_);
lean_dec(v_a_4779_);
lean_dec_ref(v_as_4778_);
v_r_4781_ = lean_box(v_res_4780_);
return v_r_4781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaFVars___lam__1(lean_object* v_fvars_4782_, lean_object* v_e_4783_, lean_object* v___y_4784_, lean_object* v___y_4785_, lean_object* v___y_4786_, lean_object* v___y_4787_){
_start:
{
lean_object* v___x_4792_; 
v___x_4792_ = l_Lean_Expr_getAppFn(v_e_4783_);
if (lean_obj_tag(v___x_4792_) == 1)
{
lean_object* v_fvarId_4793_; uint8_t v___x_4794_; 
v_fvarId_4793_ = lean_ctor_get(v___x_4792_, 0);
lean_inc(v_fvarId_4793_);
lean_dec_ref_known(v___x_4792_, 1);
v___x_4794_ = l_Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0(v_fvars_4782_, v_fvarId_4793_);
if (v___x_4794_ == 0)
{
lean_dec(v_fvarId_4793_);
lean_dec_ref(v_e_4783_);
goto v___jp_4789_;
}
else
{
uint8_t v___x_4795_; lean_object* v___x_4796_; 
v___x_4795_ = 0;
v___x_4796_ = l_Lean_FVarId_getValue_x3f___redArg(v_fvarId_4793_, v___x_4795_, v___y_4784_, v___y_4786_, v___y_4787_);
if (lean_obj_tag(v___x_4796_) == 0)
{
lean_object* v_a_4797_; 
v_a_4797_ = lean_ctor_get(v___x_4796_, 0);
lean_inc(v_a_4797_);
lean_dec_ref_known(v___x_4796_, 1);
if (lean_obj_tag(v_a_4797_) == 1)
{
lean_object* v_val_4798_; lean_object* v___x_4800_; uint8_t v_isShared_4801_; uint8_t v_isSharedCheck_4821_; 
v_val_4798_ = lean_ctor_get(v_a_4797_, 0);
v_isSharedCheck_4821_ = !lean_is_exclusive(v_a_4797_);
if (v_isSharedCheck_4821_ == 0)
{
v___x_4800_ = v_a_4797_;
v_isShared_4801_ = v_isSharedCheck_4821_;
goto v_resetjp_4799_;
}
else
{
lean_inc(v_val_4798_);
lean_dec(v_a_4797_);
v___x_4800_ = lean_box(0);
v_isShared_4801_ = v_isSharedCheck_4821_;
goto v_resetjp_4799_;
}
v_resetjp_4799_:
{
lean_object* v___x_4802_; lean_object* v_a_4803_; lean_object* v___x_4805_; uint8_t v_isShared_4806_; uint8_t v_isSharedCheck_4820_; 
v___x_4802_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(v_val_4798_, v___y_4785_);
v_a_4803_ = lean_ctor_get(v___x_4802_, 0);
v_isSharedCheck_4820_ = !lean_is_exclusive(v___x_4802_);
if (v_isSharedCheck_4820_ == 0)
{
v___x_4805_ = v___x_4802_;
v_isShared_4806_ = v_isSharedCheck_4820_;
goto v_resetjp_4804_;
}
else
{
lean_inc(v_a_4803_);
lean_dec(v___x_4802_);
v___x_4805_ = lean_box(0);
v_isShared_4806_ = v_isSharedCheck_4820_;
goto v_resetjp_4804_;
}
v_resetjp_4804_:
{
lean_object* v_dummy_4807_; lean_object* v_nargs_4808_; lean_object* v___x_4809_; lean_object* v___x_4810_; lean_object* v___x_4811_; lean_object* v___x_4812_; lean_object* v___x_4813_; lean_object* v___x_4815_; 
v_dummy_4807_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_4808_ = l_Lean_Expr_getAppNumArgs(v_e_4783_);
lean_inc(v_nargs_4808_);
v___x_4809_ = lean_mk_array(v_nargs_4808_, v_dummy_4807_);
v___x_4810_ = lean_unsigned_to_nat(1u);
v___x_4811_ = lean_nat_sub(v_nargs_4808_, v___x_4810_);
lean_dec(v_nargs_4808_);
v___x_4812_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_4783_, v___x_4809_, v___x_4811_);
v___x_4813_ = l_Lean_Expr_beta(v_a_4803_, v___x_4812_);
if (v_isShared_4801_ == 0)
{
lean_ctor_set(v___x_4800_, 0, v___x_4813_);
v___x_4815_ = v___x_4800_;
goto v_reusejp_4814_;
}
else
{
lean_object* v_reuseFailAlloc_4819_; 
v_reuseFailAlloc_4819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4819_, 0, v___x_4813_);
v___x_4815_ = v_reuseFailAlloc_4819_;
goto v_reusejp_4814_;
}
v_reusejp_4814_:
{
lean_object* v___x_4817_; 
if (v_isShared_4806_ == 0)
{
lean_ctor_set(v___x_4805_, 0, v___x_4815_);
v___x_4817_ = v___x_4805_;
goto v_reusejp_4816_;
}
else
{
lean_object* v_reuseFailAlloc_4818_; 
v_reuseFailAlloc_4818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4818_, 0, v___x_4815_);
v___x_4817_ = v_reuseFailAlloc_4818_;
goto v_reusejp_4816_;
}
v_reusejp_4816_:
{
return v___x_4817_;
}
}
}
}
}
else
{
lean_dec(v_a_4797_);
lean_dec_ref(v_e_4783_);
goto v___jp_4789_;
}
}
else
{
lean_object* v_a_4822_; lean_object* v___x_4824_; uint8_t v_isShared_4825_; uint8_t v_isSharedCheck_4829_; 
lean_dec_ref(v_e_4783_);
v_a_4822_ = lean_ctor_get(v___x_4796_, 0);
v_isSharedCheck_4829_ = !lean_is_exclusive(v___x_4796_);
if (v_isSharedCheck_4829_ == 0)
{
v___x_4824_ = v___x_4796_;
v_isShared_4825_ = v_isSharedCheck_4829_;
goto v_resetjp_4823_;
}
else
{
lean_inc(v_a_4822_);
lean_dec(v___x_4796_);
v___x_4824_ = lean_box(0);
v_isShared_4825_ = v_isSharedCheck_4829_;
goto v_resetjp_4823_;
}
v_resetjp_4823_:
{
lean_object* v___x_4827_; 
if (v_isShared_4825_ == 0)
{
v___x_4827_ = v___x_4824_;
goto v_reusejp_4826_;
}
else
{
lean_object* v_reuseFailAlloc_4828_; 
v_reuseFailAlloc_4828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4828_, 0, v_a_4822_);
v___x_4827_ = v_reuseFailAlloc_4828_;
goto v_reusejp_4826_;
}
v_reusejp_4826_:
{
return v___x_4827_;
}
}
}
}
}
else
{
lean_object* v___x_4830_; lean_object* v___x_4831_; 
lean_dec_ref(v___x_4792_);
lean_dec_ref(v_e_4783_);
v___x_4830_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_4831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4831_, 0, v___x_4830_);
return v___x_4831_;
}
v___jp_4789_:
{
lean_object* v___x_4790_; lean_object* v___x_4791_; 
v___x_4790_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_4791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4791_, 0, v___x_4790_);
return v___x_4791_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaFVars___lam__1___boxed(lean_object* v_fvars_4832_, lean_object* v_e_4833_, lean_object* v___y_4834_, lean_object* v___y_4835_, lean_object* v___y_4836_, lean_object* v___y_4837_, lean_object* v___y_4838_){
_start:
{
lean_object* v_res_4839_; 
v_res_4839_ = l_Lean_Meta_zetaDeltaFVars___lam__1(v_fvars_4832_, v_e_4833_, v___y_4834_, v___y_4835_, v___y_4836_, v___y_4837_);
lean_dec(v___y_4837_);
lean_dec_ref(v___y_4836_);
lean_dec(v___y_4835_);
lean_dec_ref(v___y_4834_);
lean_dec_ref(v_fvars_4832_);
return v_res_4839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaFVars(lean_object* v_e_4840_, lean_object* v_fvars_4841_, lean_object* v_a_4842_, lean_object* v_a_4843_, lean_object* v_a_4844_, lean_object* v_a_4845_){
_start:
{
lean_object* v___f_4847_; lean_object* v_pre_4848_; uint8_t v___x_4849_; lean_object* v___x_4850_; 
v___f_4847_ = ((lean_object*)(l_Lean_Meta_zetaReduce___closed__0));
v_pre_4848_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaDeltaFVars___lam__1___boxed), 7, 1);
lean_closure_set(v_pre_4848_, 0, v_fvars_4841_);
v___x_4849_ = 0;
v___x_4850_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(v_e_4840_, v_pre_4848_, v___f_4847_, v___x_4849_, v___x_4849_, v_a_4842_, v_a_4843_, v_a_4844_, v_a_4845_);
return v___x_4850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaFVars___boxed(lean_object* v_e_4851_, lean_object* v_fvars_4852_, lean_object* v_a_4853_, lean_object* v_a_4854_, lean_object* v_a_4855_, lean_object* v_a_4856_, lean_object* v_a_4857_){
_start:
{
lean_object* v_res_4858_; 
v_res_4858_ = l_Lean_Meta_zetaDeltaFVars(v_e_4851_, v_fvars_4852_, v_a_4853_, v_a_4854_, v_a_4855_, v_a_4856_);
lean_dec(v_a_4856_);
lean_dec_ref(v_a_4855_);
lean_dec(v_a_4854_);
lean_dec_ref(v_a_4853_);
return v_res_4858_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_4859_; 
v___x_4859_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4859_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_4860_; lean_object* v___x_4861_; 
v___x_4860_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__0, &l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__0);
v___x_4861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4861_, 0, v___x_4860_);
return v___x_4861_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_4862_; lean_object* v___x_4863_; 
v___x_4862_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__1, &l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__1);
v___x_4863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4863_, 0, v___x_4862_);
lean_ctor_set(v___x_4863_, 1, v___x_4862_);
return v___x_4863_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(lean_object* v_env_4864_, lean_object* v___y_4865_){
_start:
{
lean_object* v___x_4867_; lean_object* v_nextMacroScope_4868_; lean_object* v_ngen_4869_; lean_object* v_auxDeclNGen_4870_; lean_object* v_traceState_4871_; lean_object* v_messages_4872_; lean_object* v_infoState_4873_; lean_object* v_snapshotTasks_4874_; lean_object* v___x_4876_; uint8_t v_isShared_4877_; uint8_t v_isSharedCheck_4885_; 
v___x_4867_ = lean_st_ref_take(v___y_4865_);
v_nextMacroScope_4868_ = lean_ctor_get(v___x_4867_, 1);
v_ngen_4869_ = lean_ctor_get(v___x_4867_, 2);
v_auxDeclNGen_4870_ = lean_ctor_get(v___x_4867_, 3);
v_traceState_4871_ = lean_ctor_get(v___x_4867_, 4);
v_messages_4872_ = lean_ctor_get(v___x_4867_, 6);
v_infoState_4873_ = lean_ctor_get(v___x_4867_, 7);
v_snapshotTasks_4874_ = lean_ctor_get(v___x_4867_, 8);
v_isSharedCheck_4885_ = !lean_is_exclusive(v___x_4867_);
if (v_isSharedCheck_4885_ == 0)
{
lean_object* v_unused_4886_; lean_object* v_unused_4887_; 
v_unused_4886_ = lean_ctor_get(v___x_4867_, 5);
lean_dec(v_unused_4886_);
v_unused_4887_ = lean_ctor_get(v___x_4867_, 0);
lean_dec(v_unused_4887_);
v___x_4876_ = v___x_4867_;
v_isShared_4877_ = v_isSharedCheck_4885_;
goto v_resetjp_4875_;
}
else
{
lean_inc(v_snapshotTasks_4874_);
lean_inc(v_infoState_4873_);
lean_inc(v_messages_4872_);
lean_inc(v_traceState_4871_);
lean_inc(v_auxDeclNGen_4870_);
lean_inc(v_ngen_4869_);
lean_inc(v_nextMacroScope_4868_);
lean_dec(v___x_4867_);
v___x_4876_ = lean_box(0);
v_isShared_4877_ = v_isSharedCheck_4885_;
goto v_resetjp_4875_;
}
v_resetjp_4875_:
{
lean_object* v___x_4878_; lean_object* v___x_4880_; 
v___x_4878_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2, &l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2);
if (v_isShared_4877_ == 0)
{
lean_ctor_set(v___x_4876_, 5, v___x_4878_);
lean_ctor_set(v___x_4876_, 0, v_env_4864_);
v___x_4880_ = v___x_4876_;
goto v_reusejp_4879_;
}
else
{
lean_object* v_reuseFailAlloc_4884_; 
v_reuseFailAlloc_4884_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4884_, 0, v_env_4864_);
lean_ctor_set(v_reuseFailAlloc_4884_, 1, v_nextMacroScope_4868_);
lean_ctor_set(v_reuseFailAlloc_4884_, 2, v_ngen_4869_);
lean_ctor_set(v_reuseFailAlloc_4884_, 3, v_auxDeclNGen_4870_);
lean_ctor_set(v_reuseFailAlloc_4884_, 4, v_traceState_4871_);
lean_ctor_set(v_reuseFailAlloc_4884_, 5, v___x_4878_);
lean_ctor_set(v_reuseFailAlloc_4884_, 6, v_messages_4872_);
lean_ctor_set(v_reuseFailAlloc_4884_, 7, v_infoState_4873_);
lean_ctor_set(v_reuseFailAlloc_4884_, 8, v_snapshotTasks_4874_);
v___x_4880_ = v_reuseFailAlloc_4884_;
goto v_reusejp_4879_;
}
v_reusejp_4879_:
{
lean_object* v___x_4881_; lean_object* v___x_4882_; lean_object* v___x_4883_; 
v___x_4881_ = lean_st_ref_put(v___y_4865_, v___x_4880_);
v___x_4882_ = lean_box(0);
v___x_4883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4883_, 0, v___x_4882_);
return v___x_4883_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___boxed(lean_object* v_env_4888_, lean_object* v___y_4889_, lean_object* v___y_4890_){
_start:
{
lean_object* v_res_4891_; 
v_res_4891_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_4888_, v___y_4889_);
lean_dec(v___y_4889_);
return v_res_4891_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0(lean_object* v_env_4892_, lean_object* v___y_4893_, lean_object* v___y_4894_){
_start:
{
lean_object* v___x_4896_; 
v___x_4896_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_4892_, v___y_4894_);
return v___x_4896_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___boxed(lean_object* v_env_4897_, lean_object* v___y_4898_, lean_object* v___y_4899_, lean_object* v___y_4900_){
_start:
{
lean_object* v_res_4901_; 
v_res_4901_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0(v_env_4897_, v___y_4898_, v___y_4899_);
lean_dec(v___y_4899_);
lean_dec_ref(v___y_4898_);
return v_res_4901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___lam__1(lean_object* v_env_4902_, lean_object* v___x_4903_, uint8_t v___x_4904_, lean_object* v_e_4905_, lean_object* v___y_4906_, lean_object* v___y_4907_){
_start:
{
if (lean_obj_tag(v_e_4905_) == 4)
{
lean_object* v_declName_4909_; lean_object* v_us_4910_; uint8_t v___x_4911_; uint8_t v___x_4912_; 
v_declName_4909_ = lean_ctor_get(v_e_4905_, 0);
v_us_4910_ = lean_ctor_get(v_e_4905_, 1);
v___x_4911_ = 1;
lean_inc(v_declName_4909_);
v___x_4912_ = l_Lean_Environment_contains(v_env_4902_, v_declName_4909_, v___x_4911_);
if (v___x_4912_ == 0)
{
lean_object* v___x_4913_; 
lean_inc(v_declName_4909_);
v___x_4913_ = l_Lean_Environment_find_x3f(v___x_4903_, v_declName_4909_, v___x_4904_);
if (lean_obj_tag(v___x_4913_) == 1)
{
lean_object* v_val_4914_; lean_object* v___x_4916_; uint8_t v_isShared_4917_; uint8_t v_isSharedCheck_4943_; 
v_val_4914_ = lean_ctor_get(v___x_4913_, 0);
v_isSharedCheck_4943_ = !lean_is_exclusive(v___x_4913_);
if (v_isSharedCheck_4943_ == 0)
{
v___x_4916_ = v___x_4913_;
v_isShared_4917_ = v_isSharedCheck_4943_;
goto v_resetjp_4915_;
}
else
{
lean_inc(v_val_4914_);
lean_dec(v___x_4913_);
v___x_4916_ = lean_box(0);
v_isShared_4917_ = v_isSharedCheck_4943_;
goto v_resetjp_4915_;
}
v_resetjp_4915_:
{
uint8_t v___x_4918_; 
v___x_4918_ = l_Lean_ConstantInfo_hasValue(v_val_4914_, v___x_4911_);
if (v___x_4918_ == 0)
{
lean_object* v___x_4920_; 
lean_dec(v_val_4914_);
if (v_isShared_4917_ == 0)
{
lean_ctor_set_tag(v___x_4916_, 0);
lean_ctor_set(v___x_4916_, 0, v_e_4905_);
v___x_4920_ = v___x_4916_;
goto v_reusejp_4919_;
}
else
{
lean_object* v_reuseFailAlloc_4922_; 
v_reuseFailAlloc_4922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4922_, 0, v_e_4905_);
v___x_4920_ = v_reuseFailAlloc_4922_;
goto v_reusejp_4919_;
}
v_reusejp_4919_:
{
lean_object* v___x_4921_; 
v___x_4921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4921_, 0, v___x_4920_);
return v___x_4921_;
}
}
else
{
lean_object* v___x_4923_; 
lean_inc(v_us_4910_);
lean_dec_ref_known(v_e_4905_, 2);
v___x_4923_ = l_Lean_Core_instantiateValueLevelParams(v_val_4914_, v_us_4910_, v___x_4911_, v___y_4906_, v___y_4907_);
lean_dec(v_val_4914_);
if (lean_obj_tag(v___x_4923_) == 0)
{
lean_object* v_a_4924_; lean_object* v___x_4926_; uint8_t v_isShared_4927_; uint8_t v_isSharedCheck_4934_; 
v_a_4924_ = lean_ctor_get(v___x_4923_, 0);
v_isSharedCheck_4934_ = !lean_is_exclusive(v___x_4923_);
if (v_isSharedCheck_4934_ == 0)
{
v___x_4926_ = v___x_4923_;
v_isShared_4927_ = v_isSharedCheck_4934_;
goto v_resetjp_4925_;
}
else
{
lean_inc(v_a_4924_);
lean_dec(v___x_4923_);
v___x_4926_ = lean_box(0);
v_isShared_4927_ = v_isSharedCheck_4934_;
goto v_resetjp_4925_;
}
v_resetjp_4925_:
{
lean_object* v___x_4929_; 
if (v_isShared_4917_ == 0)
{
lean_ctor_set(v___x_4916_, 0, v_a_4924_);
v___x_4929_ = v___x_4916_;
goto v_reusejp_4928_;
}
else
{
lean_object* v_reuseFailAlloc_4933_; 
v_reuseFailAlloc_4933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4933_, 0, v_a_4924_);
v___x_4929_ = v_reuseFailAlloc_4933_;
goto v_reusejp_4928_;
}
v_reusejp_4928_:
{
lean_object* v___x_4931_; 
if (v_isShared_4927_ == 0)
{
lean_ctor_set(v___x_4926_, 0, v___x_4929_);
v___x_4931_ = v___x_4926_;
goto v_reusejp_4930_;
}
else
{
lean_object* v_reuseFailAlloc_4932_; 
v_reuseFailAlloc_4932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4932_, 0, v___x_4929_);
v___x_4931_ = v_reuseFailAlloc_4932_;
goto v_reusejp_4930_;
}
v_reusejp_4930_:
{
return v___x_4931_;
}
}
}
}
else
{
lean_object* v_a_4935_; lean_object* v___x_4937_; uint8_t v_isShared_4938_; uint8_t v_isSharedCheck_4942_; 
lean_del_object(v___x_4916_);
v_a_4935_ = lean_ctor_get(v___x_4923_, 0);
v_isSharedCheck_4942_ = !lean_is_exclusive(v___x_4923_);
if (v_isSharedCheck_4942_ == 0)
{
v___x_4937_ = v___x_4923_;
v_isShared_4938_ = v_isSharedCheck_4942_;
goto v_resetjp_4936_;
}
else
{
lean_inc(v_a_4935_);
lean_dec(v___x_4923_);
v___x_4937_ = lean_box(0);
v_isShared_4938_ = v_isSharedCheck_4942_;
goto v_resetjp_4936_;
}
v_resetjp_4936_:
{
lean_object* v___x_4940_; 
if (v_isShared_4938_ == 0)
{
v___x_4940_ = v___x_4937_;
goto v_reusejp_4939_;
}
else
{
lean_object* v_reuseFailAlloc_4941_; 
v_reuseFailAlloc_4941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4941_, 0, v_a_4935_);
v___x_4940_ = v_reuseFailAlloc_4941_;
goto v_reusejp_4939_;
}
v_reusejp_4939_:
{
return v___x_4940_;
}
}
}
}
}
}
else
{
lean_object* v___x_4944_; lean_object* v___x_4945_; 
lean_dec(v___x_4913_);
v___x_4944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4944_, 0, v_e_4905_);
v___x_4945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4945_, 0, v___x_4944_);
return v___x_4945_;
}
}
else
{
lean_object* v___x_4946_; lean_object* v___x_4947_; 
lean_dec_ref(v___x_4903_);
v___x_4946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4946_, 0, v_e_4905_);
v___x_4947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4947_, 0, v___x_4946_);
return v___x_4947_;
}
}
else
{
lean_object* v___x_4948_; lean_object* v___x_4949_; 
lean_dec_ref(v_e_4905_);
lean_dec_ref(v___x_4903_);
lean_dec_ref(v_env_4902_);
v___x_4948_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_4949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4949_, 0, v___x_4948_);
return v___x_4949_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___lam__1___boxed(lean_object* v_env_4950_, lean_object* v___x_4951_, lean_object* v___x_4952_, lean_object* v_e_4953_, lean_object* v___y_4954_, lean_object* v___y_4955_, lean_object* v___y_4956_){
_start:
{
uint8_t v___x_1992__boxed_4957_; lean_object* v_res_4958_; 
v___x_1992__boxed_4957_ = lean_unbox(v___x_4952_);
v_res_4958_ = l_Lean_Meta_unfoldDeclsFrom___lam__1(v_env_4950_, v___x_4951_, v___x_1992__boxed_4957_, v_e_4953_, v___y_4954_, v___y_4955_);
lean_dec(v___y_4955_);
lean_dec_ref(v___y_4954_);
return v_res_4958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___lam__0(lean_object* v_biggerEnv_4959_, lean_object* v_e_4960_, lean_object* v___f_4961_, lean_object* v___y_4962_, lean_object* v___y_4963_){
_start:
{
lean_object* v___x_4965_; uint8_t v___x_4966_; lean_object* v___x_4967_; lean_object* v___x_4968_; lean_object* v_env_4969_; lean_object* v___x_4970_; lean_object* v___f_4971_; lean_object* v___x_4972_; 
v___x_4965_ = lean_st_ref_get(v___y_4963_);
v___x_4966_ = 0;
v___x_4967_ = l_Lean_Environment_setExporting(v_biggerEnv_4959_, v___x_4966_);
lean_inc_ref(v___x_4967_);
v___x_4968_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v___x_4967_, v___y_4963_);
lean_dec_ref(v___x_4968_);
v_env_4969_ = lean_ctor_get(v___x_4965_, 0);
lean_inc_ref(v_env_4969_);
lean_dec(v___x_4965_);
v___x_4970_ = lean_box(v___x_4966_);
v___f_4971_ = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDeclsFrom___lam__1___boxed), 7, 3);
lean_closure_set(v___f_4971_, 0, v_env_4969_);
lean_closure_set(v___f_4971_, 1, v___x_4967_);
lean_closure_set(v___f_4971_, 2, v___x_4970_);
v___x_4972_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_4960_, v___f_4971_, v___f_4961_, v___y_4962_, v___y_4963_);
return v___x_4972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___lam__0___boxed(lean_object* v_biggerEnv_4973_, lean_object* v_e_4974_, lean_object* v___f_4975_, lean_object* v___y_4976_, lean_object* v___y_4977_, lean_object* v___y_4978_){
_start:
{
lean_object* v_res_4979_; 
v_res_4979_ = l_Lean_Meta_unfoldDeclsFrom___lam__0(v_biggerEnv_4973_, v_e_4974_, v___f_4975_, v___y_4976_, v___y_4977_);
lean_dec(v___y_4977_);
lean_dec_ref(v___y_4976_);
return v_res_4979_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg(lean_object* v_env_4980_, lean_object* v_x_4981_, lean_object* v___y_4982_, lean_object* v___y_4983_){
_start:
{
lean_object* v___x_4985_; lean_object* v_env_4986_; lean_object* v_a_4988_; lean_object* v___x_4998_; lean_object* v___x_4999_; 
v___x_4985_ = lean_st_ref_get(v___y_4983_);
v_env_4986_ = lean_ctor_get(v___x_4985_, 0);
lean_inc_ref(v_env_4986_);
lean_dec(v___x_4985_);
v___x_4998_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_4980_, v___y_4983_);
lean_dec_ref(v___x_4998_);
lean_inc(v___y_4983_);
lean_inc_ref(v___y_4982_);
v___x_4999_ = lean_apply_3(v_x_4981_, v___y_4982_, v___y_4983_, lean_box(0));
if (lean_obj_tag(v___x_4999_) == 0)
{
lean_object* v_a_5000_; lean_object* v___x_5001_; lean_object* v___x_5003_; uint8_t v_isShared_5004_; uint8_t v_isSharedCheck_5008_; 
v_a_5000_ = lean_ctor_get(v___x_4999_, 0);
lean_inc(v_a_5000_);
lean_dec_ref_known(v___x_4999_, 1);
v___x_5001_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_4986_, v___y_4983_);
v_isSharedCheck_5008_ = !lean_is_exclusive(v___x_5001_);
if (v_isSharedCheck_5008_ == 0)
{
lean_object* v_unused_5009_; 
v_unused_5009_ = lean_ctor_get(v___x_5001_, 0);
lean_dec(v_unused_5009_);
v___x_5003_ = v___x_5001_;
v_isShared_5004_ = v_isSharedCheck_5008_;
goto v_resetjp_5002_;
}
else
{
lean_dec(v___x_5001_);
v___x_5003_ = lean_box(0);
v_isShared_5004_ = v_isSharedCheck_5008_;
goto v_resetjp_5002_;
}
v_resetjp_5002_:
{
lean_object* v___x_5006_; 
if (v_isShared_5004_ == 0)
{
lean_ctor_set(v___x_5003_, 0, v_a_5000_);
v___x_5006_ = v___x_5003_;
goto v_reusejp_5005_;
}
else
{
lean_object* v_reuseFailAlloc_5007_; 
v_reuseFailAlloc_5007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5007_, 0, v_a_5000_);
v___x_5006_ = v_reuseFailAlloc_5007_;
goto v_reusejp_5005_;
}
v_reusejp_5005_:
{
return v___x_5006_;
}
}
}
else
{
lean_object* v_a_5010_; 
v_a_5010_ = lean_ctor_get(v___x_4999_, 0);
lean_inc(v_a_5010_);
lean_dec_ref_known(v___x_4999_, 1);
v_a_4988_ = v_a_5010_;
goto v___jp_4987_;
}
v___jp_4987_:
{
lean_object* v___x_4989_; lean_object* v___x_4991_; uint8_t v_isShared_4992_; uint8_t v_isSharedCheck_4996_; 
v___x_4989_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_4986_, v___y_4983_);
v_isSharedCheck_4996_ = !lean_is_exclusive(v___x_4989_);
if (v_isSharedCheck_4996_ == 0)
{
lean_object* v_unused_4997_; 
v_unused_4997_ = lean_ctor_get(v___x_4989_, 0);
lean_dec(v_unused_4997_);
v___x_4991_ = v___x_4989_;
v_isShared_4992_ = v_isSharedCheck_4996_;
goto v_resetjp_4990_;
}
else
{
lean_dec(v___x_4989_);
v___x_4991_ = lean_box(0);
v_isShared_4992_ = v_isSharedCheck_4996_;
goto v_resetjp_4990_;
}
v_resetjp_4990_:
{
lean_object* v___x_4994_; 
if (v_isShared_4992_ == 0)
{
lean_ctor_set_tag(v___x_4991_, 1);
lean_ctor_set(v___x_4991_, 0, v_a_4988_);
v___x_4994_ = v___x_4991_;
goto v_reusejp_4993_;
}
else
{
lean_object* v_reuseFailAlloc_4995_; 
v_reuseFailAlloc_4995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4995_, 0, v_a_4988_);
v___x_4994_ = v_reuseFailAlloc_4995_;
goto v_reusejp_4993_;
}
v_reusejp_4993_:
{
return v___x_4994_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg___boxed(lean_object* v_env_5011_, lean_object* v_x_5012_, lean_object* v___y_5013_, lean_object* v___y_5014_, lean_object* v___y_5015_){
_start:
{
lean_object* v_res_5016_; 
v_res_5016_ = l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg(v_env_5011_, v_x_5012_, v___y_5013_, v___y_5014_);
lean_dec(v___y_5014_);
lean_dec_ref(v___y_5013_);
return v_res_5016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom(lean_object* v_biggerEnv_5017_, lean_object* v_e_5018_, lean_object* v_a_5019_, lean_object* v_a_5020_){
_start:
{
lean_object* v___x_5022_; lean_object* v_env_5023_; lean_object* v___f_5024_; lean_object* v___f_5025_; lean_object* v___x_5026_; lean_object* v___x_5027_; 
v___x_5022_ = lean_st_ref_get(v_a_5020_);
v_env_5023_ = lean_ctor_get(v___x_5022_, 0);
lean_inc_ref(v_env_5023_);
lean_dec(v___x_5022_);
v___f_5024_ = ((lean_object*)(l_Lean_Core_betaReduce___closed__1));
v___f_5025_ = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDeclsFrom___lam__0___boxed), 6, 3);
lean_closure_set(v___f_5025_, 0, v_biggerEnv_5017_);
lean_closure_set(v___f_5025_, 1, v_e_5018_);
lean_closure_set(v___f_5025_, 2, v___f_5024_);
v___x_5026_ = l_Lean_Environment_unlockAsync(v_env_5023_);
v___x_5027_ = l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg(v___x_5026_, v___f_5025_, v_a_5019_, v_a_5020_);
return v___x_5027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___boxed(lean_object* v_biggerEnv_5028_, lean_object* v_e_5029_, lean_object* v_a_5030_, lean_object* v_a_5031_, lean_object* v_a_5032_){
_start:
{
lean_object* v_res_5033_; 
v_res_5033_ = l_Lean_Meta_unfoldDeclsFrom(v_biggerEnv_5028_, v_e_5029_, v_a_5030_, v_a_5031_);
lean_dec(v_a_5031_);
lean_dec_ref(v_a_5030_);
return v_res_5033_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1(lean_object* v_00_u03b1_5034_, lean_object* v_env_5035_, lean_object* v_x_5036_, lean_object* v___y_5037_, lean_object* v___y_5038_){
_start:
{
lean_object* v___x_5040_; 
v___x_5040_ = l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg(v_env_5035_, v_x_5036_, v___y_5037_, v___y_5038_);
return v___x_5040_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___boxed(lean_object* v_00_u03b1_5041_, lean_object* v_env_5042_, lean_object* v_x_5043_, lean_object* v___y_5044_, lean_object* v___y_5045_, lean_object* v___y_5046_){
_start:
{
lean_object* v_res_5047_; 
v_res_5047_ = l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1(v_00_u03b1_5041_, v_env_5042_, v_x_5043_, v___y_5044_, v___y_5045_);
lean_dec(v___y_5045_);
lean_dec_ref(v___y_5044_);
return v_res_5047_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0(lean_object* v_af_5048_, lean_object* v_axs_5049_, lean_object* v_numSectionVars_5050_, lean_object* v_as_5051_, size_t v_i_5052_, size_t v_stop_5053_){
_start:
{
uint8_t v___x_5054_; 
v___x_5054_ = lean_usize_dec_eq(v_i_5052_, v_stop_5053_);
if (v___x_5054_ == 0)
{
uint8_t v___x_5055_; uint8_t v___y_5057_; lean_object* v___x_5061_; lean_object* v___x_5062_; uint8_t v___x_5063_; 
v___x_5055_ = 1;
v___x_5061_ = lean_array_uget_borrowed(v_as_5051_, v_i_5052_);
v___x_5062_ = l_Lean_Expr_constName_x21(v_af_5048_);
v___x_5063_ = lean_name_eq(v___x_5062_, v___x_5061_);
lean_dec(v___x_5062_);
if (v___x_5063_ == 0)
{
v___y_5057_ = v___x_5063_;
goto v___jp_5056_;
}
else
{
lean_object* v___x_5064_; uint8_t v___x_5065_; 
v___x_5064_ = lean_array_get_size(v_axs_5049_);
v___x_5065_ = lean_nat_dec_le(v___x_5064_, v_numSectionVars_5050_);
v___y_5057_ = v___x_5065_;
goto v___jp_5056_;
}
v___jp_5056_:
{
if (v___y_5057_ == 0)
{
size_t v___x_5058_; size_t v___x_5059_; 
v___x_5058_ = ((size_t)1ULL);
v___x_5059_ = lean_usize_add(v_i_5052_, v___x_5058_);
v_i_5052_ = v___x_5059_;
goto _start;
}
else
{
return v___x_5055_;
}
}
}
else
{
uint8_t v___x_5066_; 
v___x_5066_ = 0;
return v___x_5066_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0___boxed(lean_object* v_af_5067_, lean_object* v_axs_5068_, lean_object* v_numSectionVars_5069_, lean_object* v_as_5070_, lean_object* v_i_5071_, lean_object* v_stop_5072_){
_start:
{
size_t v_i_boxed_5073_; size_t v_stop_boxed_5074_; uint8_t v_res_5075_; lean_object* v_r_5076_; 
v_i_boxed_5073_ = lean_unbox_usize(v_i_5071_);
lean_dec(v_i_5071_);
v_stop_boxed_5074_ = lean_unbox_usize(v_stop_5072_);
lean_dec(v_stop_5072_);
v_res_5075_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0(v_af_5067_, v_axs_5068_, v_numSectionVars_5069_, v_as_5070_, v_i_boxed_5073_, v_stop_boxed_5074_);
lean_dec_ref(v_as_5070_);
lean_dec(v_numSectionVars_5069_);
lean_dec_ref(v_axs_5068_);
lean_dec_ref(v_af_5067_);
v_r_5076_ = lean_box(v_res_5075_);
return v_r_5076_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1_spec__1(lean_object* v_fnNames_5077_, lean_object* v_numSectionVars_5078_, lean_object* v_x_5079_, lean_object* v_x_5080_, lean_object* v_x_5081_){
_start:
{
if (lean_obj_tag(v_x_5079_) == 5)
{
lean_object* v_fn_5082_; lean_object* v_arg_5083_; lean_object* v___x_5084_; lean_object* v___x_5085_; lean_object* v___x_5086_; 
v_fn_5082_ = lean_ctor_get(v_x_5079_, 0);
lean_inc_ref(v_fn_5082_);
v_arg_5083_ = lean_ctor_get(v_x_5079_, 1);
lean_inc_ref(v_arg_5083_);
lean_dec_ref_known(v_x_5079_, 2);
v___x_5084_ = lean_array_set(v_x_5080_, v_x_5081_, v_arg_5083_);
v___x_5085_ = lean_unsigned_to_nat(1u);
v___x_5086_ = lean_nat_sub(v_x_5081_, v___x_5085_);
lean_dec(v_x_5081_);
v_x_5079_ = v_fn_5082_;
v_x_5080_ = v___x_5084_;
v_x_5081_ = v___x_5086_;
goto _start;
}
else
{
uint8_t v___x_5088_; 
lean_dec(v_x_5081_);
v___x_5088_ = l_Lean_Expr_isConst(v_x_5079_);
if (v___x_5088_ == 0)
{
lean_dec_ref(v_x_5080_);
lean_dec_ref(v_x_5079_);
return v___x_5088_;
}
else
{
lean_object* v___x_5089_; lean_object* v___x_5090_; uint8_t v___x_5091_; 
v___x_5089_ = lean_unsigned_to_nat(0u);
v___x_5090_ = lean_array_get_size(v_fnNames_5077_);
v___x_5091_ = lean_nat_dec_lt(v___x_5089_, v___x_5090_);
if (v___x_5091_ == 0)
{
lean_dec_ref(v_x_5080_);
lean_dec_ref(v_x_5079_);
return v___x_5091_;
}
else
{
if (v___x_5091_ == 0)
{
lean_dec_ref(v_x_5080_);
lean_dec_ref(v_x_5079_);
return v___x_5091_;
}
else
{
size_t v___x_5092_; size_t v___x_5093_; uint8_t v___x_5094_; 
v___x_5092_ = ((size_t)0ULL);
v___x_5093_ = lean_usize_of_nat(v___x_5090_);
v___x_5094_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0(v_x_5079_, v_x_5080_, v_numSectionVars_5078_, v_fnNames_5077_, v___x_5092_, v___x_5093_);
lean_dec_ref(v_x_5080_);
lean_dec_ref(v_x_5079_);
return v___x_5094_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1_spec__1___boxed(lean_object* v_fnNames_5095_, lean_object* v_numSectionVars_5096_, lean_object* v_x_5097_, lean_object* v_x_5098_, lean_object* v_x_5099_){
_start:
{
uint8_t v_res_5100_; lean_object* v_r_5101_; 
v_res_5100_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1_spec__1(v_fnNames_5095_, v_numSectionVars_5096_, v_x_5097_, v_x_5098_, v_x_5099_);
lean_dec(v_numSectionVars_5096_);
lean_dec_ref(v_fnNames_5095_);
v_r_5101_ = lean_box(v_res_5100_);
return v_r_5101_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1(lean_object* v_numSectionVars_5102_, lean_object* v_fnNames_5103_, lean_object* v_x_5104_, lean_object* v_x_5105_, lean_object* v_x_5106_){
_start:
{
if (lean_obj_tag(v_x_5104_) == 5)
{
lean_object* v_fn_5107_; lean_object* v_arg_5108_; lean_object* v___x_5109_; lean_object* v___x_5110_; lean_object* v___x_5111_; uint8_t v___x_5112_; 
v_fn_5107_ = lean_ctor_get(v_x_5104_, 0);
lean_inc_ref(v_fn_5107_);
v_arg_5108_ = lean_ctor_get(v_x_5104_, 1);
lean_inc_ref(v_arg_5108_);
lean_dec_ref_known(v_x_5104_, 2);
v___x_5109_ = lean_array_set(v_x_5105_, v_x_5106_, v_arg_5108_);
v___x_5110_ = lean_unsigned_to_nat(1u);
v___x_5111_ = lean_nat_sub(v_x_5106_, v___x_5110_);
v___x_5112_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1_spec__1(v_fnNames_5103_, v_numSectionVars_5102_, v_fn_5107_, v___x_5109_, v___x_5111_);
return v___x_5112_;
}
else
{
uint8_t v___x_5113_; 
v___x_5113_ = l_Lean_Expr_isConst(v_x_5104_);
if (v___x_5113_ == 0)
{
lean_dec_ref(v_x_5105_);
lean_dec_ref(v_x_5104_);
return v___x_5113_;
}
else
{
lean_object* v___x_5114_; lean_object* v___x_5115_; uint8_t v___x_5116_; 
v___x_5114_ = lean_unsigned_to_nat(0u);
v___x_5115_ = lean_array_get_size(v_fnNames_5103_);
v___x_5116_ = lean_nat_dec_lt(v___x_5114_, v___x_5115_);
if (v___x_5116_ == 0)
{
lean_dec_ref(v_x_5105_);
lean_dec_ref(v_x_5104_);
return v___x_5116_;
}
else
{
if (v___x_5116_ == 0)
{
lean_dec_ref(v_x_5105_);
lean_dec_ref(v_x_5104_);
return v___x_5116_;
}
else
{
size_t v___x_5117_; size_t v___x_5118_; uint8_t v___x_5119_; 
v___x_5117_ = ((size_t)0ULL);
v___x_5118_ = lean_usize_of_nat(v___x_5115_);
v___x_5119_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0(v_x_5104_, v_x_5105_, v_numSectionVars_5102_, v_fnNames_5103_, v___x_5117_, v___x_5118_);
lean_dec_ref(v_x_5105_);
lean_dec_ref(v_x_5104_);
return v___x_5119_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1___boxed(lean_object* v_numSectionVars_5120_, lean_object* v_fnNames_5121_, lean_object* v_x_5122_, lean_object* v_x_5123_, lean_object* v_x_5124_){
_start:
{
uint8_t v_res_5125_; lean_object* v_r_5126_; 
v_res_5125_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1(v_numSectionVars_5120_, v_fnNames_5121_, v_x_5122_, v_x_5123_, v_x_5124_);
lean_dec(v_x_5124_);
lean_dec_ref(v_fnNames_5121_);
lean_dec(v_numSectionVars_5120_);
v_r_5126_ = lean_box(v_res_5125_);
return v_r_5126_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg(lean_object* v_fnNames_5127_, lean_object* v_numSectionVars_5128_, lean_object* v_a_5129_){
_start:
{
lean_object* v_dummy_5130_; lean_object* v_nargs_5131_; lean_object* v___x_5132_; lean_object* v___x_5133_; lean_object* v___x_5134_; uint8_t v___x_5135_; 
v_dummy_5130_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_5131_ = l_Lean_Expr_getAppNumArgs(v_a_5129_);
lean_inc(v_nargs_5131_);
v___x_5132_ = lean_mk_array(v_nargs_5131_, v_dummy_5130_);
v___x_5133_ = lean_unsigned_to_nat(1u);
v___x_5134_ = lean_nat_sub(v_nargs_5131_, v___x_5133_);
lean_dec(v_nargs_5131_);
v___x_5135_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1(v_numSectionVars_5128_, v_fnNames_5127_, v_a_5129_, v___x_5132_, v___x_5134_);
lean_dec(v___x_5134_);
return v___x_5135_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg___boxed(lean_object* v_fnNames_5136_, lean_object* v_numSectionVars_5137_, lean_object* v_a_5138_){
_start:
{
uint8_t v_res_5139_; lean_object* v_r_5140_; 
v_res_5139_ = l___private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg(v_fnNames_5136_, v_numSectionVars_5137_, v_a_5138_);
lean_dec(v_numSectionVars_5137_);
lean_dec_ref(v_fnNames_5136_);
v_r_5140_ = lean_box(v_res_5139_);
return v_r_5140_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__0(lean_object* v_fnNames_5141_, lean_object* v_numSectionVars_5142_, lean_object* v_as_5143_, size_t v_i_5144_, size_t v_stop_5145_){
_start:
{
uint8_t v___x_5146_; 
v___x_5146_ = lean_usize_dec_eq(v_i_5144_, v_stop_5145_);
if (v___x_5146_ == 0)
{
lean_object* v___x_5147_; uint8_t v___x_5148_; 
v___x_5147_ = lean_array_uget_borrowed(v_as_5143_, v_i_5144_);
lean_inc(v___x_5147_);
v___x_5148_ = l___private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg(v_fnNames_5141_, v_numSectionVars_5142_, v___x_5147_);
if (v___x_5148_ == 0)
{
size_t v___x_5149_; size_t v___x_5150_; 
v___x_5149_ = ((size_t)1ULL);
v___x_5150_ = lean_usize_add(v_i_5144_, v___x_5149_);
v_i_5144_ = v___x_5150_;
goto _start;
}
else
{
return v___x_5148_;
}
}
else
{
uint8_t v___x_5152_; 
v___x_5152_ = 0;
return v___x_5152_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__0___boxed(lean_object* v_fnNames_5153_, lean_object* v_numSectionVars_5154_, lean_object* v_as_5155_, lean_object* v_i_5156_, lean_object* v_stop_5157_){
_start:
{
size_t v_i_boxed_5158_; size_t v_stop_boxed_5159_; uint8_t v_res_5160_; lean_object* v_r_5161_; 
v_i_boxed_5158_ = lean_unbox_usize(v_i_5156_);
lean_dec(v_i_5156_);
v_stop_boxed_5159_ = lean_unbox_usize(v_stop_5157_);
lean_dec(v_stop_5157_);
v_res_5160_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__0(v_fnNames_5153_, v_numSectionVars_5154_, v_as_5155_, v_i_boxed_5158_, v_stop_boxed_5159_);
lean_dec_ref(v_as_5155_);
lean_dec(v_numSectionVars_5154_);
lean_dec_ref(v_fnNames_5153_);
v_r_5161_ = lean_box(v_res_5160_);
return v_r_5161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__1(lean_object* v_fnNames_5162_, lean_object* v_numSectionVars_5163_, lean_object* v___x_5164_, lean_object* v_x_5165_, lean_object* v_x_5166_, lean_object* v___y_5167_, lean_object* v___y_5168_){
_start:
{
if (lean_obj_tag(v_x_5165_) == 5)
{
lean_object* v_fn_5173_; lean_object* v_arg_5174_; lean_object* v___x_5175_; 
v_fn_5173_ = lean_ctor_get(v_x_5165_, 0);
lean_inc_ref(v_fn_5173_);
v_arg_5174_ = lean_ctor_get(v_x_5165_, 1);
lean_inc_ref(v_arg_5174_);
lean_dec_ref_known(v_x_5165_, 2);
v___x_5175_ = lean_array_push(v_x_5166_, v_arg_5174_);
v_x_5165_ = v_fn_5173_;
v_x_5166_ = v___x_5175_;
goto _start;
}
else
{
uint8_t v___x_5177_; 
v___x_5177_ = l_Lean_Expr_isConst(v_x_5165_);
if (v___x_5177_ == 0)
{
lean_dec_ref(v_x_5166_);
lean_dec_ref(v_x_5165_);
lean_dec_ref(v___x_5164_);
goto v___jp_5170_;
}
else
{
lean_object* v___x_5178_; lean_object* v___x_5179_; uint8_t v___x_5180_; 
v___x_5178_ = lean_unsigned_to_nat(0u);
v___x_5179_ = lean_array_get_size(v_x_5166_);
v___x_5180_ = lean_nat_dec_lt(v___x_5178_, v___x_5179_);
if (v___x_5180_ == 0)
{
lean_dec_ref(v_x_5166_);
lean_dec_ref(v_x_5165_);
lean_dec_ref(v___x_5164_);
goto v___jp_5170_;
}
else
{
if (v___x_5180_ == 0)
{
lean_dec_ref(v_x_5166_);
lean_dec_ref(v_x_5165_);
lean_dec_ref(v___x_5164_);
goto v___jp_5170_;
}
else
{
size_t v___x_5181_; size_t v___x_5182_; uint8_t v___x_5183_; 
v___x_5181_ = ((size_t)0ULL);
v___x_5182_ = lean_usize_of_nat(v___x_5179_);
v___x_5183_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__0(v_fnNames_5162_, v_numSectionVars_5163_, v_x_5166_, v___x_5181_, v___x_5182_);
if (v___x_5183_ == 0)
{
lean_dec_ref(v_x_5166_);
lean_dec_ref(v_x_5165_);
lean_dec_ref(v___x_5164_);
goto v___jp_5170_;
}
else
{
lean_object* v___x_5184_; uint8_t v___x_5185_; lean_object* v___x_5186_; 
v___x_5184_ = l_Lean_Expr_constName_x21(v_x_5165_);
v___x_5185_ = 0;
v___x_5186_ = l_Lean_Environment_find_x3f(v___x_5164_, v___x_5184_, v___x_5185_);
if (lean_obj_tag(v___x_5186_) == 1)
{
lean_object* v_val_5187_; 
v_val_5187_ = lean_ctor_get(v___x_5186_, 0);
lean_inc(v_val_5187_);
lean_dec_ref_known(v___x_5186_, 1);
if (lean_obj_tag(v_val_5187_) == 2)
{
lean_object* v___x_5188_; lean_object* v___x_5189_; lean_object* v___x_5191_; uint8_t v_isShared_5192_; uint8_t v_isSharedCheck_5213_; 
v___x_5188_ = l_Lean_Expr_constLevels_x21(v_x_5165_);
lean_dec_ref(v_x_5165_);
v___x_5189_ = l_Lean_Core_instantiateValueLevelParams(v_val_5187_, v___x_5188_, v___x_5180_, v___y_5167_, v___y_5168_);
v_isSharedCheck_5213_ = !lean_is_exclusive(v_val_5187_);
if (v_isSharedCheck_5213_ == 0)
{
lean_object* v_unused_5214_; 
v_unused_5214_ = lean_ctor_get(v_val_5187_, 0);
lean_dec(v_unused_5214_);
v___x_5191_ = v_val_5187_;
v_isShared_5192_ = v_isSharedCheck_5213_;
goto v_resetjp_5190_;
}
else
{
lean_dec(v_val_5187_);
v___x_5191_ = lean_box(0);
v_isShared_5192_ = v_isSharedCheck_5213_;
goto v_resetjp_5190_;
}
v_resetjp_5190_:
{
if (lean_obj_tag(v___x_5189_) == 0)
{
lean_object* v_a_5193_; lean_object* v___x_5195_; uint8_t v_isShared_5196_; uint8_t v_isSharedCheck_5204_; 
v_a_5193_ = lean_ctor_get(v___x_5189_, 0);
v_isSharedCheck_5204_ = !lean_is_exclusive(v___x_5189_);
if (v_isSharedCheck_5204_ == 0)
{
v___x_5195_ = v___x_5189_;
v_isShared_5196_ = v_isSharedCheck_5204_;
goto v_resetjp_5194_;
}
else
{
lean_inc(v_a_5193_);
lean_dec(v___x_5189_);
v___x_5195_ = lean_box(0);
v_isShared_5196_ = v_isSharedCheck_5204_;
goto v_resetjp_5194_;
}
v_resetjp_5194_:
{
lean_object* v___x_5197_; lean_object* v___x_5199_; 
v___x_5197_ = l_Lean_Expr_betaRev(v_a_5193_, v_x_5166_, v___x_5185_, v___x_5185_);
lean_dec_ref(v_x_5166_);
if (v_isShared_5192_ == 0)
{
lean_ctor_set_tag(v___x_5191_, 1);
lean_ctor_set(v___x_5191_, 0, v___x_5197_);
v___x_5199_ = v___x_5191_;
goto v_reusejp_5198_;
}
else
{
lean_object* v_reuseFailAlloc_5203_; 
v_reuseFailAlloc_5203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5203_, 0, v___x_5197_);
v___x_5199_ = v_reuseFailAlloc_5203_;
goto v_reusejp_5198_;
}
v_reusejp_5198_:
{
lean_object* v___x_5201_; 
if (v_isShared_5196_ == 0)
{
lean_ctor_set(v___x_5195_, 0, v___x_5199_);
v___x_5201_ = v___x_5195_;
goto v_reusejp_5200_;
}
else
{
lean_object* v_reuseFailAlloc_5202_; 
v_reuseFailAlloc_5202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5202_, 0, v___x_5199_);
v___x_5201_ = v_reuseFailAlloc_5202_;
goto v_reusejp_5200_;
}
v_reusejp_5200_:
{
return v___x_5201_;
}
}
}
}
else
{
lean_object* v_a_5205_; lean_object* v___x_5207_; uint8_t v_isShared_5208_; uint8_t v_isSharedCheck_5212_; 
lean_del_object(v___x_5191_);
lean_dec_ref(v_x_5166_);
v_a_5205_ = lean_ctor_get(v___x_5189_, 0);
v_isSharedCheck_5212_ = !lean_is_exclusive(v___x_5189_);
if (v_isSharedCheck_5212_ == 0)
{
v___x_5207_ = v___x_5189_;
v_isShared_5208_ = v_isSharedCheck_5212_;
goto v_resetjp_5206_;
}
else
{
lean_inc(v_a_5205_);
lean_dec(v___x_5189_);
v___x_5207_ = lean_box(0);
v_isShared_5208_ = v_isSharedCheck_5212_;
goto v_resetjp_5206_;
}
v_resetjp_5206_:
{
lean_object* v___x_5210_; 
if (v_isShared_5208_ == 0)
{
v___x_5210_ = v___x_5207_;
goto v_reusejp_5209_;
}
else
{
lean_object* v_reuseFailAlloc_5211_; 
v_reuseFailAlloc_5211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5211_, 0, v_a_5205_);
v___x_5210_ = v_reuseFailAlloc_5211_;
goto v_reusejp_5209_;
}
v_reusejp_5209_:
{
return v___x_5210_;
}
}
}
}
}
else
{
lean_dec(v_val_5187_);
lean_dec_ref(v_x_5166_);
lean_dec_ref(v_x_5165_);
goto v___jp_5170_;
}
}
else
{
lean_dec(v___x_5186_);
lean_dec_ref(v_x_5166_);
lean_dec_ref(v_x_5165_);
goto v___jp_5170_;
}
}
}
}
}
}
v___jp_5170_:
{
lean_object* v___x_5171_; lean_object* v___x_5172_; 
v___x_5171_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_5172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5172_, 0, v___x_5171_);
return v___x_5172_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__1___boxed(lean_object* v_fnNames_5215_, lean_object* v_numSectionVars_5216_, lean_object* v___x_5217_, lean_object* v_x_5218_, lean_object* v_x_5219_, lean_object* v___y_5220_, lean_object* v___y_5221_, lean_object* v___y_5222_){
_start:
{
lean_object* v_res_5223_; 
v_res_5223_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__1(v_fnNames_5215_, v_numSectionVars_5216_, v___x_5217_, v_x_5218_, v_x_5219_, v___y_5220_, v___y_5221_);
lean_dec(v___y_5221_);
lean_dec_ref(v___y_5220_);
lean_dec(v_numSectionVars_5216_);
lean_dec_ref(v_fnNames_5215_);
return v_res_5223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___lam__1(lean_object* v_fnNames_5224_, lean_object* v_numSectionVars_5225_, lean_object* v_env_5226_, lean_object* v_e_5227_, lean_object* v___y_5228_, lean_object* v___y_5229_){
_start:
{
lean_object* v___x_5231_; lean_object* v___x_5232_; lean_object* v___x_5233_; 
v___x_5231_ = l_Lean_Expr_getAppNumArgs(v_e_5227_);
v___x_5232_ = lean_mk_empty_array_with_capacity(v___x_5231_);
lean_dec(v___x_5231_);
v___x_5233_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__1(v_fnNames_5224_, v_numSectionVars_5225_, v_env_5226_, v_e_5227_, v___x_5232_, v___y_5228_, v___y_5229_);
return v___x_5233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___lam__1___boxed(lean_object* v_fnNames_5234_, lean_object* v_numSectionVars_5235_, lean_object* v_env_5236_, lean_object* v_e_5237_, lean_object* v___y_5238_, lean_object* v___y_5239_, lean_object* v___y_5240_){
_start:
{
lean_object* v_res_5241_; 
v_res_5241_ = l_Lean_Meta_unfoldIfArgIsAppOf___lam__1(v_fnNames_5234_, v_numSectionVars_5235_, v_env_5236_, v_e_5237_, v___y_5238_, v___y_5239_);
lean_dec(v___y_5239_);
lean_dec_ref(v___y_5238_);
lean_dec(v_numSectionVars_5235_);
lean_dec_ref(v_fnNames_5234_);
return v_res_5241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___lam__0(lean_object* v_fnNames_5242_, lean_object* v_numSectionVars_5243_, lean_object* v_e_5244_, lean_object* v___f_5245_, lean_object* v___y_5246_, lean_object* v___y_5247_){
_start:
{
lean_object* v___x_5249_; lean_object* v_env_5250_; lean_object* v___f_5251_; lean_object* v___x_5252_; 
v___x_5249_ = lean_st_ref_get(v___y_5247_);
v_env_5250_ = lean_ctor_get(v___x_5249_, 0);
lean_inc_ref(v_env_5250_);
lean_dec(v___x_5249_);
v___f_5251_ = lean_alloc_closure((void*)(l_Lean_Meta_unfoldIfArgIsAppOf___lam__1___boxed), 7, 3);
lean_closure_set(v___f_5251_, 0, v_fnNames_5242_);
lean_closure_set(v___f_5251_, 1, v_numSectionVars_5243_);
lean_closure_set(v___f_5251_, 2, v_env_5250_);
v___x_5252_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_5244_, v___f_5251_, v___f_5245_, v___y_5246_, v___y_5247_);
return v___x_5252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___lam__0___boxed(lean_object* v_fnNames_5253_, lean_object* v_numSectionVars_5254_, lean_object* v_e_5255_, lean_object* v___f_5256_, lean_object* v___y_5257_, lean_object* v___y_5258_, lean_object* v___y_5259_){
_start:
{
lean_object* v_res_5260_; 
v_res_5260_ = l_Lean_Meta_unfoldIfArgIsAppOf___lam__0(v_fnNames_5253_, v_numSectionVars_5254_, v_e_5255_, v___f_5256_, v___y_5257_, v___y_5258_);
lean_dec(v___y_5258_);
lean_dec_ref(v___y_5257_);
return v_res_5260_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0(lean_object* v___y_5261_, uint8_t v_isExporting_5262_, lean_object* v___x_5263_, lean_object* v_a_x3f_5264_){
_start:
{
lean_object* v___x_5266_; lean_object* v_env_5267_; lean_object* v_nextMacroScope_5268_; lean_object* v_ngen_5269_; lean_object* v_auxDeclNGen_5270_; lean_object* v_traceState_5271_; lean_object* v_messages_5272_; lean_object* v_infoState_5273_; lean_object* v_snapshotTasks_5274_; lean_object* v___x_5276_; uint8_t v_isShared_5277_; uint8_t v_isSharedCheck_5285_; 
v___x_5266_ = lean_st_ref_take(v___y_5261_);
v_env_5267_ = lean_ctor_get(v___x_5266_, 0);
v_nextMacroScope_5268_ = lean_ctor_get(v___x_5266_, 1);
v_ngen_5269_ = lean_ctor_get(v___x_5266_, 2);
v_auxDeclNGen_5270_ = lean_ctor_get(v___x_5266_, 3);
v_traceState_5271_ = lean_ctor_get(v___x_5266_, 4);
v_messages_5272_ = lean_ctor_get(v___x_5266_, 6);
v_infoState_5273_ = lean_ctor_get(v___x_5266_, 7);
v_snapshotTasks_5274_ = lean_ctor_get(v___x_5266_, 8);
v_isSharedCheck_5285_ = !lean_is_exclusive(v___x_5266_);
if (v_isSharedCheck_5285_ == 0)
{
lean_object* v_unused_5286_; 
v_unused_5286_ = lean_ctor_get(v___x_5266_, 5);
lean_dec(v_unused_5286_);
v___x_5276_ = v___x_5266_;
v_isShared_5277_ = v_isSharedCheck_5285_;
goto v_resetjp_5275_;
}
else
{
lean_inc(v_snapshotTasks_5274_);
lean_inc(v_infoState_5273_);
lean_inc(v_messages_5272_);
lean_inc(v_traceState_5271_);
lean_inc(v_auxDeclNGen_5270_);
lean_inc(v_ngen_5269_);
lean_inc(v_nextMacroScope_5268_);
lean_inc(v_env_5267_);
lean_dec(v___x_5266_);
v___x_5276_ = lean_box(0);
v_isShared_5277_ = v_isSharedCheck_5285_;
goto v_resetjp_5275_;
}
v_resetjp_5275_:
{
lean_object* v___x_5278_; lean_object* v___x_5280_; 
v___x_5278_ = l_Lean_Environment_setExporting(v_env_5267_, v_isExporting_5262_);
if (v_isShared_5277_ == 0)
{
lean_ctor_set(v___x_5276_, 5, v___x_5263_);
lean_ctor_set(v___x_5276_, 0, v___x_5278_);
v___x_5280_ = v___x_5276_;
goto v_reusejp_5279_;
}
else
{
lean_object* v_reuseFailAlloc_5284_; 
v_reuseFailAlloc_5284_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5284_, 0, v___x_5278_);
lean_ctor_set(v_reuseFailAlloc_5284_, 1, v_nextMacroScope_5268_);
lean_ctor_set(v_reuseFailAlloc_5284_, 2, v_ngen_5269_);
lean_ctor_set(v_reuseFailAlloc_5284_, 3, v_auxDeclNGen_5270_);
lean_ctor_set(v_reuseFailAlloc_5284_, 4, v_traceState_5271_);
lean_ctor_set(v_reuseFailAlloc_5284_, 5, v___x_5263_);
lean_ctor_set(v_reuseFailAlloc_5284_, 6, v_messages_5272_);
lean_ctor_set(v_reuseFailAlloc_5284_, 7, v_infoState_5273_);
lean_ctor_set(v_reuseFailAlloc_5284_, 8, v_snapshotTasks_5274_);
v___x_5280_ = v_reuseFailAlloc_5284_;
goto v_reusejp_5279_;
}
v_reusejp_5279_:
{
lean_object* v___x_5281_; lean_object* v___x_5282_; lean_object* v___x_5283_; 
v___x_5281_ = lean_st_ref_put(v___y_5261_, v___x_5280_);
v___x_5282_ = lean_box(0);
v___x_5283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5283_, 0, v___x_5282_);
return v___x_5283_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0___boxed(lean_object* v___y_5287_, lean_object* v_isExporting_5288_, lean_object* v___x_5289_, lean_object* v_a_x3f_5290_, lean_object* v___y_5291_){
_start:
{
uint8_t v_isExporting_boxed_5292_; lean_object* v_res_5293_; 
v_isExporting_boxed_5292_ = lean_unbox(v_isExporting_5288_);
v_res_5293_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0(v___y_5287_, v_isExporting_boxed_5292_, v___x_5289_, v_a_x3f_5290_);
lean_dec(v_a_x3f_5290_);
lean_dec(v___y_5287_);
return v_res_5293_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg(lean_object* v_x_5294_, uint8_t v_isExporting_5295_, lean_object* v___y_5296_, lean_object* v___y_5297_){
_start:
{
lean_object* v___x_5299_; lean_object* v_env_5300_; lean_object* v___x_5301_; uint8_t v_isModule_5302_; 
v___x_5299_ = lean_st_ref_get(v___y_5297_);
v_env_5300_ = lean_ctor_get(v___x_5299_, 0);
lean_inc_ref(v_env_5300_);
lean_dec(v___x_5299_);
v___x_5301_ = l_Lean_Environment_header(v_env_5300_);
v_isModule_5302_ = lean_ctor_get_uint8(v___x_5301_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_5301_);
if (v_isModule_5302_ == 0)
{
lean_object* v___x_5303_; 
lean_dec_ref(v_env_5300_);
lean_inc(v___y_5297_);
lean_inc_ref(v___y_5296_);
v___x_5303_ = lean_apply_3(v_x_5294_, v___y_5296_, v___y_5297_, lean_box(0));
return v___x_5303_;
}
else
{
uint8_t v_isExporting_5304_; 
v_isExporting_5304_ = lean_ctor_get_uint8(v_env_5300_, sizeof(void*)*8);
lean_dec_ref(v_env_5300_);
if (v_isExporting_5295_ == 0)
{
if (v_isExporting_5304_ == 0)
{
lean_object* v___x_5355_; 
lean_inc(v___y_5297_);
lean_inc_ref(v___y_5296_);
v___x_5355_ = lean_apply_3(v_x_5294_, v___y_5296_, v___y_5297_, lean_box(0));
return v___x_5355_;
}
else
{
goto v___jp_5305_;
}
}
else
{
if (v_isExporting_5304_ == 0)
{
goto v___jp_5305_;
}
else
{
lean_object* v___x_5356_; 
lean_inc(v___y_5297_);
lean_inc_ref(v___y_5296_);
v___x_5356_ = lean_apply_3(v_x_5294_, v___y_5296_, v___y_5297_, lean_box(0));
return v___x_5356_;
}
}
v___jp_5305_:
{
lean_object* v___x_5306_; lean_object* v_env_5307_; lean_object* v_nextMacroScope_5308_; lean_object* v_ngen_5309_; lean_object* v_auxDeclNGen_5310_; lean_object* v_traceState_5311_; lean_object* v_messages_5312_; lean_object* v_infoState_5313_; lean_object* v_snapshotTasks_5314_; lean_object* v___x_5316_; uint8_t v_isShared_5317_; uint8_t v_isSharedCheck_5353_; 
v___x_5306_ = lean_st_ref_take(v___y_5297_);
v_env_5307_ = lean_ctor_get(v___x_5306_, 0);
v_nextMacroScope_5308_ = lean_ctor_get(v___x_5306_, 1);
v_ngen_5309_ = lean_ctor_get(v___x_5306_, 2);
v_auxDeclNGen_5310_ = lean_ctor_get(v___x_5306_, 3);
v_traceState_5311_ = lean_ctor_get(v___x_5306_, 4);
v_messages_5312_ = lean_ctor_get(v___x_5306_, 6);
v_infoState_5313_ = lean_ctor_get(v___x_5306_, 7);
v_snapshotTasks_5314_ = lean_ctor_get(v___x_5306_, 8);
v_isSharedCheck_5353_ = !lean_is_exclusive(v___x_5306_);
if (v_isSharedCheck_5353_ == 0)
{
lean_object* v_unused_5354_; 
v_unused_5354_ = lean_ctor_get(v___x_5306_, 5);
lean_dec(v_unused_5354_);
v___x_5316_ = v___x_5306_;
v_isShared_5317_ = v_isSharedCheck_5353_;
goto v_resetjp_5315_;
}
else
{
lean_inc(v_snapshotTasks_5314_);
lean_inc(v_infoState_5313_);
lean_inc(v_messages_5312_);
lean_inc(v_traceState_5311_);
lean_inc(v_auxDeclNGen_5310_);
lean_inc(v_ngen_5309_);
lean_inc(v_nextMacroScope_5308_);
lean_inc(v_env_5307_);
lean_dec(v___x_5306_);
v___x_5316_ = lean_box(0);
v_isShared_5317_ = v_isSharedCheck_5353_;
goto v_resetjp_5315_;
}
v_resetjp_5315_:
{
lean_object* v___x_5318_; lean_object* v___x_5319_; lean_object* v___x_5321_; 
v___x_5318_ = l_Lean_Environment_setExporting(v_env_5307_, v_isExporting_5295_);
v___x_5319_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2, &l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2);
if (v_isShared_5317_ == 0)
{
lean_ctor_set(v___x_5316_, 5, v___x_5319_);
lean_ctor_set(v___x_5316_, 0, v___x_5318_);
v___x_5321_ = v___x_5316_;
goto v_reusejp_5320_;
}
else
{
lean_object* v_reuseFailAlloc_5352_; 
v_reuseFailAlloc_5352_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5352_, 0, v___x_5318_);
lean_ctor_set(v_reuseFailAlloc_5352_, 1, v_nextMacroScope_5308_);
lean_ctor_set(v_reuseFailAlloc_5352_, 2, v_ngen_5309_);
lean_ctor_set(v_reuseFailAlloc_5352_, 3, v_auxDeclNGen_5310_);
lean_ctor_set(v_reuseFailAlloc_5352_, 4, v_traceState_5311_);
lean_ctor_set(v_reuseFailAlloc_5352_, 5, v___x_5319_);
lean_ctor_set(v_reuseFailAlloc_5352_, 6, v_messages_5312_);
lean_ctor_set(v_reuseFailAlloc_5352_, 7, v_infoState_5313_);
lean_ctor_set(v_reuseFailAlloc_5352_, 8, v_snapshotTasks_5314_);
v___x_5321_ = v_reuseFailAlloc_5352_;
goto v_reusejp_5320_;
}
v_reusejp_5320_:
{
lean_object* v___x_5322_; lean_object* v_r_5323_; 
v___x_5322_ = lean_st_ref_put(v___y_5297_, v___x_5321_);
lean_inc(v___y_5297_);
lean_inc_ref(v___y_5296_);
v_r_5323_ = lean_apply_3(v_x_5294_, v___y_5296_, v___y_5297_, lean_box(0));
if (lean_obj_tag(v_r_5323_) == 0)
{
lean_object* v_a_5324_; lean_object* v___x_5326_; uint8_t v_isShared_5327_; uint8_t v_isSharedCheck_5340_; 
v_a_5324_ = lean_ctor_get(v_r_5323_, 0);
v_isSharedCheck_5340_ = !lean_is_exclusive(v_r_5323_);
if (v_isSharedCheck_5340_ == 0)
{
v___x_5326_ = v_r_5323_;
v_isShared_5327_ = v_isSharedCheck_5340_;
goto v_resetjp_5325_;
}
else
{
lean_inc(v_a_5324_);
lean_dec(v_r_5323_);
v___x_5326_ = lean_box(0);
v_isShared_5327_ = v_isSharedCheck_5340_;
goto v_resetjp_5325_;
}
v_resetjp_5325_:
{
lean_object* v___x_5329_; 
lean_inc(v_a_5324_);
if (v_isShared_5327_ == 0)
{
lean_ctor_set_tag(v___x_5326_, 1);
v___x_5329_ = v___x_5326_;
goto v_reusejp_5328_;
}
else
{
lean_object* v_reuseFailAlloc_5339_; 
v_reuseFailAlloc_5339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5339_, 0, v_a_5324_);
v___x_5329_ = v_reuseFailAlloc_5339_;
goto v_reusejp_5328_;
}
v_reusejp_5328_:
{
lean_object* v___x_5330_; lean_object* v___x_5332_; uint8_t v_isShared_5333_; uint8_t v_isSharedCheck_5337_; 
v___x_5330_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0(v___y_5297_, v_isExporting_5304_, v___x_5319_, v___x_5329_);
lean_dec_ref(v___x_5329_);
v_isSharedCheck_5337_ = !lean_is_exclusive(v___x_5330_);
if (v_isSharedCheck_5337_ == 0)
{
lean_object* v_unused_5338_; 
v_unused_5338_ = lean_ctor_get(v___x_5330_, 0);
lean_dec(v_unused_5338_);
v___x_5332_ = v___x_5330_;
v_isShared_5333_ = v_isSharedCheck_5337_;
goto v_resetjp_5331_;
}
else
{
lean_dec(v___x_5330_);
v___x_5332_ = lean_box(0);
v_isShared_5333_ = v_isSharedCheck_5337_;
goto v_resetjp_5331_;
}
v_resetjp_5331_:
{
lean_object* v___x_5335_; 
if (v_isShared_5333_ == 0)
{
lean_ctor_set(v___x_5332_, 0, v_a_5324_);
v___x_5335_ = v___x_5332_;
goto v_reusejp_5334_;
}
else
{
lean_object* v_reuseFailAlloc_5336_; 
v_reuseFailAlloc_5336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5336_, 0, v_a_5324_);
v___x_5335_ = v_reuseFailAlloc_5336_;
goto v_reusejp_5334_;
}
v_reusejp_5334_:
{
return v___x_5335_;
}
}
}
}
}
else
{
lean_object* v_a_5341_; lean_object* v___x_5342_; lean_object* v___x_5343_; lean_object* v___x_5345_; uint8_t v_isShared_5346_; uint8_t v_isSharedCheck_5350_; 
v_a_5341_ = lean_ctor_get(v_r_5323_, 0);
lean_inc(v_a_5341_);
lean_dec_ref_known(v_r_5323_, 1);
v___x_5342_ = lean_box(0);
v___x_5343_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0(v___y_5297_, v_isExporting_5304_, v___x_5319_, v___x_5342_);
v_isSharedCheck_5350_ = !lean_is_exclusive(v___x_5343_);
if (v_isSharedCheck_5350_ == 0)
{
lean_object* v_unused_5351_; 
v_unused_5351_ = lean_ctor_get(v___x_5343_, 0);
lean_dec(v_unused_5351_);
v___x_5345_ = v___x_5343_;
v_isShared_5346_ = v_isSharedCheck_5350_;
goto v_resetjp_5344_;
}
else
{
lean_dec(v___x_5343_);
v___x_5345_ = lean_box(0);
v_isShared_5346_ = v_isSharedCheck_5350_;
goto v_resetjp_5344_;
}
v_resetjp_5344_:
{
lean_object* v___x_5348_; 
if (v_isShared_5346_ == 0)
{
lean_ctor_set_tag(v___x_5345_, 1);
lean_ctor_set(v___x_5345_, 0, v_a_5341_);
v___x_5348_ = v___x_5345_;
goto v_reusejp_5347_;
}
else
{
lean_object* v_reuseFailAlloc_5349_; 
v_reuseFailAlloc_5349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5349_, 0, v_a_5341_);
v___x_5348_ = v_reuseFailAlloc_5349_;
goto v_reusejp_5347_;
}
v_reusejp_5347_:
{
return v___x_5348_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___boxed(lean_object* v_x_5357_, lean_object* v_isExporting_5358_, lean_object* v___y_5359_, lean_object* v___y_5360_, lean_object* v___y_5361_){
_start:
{
uint8_t v_isExporting_boxed_5362_; lean_object* v_res_5363_; 
v_isExporting_boxed_5362_ = lean_unbox(v_isExporting_5358_);
v_res_5363_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg(v_x_5357_, v_isExporting_boxed_5362_, v___y_5359_, v___y_5360_);
lean_dec(v___y_5360_);
lean_dec_ref(v___y_5359_);
return v_res_5363_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg(lean_object* v_x_5364_, uint8_t v_when_5365_, lean_object* v___y_5366_, lean_object* v___y_5367_){
_start:
{
if (v_when_5365_ == 0)
{
lean_object* v___x_5369_; 
lean_inc(v___y_5367_);
lean_inc_ref(v___y_5366_);
v___x_5369_ = lean_apply_3(v_x_5364_, v___y_5366_, v___y_5367_, lean_box(0));
return v___x_5369_;
}
else
{
uint8_t v___x_5370_; lean_object* v___x_5371_; 
v___x_5370_ = 0;
v___x_5371_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg(v_x_5364_, v___x_5370_, v___y_5366_, v___y_5367_);
return v___x_5371_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg___boxed(lean_object* v_x_5372_, lean_object* v_when_5373_, lean_object* v___y_5374_, lean_object* v___y_5375_, lean_object* v___y_5376_){
_start:
{
uint8_t v_when_boxed_5377_; lean_object* v_res_5378_; 
v_when_boxed_5377_ = lean_unbox(v_when_5373_);
v_res_5378_ = l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg(v_x_5372_, v_when_boxed_5377_, v___y_5374_, v___y_5375_);
lean_dec(v___y_5375_);
lean_dec_ref(v___y_5374_);
return v_res_5378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf(lean_object* v_fnNames_5379_, lean_object* v_numSectionVars_5380_, lean_object* v_e_5381_, lean_object* v_a_5382_, lean_object* v_a_5383_){
_start:
{
lean_object* v___f_5385_; lean_object* v___f_5386_; uint8_t v___x_5387_; lean_object* v___x_5388_; 
v___f_5385_ = ((lean_object*)(l_Lean_Core_betaReduce___closed__1));
v___f_5386_ = lean_alloc_closure((void*)(l_Lean_Meta_unfoldIfArgIsAppOf___lam__0___boxed), 7, 4);
lean_closure_set(v___f_5386_, 0, v_fnNames_5379_);
lean_closure_set(v___f_5386_, 1, v_numSectionVars_5380_);
lean_closure_set(v___f_5386_, 2, v_e_5381_);
lean_closure_set(v___f_5386_, 3, v___f_5385_);
v___x_5387_ = 1;
v___x_5388_ = l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg(v___f_5386_, v___x_5387_, v_a_5382_, v_a_5383_);
return v___x_5388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___boxed(lean_object* v_fnNames_5389_, lean_object* v_numSectionVars_5390_, lean_object* v_e_5391_, lean_object* v_a_5392_, lean_object* v_a_5393_, lean_object* v_a_5394_){
_start:
{
lean_object* v_res_5395_; 
v_res_5395_ = l_Lean_Meta_unfoldIfArgIsAppOf(v_fnNames_5389_, v_numSectionVars_5390_, v_e_5391_, v_a_5392_, v_a_5393_);
lean_dec(v_a_5393_);
lean_dec_ref(v_a_5392_);
return v_res_5395_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2(lean_object* v_00_u03b1_5396_, lean_object* v_x_5397_, uint8_t v_isExporting_5398_, lean_object* v___y_5399_, lean_object* v___y_5400_){
_start:
{
lean_object* v___x_5402_; 
v___x_5402_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg(v_x_5397_, v_isExporting_5398_, v___y_5399_, v___y_5400_);
return v___x_5402_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___boxed(lean_object* v_00_u03b1_5403_, lean_object* v_x_5404_, lean_object* v_isExporting_5405_, lean_object* v___y_5406_, lean_object* v___y_5407_, lean_object* v___y_5408_){
_start:
{
uint8_t v_isExporting_boxed_5409_; lean_object* v_res_5410_; 
v_isExporting_boxed_5409_ = lean_unbox(v_isExporting_5405_);
v_res_5410_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2(v_00_u03b1_5403_, v_x_5404_, v_isExporting_boxed_5409_, v___y_5406_, v___y_5407_);
lean_dec(v___y_5407_);
lean_dec_ref(v___y_5406_);
return v_res_5410_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2(lean_object* v_00_u03b1_5411_, lean_object* v_x_5412_, uint8_t v_when_5413_, lean_object* v___y_5414_, lean_object* v___y_5415_){
_start:
{
lean_object* v___x_5417_; 
v___x_5417_ = l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg(v_x_5412_, v_when_5413_, v___y_5414_, v___y_5415_);
return v___x_5417_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___boxed(lean_object* v_00_u03b1_5418_, lean_object* v_x_5419_, lean_object* v_when_5420_, lean_object* v___y_5421_, lean_object* v___y_5422_, lean_object* v___y_5423_){
_start:
{
uint8_t v_when_boxed_5424_; lean_object* v_res_5425_; 
v_when_boxed_5424_ = lean_unbox(v_when_5420_);
v_res_5425_ = l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2(v_00_u03b1_5418_, v_x_5419_, v_when_boxed_5424_, v___y_5421_, v___y_5422_);
lean_dec(v___y_5422_);
lean_dec_ref(v___y_5421_);
return v_res_5425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___lam__0(lean_object* v_x_5426_, lean_object* v___y_5427_, lean_object* v___y_5428_){
_start:
{
lean_object* v___x_5430_; lean_object* v___x_5431_; 
v___x_5430_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_5431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5431_, 0, v___x_5430_);
return v___x_5431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___lam__0___boxed(lean_object* v_x_5432_, lean_object* v___y_5433_, lean_object* v___y_5434_, lean_object* v___y_5435_){
_start:
{
lean_object* v_res_5436_; 
v_res_5436_ = l_Lean_Meta_eraseInaccessibleAnnotations___lam__0(v_x_5432_, v___y_5433_, v___y_5434_);
lean_dec(v___y_5434_);
lean_dec_ref(v___y_5433_);
lean_dec_ref(v_x_5432_);
return v_res_5436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___lam__1(lean_object* v_e_5437_, lean_object* v___y_5438_, lean_object* v___y_5439_){
_start:
{
lean_object* v___y_5442_; lean_object* v___x_5445_; 
v___x_5445_ = l_Lean_inaccessible_x3f(v_e_5437_);
if (lean_obj_tag(v___x_5445_) == 1)
{
lean_object* v_val_5446_; 
lean_dec_ref(v_e_5437_);
v_val_5446_ = lean_ctor_get(v___x_5445_, 0);
lean_inc(v_val_5446_);
lean_dec_ref_known(v___x_5445_, 1);
v___y_5442_ = v_val_5446_;
goto v___jp_5441_;
}
else
{
lean_dec(v___x_5445_);
v___y_5442_ = v_e_5437_;
goto v___jp_5441_;
}
v___jp_5441_:
{
lean_object* v___x_5443_; lean_object* v___x_5444_; 
v___x_5443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5443_, 0, v___y_5442_);
v___x_5444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5444_, 0, v___x_5443_);
return v___x_5444_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___lam__1___boxed(lean_object* v_e_5447_, lean_object* v___y_5448_, lean_object* v___y_5449_, lean_object* v___y_5450_){
_start:
{
lean_object* v_res_5451_; 
v_res_5451_ = l_Lean_Meta_eraseInaccessibleAnnotations___lam__1(v_e_5447_, v___y_5448_, v___y_5449_);
lean_dec(v___y_5449_);
lean_dec_ref(v___y_5448_);
return v_res_5451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations(lean_object* v_e_5454_, lean_object* v_a_5455_, lean_object* v_a_5456_){
_start:
{
lean_object* v___f_5458_; lean_object* v___f_5459_; lean_object* v___x_5460_; 
v___f_5458_ = ((lean_object*)(l_Lean_Meta_eraseInaccessibleAnnotations___closed__0));
v___f_5459_ = ((lean_object*)(l_Lean_Meta_eraseInaccessibleAnnotations___closed__1));
v___x_5460_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_5454_, v___f_5458_, v___f_5459_, v_a_5455_, v_a_5456_);
return v___x_5460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___boxed(lean_object* v_e_5461_, lean_object* v_a_5462_, lean_object* v_a_5463_, lean_object* v_a_5464_){
_start:
{
lean_object* v_res_5465_; 
v_res_5465_ = l_Lean_Meta_eraseInaccessibleAnnotations(v_e_5461_, v_a_5462_, v_a_5463_);
lean_dec(v_a_5463_);
lean_dec_ref(v_a_5462_);
return v_res_5465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_erasePatternRefAnnotations___lam__1(lean_object* v_e_5466_, lean_object* v___y_5467_, lean_object* v___y_5468_){
_start:
{
lean_object* v___y_5471_; lean_object* v___x_5474_; 
v___x_5474_ = l_Lean_patternWithRef_x3f(v_e_5466_);
if (lean_obj_tag(v___x_5474_) == 1)
{
lean_object* v_val_5475_; lean_object* v_snd_5476_; 
lean_dec_ref(v_e_5466_);
v_val_5475_ = lean_ctor_get(v___x_5474_, 0);
lean_inc(v_val_5475_);
lean_dec_ref_known(v___x_5474_, 1);
v_snd_5476_ = lean_ctor_get(v_val_5475_, 1);
lean_inc(v_snd_5476_);
lean_dec(v_val_5475_);
v___y_5471_ = v_snd_5476_;
goto v___jp_5470_;
}
else
{
lean_dec(v___x_5474_);
v___y_5471_ = v_e_5466_;
goto v___jp_5470_;
}
v___jp_5470_:
{
lean_object* v___x_5472_; lean_object* v___x_5473_; 
v___x_5472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5472_, 0, v___y_5471_);
v___x_5473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5473_, 0, v___x_5472_);
return v___x_5473_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_erasePatternRefAnnotations___lam__1___boxed(lean_object* v_e_5477_, lean_object* v___y_5478_, lean_object* v___y_5479_, lean_object* v___y_5480_){
_start:
{
lean_object* v_res_5481_; 
v_res_5481_ = l_Lean_Meta_erasePatternRefAnnotations___lam__1(v_e_5477_, v___y_5478_, v___y_5479_);
lean_dec(v___y_5479_);
lean_dec_ref(v___y_5478_);
return v_res_5481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_erasePatternRefAnnotations(lean_object* v_e_5483_, lean_object* v_a_5484_, lean_object* v_a_5485_){
_start:
{
lean_object* v___f_5487_; lean_object* v___f_5488_; lean_object* v___x_5489_; 
v___f_5487_ = ((lean_object*)(l_Lean_Meta_eraseInaccessibleAnnotations___closed__0));
v___f_5488_ = ((lean_object*)(l_Lean_Meta_erasePatternRefAnnotations___closed__0));
v___x_5489_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_5483_, v___f_5487_, v___f_5488_, v_a_5484_, v_a_5485_);
return v___x_5489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_erasePatternRefAnnotations___boxed(lean_object* v_e_5490_, lean_object* v_a_5491_, lean_object* v_a_5492_, lean_object* v_a_5493_){
_start:
{
lean_object* v_res_5494_; 
v_res_5494_ = l_Lean_Meta_erasePatternRefAnnotations(v_e_5490_, v_a_5491_, v_a_5492_);
lean_dec(v_a_5492_);
lean_dec_ref(v_a_5491_);
return v_res_5494_;
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
