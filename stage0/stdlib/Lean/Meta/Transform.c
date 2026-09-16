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
lean_object* v___y_1099_; lean_object* v___y_1109_; lean_object* v___y_1110_; lean_object* v___y_1111_; lean_object* v___y_1112_; lean_object* v___y_1113_; lean_object* v___y_1114_; lean_object* v___y_1115_; lean_object* v___y_1116_; lean_object* v___y_1117_; uint8_t v___y_1118_; lean_object* v___y_1119_; uint8_t v___y_1120_; lean_object* v___y_1121_; lean_object* v___y_1122_; lean_object* v___y_1123_; lean_object* v___y_1124_; lean_object* v_fileName_1129_; lean_object* v_fileMap_1130_; lean_object* v_options_1131_; lean_object* v_currRecDepth_1132_; lean_object* v_maxRecDepth_1133_; lean_object* v_ref_1134_; lean_object* v_currNamespace_1135_; lean_object* v_openDecls_1136_; lean_object* v_initHeartbeats_1137_; lean_object* v_maxHeartbeats_1138_; lean_object* v_quotContext_1139_; lean_object* v_currMacroScope_1140_; uint8_t v_diag_1141_; lean_object* v_cancelTk_x3f_1142_; uint8_t v_suppressElabErrors_1143_; lean_object* v_inheritedTraceOptions_1144_; 
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
v___x_1126_ = lean_nat_add(v___y_1114_, v___x_1125_);
lean_inc_ref(v___y_1115_);
lean_inc(v___y_1112_);
lean_inc(v___y_1109_);
lean_inc(v___y_1123_);
lean_inc(v___y_1117_);
lean_inc(v___y_1124_);
lean_inc(v___y_1122_);
lean_inc(v___y_1110_);
lean_inc(v___y_1116_);
lean_inc_ref(v___y_1119_);
lean_inc_ref(v___y_1113_);
lean_inc_ref(v___y_1111_);
v___x_1127_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1127_, 0, v___y_1111_);
lean_ctor_set(v___x_1127_, 1, v___y_1113_);
lean_ctor_set(v___x_1127_, 2, v___y_1119_);
lean_ctor_set(v___x_1127_, 3, v___x_1126_);
lean_ctor_set(v___x_1127_, 4, v___y_1116_);
lean_ctor_set(v___x_1127_, 5, v___y_1121_);
lean_ctor_set(v___x_1127_, 6, v___y_1110_);
lean_ctor_set(v___x_1127_, 7, v___y_1122_);
lean_ctor_set(v___x_1127_, 8, v___y_1124_);
lean_ctor_set(v___x_1127_, 9, v___y_1117_);
lean_ctor_set(v___x_1127_, 10, v___y_1123_);
lean_ctor_set(v___x_1127_, 11, v___y_1109_);
lean_ctor_set(v___x_1127_, 12, v___y_1112_);
lean_ctor_set(v___x_1127_, 13, v___y_1115_);
lean_ctor_set_uint8(v___x_1127_, sizeof(void*)*14, v___y_1120_);
lean_ctor_set_uint8(v___x_1127_, sizeof(void*)*14 + 1, v___y_1118_);
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
v___y_1109_ = v_currMacroScope_1140_;
v___y_1110_ = v_currNamespace_1135_;
v___y_1111_ = v_fileName_1129_;
v___y_1112_ = v_cancelTk_x3f_1142_;
v___y_1113_ = v_fileMap_1130_;
v___y_1114_ = v_currRecDepth_1132_;
v___y_1115_ = v_inheritedTraceOptions_1144_;
v___y_1116_ = v_maxRecDepth_1133_;
v___y_1117_ = v_maxHeartbeats_1138_;
v___y_1118_ = v_suppressElabErrors_1143_;
v___y_1119_ = v_options_1131_;
v___y_1120_ = v_diag_1141_;
v___y_1121_ = v_ref_1134_;
v___y_1122_ = v_openDecls_1136_;
v___y_1123_ = v_quotContext_1139_;
v___y_1124_ = v_initHeartbeats_1137_;
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
v___y_1109_ = v_currMacroScope_1140_;
v___y_1110_ = v_currNamespace_1135_;
v___y_1111_ = v_fileName_1129_;
v___y_1112_ = v_cancelTk_x3f_1142_;
v___y_1113_ = v_fileMap_1130_;
v___y_1114_ = v_currRecDepth_1132_;
v___y_1115_ = v_inheritedTraceOptions_1144_;
v___y_1116_ = v_maxRecDepth_1133_;
v___y_1117_ = v_maxHeartbeats_1138_;
v___y_1118_ = v_suppressElabErrors_1143_;
v___y_1119_ = v_options_1131_;
v___y_1120_ = v_diag_1141_;
v___y_1121_ = v_ref_1134_;
v___y_1122_ = v_openDecls_1136_;
v___y_1123_ = v_quotContext_1139_;
v___y_1124_ = v_initHeartbeats_1137_;
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
v___x_1311_ = lean_st_ref_put(v_a_1305_, v___x_1310_);
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
lean_dec_ref_known(v___x_1363_, 1);
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
lean_dec_ref_known(v_x_1381_, 2);
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
lean_dec_ref_known(v___x_1394_, 1);
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
lean_dec_ref_known(v___x_1398_, 1);
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
lean_object* v___x_1418_; 
v___x_1418_ = l_Lean_Core_checkSystem(v___x_1410_, v___y_1415_, v___y_1416_);
if (lean_obj_tag(v___x_1418_) == 0)
{
lean_object* v___x_1419_; 
lean_dec_ref_known(v___x_1418_, 1);
lean_inc_ref(v_pre_1411_);
lean_inc(v___y_1416_);
lean_inc_ref(v___y_1415_);
lean_inc_ref(v_e_1412_);
v___x_1419_ = lean_apply_4(v_pre_1411_, v_e_1412_, v___y_1415_, v___y_1416_, lean_box(0));
if (lean_obj_tag(v___x_1419_) == 0)
{
lean_object* v_a_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1535_; 
v_a_1420_ = lean_ctor_get(v___x_1419_, 0);
v_isSharedCheck_1535_ = !lean_is_exclusive(v___x_1419_);
if (v_isSharedCheck_1535_ == 0)
{
v___x_1422_ = v___x_1419_;
v_isShared_1423_ = v_isSharedCheck_1535_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_a_1420_);
lean_dec(v___x_1419_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1535_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
lean_object* v___y_1425_; 
switch(lean_obj_tag(v_a_1420_))
{
case 0:
{
lean_object* v_e_1525_; lean_object* v___x_1527_; 
lean_dec_ref(v_post_1413_);
lean_dec_ref(v_e_1412_);
lean_dec_ref(v_pre_1411_);
v_e_1525_ = lean_ctor_get(v_a_1420_, 0);
lean_inc_ref(v_e_1525_);
lean_dec_ref_known(v_a_1420_, 1);
if (v_isShared_1423_ == 0)
{
lean_ctor_set(v___x_1422_, 0, v_e_1525_);
v___x_1527_ = v___x_1422_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v_e_1525_);
v___x_1527_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
return v___x_1527_;
}
}
case 1:
{
lean_object* v_e_1529_; lean_object* v___x_1530_; 
lean_del_object(v___x_1422_);
lean_dec_ref(v_e_1412_);
v_e_1529_ = lean_ctor_get(v_a_1420_, 0);
lean_inc_ref(v_e_1529_);
lean_dec_ref_known(v_a_1420_, 1);
lean_inc_ref(v_post_1413_);
lean_inc_ref(v_pre_1411_);
v___x_1530_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1411_, v_post_1413_, v_e_1529_, v___y_1414_, v___y_1415_, v___y_1416_);
if (lean_obj_tag(v___x_1530_) == 0)
{
lean_object* v_a_1531_; lean_object* v___x_1532_; 
v_a_1531_ = lean_ctor_get(v___x_1530_, 0);
lean_inc(v_a_1531_);
lean_dec_ref_known(v___x_1530_, 1);
v___x_1532_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1411_, v_post_1413_, v_a_1531_, v___y_1414_, v___y_1415_, v___y_1416_);
return v___x_1532_;
}
else
{
lean_dec_ref(v_post_1413_);
lean_dec_ref(v_pre_1411_);
return v___x_1530_;
}
}
default: 
{
lean_object* v_e_x3f_1533_; 
lean_del_object(v___x_1422_);
v_e_x3f_1533_ = lean_ctor_get(v_a_1420_, 0);
lean_inc(v_e_x3f_1533_);
lean_dec_ref_known(v_a_1420_, 1);
if (lean_obj_tag(v_e_x3f_1533_) == 0)
{
v___y_1425_ = v_e_1412_;
goto v___jp_1424_;
}
else
{
lean_object* v_val_1534_; 
lean_dec_ref(v_e_1412_);
v_val_1534_ = lean_ctor_get(v_e_x3f_1533_, 0);
lean_inc(v_val_1534_);
lean_dec_ref_known(v_e_x3f_1533_, 1);
v___y_1425_ = v_val_1534_;
goto v___jp_1424_;
}
}
}
v___jp_1424_:
{
switch(lean_obj_tag(v___y_1425_))
{
case 7:
{
lean_object* v_binderName_1426_; lean_object* v_binderType_1427_; lean_object* v_body_1428_; uint8_t v_binderInfo_1429_; lean_object* v___x_1430_; 
v_binderName_1426_ = lean_ctor_get(v___y_1425_, 0);
v_binderType_1427_ = lean_ctor_get(v___y_1425_, 1);
v_body_1428_ = lean_ctor_get(v___y_1425_, 2);
v_binderInfo_1429_ = lean_ctor_get_uint8(v___y_1425_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1427_);
lean_inc_ref(v_post_1413_);
lean_inc_ref(v_pre_1411_);
v___x_1430_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1411_, v_post_1413_, v_binderType_1427_, v___y_1414_, v___y_1415_, v___y_1416_);
if (lean_obj_tag(v___x_1430_) == 0)
{
lean_object* v_a_1431_; lean_object* v___x_1432_; 
v_a_1431_ = lean_ctor_get(v___x_1430_, 0);
lean_inc(v_a_1431_);
lean_dec_ref_known(v___x_1430_, 1);
lean_inc_ref(v_body_1428_);
lean_inc_ref(v_post_1413_);
lean_inc_ref(v_pre_1411_);
v___x_1432_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1411_, v_post_1413_, v_body_1428_, v___y_1414_, v___y_1415_, v___y_1416_);
if (lean_obj_tag(v___x_1432_) == 0)
{
lean_object* v_a_1433_; size_t v___x_1434_; size_t v___x_1435_; uint8_t v___x_1436_; 
v_a_1433_ = lean_ctor_get(v___x_1432_, 0);
lean_inc(v_a_1433_);
lean_dec_ref_known(v___x_1432_, 1);
v___x_1434_ = lean_ptr_addr(v_binderType_1427_);
v___x_1435_ = lean_ptr_addr(v_a_1431_);
v___x_1436_ = lean_usize_dec_eq(v___x_1434_, v___x_1435_);
if (v___x_1436_ == 0)
{
lean_object* v___x_1437_; lean_object* v___x_1438_; 
lean_inc(v_binderName_1426_);
lean_dec_ref_known(v___y_1425_, 3);
v___x_1437_ = l_Lean_Expr_forallE___override(v_binderName_1426_, v_a_1431_, v_a_1433_, v_binderInfo_1429_);
v___x_1438_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1411_, v_post_1413_, v___x_1437_, v___y_1414_, v___y_1415_, v___y_1416_);
return v___x_1438_;
}
else
{
size_t v___x_1439_; size_t v___x_1440_; uint8_t v___x_1441_; 
v___x_1439_ = lean_ptr_addr(v_body_1428_);
v___x_1440_ = lean_ptr_addr(v_a_1433_);
v___x_1441_ = lean_usize_dec_eq(v___x_1439_, v___x_1440_);
if (v___x_1441_ == 0)
{
lean_object* v___x_1442_; lean_object* v___x_1443_; 
lean_inc(v_binderName_1426_);
lean_dec_ref_known(v___y_1425_, 3);
v___x_1442_ = l_Lean_Expr_forallE___override(v_binderName_1426_, v_a_1431_, v_a_1433_, v_binderInfo_1429_);
v___x_1443_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1411_, v_post_1413_, v___x_1442_, v___y_1414_, v___y_1415_, v___y_1416_);
return v___x_1443_;
}
else
{
uint8_t v___x_1444_; 
v___x_1444_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1429_, v_binderInfo_1429_);
if (v___x_1444_ == 0)
{
lean_object* v___x_1445_; lean_object* v___x_1446_; 
lean_inc(v_binderName_1426_);
lean_dec_ref_known(v___y_1425_, 3);
v___x_1445_ = l_Lean_Expr_forallE___override(v_binderName_1426_, v_a_1431_, v_a_1433_, v_binderInfo_1429_);
v___x_1446_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1411_, v_post_1413_, v___x_1445_, v___y_1414_, v___y_1415_, v___y_1416_);
return v___x_1446_;
}
else
{
lean_object* v___x_1447_; 
lean_dec(v_a_1433_);
lean_dec(v_a_1431_);
v___x_1447_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1411_, v_post_1413_, v___y_1425_, v___y_1414_, v___y_1415_, v___y_1416_);
return v___x_1447_;
}
}
}
}
else
{
lean_dec(v_a_1431_);
lean_dec_ref_known(v___y_1425_, 3);
lean_dec_ref(v_post_1413_);
lean_dec_ref(v_pre_1411_);
return v___x_1432_;
}
}
else
{
lean_dec_ref_known(v___y_1425_, 3);
lean_dec_ref(v_post_1413_);
lean_dec_ref(v_pre_1411_);
return v___x_1430_;
}
}
case 6:
{
lean_object* v_binderName_1448_; lean_object* v_binderType_1449_; lean_object* v_body_1450_; uint8_t v_binderInfo_1451_; lean_object* v___x_1452_; 
v_binderName_1448_ = lean_ctor_get(v___y_1425_, 0);
v_binderType_1449_ = lean_ctor_get(v___y_1425_, 1);
v_body_1450_ = lean_ctor_get(v___y_1425_, 2);
v_binderInfo_1451_ = lean_ctor_get_uint8(v___y_1425_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1449_);
lean_inc_ref(v_post_1413_);
lean_inc_ref(v_pre_1411_);
v___x_1452_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1411_, v_post_1413_, v_binderType_1449_, v___y_1414_, v___y_1415_, v___y_1416_);
if (lean_obj_tag(v___x_1452_) == 0)
{
lean_object* v_a_1453_; lean_object* v___x_1454_; 
v_a_1453_ = lean_ctor_get(v___x_1452_, 0);
lean_inc(v_a_1453_);
lean_dec_ref_known(v___x_1452_, 1);
lean_inc_ref(v_body_1450_);
lean_inc_ref(v_post_1413_);
lean_inc_ref(v_pre_1411_);
v___x_1454_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1411_, v_post_1413_, v_body_1450_, v___y_1414_, v___y_1415_, v___y_1416_);
if (lean_obj_tag(v___x_1454_) == 0)
{
lean_object* v_a_1455_; size_t v___x_1456_; size_t v___x_1457_; uint8_t v___x_1458_; 
v_a_1455_ = lean_ctor_get(v___x_1454_, 0);
lean_inc(v_a_1455_);
lean_dec_ref_known(v___x_1454_, 1);
v___x_1456_ = lean_ptr_addr(v_binderType_1449_);
v___x_1457_ = lean_ptr_addr(v_a_1453_);
v___x_1458_ = lean_usize_dec_eq(v___x_1456_, v___x_1457_);
if (v___x_1458_ == 0)
{
lean_object* v___x_1459_; lean_object* v___x_1460_; 
lean_inc(v_binderName_1448_);
lean_dec_ref_known(v___y_1425_, 3);
v___x_1459_ = l_Lean_Expr_lam___override(v_binderName_1448_, v_a_1453_, v_a_1455_, v_binderInfo_1451_);
v___x_1460_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1411_, v_post_1413_, v___x_1459_, v___y_1414_, v___y_1415_, v___y_1416_);
return v___x_1460_;
}
else
{
size_t v___x_1461_; size_t v___x_1462_; uint8_t v___x_1463_; 
v___x_1461_ = lean_ptr_addr(v_body_1450_);
v___x_1462_ = lean_ptr_addr(v_a_1455_);
v___x_1463_ = lean_usize_dec_eq(v___x_1461_, v___x_1462_);
if (v___x_1463_ == 0)
{
lean_object* v___x_1464_; lean_object* v___x_1465_; 
lean_inc(v_binderName_1448_);
lean_dec_ref_known(v___y_1425_, 3);
v___x_1464_ = l_Lean_Expr_lam___override(v_binderName_1448_, v_a_1453_, v_a_1455_, v_binderInfo_1451_);
v___x_1465_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1411_, v_post_1413_, v___x_1464_, v___y_1414_, v___y_1415_, v___y_1416_);
return v___x_1465_;
}
else
{
uint8_t v___x_1466_; 
v___x_1466_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1451_, v_binderInfo_1451_);
if (v___x_1466_ == 0)
{
lean_object* v___x_1467_; lean_object* v___x_1468_; 
lean_inc(v_binderName_1448_);
lean_dec_ref_known(v___y_1425_, 3);
v___x_1467_ = l_Lean_Expr_lam___override(v_binderName_1448_, v_a_1453_, v_a_1455_, v_binderInfo_1451_);
v___x_1468_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1411_, v_post_1413_, v___x_1467_, v___y_1414_, v___y_1415_, v___y_1416_);
return v___x_1468_;
}
else
{
lean_object* v___x_1469_; 
lean_dec(v_a_1455_);
lean_dec(v_a_1453_);
v___x_1469_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1411_, v_post_1413_, v___y_1425_, v___y_1414_, v___y_1415_, v___y_1416_);
return v___x_1469_;
}
}
}
}
else
{
lean_dec(v_a_1453_);
lean_dec_ref_known(v___y_1425_, 3);
lean_dec_ref(v_post_1413_);
lean_dec_ref(v_pre_1411_);
return v___x_1454_;
}
}
else
{
lean_dec_ref_known(v___y_1425_, 3);
lean_dec_ref(v_post_1413_);
lean_dec_ref(v_pre_1411_);
return v___x_1452_;
}
}
case 8:
{
lean_object* v_declName_1470_; lean_object* v_type_1471_; lean_object* v_value_1472_; lean_object* v_body_1473_; uint8_t v_nondep_1474_; lean_object* v___x_1475_; 
v_declName_1470_ = lean_ctor_get(v___y_1425_, 0);
v_type_1471_ = lean_ctor_get(v___y_1425_, 1);
v_value_1472_ = lean_ctor_get(v___y_1425_, 2);
v_body_1473_ = lean_ctor_get(v___y_1425_, 3);
v_nondep_1474_ = lean_ctor_get_uint8(v___y_1425_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_1471_);
lean_inc_ref(v_post_1413_);
lean_inc_ref(v_pre_1411_);
v___x_1475_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1411_, v_post_1413_, v_type_1471_, v___y_1414_, v___y_1415_, v___y_1416_);
if (lean_obj_tag(v___x_1475_) == 0)
{
lean_object* v_a_1476_; lean_object* v___x_1477_; 
v_a_1476_ = lean_ctor_get(v___x_1475_, 0);
lean_inc(v_a_1476_);
lean_dec_ref_known(v___x_1475_, 1);
lean_inc_ref(v_value_1472_);
lean_inc_ref(v_post_1413_);
lean_inc_ref(v_pre_1411_);
v___x_1477_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1411_, v_post_1413_, v_value_1472_, v___y_1414_, v___y_1415_, v___y_1416_);
if (lean_obj_tag(v___x_1477_) == 0)
{
lean_object* v_a_1478_; lean_object* v___x_1479_; 
v_a_1478_ = lean_ctor_get(v___x_1477_, 0);
lean_inc(v_a_1478_);
lean_dec_ref_known(v___x_1477_, 1);
lean_inc_ref(v_body_1473_);
lean_inc_ref(v_post_1413_);
lean_inc_ref(v_pre_1411_);
v___x_1479_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1411_, v_post_1413_, v_body_1473_, v___y_1414_, v___y_1415_, v___y_1416_);
if (lean_obj_tag(v___x_1479_) == 0)
{
lean_object* v_a_1480_; size_t v___x_1481_; size_t v___x_1482_; uint8_t v___x_1483_; 
v_a_1480_ = lean_ctor_get(v___x_1479_, 0);
lean_inc(v_a_1480_);
lean_dec_ref_known(v___x_1479_, 1);
v___x_1481_ = lean_ptr_addr(v_type_1471_);
v___x_1482_ = lean_ptr_addr(v_a_1476_);
v___x_1483_ = lean_usize_dec_eq(v___x_1481_, v___x_1482_);
if (v___x_1483_ == 0)
{
lean_object* v___x_1484_; lean_object* v___x_1485_; 
lean_inc(v_declName_1470_);
lean_dec_ref_known(v___y_1425_, 4);
v___x_1484_ = l_Lean_Expr_letE___override(v_declName_1470_, v_a_1476_, v_a_1478_, v_a_1480_, v_nondep_1474_);
v___x_1485_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1411_, v_post_1413_, v___x_1484_, v___y_1414_, v___y_1415_, v___y_1416_);
return v___x_1485_;
}
else
{
size_t v___x_1486_; size_t v___x_1487_; uint8_t v___x_1488_; 
v___x_1486_ = lean_ptr_addr(v_value_1472_);
v___x_1487_ = lean_ptr_addr(v_a_1478_);
v___x_1488_ = lean_usize_dec_eq(v___x_1486_, v___x_1487_);
if (v___x_1488_ == 0)
{
lean_object* v___x_1489_; lean_object* v___x_1490_; 
lean_inc(v_declName_1470_);
lean_dec_ref_known(v___y_1425_, 4);
v___x_1489_ = l_Lean_Expr_letE___override(v_declName_1470_, v_a_1476_, v_a_1478_, v_a_1480_, v_nondep_1474_);
v___x_1490_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1411_, v_post_1413_, v___x_1489_, v___y_1414_, v___y_1415_, v___y_1416_);
return v___x_1490_;
}
else
{
size_t v___x_1491_; size_t v___x_1492_; uint8_t v___x_1493_; 
v___x_1491_ = lean_ptr_addr(v_body_1473_);
v___x_1492_ = lean_ptr_addr(v_a_1480_);
v___x_1493_ = lean_usize_dec_eq(v___x_1491_, v___x_1492_);
if (v___x_1493_ == 0)
{
lean_object* v___x_1494_; lean_object* v___x_1495_; 
lean_inc(v_declName_1470_);
lean_dec_ref_known(v___y_1425_, 4);
v___x_1494_ = l_Lean_Expr_letE___override(v_declName_1470_, v_a_1476_, v_a_1478_, v_a_1480_, v_nondep_1474_);
v___x_1495_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1411_, v_post_1413_, v___x_1494_, v___y_1414_, v___y_1415_, v___y_1416_);
return v___x_1495_;
}
else
{
lean_object* v___x_1496_; 
lean_dec(v_a_1480_);
lean_dec(v_a_1478_);
lean_dec(v_a_1476_);
v___x_1496_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1411_, v_post_1413_, v___y_1425_, v___y_1414_, v___y_1415_, v___y_1416_);
return v___x_1496_;
}
}
}
}
else
{
lean_dec(v_a_1478_);
lean_dec(v_a_1476_);
lean_dec_ref_known(v___y_1425_, 4);
lean_dec_ref(v_post_1413_);
lean_dec_ref(v_pre_1411_);
return v___x_1479_;
}
}
else
{
lean_dec(v_a_1476_);
lean_dec_ref_known(v___y_1425_, 4);
lean_dec_ref(v_post_1413_);
lean_dec_ref(v_pre_1411_);
return v___x_1477_;
}
}
else
{
lean_dec_ref_known(v___y_1425_, 4);
lean_dec_ref(v_post_1413_);
lean_dec_ref(v_pre_1411_);
return v___x_1475_;
}
}
case 5:
{
lean_object* v_dummy_1497_; lean_object* v_nargs_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; 
v_dummy_1497_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_1498_ = l_Lean_Expr_getAppNumArgs(v___y_1425_);
lean_inc(v_nargs_1498_);
v___x_1499_ = lean_mk_array(v_nargs_1498_, v_dummy_1497_);
v___x_1500_ = lean_unsigned_to_nat(1u);
v___x_1501_ = lean_nat_sub(v_nargs_1498_, v___x_1500_);
lean_dec(v_nargs_1498_);
v___x_1502_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__4(v_pre_1411_, v_post_1413_, v___y_1425_, v___x_1499_, v___x_1501_, v___y_1414_, v___y_1415_, v___y_1416_);
return v___x_1502_;
}
case 10:
{
lean_object* v_data_1503_; lean_object* v_expr_1504_; lean_object* v___x_1505_; 
v_data_1503_ = lean_ctor_get(v___y_1425_, 0);
v_expr_1504_ = lean_ctor_get(v___y_1425_, 1);
lean_inc_ref(v_expr_1504_);
lean_inc_ref(v_post_1413_);
lean_inc_ref(v_pre_1411_);
v___x_1505_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1411_, v_post_1413_, v_expr_1504_, v___y_1414_, v___y_1415_, v___y_1416_);
if (lean_obj_tag(v___x_1505_) == 0)
{
lean_object* v_a_1506_; size_t v___x_1507_; size_t v___x_1508_; uint8_t v___x_1509_; 
v_a_1506_ = lean_ctor_get(v___x_1505_, 0);
lean_inc(v_a_1506_);
lean_dec_ref_known(v___x_1505_, 1);
v___x_1507_ = lean_ptr_addr(v_expr_1504_);
v___x_1508_ = lean_ptr_addr(v_a_1506_);
v___x_1509_ = lean_usize_dec_eq(v___x_1507_, v___x_1508_);
if (v___x_1509_ == 0)
{
lean_object* v___x_1510_; lean_object* v___x_1511_; 
lean_inc(v_data_1503_);
lean_dec_ref_known(v___y_1425_, 2);
v___x_1510_ = l_Lean_Expr_mdata___override(v_data_1503_, v_a_1506_);
v___x_1511_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1411_, v_post_1413_, v___x_1510_, v___y_1414_, v___y_1415_, v___y_1416_);
return v___x_1511_;
}
else
{
lean_object* v___x_1512_; 
lean_dec(v_a_1506_);
v___x_1512_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1411_, v_post_1413_, v___y_1425_, v___y_1414_, v___y_1415_, v___y_1416_);
return v___x_1512_;
}
}
else
{
lean_dec_ref_known(v___y_1425_, 2);
lean_dec_ref(v_post_1413_);
lean_dec_ref(v_pre_1411_);
return v___x_1505_;
}
}
case 11:
{
lean_object* v_typeName_1513_; lean_object* v_idx_1514_; lean_object* v_struct_1515_; lean_object* v___x_1516_; 
v_typeName_1513_ = lean_ctor_get(v___y_1425_, 0);
v_idx_1514_ = lean_ctor_get(v___y_1425_, 1);
v_struct_1515_ = lean_ctor_get(v___y_1425_, 2);
lean_inc_ref(v_struct_1515_);
lean_inc_ref(v_post_1413_);
lean_inc_ref(v_pre_1411_);
v___x_1516_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1411_, v_post_1413_, v_struct_1515_, v___y_1414_, v___y_1415_, v___y_1416_);
if (lean_obj_tag(v___x_1516_) == 0)
{
lean_object* v_a_1517_; size_t v___x_1518_; size_t v___x_1519_; uint8_t v___x_1520_; 
v_a_1517_ = lean_ctor_get(v___x_1516_, 0);
lean_inc(v_a_1517_);
lean_dec_ref_known(v___x_1516_, 1);
v___x_1518_ = lean_ptr_addr(v_struct_1515_);
v___x_1519_ = lean_ptr_addr(v_a_1517_);
v___x_1520_ = lean_usize_dec_eq(v___x_1518_, v___x_1519_);
if (v___x_1520_ == 0)
{
lean_object* v___x_1521_; lean_object* v___x_1522_; 
lean_inc(v_idx_1514_);
lean_inc(v_typeName_1513_);
lean_dec_ref_known(v___y_1425_, 3);
v___x_1521_ = l_Lean_Expr_proj___override(v_typeName_1513_, v_idx_1514_, v_a_1517_);
v___x_1522_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1411_, v_post_1413_, v___x_1521_, v___y_1414_, v___y_1415_, v___y_1416_);
return v___x_1522_;
}
else
{
lean_object* v___x_1523_; 
lean_dec(v_a_1517_);
v___x_1523_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1411_, v_post_1413_, v___y_1425_, v___y_1414_, v___y_1415_, v___y_1416_);
return v___x_1523_;
}
}
else
{
lean_dec_ref_known(v___y_1425_, 3);
lean_dec_ref(v_post_1413_);
lean_dec_ref(v_pre_1411_);
return v___x_1516_;
}
}
default: 
{
lean_object* v___x_1524_; 
v___x_1524_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1411_, v_post_1413_, v___y_1425_, v___y_1414_, v___y_1415_, v___y_1416_);
return v___x_1524_;
}
}
}
}
}
else
{
lean_object* v_a_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1543_; 
lean_dec_ref(v_post_1413_);
lean_dec_ref(v_e_1412_);
lean_dec_ref(v_pre_1411_);
v_a_1536_ = lean_ctor_get(v___x_1419_, 0);
v_isSharedCheck_1543_ = !lean_is_exclusive(v___x_1419_);
if (v_isSharedCheck_1543_ == 0)
{
v___x_1538_ = v___x_1419_;
v_isShared_1539_ = v_isSharedCheck_1543_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_a_1536_);
lean_dec(v___x_1419_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1543_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
lean_object* v___x_1541_; 
if (v_isShared_1539_ == 0)
{
v___x_1541_ = v___x_1538_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v_a_1536_);
v___x_1541_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
return v___x_1541_;
}
}
}
}
else
{
lean_object* v_a_1544_; lean_object* v___x_1546_; uint8_t v_isShared_1547_; uint8_t v_isSharedCheck_1551_; 
lean_dec_ref(v_post_1413_);
lean_dec_ref(v_e_1412_);
lean_dec_ref(v_pre_1411_);
v_a_1544_ = lean_ctor_get(v___x_1418_, 0);
v_isSharedCheck_1551_ = !lean_is_exclusive(v___x_1418_);
if (v_isSharedCheck_1551_ == 0)
{
v___x_1546_ = v___x_1418_;
v_isShared_1547_ = v_isSharedCheck_1551_;
goto v_resetjp_1545_;
}
else
{
lean_inc(v_a_1544_);
lean_dec(v___x_1418_);
v___x_1546_ = lean_box(0);
v_isShared_1547_ = v_isSharedCheck_1551_;
goto v_resetjp_1545_;
}
v_resetjp_1545_:
{
lean_object* v___x_1549_; 
if (v_isShared_1547_ == 0)
{
v___x_1549_ = v___x_1546_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v_a_1544_);
v___x_1549_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
return v___x_1549_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__1___boxed(lean_object* v___x_1552_, lean_object* v_pre_1553_, lean_object* v_e_1554_, lean_object* v_post_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_){
_start:
{
lean_object* v_res_1560_; 
v_res_1560_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__1(v___x_1552_, v_pre_1553_, v_e_1554_, v_post_1555_, v___y_1556_, v___y_1557_, v___y_1558_);
lean_dec(v___y_1558_);
lean_dec_ref(v___y_1557_);
lean_dec(v___y_1556_);
return v_res_1560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(lean_object* v_pre_1561_, lean_object* v_post_1562_, lean_object* v_e_1563_, lean_object* v_a_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_){
_start:
{
lean_object* v___x_1568_; lean_object* v___x_1569_; 
lean_inc(v_a_1564_);
v___x_1568_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1568_, 0, lean_box(0));
lean_closure_set(v___x_1568_, 1, lean_box(0));
lean_closure_set(v___x_1568_, 2, v_a_1564_);
v___x_1569_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__0(lean_box(0), v___x_1568_, v___y_1565_, v___y_1566_);
if (lean_obj_tag(v___x_1569_) == 0)
{
lean_object* v_a_1570_; lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1601_; 
v_a_1570_ = lean_ctor_get(v___x_1569_, 0);
v_isSharedCheck_1601_ = !lean_is_exclusive(v___x_1569_);
if (v_isSharedCheck_1601_ == 0)
{
v___x_1572_ = v___x_1569_;
v_isShared_1573_ = v_isSharedCheck_1601_;
goto v_resetjp_1571_;
}
else
{
lean_inc(v_a_1570_);
lean_dec(v___x_1569_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1601_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
lean_object* v___x_1574_; 
v___x_1574_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg(v_a_1570_, v_e_1563_);
lean_dec(v_a_1570_);
if (lean_obj_tag(v___x_1574_) == 0)
{
lean_object* v___x_1575_; lean_object* v___f_1576_; lean_object* v___x_1577_; 
lean_del_object(v___x_1572_);
v___x_1575_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__19___closed__0));
lean_inc_ref(v_e_1563_);
v___f_1576_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__1___boxed), 8, 4);
lean_closure_set(v___f_1576_, 0, v___x_1575_);
lean_closure_set(v___f_1576_, 1, v_pre_1561_);
lean_closure_set(v___f_1576_, 2, v_e_1563_);
lean_closure_set(v___f_1576_, 3, v_post_1562_);
v___x_1577_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___redArg(v___f_1576_, v_a_1564_, v___y_1565_, v___y_1566_);
if (lean_obj_tag(v___x_1577_) == 0)
{
lean_object* v_a_1578_; lean_object* v___f_1579_; lean_object* v___x_1580_; 
v_a_1578_ = lean_ctor_get(v___x_1577_, 0);
lean_inc_n(v_a_1578_, 2);
lean_dec_ref_known(v___x_1577_, 1);
lean_inc(v_a_1564_);
v___f_1579_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1579_, 0, v_a_1564_);
lean_closure_set(v___f_1579_, 1, v_e_1563_);
lean_closure_set(v___f_1579_, 2, v_a_1578_);
v___x_1580_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__0(lean_box(0), v___f_1579_, v___y_1565_, v___y_1566_);
if (lean_obj_tag(v___x_1580_) == 0)
{
lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1587_; 
v_isSharedCheck_1587_ = !lean_is_exclusive(v___x_1580_);
if (v_isSharedCheck_1587_ == 0)
{
lean_object* v_unused_1588_; 
v_unused_1588_ = lean_ctor_get(v___x_1580_, 0);
lean_dec(v_unused_1588_);
v___x_1582_ = v___x_1580_;
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
else
{
lean_dec(v___x_1580_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
lean_object* v___x_1585_; 
if (v_isShared_1583_ == 0)
{
lean_ctor_set(v___x_1582_, 0, v_a_1578_);
v___x_1585_ = v___x_1582_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v_a_1578_);
v___x_1585_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
return v___x_1585_;
}
}
}
else
{
lean_object* v_a_1589_; lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1596_; 
lean_dec(v_a_1578_);
v_a_1589_ = lean_ctor_get(v___x_1580_, 0);
v_isSharedCheck_1596_ = !lean_is_exclusive(v___x_1580_);
if (v_isSharedCheck_1596_ == 0)
{
v___x_1591_ = v___x_1580_;
v_isShared_1592_ = v_isSharedCheck_1596_;
goto v_resetjp_1590_;
}
else
{
lean_inc(v_a_1589_);
lean_dec(v___x_1580_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1596_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
lean_object* v___x_1594_; 
if (v_isShared_1592_ == 0)
{
v___x_1594_ = v___x_1591_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v_a_1589_);
v___x_1594_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
return v___x_1594_;
}
}
}
}
else
{
lean_dec_ref(v_e_1563_);
return v___x_1577_;
}
}
else
{
lean_object* v_val_1597_; lean_object* v___x_1599_; 
lean_dec_ref(v_e_1563_);
lean_dec_ref(v_post_1562_);
lean_dec_ref(v_pre_1561_);
v_val_1597_ = lean_ctor_get(v___x_1574_, 0);
lean_inc(v_val_1597_);
lean_dec_ref_known(v___x_1574_, 1);
if (v_isShared_1573_ == 0)
{
lean_ctor_set(v___x_1572_, 0, v_val_1597_);
v___x_1599_ = v___x_1572_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v_val_1597_);
v___x_1599_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
return v___x_1599_;
}
}
}
}
else
{
lean_object* v_a_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1609_; 
lean_dec_ref(v_e_1563_);
lean_dec_ref(v_post_1562_);
lean_dec_ref(v_pre_1561_);
v_a_1602_ = lean_ctor_get(v___x_1569_, 0);
v_isSharedCheck_1609_ = !lean_is_exclusive(v___x_1569_);
if (v_isSharedCheck_1609_ == 0)
{
v___x_1604_ = v___x_1569_;
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_a_1602_);
lean_dec(v___x_1569_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v___x_1607_; 
if (v_isShared_1605_ == 0)
{
v___x_1607_ = v___x_1604_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v_a_1602_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
return v___x_1607_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(lean_object* v_pre_1610_, lean_object* v_post_1611_, lean_object* v_e_1612_, lean_object* v_a_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_){
_start:
{
lean_object* v___x_1617_; 
lean_inc_ref(v_post_1611_);
lean_inc(v___y_1615_);
lean_inc_ref(v___y_1614_);
lean_inc_ref(v_e_1612_);
v___x_1617_ = lean_apply_4(v_post_1611_, v_e_1612_, v___y_1614_, v___y_1615_, lean_box(0));
if (lean_obj_tag(v___x_1617_) == 0)
{
lean_object* v_a_1618_; lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1636_; 
v_a_1618_ = lean_ctor_get(v___x_1617_, 0);
v_isSharedCheck_1636_ = !lean_is_exclusive(v___x_1617_);
if (v_isSharedCheck_1636_ == 0)
{
v___x_1620_ = v___x_1617_;
v_isShared_1621_ = v_isSharedCheck_1636_;
goto v_resetjp_1619_;
}
else
{
lean_inc(v_a_1618_);
lean_dec(v___x_1617_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1636_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
switch(lean_obj_tag(v_a_1618_))
{
case 0:
{
lean_object* v_e_1622_; lean_object* v___x_1624_; 
lean_dec_ref(v_e_1612_);
lean_dec_ref(v_post_1611_);
lean_dec_ref(v_pre_1610_);
v_e_1622_ = lean_ctor_get(v_a_1618_, 0);
lean_inc_ref(v_e_1622_);
lean_dec_ref_known(v_a_1618_, 1);
if (v_isShared_1621_ == 0)
{
lean_ctor_set(v___x_1620_, 0, v_e_1622_);
v___x_1624_ = v___x_1620_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v_e_1622_);
v___x_1624_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
return v___x_1624_;
}
}
case 1:
{
lean_object* v_e_1626_; lean_object* v___x_1627_; 
lean_del_object(v___x_1620_);
lean_dec_ref(v_e_1612_);
v_e_1626_ = lean_ctor_get(v_a_1618_, 0);
lean_inc_ref(v_e_1626_);
lean_dec_ref_known(v_a_1618_, 1);
v___x_1627_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1610_, v_post_1611_, v_e_1626_, v_a_1613_, v___y_1614_, v___y_1615_);
return v___x_1627_;
}
default: 
{
lean_object* v_e_x3f_1628_; 
lean_dec_ref(v_post_1611_);
lean_dec_ref(v_pre_1610_);
v_e_x3f_1628_ = lean_ctor_get(v_a_1618_, 0);
lean_inc(v_e_x3f_1628_);
lean_dec_ref_known(v_a_1618_, 1);
if (lean_obj_tag(v_e_x3f_1628_) == 0)
{
lean_object* v___x_1630_; 
if (v_isShared_1621_ == 0)
{
lean_ctor_set(v___x_1620_, 0, v_e_1612_);
v___x_1630_ = v___x_1620_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v_e_1612_);
v___x_1630_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
return v___x_1630_;
}
}
else
{
lean_object* v_val_1632_; lean_object* v___x_1634_; 
lean_dec_ref(v_e_1612_);
v_val_1632_ = lean_ctor_get(v_e_x3f_1628_, 0);
lean_inc(v_val_1632_);
lean_dec_ref_known(v_e_x3f_1628_, 1);
if (v_isShared_1621_ == 0)
{
lean_ctor_set(v___x_1620_, 0, v_val_1632_);
v___x_1634_ = v___x_1620_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1635_; 
v_reuseFailAlloc_1635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1635_, 0, v_val_1632_);
v___x_1634_ = v_reuseFailAlloc_1635_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
return v___x_1634_;
}
}
}
}
}
}
else
{
lean_object* v_a_1637_; lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1644_; 
lean_dec_ref(v_e_1612_);
lean_dec_ref(v_post_1611_);
lean_dec_ref(v_pre_1610_);
v_a_1637_ = lean_ctor_get(v___x_1617_, 0);
v_isSharedCheck_1644_ = !lean_is_exclusive(v___x_1617_);
if (v_isSharedCheck_1644_ == 0)
{
v___x_1639_ = v___x_1617_;
v_isShared_1640_ = v_isSharedCheck_1644_;
goto v_resetjp_1638_;
}
else
{
lean_inc(v_a_1637_);
lean_dec(v___x_1617_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1644_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
lean_object* v___x_1642_; 
if (v_isShared_1640_ == 0)
{
v___x_1642_ = v___x_1639_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v_a_1637_);
v___x_1642_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
return v___x_1642_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_1645_, lean_object* v_post_1646_, lean_object* v_e_1647_, lean_object* v_a_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_){
_start:
{
lean_object* v_res_1652_; 
v_res_1652_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1645_, v_post_1646_, v_e_1647_, v_a_1648_, v___y_1649_, v___y_1650_);
lean_dec(v___y_1650_);
lean_dec_ref(v___y_1649_);
lean_dec(v_a_1648_);
return v_res_1652_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_1653_, lean_object* v_post_1654_, lean_object* v_sz_1655_, lean_object* v_i_1656_, lean_object* v_bs_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_){
_start:
{
size_t v_sz_boxed_1662_; size_t v_i_boxed_1663_; lean_object* v_res_1664_; 
v_sz_boxed_1662_ = lean_unbox_usize(v_sz_1655_);
lean_dec(v_sz_1655_);
v_i_boxed_1663_ = lean_unbox_usize(v_i_1656_);
lean_dec(v_i_1656_);
v_res_1664_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1(v_pre_1653_, v_post_1654_, v_sz_boxed_1662_, v_i_boxed_1663_, v_bs_1657_, v___y_1658_, v___y_1659_, v___y_1660_);
lean_dec(v___y_1660_);
lean_dec_ref(v___y_1659_);
lean_dec(v___y_1658_);
return v_res_1664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__4___boxed(lean_object* v_pre_1665_, lean_object* v_post_1666_, lean_object* v_x_1667_, lean_object* v_x_1668_, lean_object* v_x_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_){
_start:
{
lean_object* v_res_1674_; 
v_res_1674_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__4(v_pre_1665_, v_post_1666_, v_x_1667_, v_x_1668_, v_x_1669_, v___y_1670_, v___y_1671_, v___y_1672_);
lean_dec(v___y_1672_);
lean_dec_ref(v___y_1671_);
lean_dec(v___y_1670_);
return v_res_1674_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___boxed(lean_object* v_pre_1675_, lean_object* v_post_1676_, lean_object* v_e_1677_, lean_object* v_a_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_){
_start:
{
lean_object* v_res_1682_; 
v_res_1682_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1675_, v_post_1676_, v_e_1677_, v_a_1678_, v___y_1679_, v___y_1680_);
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
lean_dec(v_a_1678_);
return v_res_1682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___lam__0(lean_object* v_00_u03b1_1683_, lean_object* v_x_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_){
_start:
{
lean_object* v___x_1688_; lean_object* v___x_1689_; 
v___x_1688_ = lean_apply_1(v_x_1684_, lean_box(0));
v___x_1689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1689_, 0, v___x_1688_);
return v___x_1689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___lam__0___boxed(lean_object* v_00_u03b1_1690_, lean_object* v_x_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_){
_start:
{
lean_object* v_res_1695_; 
v_res_1695_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___lam__0(v_00_u03b1_1690_, v_x_1691_, v___y_1692_, v___y_1693_);
lean_dec(v___y_1693_);
lean_dec_ref(v___y_1692_);
return v_res_1695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(lean_object* v_input_1696_, lean_object* v_pre_1697_, lean_object* v_post_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_){
_start:
{
lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v_a_1704_; lean_object* v___x_1705_; 
v___x_1702_ = lean_obj_once(&l_Lean_Core_transform___redArg___closed__2, &l_Lean_Core_transform___redArg___closed__2_once, _init_l_Lean_Core_transform___redArg___closed__2);
v___x_1703_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___lam__0(lean_box(0), v___x_1702_, v___y_1699_, v___y_1700_);
v_a_1704_ = lean_ctor_get(v___x_1703_, 0);
lean_inc(v_a_1704_);
lean_dec_ref(v___x_1703_);
v___x_1705_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1697_, v_post_1698_, v_input_1696_, v_a_1704_, v___y_1699_, v___y_1700_);
if (lean_obj_tag(v___x_1705_) == 0)
{
lean_object* v_a_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1715_; 
v_a_1706_ = lean_ctor_get(v___x_1705_, 0);
lean_inc(v_a_1706_);
lean_dec_ref_known(v___x_1705_, 1);
v___x_1707_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1707_, 0, lean_box(0));
lean_closure_set(v___x_1707_, 1, lean_box(0));
lean_closure_set(v___x_1707_, 2, v_a_1704_);
v___x_1708_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___lam__0(lean_box(0), v___x_1707_, v___y_1699_, v___y_1700_);
v_isSharedCheck_1715_ = !lean_is_exclusive(v___x_1708_);
if (v_isSharedCheck_1715_ == 0)
{
lean_object* v_unused_1716_; 
v_unused_1716_ = lean_ctor_get(v___x_1708_, 0);
lean_dec(v_unused_1716_);
v___x_1710_ = v___x_1708_;
v_isShared_1711_ = v_isSharedCheck_1715_;
goto v_resetjp_1709_;
}
else
{
lean_dec(v___x_1708_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1715_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
lean_object* v___x_1713_; 
if (v_isShared_1711_ == 0)
{
lean_ctor_set(v___x_1710_, 0, v_a_1706_);
v___x_1713_ = v___x_1710_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v_a_1706_);
v___x_1713_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
return v___x_1713_;
}
}
}
else
{
lean_dec(v_a_1704_);
return v___x_1705_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___boxed(lean_object* v_input_1717_, lean_object* v_pre_1718_, lean_object* v_post_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_){
_start:
{
lean_object* v_res_1723_; 
v_res_1723_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_input_1717_, v_pre_1718_, v_post_1719_, v___y_1720_, v___y_1721_);
lean_dec(v___y_1721_);
lean_dec_ref(v___y_1720_);
return v_res_1723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_betaReduce(lean_object* v_e_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_){
_start:
{
lean_object* v___f_1730_; lean_object* v___f_1731_; lean_object* v___x_1732_; 
v___f_1730_ = ((lean_object*)(l_Lean_Core_betaReduce___closed__0));
v___f_1731_ = ((lean_object*)(l_Lean_Core_betaReduce___closed__1));
v___x_1732_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_1726_, v___f_1730_, v___f_1731_, v_a_1727_, v_a_1728_);
return v___x_1732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_betaReduce___boxed(lean_object* v_e_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_){
_start:
{
lean_object* v_res_1737_; 
v_res_1737_ = l_Lean_Core_betaReduce(v_e_1733_, v_a_1734_, v_a_1735_);
lean_dec(v_a_1735_);
lean_dec_ref(v_a_1734_);
return v_res_1737_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_1738_, lean_object* v_m_1739_, lean_object* v_a_1740_){
_start:
{
lean_object* v___x_1741_; 
v___x_1741_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg(v_m_1739_, v_a_1740_);
return v___x_1741_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_1742_, lean_object* v_m_1743_, lean_object* v_a_1744_){
_start:
{
lean_object* v_res_1745_; 
v_res_1745_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3(v_00_u03b2_1742_, v_m_1743_, v_a_1744_);
lean_dec_ref(v_a_1744_);
lean_dec_ref(v_m_1743_);
return v_res_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_1746_, lean_object* v_ref_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_){
_start:
{
lean_object* v___x_1751_; 
v___x_1751_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_1747_);
return v___x_1751_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1752_, lean_object* v_ref_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_){
_start:
{
lean_object* v_res_1757_; 
v_res_1757_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_1752_, v_ref_1753_, v___y_1754_, v___y_1755_);
lean_dec(v___y_1755_);
lean_dec_ref(v___y_1754_);
return v_res_1757_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8(lean_object* v_00_u03b1_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_){
_start:
{
lean_object* v___x_1762_; 
v___x_1762_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___redArg();
return v___x_1762_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___boxed(lean_object* v_00_u03b1_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_){
_start:
{
lean_object* v_res_1767_; 
v_res_1767_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8(v_00_u03b1_1763_, v___y_1764_, v___y_1765_);
lean_dec(v___y_1765_);
lean_dec_ref(v___y_1764_);
return v_res_1767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5(lean_object* v_00_u03b1_1768_, lean_object* v_x_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_){
_start:
{
lean_object* v___x_1774_; 
v___x_1774_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___redArg(v_x_1769_, v___y_1770_, v___y_1771_, v___y_1772_);
return v___x_1774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b1_1775_, lean_object* v_x_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_){
_start:
{
lean_object* v_res_1781_; 
v_res_1781_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5(v_00_u03b1_1775_, v_x_1776_, v___y_1777_, v___y_1778_, v___y_1779_);
lean_dec(v___y_1779_);
lean_dec_ref(v___y_1778_);
lean_dec(v___y_1777_);
return v_res_1781_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6(lean_object* v_00_u03b2_1782_, lean_object* v_m_1783_, lean_object* v_a_1784_, lean_object* v_b_1785_){
_start:
{
lean_object* v___x_1786_; 
v___x_1786_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6___redArg(v_m_1783_, v_a_1784_, v_b_1785_);
return v___x_1786_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4(lean_object* v_00_u03b2_1787_, lean_object* v_a_1788_, lean_object* v_x_1789_){
_start:
{
lean_object* v___x_1790_; 
v___x_1790_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___redArg(v_a_1788_, v_x_1789_);
return v___x_1790_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___boxed(lean_object* v_00_u03b2_1791_, lean_object* v_a_1792_, lean_object* v_x_1793_){
_start:
{
lean_object* v_res_1794_; 
v_res_1794_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4(v_00_u03b2_1791_, v_a_1792_, v_x_1793_);
lean_dec(v_x_1793_);
lean_dec_ref(v_a_1792_);
return v_res_1794_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10(lean_object* v_00_u03b2_1795_, lean_object* v_a_1796_, lean_object* v_x_1797_){
_start:
{
uint8_t v___x_1798_; 
v___x_1798_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___redArg(v_a_1796_, v_x_1797_);
return v___x_1798_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___boxed(lean_object* v_00_u03b2_1799_, lean_object* v_a_1800_, lean_object* v_x_1801_){
_start:
{
uint8_t v_res_1802_; lean_object* v_r_1803_; 
v_res_1802_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10(v_00_u03b2_1799_, v_a_1800_, v_x_1801_);
lean_dec(v_x_1801_);
lean_dec_ref(v_a_1800_);
v_r_1803_ = lean_box(v_res_1802_);
return v_r_1803_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11(lean_object* v_00_u03b2_1804_, lean_object* v_data_1805_){
_start:
{
lean_object* v___x_1806_; 
v___x_1806_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11___redArg(v_data_1805_);
return v___x_1806_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__12(lean_object* v_00_u03b2_1807_, lean_object* v_a_1808_, lean_object* v_b_1809_, lean_object* v_x_1810_){
_start:
{
lean_object* v___x_1811_; 
v___x_1811_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__12___redArg(v_a_1808_, v_b_1809_, v_x_1810_);
return v___x_1811_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12(lean_object* v_00_u03b2_1812_, lean_object* v_i_1813_, lean_object* v_source_1814_, lean_object* v_target_1815_){
_start:
{
lean_object* v___x_1816_; 
v___x_1816_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v_i_1813_, v_source_1814_, v_target_1815_);
return v___x_1816_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13(lean_object* v_00_u03b2_1817_, lean_object* v_x_1818_, lean_object* v_x_1819_){
_start:
{
lean_object* v___x_1820_; 
v___x_1820_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_x_1818_, v_x_1819_);
return v___x_1820_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__0(lean_object* v_toApplicative_1821_, lean_object* v_a_1822_){
_start:
{
lean_object* v_toPure_1823_; lean_object* v___x_1824_; 
v_toPure_1823_ = lean_ctor_get(v_toApplicative_1821_, 1);
lean_inc(v_toPure_1823_);
lean_dec_ref(v_toApplicative_1821_);
v___x_1824_ = lean_apply_2(v_toPure_1823_, lean_box(0), v_a_1822_);
return v___x_1824_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__13(lean_object* v___x_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_){
_start:
{
lean_object* v___x_1831_; 
v___x_1831_ = l_Lean_Core_checkSystem(v___x_1825_, v___y_1828_, v___y_1829_);
return v___x_1831_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__13___boxed(lean_object* v___x_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_){
_start:
{
lean_object* v_res_1838_; 
v_res_1838_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__13(v___x_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_);
lean_dec(v___y_1836_);
lean_dec_ref(v___y_1835_);
lean_dec(v___y_1834_);
lean_dec_ref(v___y_1833_);
return v_res_1838_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14(lean_object* v_inst_1841_, lean_object* v_x_1842_, lean_object* v___x_1843_, lean_object* v___x_1844_, lean_object* v_inst_1845_, lean_object* v___f_1846_, lean_object* v___x_1847_, lean_object* v___x_1848_, lean_object* v_a_1849_, lean_object* v_toBind_1850_, lean_object* v___f_1851_, lean_object* v_toApplicative_1852_, lean_object* v_a_1853_){
_start:
{
if (lean_obj_tag(v_a_1853_) == 0)
{
lean_object* v___f_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_3407__overap_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; 
lean_dec_ref(v_toApplicative_1852_);
v___f_1854_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14___closed__0));
v___x_1855_ = lean_apply_2(v_inst_1841_, lean_box(0), v___f_1854_);
lean_inc_ref(v___x_1844_);
lean_inc_ref(v___x_1843_);
v___x_1856_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonadLift___aux__1___boxed), 10, 9);
lean_closure_set(v___x_1856_, 0, lean_box(0));
lean_closure_set(v___x_1856_, 1, lean_box(0));
lean_closure_set(v___x_1856_, 2, lean_box(0));
lean_closure_set(v___x_1856_, 3, lean_box(0));
lean_closure_set(v___x_1856_, 4, v_x_1842_);
lean_closure_set(v___x_1856_, 5, v___x_1843_);
lean_closure_set(v___x_1856_, 6, v___x_1844_);
lean_closure_set(v___x_1856_, 7, lean_box(0));
lean_closure_set(v___x_1856_, 8, v___x_1855_);
v___x_1857_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonad___aux__13___boxed), 13, 12);
lean_closure_set(v___x_1857_, 0, lean_box(0));
lean_closure_set(v___x_1857_, 1, lean_box(0));
lean_closure_set(v___x_1857_, 2, lean_box(0));
lean_closure_set(v___x_1857_, 3, lean_box(0));
lean_closure_set(v___x_1857_, 4, v_x_1842_);
lean_closure_set(v___x_1857_, 5, v___x_1843_);
lean_closure_set(v___x_1857_, 6, v___x_1844_);
lean_closure_set(v___x_1857_, 7, v_inst_1845_);
lean_closure_set(v___x_1857_, 8, lean_box(0));
lean_closure_set(v___x_1857_, 9, lean_box(0));
lean_closure_set(v___x_1857_, 10, v___x_1856_);
lean_closure_set(v___x_1857_, 11, v___f_1846_);
v___x_3407__overap_1858_ = l_Lean_Meta_withIncRecDepth___redArg(v___x_1847_, v___x_1848_, v___x_1857_);
lean_inc(v_a_1849_);
v___x_1859_ = lean_apply_1(v___x_3407__overap_1858_, v_a_1849_);
v___x_1860_ = lean_apply_4(v_toBind_1850_, lean_box(0), lean_box(0), v___x_1859_, v___f_1851_);
return v___x_1860_;
}
else
{
lean_object* v_val_1861_; lean_object* v_toPure_1862_; lean_object* v___x_1863_; 
lean_dec(v___f_1851_);
lean_dec(v_toBind_1850_);
lean_dec_ref(v___x_1848_);
lean_dec_ref(v___x_1847_);
lean_dec(v___f_1846_);
lean_dec_ref(v_inst_1845_);
lean_dec_ref(v___x_1844_);
lean_dec_ref(v___x_1843_);
lean_dec(v_inst_1841_);
v_val_1861_ = lean_ctor_get(v_a_1853_, 0);
lean_inc(v_val_1861_);
lean_dec_ref_known(v_a_1853_, 1);
v_toPure_1862_ = lean_ctor_get(v_toApplicative_1852_, 1);
lean_inc(v_toPure_1862_);
lean_dec_ref(v_toApplicative_1852_);
v___x_1863_ = lean_apply_2(v_toPure_1862_, lean_box(0), v_val_1861_);
return v___x_1863_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14___boxed(lean_object* v_inst_1864_, lean_object* v_x_1865_, lean_object* v___x_1866_, lean_object* v___x_1867_, lean_object* v_inst_1868_, lean_object* v___f_1869_, lean_object* v___x_1870_, lean_object* v___x_1871_, lean_object* v_a_1872_, lean_object* v_toBind_1873_, lean_object* v___f_1874_, lean_object* v_toApplicative_1875_, lean_object* v_a_1876_){
_start:
{
lean_object* v_res_1877_; 
v_res_1877_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14(v_inst_1864_, v_x_1865_, v___x_1866_, v___x_1867_, v_inst_1868_, v___f_1869_, v___x_1870_, v___x_1871_, v_a_1872_, v_toBind_1873_, v___f_1874_, v_toApplicative_1875_, v_a_1876_);
lean_dec(v_a_1872_);
return v_res_1877_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__1(lean_object* v___x_1878_, lean_object* v___x_1879_, lean_object* v_declName_1880_, lean_object* v_a_1881_, lean_object* v___f_1882_, uint8_t v_nondep_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_){
_start:
{
uint8_t v___x_1886_; lean_object* v___x_3426__overap_1887_; lean_object* v___x_1888_; 
v___x_1886_ = 0;
v___x_3426__overap_1887_ = l_Lean_Meta_withLetDecl___redArg(v___x_1878_, v___x_1879_, v_declName_1880_, v_a_1881_, v_a_1885_, v___f_1882_, v_nondep_1883_, v___x_1886_);
lean_inc(v_a_1884_);
v___x_1888_ = lean_apply_1(v___x_3426__overap_1887_, v_a_1884_);
return v___x_1888_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__1___boxed(lean_object* v___x_1889_, lean_object* v___x_1890_, lean_object* v_declName_1891_, lean_object* v_a_1892_, lean_object* v___f_1893_, lean_object* v_nondep_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_){
_start:
{
uint8_t v_nondep_3605__boxed_1897_; lean_object* v_res_1898_; 
v_nondep_3605__boxed_1897_ = lean_unbox(v_nondep_1894_);
v_res_1898_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__1(v___x_1889_, v___x_1890_, v_declName_1891_, v_a_1892_, v___f_1893_, v_nondep_3605__boxed_1897_, v_a_1895_, v_a_1896_);
lean_dec(v_a_1895_);
return v_res_1898_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__4(lean_object* v_fvars_1899_, uint8_t v_usedLetOnly_1900_, lean_object* v_inst_1901_, lean_object* v_toBind_1902_, lean_object* v___f_1903_, lean_object* v_a_1904_){
_start:
{
uint8_t v___x_1905_; uint8_t v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; 
v___x_1905_ = 0;
v___x_1906_ = 1;
v___x_1907_ = lean_box(v_usedLetOnly_1900_);
v___x_1908_ = lean_box(v___x_1905_);
v___x_1909_ = lean_box(v___x_1906_);
v___x_1910_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLetFVars___boxed), 10, 5);
lean_closure_set(v___x_1910_, 0, v_fvars_1899_);
lean_closure_set(v___x_1910_, 1, v_a_1904_);
lean_closure_set(v___x_1910_, 2, v___x_1907_);
lean_closure_set(v___x_1910_, 3, v___x_1908_);
lean_closure_set(v___x_1910_, 4, v___x_1909_);
v___x_1911_ = lean_apply_2(v_inst_1901_, lean_box(0), v___x_1910_);
v___x_1912_ = lean_apply_4(v_toBind_1902_, lean_box(0), lean_box(0), v___x_1911_, v___f_1903_);
return v___x_1912_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__4___boxed(lean_object* v_fvars_1913_, lean_object* v_usedLetOnly_1914_, lean_object* v_inst_1915_, lean_object* v_toBind_1916_, lean_object* v___f_1917_, lean_object* v_a_1918_){
_start:
{
uint8_t v_usedLetOnly_boxed_1919_; lean_object* v_res_1920_; 
v_usedLetOnly_boxed_1919_ = lean_unbox(v_usedLetOnly_1914_);
v_res_1920_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__4(v_fvars_1913_, v_usedLetOnly_boxed_1919_, v_inst_1915_, v_toBind_1916_, v___f_1917_, v_a_1918_);
return v_res_1920_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__3(lean_object* v_fvars_1921_, uint8_t v_usedLetOnly_1922_, lean_object* v_inst_1923_, lean_object* v_toBind_1924_, lean_object* v___f_1925_, lean_object* v_a_1926_){
_start:
{
uint8_t v___x_1927_; uint8_t v___x_1928_; uint8_t v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; 
v___x_1927_ = 0;
v___x_1928_ = 1;
v___x_1929_ = 1;
v___x_1930_ = lean_box(v___x_1927_);
v___x_1931_ = lean_box(v_usedLetOnly_1922_);
v___x_1932_ = lean_box(v___x_1927_);
v___x_1933_ = lean_box(v___x_1928_);
v___x_1934_ = lean_box(v___x_1929_);
v___x_1935_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(v___x_1935_, 0, v_fvars_1921_);
lean_closure_set(v___x_1935_, 1, v_a_1926_);
lean_closure_set(v___x_1935_, 2, v___x_1930_);
lean_closure_set(v___x_1935_, 3, v___x_1931_);
lean_closure_set(v___x_1935_, 4, v___x_1932_);
lean_closure_set(v___x_1935_, 5, v___x_1933_);
lean_closure_set(v___x_1935_, 6, v___x_1934_);
v___x_1936_ = lean_apply_2(v_inst_1923_, lean_box(0), v___x_1935_);
v___x_1937_ = lean_apply_4(v_toBind_1924_, lean_box(0), lean_box(0), v___x_1936_, v___f_1925_);
return v___x_1937_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__3___boxed(lean_object* v_fvars_1938_, lean_object* v_usedLetOnly_1939_, lean_object* v_inst_1940_, lean_object* v_toBind_1941_, lean_object* v___f_1942_, lean_object* v_a_1943_){
_start:
{
uint8_t v_usedLetOnly_boxed_1944_; lean_object* v_res_1945_; 
v_usedLetOnly_boxed_1944_ = lean_unbox(v_usedLetOnly_1939_);
v_res_1945_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__3(v_fvars_1938_, v_usedLetOnly_boxed_1944_, v_inst_1940_, v_toBind_1941_, v___f_1942_, v_a_1943_);
return v_res_1945_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1(lean_object* v___x_1946_, lean_object* v___x_1947_, lean_object* v_binderName_1948_, uint8_t v_binderInfo_1949_, lean_object* v___f_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_){
_start:
{
uint8_t v___x_1953_; lean_object* v___x_3484__overap_1954_; lean_object* v___x_1955_; 
v___x_1953_ = 0;
v___x_3484__overap_1954_ = l_Lean_Meta_withLocalDecl___redArg(v___x_1946_, v___x_1947_, v_binderName_1948_, v_binderInfo_1949_, v_a_1952_, v___f_1950_, v___x_1953_);
lean_inc(v_a_1951_);
v___x_1955_ = lean_apply_1(v___x_3484__overap_1954_, v_a_1951_);
return v___x_1955_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1___boxed(lean_object* v___x_1956_, lean_object* v___x_1957_, lean_object* v_binderName_1958_, lean_object* v_binderInfo_1959_, lean_object* v___f_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_){
_start:
{
uint8_t v_binderInfo_3673__boxed_1963_; lean_object* v_res_1964_; 
v_binderInfo_3673__boxed_1963_ = lean_unbox(v_binderInfo_1959_);
v_res_1964_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1(v___x_1956_, v___x_1957_, v_binderName_1958_, v_binderInfo_3673__boxed_1963_, v___f_1960_, v_a_1961_, v_a_1962_);
lean_dec(v_a_1961_);
return v_res_1964_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__3(lean_object* v_fvars_1965_, uint8_t v_usedLetOnly_1966_, lean_object* v_inst_1967_, lean_object* v_toBind_1968_, lean_object* v___f_1969_, lean_object* v_a_1970_){
_start:
{
uint8_t v___x_1971_; uint8_t v___x_1972_; uint8_t v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; 
v___x_1971_ = 0;
v___x_1972_ = 1;
v___x_1973_ = 1;
v___x_1974_ = lean_box(v___x_1971_);
v___x_1975_ = lean_box(v_usedLetOnly_1966_);
v___x_1976_ = lean_box(v___x_1972_);
v___x_1977_ = lean_box(v___x_1973_);
v___x_1978_ = lean_alloc_closure((void*)(l_Lean_Meta_mkForallFVars___boxed), 11, 6);
lean_closure_set(v___x_1978_, 0, v_fvars_1965_);
lean_closure_set(v___x_1978_, 1, v_a_1970_);
lean_closure_set(v___x_1978_, 2, v___x_1974_);
lean_closure_set(v___x_1978_, 3, v___x_1975_);
lean_closure_set(v___x_1978_, 4, v___x_1976_);
lean_closure_set(v___x_1978_, 5, v___x_1977_);
v___x_1979_ = lean_apply_2(v_inst_1967_, lean_box(0), v___x_1978_);
v___x_1980_ = lean_apply_4(v_toBind_1968_, lean_box(0), lean_box(0), v___x_1979_, v___f_1969_);
return v___x_1980_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__3___boxed(lean_object* v_fvars_1981_, lean_object* v_usedLetOnly_1982_, lean_object* v_inst_1983_, lean_object* v_toBind_1984_, lean_object* v___f_1985_, lean_object* v_a_1986_){
_start:
{
uint8_t v_usedLetOnly_boxed_1987_; lean_object* v_res_1988_; 
v_usedLetOnly_boxed_1987_ = lean_unbox(v_usedLetOnly_1982_);
v_res_1988_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__3(v_fvars_1981_, v_usedLetOnly_boxed_1987_, v_inst_1983_, v_toBind_1984_, v___f_1985_, v_a_1986_);
return v_res_1988_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__7(lean_object* v___f_1989_, lean_object* v___y_1990_, lean_object* v_a_1991_){
_start:
{
lean_object* v___x_1992_; 
lean_inc(v___y_1990_);
v___x_1992_ = lean_apply_2(v___f_1989_, v_a_1991_, v___y_1990_);
return v___x_1992_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__7___boxed(lean_object* v___f_1993_, lean_object* v___y_1994_, lean_object* v_a_1995_){
_start:
{
lean_object* v_res_1996_; 
v_res_1996_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__7(v___f_1993_, v___y_1994_, v_a_1995_);
lean_dec(v___y_1994_);
return v_res_1996_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1(lean_object* v_toApplicative_1997_, lean_object* v_acc_1998_, lean_object* v_next_1999_, lean_object* v_a_2000_){
_start:
{
lean_object* v_toPure_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; 
v_toPure_2001_ = lean_ctor_get(v_toApplicative_1997_, 1);
lean_inc(v_toPure_2001_);
lean_dec_ref(v_toApplicative_1997_);
v___x_2002_ = lean_array_fset(v_acc_1998_, v_next_1999_, v_a_2000_);
v___x_2003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2003_, 0, v___x_2002_);
v___x_2004_ = lean_apply_2(v_toPure_2001_, lean_box(0), v___x_2003_);
return v___x_2004_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1___boxed(lean_object* v_toApplicative_2005_, lean_object* v_acc_2006_, lean_object* v_next_2007_, lean_object* v_a_2008_){
_start:
{
lean_object* v_res_2009_; 
v_res_2009_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1(v_toApplicative_2005_, v_acc_2006_, v_next_2007_, v_a_2008_);
lean_dec(v_next_2007_);
return v_res_2009_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__2(lean_object* v_toApplicative_2010_, lean_object* v_next_2011_, lean_object* v_G_2012_, lean_object* v___y_2013_, lean_object* v_a_2014_){
_start:
{
if (lean_obj_tag(v_a_2014_) == 0)
{
lean_object* v_a_2015_; lean_object* v_toPure_2016_; lean_object* v___x_2017_; 
lean_dec(v_G_2012_);
v_a_2015_ = lean_ctor_get(v_a_2014_, 0);
lean_inc(v_a_2015_);
lean_dec_ref_known(v_a_2014_, 1);
v_toPure_2016_ = lean_ctor_get(v_toApplicative_2010_, 1);
lean_inc(v_toPure_2016_);
lean_dec_ref(v_toApplicative_2010_);
v___x_2017_ = lean_apply_2(v_toPure_2016_, lean_box(0), v_a_2015_);
return v___x_2017_;
}
else
{
lean_object* v_a_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; 
lean_dec_ref(v_toApplicative_2010_);
v_a_2018_ = lean_ctor_get(v_a_2014_, 0);
lean_inc(v_a_2018_);
lean_dec_ref_known(v_a_2014_, 1);
v___x_2019_ = lean_unsigned_to_nat(1u);
v___x_2020_ = lean_nat_add(v_next_2011_, v___x_2019_);
lean_inc(v___y_2013_);
v___x_2021_ = lean_apply_5(v_G_2012_, v___x_2020_, v_a_2018_, lean_box(0), lean_box(0), v___y_2013_);
return v___x_2021_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__2___boxed(lean_object* v_toApplicative_2022_, lean_object* v_next_2023_, lean_object* v_G_2024_, lean_object* v___y_2025_, lean_object* v_a_2026_){
_start:
{
lean_object* v_res_2027_; 
v_res_2027_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__2(v_toApplicative_2022_, v_next_2023_, v_G_2024_, v___y_2025_, v_a_2026_);
lean_dec(v___y_2025_);
lean_dec(v_next_2023_);
return v_res_2027_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5(lean_object* v_f_2028_, lean_object* v_inst_2029_, lean_object* v_inst_2030_, lean_object* v_inst_2031_, lean_object* v_pre_2032_, lean_object* v_post_2033_, uint8_t v_usedLetOnly_2034_, uint8_t v_skipConstInApp_2035_, uint8_t v_skipInstances_2036_, lean_object* v_x_2037_, lean_object* v_x_2038_, lean_object* v___y_2039_, lean_object* v_a_2040_){
_start:
{
lean_object* v___x_2041_; lean_object* v___x_2042_; 
v___x_2041_ = l_Lean_mkAppN(v_f_2028_, v_a_2040_);
v___x_2042_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2029_, v_inst_2030_, v_inst_2031_, v_pre_2032_, v_post_2033_, v_usedLetOnly_2034_, v_skipConstInApp_2035_, v_skipInstances_2036_, v_x_2037_, v_x_2038_, v___x_2041_, v___y_2039_);
return v___x_2042_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5___boxed(lean_object* v_f_2043_, lean_object* v_inst_2044_, lean_object* v_inst_2045_, lean_object* v_inst_2046_, lean_object* v_pre_2047_, lean_object* v_post_2048_, lean_object* v_usedLetOnly_2049_, lean_object* v_skipConstInApp_2050_, lean_object* v_skipInstances_2051_, lean_object* v_x_2052_, lean_object* v_x_2053_, lean_object* v___y_2054_, lean_object* v_a_2055_){
_start:
{
uint8_t v_usedLetOnly_boxed_2056_; uint8_t v_skipConstInApp_boxed_2057_; uint8_t v_skipInstances_boxed_2058_; lean_object* v_res_2059_; 
v_usedLetOnly_boxed_2056_ = lean_unbox(v_usedLetOnly_2049_);
v_skipConstInApp_boxed_2057_ = lean_unbox(v_skipConstInApp_2050_);
v_skipInstances_boxed_2058_ = lean_unbox(v_skipInstances_2051_);
v_res_2059_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5(v_f_2043_, v_inst_2044_, v_inst_2045_, v_inst_2046_, v_pre_2047_, v_post_2048_, v_usedLetOnly_boxed_2056_, v_skipConstInApp_boxed_2057_, v_skipInstances_boxed_2058_, v_x_2052_, v_x_2053_, v___y_2054_, v_a_2055_);
lean_dec_ref(v_a_2055_);
lean_dec(v___y_2054_);
return v_res_2059_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___boxed(lean_object* v_inst_2060_, lean_object* v_inst_2061_, lean_object* v_inst_2062_, lean_object* v_pre_2063_, lean_object* v_post_2064_, lean_object* v_usedLetOnly_2065_, lean_object* v_skipConstInApp_2066_, lean_object* v_skipInstances_2067_, lean_object* v_x_2068_, lean_object* v_x_2069_, lean_object* v_e_2070_, lean_object* v_a_2071_){
_start:
{
uint8_t v_usedLetOnly_boxed_2072_; uint8_t v_skipConstInApp_boxed_2073_; uint8_t v_skipInstances_boxed_2074_; lean_object* v_res_2075_; 
v_usedLetOnly_boxed_2072_ = lean_unbox(v_usedLetOnly_2065_);
v_skipConstInApp_boxed_2073_ = lean_unbox(v_skipConstInApp_2066_);
v_skipInstances_boxed_2074_ = lean_unbox(v_skipInstances_2067_);
v_res_2075_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2060_, v_inst_2061_, v_inst_2062_, v_pre_2063_, v_post_2064_, v_usedLetOnly_boxed_2072_, v_skipConstInApp_boxed_2073_, v_skipInstances_boxed_2074_, v_x_2068_, v_x_2069_, v_e_2070_, v_a_2071_);
lean_dec(v_a_2071_);
return v_res_2075_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__4(lean_object* v___x_2076_, lean_object* v_toApplicative_2077_, lean_object* v_toBind_2078_, lean_object* v___f_2079_, lean_object* v_paramInfo_2080_, lean_object* v_inst_2081_, lean_object* v_inst_2082_, lean_object* v_inst_2083_, lean_object* v_pre_2084_, lean_object* v_post_2085_, uint8_t v_usedLetOnly_2086_, uint8_t v_skipConstInApp_2087_, uint8_t v_skipInstances_2088_, lean_object* v_x_2089_, lean_object* v_x_2090_, lean_object* v_next_2091_, lean_object* v_acc_2092_, lean_object* v_h_2093_, lean_object* v_G_2094_, lean_object* v___y_2095_){
_start:
{
uint8_t v___x_2096_; 
v___x_2096_ = lean_nat_dec_lt(v_next_2091_, v___x_2076_);
if (v___x_2096_ == 0)
{
lean_object* v_toPure_2097_; lean_object* v___x_2098_; 
lean_dec(v_G_2094_);
lean_dec(v_next_2091_);
lean_dec(v_x_2090_);
lean_dec(v_post_2085_);
lean_dec(v_pre_2084_);
lean_dec_ref(v_inst_2083_);
lean_dec(v_inst_2082_);
lean_dec_ref(v_inst_2081_);
lean_dec(v___f_2079_);
lean_dec(v_toBind_2078_);
v_toPure_2097_ = lean_ctor_get(v_toApplicative_2077_, 1);
lean_inc(v_toPure_2097_);
lean_dec_ref(v_toApplicative_2077_);
v___x_2098_ = lean_apply_2(v_toPure_2097_, lean_box(0), v_acc_2092_);
return v___x_2098_;
}
else
{
lean_object* v___f_2099_; lean_object* v___y_2101_; lean_object* v___x_2104_; lean_object* v___x_2105_; uint8_t v___x_2106_; 
lean_inc(v___y_2095_);
lean_inc(v_next_2091_);
lean_inc_ref(v_toApplicative_2077_);
v___f_2099_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__2___boxed), 5, 4);
lean_closure_set(v___f_2099_, 0, v_toApplicative_2077_);
lean_closure_set(v___f_2099_, 1, v_next_2091_);
lean_closure_set(v___f_2099_, 2, v_G_2094_);
lean_closure_set(v___f_2099_, 3, v___y_2095_);
v___x_2104_ = lean_array_fget_borrowed(v_acc_2092_, v_next_2091_);
v___x_2105_ = lean_array_get_size(v_paramInfo_2080_);
v___x_2106_ = lean_nat_dec_lt(v_next_2091_, v___x_2105_);
if (v___x_2106_ == 0)
{
lean_object* v___f_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; 
lean_inc(v___x_2104_);
v___f_2107_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2107_, 0, v_toApplicative_2077_);
lean_closure_set(v___f_2107_, 1, v_acc_2092_);
lean_closure_set(v___f_2107_, 2, v_next_2091_);
v___x_2108_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2081_, v_inst_2082_, v_inst_2083_, v_pre_2084_, v_post_2085_, v_usedLetOnly_2086_, v_skipConstInApp_2087_, v_skipInstances_2088_, v_x_2089_, v_x_2090_, v___x_2104_, v___y_2095_);
lean_inc(v_toBind_2078_);
v___x_2109_ = lean_apply_4(v_toBind_2078_, lean_box(0), lean_box(0), v___x_2108_, v___f_2107_);
v___y_2101_ = v___x_2109_;
goto v___jp_2100_;
}
else
{
lean_object* v___x_2110_; uint8_t v_isInstance_2111_; 
v___x_2110_ = lean_array_fget_borrowed(v_paramInfo_2080_, v_next_2091_);
v_isInstance_2111_ = lean_ctor_get_uint8(v___x_2110_, sizeof(void*)*1 + 4);
if (v_isInstance_2111_ == 0)
{
lean_object* v___f_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; 
lean_inc(v___x_2104_);
v___f_2112_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2112_, 0, v_toApplicative_2077_);
lean_closure_set(v___f_2112_, 1, v_acc_2092_);
lean_closure_set(v___f_2112_, 2, v_next_2091_);
v___x_2113_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2081_, v_inst_2082_, v_inst_2083_, v_pre_2084_, v_post_2085_, v_usedLetOnly_2086_, v_skipConstInApp_2087_, v_skipInstances_2088_, v_x_2089_, v_x_2090_, v___x_2104_, v___y_2095_);
lean_inc(v_toBind_2078_);
v___x_2114_ = lean_apply_4(v_toBind_2078_, lean_box(0), lean_box(0), v___x_2113_, v___f_2112_);
v___y_2101_ = v___x_2114_;
goto v___jp_2100_;
}
else
{
lean_object* v_toPure_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; 
lean_dec(v_next_2091_);
lean_dec(v_x_2090_);
lean_dec(v_post_2085_);
lean_dec(v_pre_2084_);
lean_dec_ref(v_inst_2083_);
lean_dec(v_inst_2082_);
lean_dec_ref(v_inst_2081_);
v_toPure_2115_ = lean_ctor_get(v_toApplicative_2077_, 1);
lean_inc(v_toPure_2115_);
lean_dec_ref(v_toApplicative_2077_);
v___x_2116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2116_, 0, v_acc_2092_);
v___x_2117_ = lean_apply_2(v_toPure_2115_, lean_box(0), v___x_2116_);
v___y_2101_ = v___x_2117_;
goto v___jp_2100_;
}
}
v___jp_2100_:
{
lean_object* v___x_2102_; lean_object* v___x_2103_; 
lean_inc(v_toBind_2078_);
v___x_2102_ = lean_apply_4(v_toBind_2078_, lean_box(0), lean_box(0), v___y_2101_, v___f_2079_);
v___x_2103_ = lean_apply_4(v_toBind_2078_, lean_box(0), lean_box(0), v___x_2102_, v___f_2099_);
return v___x_2103_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__4___boxed(lean_object** _args){
lean_object* v___x_2118_ = _args[0];
lean_object* v_toApplicative_2119_ = _args[1];
lean_object* v_toBind_2120_ = _args[2];
lean_object* v___f_2121_ = _args[3];
lean_object* v_paramInfo_2122_ = _args[4];
lean_object* v_inst_2123_ = _args[5];
lean_object* v_inst_2124_ = _args[6];
lean_object* v_inst_2125_ = _args[7];
lean_object* v_pre_2126_ = _args[8];
lean_object* v_post_2127_ = _args[9];
lean_object* v_usedLetOnly_2128_ = _args[10];
lean_object* v_skipConstInApp_2129_ = _args[11];
lean_object* v_skipInstances_2130_ = _args[12];
lean_object* v_x_2131_ = _args[13];
lean_object* v_x_2132_ = _args[14];
lean_object* v_next_2133_ = _args[15];
lean_object* v_acc_2134_ = _args[16];
lean_object* v_h_2135_ = _args[17];
lean_object* v_G_2136_ = _args[18];
lean_object* v___y_2137_ = _args[19];
_start:
{
uint8_t v_usedLetOnly_boxed_2138_; uint8_t v_skipConstInApp_boxed_2139_; uint8_t v_skipInstances_boxed_2140_; lean_object* v_res_2141_; 
v_usedLetOnly_boxed_2138_ = lean_unbox(v_usedLetOnly_2128_);
v_skipConstInApp_boxed_2139_ = lean_unbox(v_skipConstInApp_2129_);
v_skipInstances_boxed_2140_ = lean_unbox(v_skipInstances_2130_);
v_res_2141_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__4(v___x_2118_, v_toApplicative_2119_, v_toBind_2120_, v___f_2121_, v_paramInfo_2122_, v_inst_2123_, v_inst_2124_, v_inst_2125_, v_pre_2126_, v_post_2127_, v_usedLetOnly_boxed_2138_, v_skipConstInApp_boxed_2139_, v_skipInstances_boxed_2140_, v_x_2131_, v_x_2132_, v_next_2133_, v_acc_2134_, v_h_2135_, v_G_2136_, v___y_2137_);
lean_dec(v___y_2137_);
lean_dec_ref(v_paramInfo_2122_);
lean_dec(v___x_2118_);
return v_res_2141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__3(lean_object* v___x_2142_, lean_object* v_toApplicative_2143_, lean_object* v_toBind_2144_, lean_object* v___f_2145_, lean_object* v_inst_2146_, lean_object* v_inst_2147_, lean_object* v_inst_2148_, lean_object* v_pre_2149_, lean_object* v_post_2150_, uint8_t v_usedLetOnly_2151_, uint8_t v_skipConstInApp_2152_, uint8_t v_skipInstances_2153_, lean_object* v_x_2154_, lean_object* v_x_2155_, lean_object* v_args_2156_, lean_object* v___y_2157_, lean_object* v___f_2158_, lean_object* v_a_2159_){
_start:
{
lean_object* v_paramInfo_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___f_2165_; lean_object* v___x_3244__overap_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; 
v_paramInfo_2160_ = lean_ctor_get(v_a_2159_, 0);
lean_inc_ref(v_paramInfo_2160_);
lean_dec_ref(v_a_2159_);
v___x_2161_ = lean_unsigned_to_nat(0u);
v___x_2162_ = lean_box(v_usedLetOnly_2151_);
v___x_2163_ = lean_box(v_skipConstInApp_2152_);
v___x_2164_ = lean_box(v_skipInstances_2153_);
lean_inc(v_toBind_2144_);
v___f_2165_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__4___boxed), 20, 15);
lean_closure_set(v___f_2165_, 0, v___x_2142_);
lean_closure_set(v___f_2165_, 1, v_toApplicative_2143_);
lean_closure_set(v___f_2165_, 2, v_toBind_2144_);
lean_closure_set(v___f_2165_, 3, v___f_2145_);
lean_closure_set(v___f_2165_, 4, v_paramInfo_2160_);
lean_closure_set(v___f_2165_, 5, v_inst_2146_);
lean_closure_set(v___f_2165_, 6, v_inst_2147_);
lean_closure_set(v___f_2165_, 7, v_inst_2148_);
lean_closure_set(v___f_2165_, 8, v_pre_2149_);
lean_closure_set(v___f_2165_, 9, v_post_2150_);
lean_closure_set(v___f_2165_, 10, v___x_2162_);
lean_closure_set(v___f_2165_, 11, v___x_2163_);
lean_closure_set(v___f_2165_, 12, v___x_2164_);
lean_closure_set(v___f_2165_, 13, v_x_2154_);
lean_closure_set(v___f_2165_, 14, v_x_2155_);
v___x_3244__overap_2166_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_2165_, v___x_2161_, v_args_2156_, lean_box(0));
lean_inc(v___y_2157_);
v___x_2167_ = lean_apply_1(v___x_3244__overap_2166_, v___y_2157_);
v___x_2168_ = lean_apply_4(v_toBind_2144_, lean_box(0), lean_box(0), v___x_2167_, v___f_2158_);
return v___x_2168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__3___boxed(lean_object** _args){
lean_object* v___x_2169_ = _args[0];
lean_object* v_toApplicative_2170_ = _args[1];
lean_object* v_toBind_2171_ = _args[2];
lean_object* v___f_2172_ = _args[3];
lean_object* v_inst_2173_ = _args[4];
lean_object* v_inst_2174_ = _args[5];
lean_object* v_inst_2175_ = _args[6];
lean_object* v_pre_2176_ = _args[7];
lean_object* v_post_2177_ = _args[8];
lean_object* v_usedLetOnly_2178_ = _args[9];
lean_object* v_skipConstInApp_2179_ = _args[10];
lean_object* v_skipInstances_2180_ = _args[11];
lean_object* v_x_2181_ = _args[12];
lean_object* v_x_2182_ = _args[13];
lean_object* v_args_2183_ = _args[14];
lean_object* v___y_2184_ = _args[15];
lean_object* v___f_2185_ = _args[16];
lean_object* v_a_2186_ = _args[17];
_start:
{
uint8_t v_usedLetOnly_boxed_2187_; uint8_t v_skipConstInApp_boxed_2188_; uint8_t v_skipInstances_boxed_2189_; lean_object* v_res_2190_; 
v_usedLetOnly_boxed_2187_ = lean_unbox(v_usedLetOnly_2178_);
v_skipConstInApp_boxed_2188_ = lean_unbox(v_skipConstInApp_2179_);
v_skipInstances_boxed_2189_ = lean_unbox(v_skipInstances_2180_);
v_res_2190_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__3(v___x_2169_, v_toApplicative_2170_, v_toBind_2171_, v___f_2172_, v_inst_2173_, v_inst_2174_, v_inst_2175_, v_pre_2176_, v_post_2177_, v_usedLetOnly_boxed_2187_, v_skipConstInApp_boxed_2188_, v_skipInstances_boxed_2189_, v_x_2181_, v_x_2182_, v_args_2183_, v___y_2184_, v___f_2185_, v_a_2186_);
lean_dec(v___y_2184_);
return v_res_2190_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__6(uint8_t v_skipInstances_2191_, lean_object* v_inst_2192_, lean_object* v_inst_2193_, lean_object* v_inst_2194_, lean_object* v_pre_2195_, lean_object* v_post_2196_, uint8_t v_usedLetOnly_2197_, uint8_t v_skipConstInApp_2198_, lean_object* v_x_2199_, lean_object* v_x_2200_, lean_object* v_args_2201_, lean_object* v___x_2202_, lean_object* v_toBind_2203_, lean_object* v_toApplicative_2204_, lean_object* v___f_2205_, lean_object* v_f_2206_, lean_object* v___y_2207_){
_start:
{
if (v_skipInstances_2191_ == 0)
{
lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___f_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; size_t v_sz_2216_; size_t v___x_2217_; lean_object* v___x_3257__overap_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; 
lean_dec(v___f_2205_);
lean_dec_ref(v_toApplicative_2204_);
v___x_2208_ = lean_box(v_usedLetOnly_2197_);
v___x_2209_ = lean_box(v_skipConstInApp_2198_);
v___x_2210_ = lean_box(v_skipInstances_2191_);
lean_inc_n(v___y_2207_, 2);
lean_inc(v_x_2200_);
lean_inc(v_post_2196_);
lean_inc(v_pre_2195_);
lean_inc_ref(v_inst_2194_);
lean_inc(v_inst_2193_);
lean_inc_ref(v_inst_2192_);
v___f_2211_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5___boxed), 13, 12);
lean_closure_set(v___f_2211_, 0, v_f_2206_);
lean_closure_set(v___f_2211_, 1, v_inst_2192_);
lean_closure_set(v___f_2211_, 2, v_inst_2193_);
lean_closure_set(v___f_2211_, 3, v_inst_2194_);
lean_closure_set(v___f_2211_, 4, v_pre_2195_);
lean_closure_set(v___f_2211_, 5, v_post_2196_);
lean_closure_set(v___f_2211_, 6, v___x_2208_);
lean_closure_set(v___f_2211_, 7, v___x_2209_);
lean_closure_set(v___f_2211_, 8, v___x_2210_);
lean_closure_set(v___f_2211_, 9, v_x_2199_);
lean_closure_set(v___f_2211_, 10, v_x_2200_);
lean_closure_set(v___f_2211_, 11, v___y_2207_);
v___x_2212_ = lean_box(v_usedLetOnly_2197_);
v___x_2213_ = lean_box(v_skipConstInApp_2198_);
v___x_2214_ = lean_box(v_skipInstances_2191_);
v___x_2215_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___boxed), 12, 10);
lean_closure_set(v___x_2215_, 0, v_inst_2192_);
lean_closure_set(v___x_2215_, 1, v_inst_2193_);
lean_closure_set(v___x_2215_, 2, v_inst_2194_);
lean_closure_set(v___x_2215_, 3, v_pre_2195_);
lean_closure_set(v___x_2215_, 4, v_post_2196_);
lean_closure_set(v___x_2215_, 5, v___x_2212_);
lean_closure_set(v___x_2215_, 6, v___x_2213_);
lean_closure_set(v___x_2215_, 7, v___x_2214_);
lean_closure_set(v___x_2215_, 8, v_x_2199_);
lean_closure_set(v___x_2215_, 9, v_x_2200_);
v_sz_2216_ = lean_array_size(v_args_2201_);
v___x_2217_ = ((size_t)0ULL);
v___x_3257__overap_2218_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2202_, v___x_2215_, v_sz_2216_, v___x_2217_, v_args_2201_);
v___x_2219_ = lean_apply_1(v___x_3257__overap_2218_, v___y_2207_);
v___x_2220_ = lean_apply_4(v_toBind_2203_, lean_box(0), lean_box(0), v___x_2219_, v___f_2211_);
return v___x_2220_;
}
else
{
lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___f_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___f_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; 
lean_dec_ref(v___x_2202_);
v___x_2221_ = lean_box(v_usedLetOnly_2197_);
v___x_2222_ = lean_box(v_skipConstInApp_2198_);
v___x_2223_ = lean_box(v_skipInstances_2191_);
lean_inc_n(v___y_2207_, 2);
lean_inc(v_x_2200_);
lean_inc(v_post_2196_);
lean_inc(v_pre_2195_);
lean_inc_ref(v_inst_2194_);
lean_inc_n(v_inst_2193_, 2);
lean_inc_ref(v_inst_2192_);
lean_inc_ref(v_f_2206_);
v___f_2224_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5___boxed), 13, 12);
lean_closure_set(v___f_2224_, 0, v_f_2206_);
lean_closure_set(v___f_2224_, 1, v_inst_2192_);
lean_closure_set(v___f_2224_, 2, v_inst_2193_);
lean_closure_set(v___f_2224_, 3, v_inst_2194_);
lean_closure_set(v___f_2224_, 4, v_pre_2195_);
lean_closure_set(v___f_2224_, 5, v_post_2196_);
lean_closure_set(v___f_2224_, 6, v___x_2221_);
lean_closure_set(v___f_2224_, 7, v___x_2222_);
lean_closure_set(v___f_2224_, 8, v___x_2223_);
lean_closure_set(v___f_2224_, 9, v_x_2199_);
lean_closure_set(v___f_2224_, 10, v_x_2200_);
lean_closure_set(v___f_2224_, 11, v___y_2207_);
v___x_2225_ = lean_array_get_size(v_args_2201_);
v___x_2226_ = lean_box(v_usedLetOnly_2197_);
v___x_2227_ = lean_box(v_skipConstInApp_2198_);
v___x_2228_ = lean_box(v_skipInstances_2191_);
lean_inc(v_toBind_2203_);
v___f_2229_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__3___boxed), 18, 17);
lean_closure_set(v___f_2229_, 0, v___x_2225_);
lean_closure_set(v___f_2229_, 1, v_toApplicative_2204_);
lean_closure_set(v___f_2229_, 2, v_toBind_2203_);
lean_closure_set(v___f_2229_, 3, v___f_2205_);
lean_closure_set(v___f_2229_, 4, v_inst_2192_);
lean_closure_set(v___f_2229_, 5, v_inst_2193_);
lean_closure_set(v___f_2229_, 6, v_inst_2194_);
lean_closure_set(v___f_2229_, 7, v_pre_2195_);
lean_closure_set(v___f_2229_, 8, v_post_2196_);
lean_closure_set(v___f_2229_, 9, v___x_2226_);
lean_closure_set(v___f_2229_, 10, v___x_2227_);
lean_closure_set(v___f_2229_, 11, v___x_2228_);
lean_closure_set(v___f_2229_, 12, v_x_2199_);
lean_closure_set(v___f_2229_, 13, v_x_2200_);
lean_closure_set(v___f_2229_, 14, v_args_2201_);
lean_closure_set(v___f_2229_, 15, v___y_2207_);
lean_closure_set(v___f_2229_, 16, v___f_2224_);
v___x_2230_ = lean_alloc_closure((void*)(l_Lean_Meta_getFunInfoNArgs___boxed), 7, 2);
lean_closure_set(v___x_2230_, 0, v_f_2206_);
lean_closure_set(v___x_2230_, 1, v___x_2225_);
v___x_2231_ = lean_apply_2(v_inst_2193_, lean_box(0), v___x_2230_);
v___x_2232_ = lean_apply_4(v_toBind_2203_, lean_box(0), lean_box(0), v___x_2231_, v___f_2229_);
return v___x_2232_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__6___boxed(lean_object** _args){
lean_object* v_skipInstances_2233_ = _args[0];
lean_object* v_inst_2234_ = _args[1];
lean_object* v_inst_2235_ = _args[2];
lean_object* v_inst_2236_ = _args[3];
lean_object* v_pre_2237_ = _args[4];
lean_object* v_post_2238_ = _args[5];
lean_object* v_usedLetOnly_2239_ = _args[6];
lean_object* v_skipConstInApp_2240_ = _args[7];
lean_object* v_x_2241_ = _args[8];
lean_object* v_x_2242_ = _args[9];
lean_object* v_args_2243_ = _args[10];
lean_object* v___x_2244_ = _args[11];
lean_object* v_toBind_2245_ = _args[12];
lean_object* v_toApplicative_2246_ = _args[13];
lean_object* v___f_2247_ = _args[14];
lean_object* v_f_2248_ = _args[15];
lean_object* v___y_2249_ = _args[16];
_start:
{
uint8_t v_skipInstances_boxed_2250_; uint8_t v_usedLetOnly_boxed_2251_; uint8_t v_skipConstInApp_boxed_2252_; lean_object* v_res_2253_; 
v_skipInstances_boxed_2250_ = lean_unbox(v_skipInstances_2233_);
v_usedLetOnly_boxed_2251_ = lean_unbox(v_usedLetOnly_2239_);
v_skipConstInApp_boxed_2252_ = lean_unbox(v_skipConstInApp_2240_);
v_res_2253_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__6(v_skipInstances_boxed_2250_, v_inst_2234_, v_inst_2235_, v_inst_2236_, v_pre_2237_, v_post_2238_, v_usedLetOnly_boxed_2251_, v_skipConstInApp_boxed_2252_, v_x_2241_, v_x_2242_, v_args_2243_, v___x_2244_, v_toBind_2245_, v_toApplicative_2246_, v___f_2247_, v_f_2248_, v___y_2249_);
lean_dec(v___y_2249_);
return v_res_2253_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__9(uint8_t v_skipInstances_2254_, lean_object* v_inst_2255_, lean_object* v_inst_2256_, lean_object* v_inst_2257_, lean_object* v_pre_2258_, lean_object* v_post_2259_, uint8_t v_usedLetOnly_2260_, uint8_t v_skipConstInApp_2261_, lean_object* v_x_2262_, lean_object* v_x_2263_, lean_object* v___x_2264_, lean_object* v_toBind_2265_, lean_object* v_toApplicative_2266_, lean_object* v___f_2267_, lean_object* v_f_2268_, lean_object* v_args_2269_, lean_object* v___y_2270_){
_start:
{
lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___f_2274_; lean_object* v___f_2275_; 
v___x_2271_ = lean_box(v_skipInstances_2254_);
v___x_2272_ = lean_box(v_usedLetOnly_2260_);
v___x_2273_ = lean_box(v_skipConstInApp_2261_);
lean_inc_ref(v_toApplicative_2266_);
lean_inc(v_toBind_2265_);
lean_inc(v_x_2263_);
lean_inc(v_post_2259_);
lean_inc(v_pre_2258_);
lean_inc_ref(v_inst_2257_);
lean_inc(v_inst_2256_);
lean_inc_ref(v_inst_2255_);
v___f_2274_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__6___boxed), 17, 15);
lean_closure_set(v___f_2274_, 0, v___x_2271_);
lean_closure_set(v___f_2274_, 1, v_inst_2255_);
lean_closure_set(v___f_2274_, 2, v_inst_2256_);
lean_closure_set(v___f_2274_, 3, v_inst_2257_);
lean_closure_set(v___f_2274_, 4, v_pre_2258_);
lean_closure_set(v___f_2274_, 5, v_post_2259_);
lean_closure_set(v___f_2274_, 6, v___x_2272_);
lean_closure_set(v___f_2274_, 7, v___x_2273_);
lean_closure_set(v___f_2274_, 8, v_x_2262_);
lean_closure_set(v___f_2274_, 9, v_x_2263_);
lean_closure_set(v___f_2274_, 10, v_args_2269_);
lean_closure_set(v___f_2274_, 11, v___x_2264_);
lean_closure_set(v___f_2274_, 12, v_toBind_2265_);
lean_closure_set(v___f_2274_, 13, v_toApplicative_2266_);
lean_closure_set(v___f_2274_, 14, v___f_2267_);
lean_inc(v___y_2270_);
v___f_2275_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__7___boxed), 3, 2);
lean_closure_set(v___f_2275_, 0, v___f_2274_);
lean_closure_set(v___f_2275_, 1, v___y_2270_);
if (v_skipConstInApp_2261_ == 0)
{
lean_dec_ref(v_toApplicative_2266_);
goto v___jp_2276_;
}
else
{
uint8_t v___x_2279_; 
v___x_2279_ = l_Lean_Expr_isConst(v_f_2268_);
if (v___x_2279_ == 0)
{
lean_dec_ref(v_toApplicative_2266_);
goto v___jp_2276_;
}
else
{
lean_object* v_toPure_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; 
lean_dec(v_x_2263_);
lean_dec(v_post_2259_);
lean_dec(v_pre_2258_);
lean_dec_ref(v_inst_2257_);
lean_dec(v_inst_2256_);
lean_dec_ref(v_inst_2255_);
v_toPure_2280_ = lean_ctor_get(v_toApplicative_2266_, 1);
lean_inc(v_toPure_2280_);
lean_dec_ref(v_toApplicative_2266_);
v___x_2281_ = lean_apply_2(v_toPure_2280_, lean_box(0), v_f_2268_);
v___x_2282_ = lean_apply_4(v_toBind_2265_, lean_box(0), lean_box(0), v___x_2281_, v___f_2275_);
return v___x_2282_;
}
}
v___jp_2276_:
{
lean_object* v___x_2277_; lean_object* v___x_2278_; 
v___x_2277_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2255_, v_inst_2256_, v_inst_2257_, v_pre_2258_, v_post_2259_, v_usedLetOnly_2260_, v_skipConstInApp_2261_, v_skipInstances_2254_, v_x_2262_, v_x_2263_, v_f_2268_, v___y_2270_);
v___x_2278_ = lean_apply_4(v_toBind_2265_, lean_box(0), lean_box(0), v___x_2277_, v___f_2275_);
return v___x_2278_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__9___boxed(lean_object** _args){
lean_object* v_skipInstances_2283_ = _args[0];
lean_object* v_inst_2284_ = _args[1];
lean_object* v_inst_2285_ = _args[2];
lean_object* v_inst_2286_ = _args[3];
lean_object* v_pre_2287_ = _args[4];
lean_object* v_post_2288_ = _args[5];
lean_object* v_usedLetOnly_2289_ = _args[6];
lean_object* v_skipConstInApp_2290_ = _args[7];
lean_object* v_x_2291_ = _args[8];
lean_object* v_x_2292_ = _args[9];
lean_object* v___x_2293_ = _args[10];
lean_object* v_toBind_2294_ = _args[11];
lean_object* v_toApplicative_2295_ = _args[12];
lean_object* v___f_2296_ = _args[13];
lean_object* v_f_2297_ = _args[14];
lean_object* v_args_2298_ = _args[15];
lean_object* v___y_2299_ = _args[16];
_start:
{
uint8_t v_skipInstances_boxed_2300_; uint8_t v_usedLetOnly_boxed_2301_; uint8_t v_skipConstInApp_boxed_2302_; lean_object* v_res_2303_; 
v_skipInstances_boxed_2300_ = lean_unbox(v_skipInstances_2283_);
v_usedLetOnly_boxed_2301_ = lean_unbox(v_usedLetOnly_2289_);
v_skipConstInApp_boxed_2302_ = lean_unbox(v_skipConstInApp_2290_);
v_res_2303_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__9(v_skipInstances_boxed_2300_, v_inst_2284_, v_inst_2285_, v_inst_2286_, v_pre_2287_, v_post_2288_, v_usedLetOnly_boxed_2301_, v_skipConstInApp_boxed_2302_, v_x_2291_, v_x_2292_, v___x_2293_, v_toBind_2294_, v_toApplicative_2295_, v___f_2296_, v_f_2297_, v_args_2298_, v___y_2299_);
lean_dec(v___y_2299_);
return v_res_2303_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__0(lean_object* v_fvars_2306_, lean_object* v_inst_2307_, lean_object* v_inst_2308_, lean_object* v_inst_2309_, lean_object* v_pre_2310_, lean_object* v_post_2311_, uint8_t v_usedLetOnly_2312_, uint8_t v_skipConstInApp_2313_, uint8_t v_skipInstances_2314_, lean_object* v_x_2315_, lean_object* v_x_2316_, lean_object* v_body_2317_, lean_object* v_x_2318_, lean_object* v___y_2319_){
_start:
{
lean_object* v___x_2320_; lean_object* v___x_2321_; 
v___x_2320_ = lean_array_push(v_fvars_2306_, v_x_2318_);
v___x_2321_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(v_inst_2307_, v_inst_2308_, v_inst_2309_, v_pre_2310_, v_post_2311_, v_usedLetOnly_2312_, v_skipConstInApp_2313_, v_skipInstances_2314_, v_x_2315_, v_x_2316_, v___x_2320_, v_body_2317_, v___y_2319_);
return v___x_2321_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__0___boxed(lean_object* v_fvars_2322_, lean_object* v_inst_2323_, lean_object* v_inst_2324_, lean_object* v_inst_2325_, lean_object* v_pre_2326_, lean_object* v_post_2327_, lean_object* v_usedLetOnly_2328_, lean_object* v_skipConstInApp_2329_, lean_object* v_skipInstances_2330_, lean_object* v_x_2331_, lean_object* v_x_2332_, lean_object* v_body_2333_, lean_object* v_x_2334_, lean_object* v___y_2335_){
_start:
{
uint8_t v_usedLetOnly_boxed_2336_; uint8_t v_skipConstInApp_boxed_2337_; uint8_t v_skipInstances_boxed_2338_; lean_object* v_res_2339_; 
v_usedLetOnly_boxed_2336_ = lean_unbox(v_usedLetOnly_2328_);
v_skipConstInApp_boxed_2337_ = lean_unbox(v_skipConstInApp_2329_);
v_skipInstances_boxed_2338_ = lean_unbox(v_skipInstances_2330_);
v_res_2339_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__0(v_fvars_2322_, v_inst_2323_, v_inst_2324_, v_inst_2325_, v_pre_2326_, v_post_2327_, v_usedLetOnly_boxed_2336_, v_skipConstInApp_boxed_2337_, v_skipInstances_boxed_2338_, v_x_2331_, v_x_2332_, v_body_2333_, v_x_2334_, v___y_2335_);
lean_dec(v___y_2335_);
return v_res_2339_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3___boxed(lean_object* v_inst_2340_, lean_object* v_inst_2341_, lean_object* v_inst_2342_, lean_object* v_pre_2343_, lean_object* v_post_2344_, lean_object* v_usedLetOnly_2345_, lean_object* v_skipConstInApp_2346_, lean_object* v_skipInstances_2347_, lean_object* v_x_2348_, lean_object* v_x_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_){
_start:
{
uint8_t v_usedLetOnly_boxed_2352_; uint8_t v_skipConstInApp_boxed_2353_; uint8_t v_skipInstances_boxed_2354_; lean_object* v_res_2355_; 
v_usedLetOnly_boxed_2352_ = lean_unbox(v_usedLetOnly_2345_);
v_skipConstInApp_boxed_2353_ = lean_unbox(v_skipConstInApp_2346_);
v_skipInstances_boxed_2354_ = lean_unbox(v_skipInstances_2347_);
v_res_2355_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3(v_inst_2340_, v_inst_2341_, v_inst_2342_, v_pre_2343_, v_post_2344_, v_usedLetOnly_boxed_2352_, v_skipConstInApp_boxed_2353_, v_skipInstances_boxed_2354_, v_x_2348_, v_x_2349_, v_a_2350_, v_a_2351_);
lean_dec(v_a_2350_);
return v_res_2355_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(lean_object* v_inst_2356_, lean_object* v_inst_2357_, lean_object* v_inst_2358_, lean_object* v_pre_2359_, lean_object* v_post_2360_, uint8_t v_usedLetOnly_2361_, uint8_t v_skipConstInApp_2362_, uint8_t v_skipInstances_2363_, lean_object* v_x_2364_, lean_object* v_x_2365_, lean_object* v_fvars_2366_, lean_object* v_e_2367_, lean_object* v_a_2368_){
_start:
{
lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___f_2373_; lean_object* v___f_2374_; lean_object* v___x_2375_; 
v___x_2369_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0));
v___x_2370_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1));
lean_inc_ref(v_inst_2356_);
v___x_2371_ = l_Lean_MonadCacheT_instMonad___redArg(v_x_2364_, v___x_2369_, v___x_2370_, v_inst_2356_);
v___x_2372_ = l_Lean_MonadCacheT_instMonadControl___redArg(v_x_2364_, v___x_2369_, v___x_2370_);
lean_inc_ref_n(v_inst_2358_, 2);
lean_inc_ref(v___x_2372_);
v___f_2373_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_2373_, 0, v___x_2372_);
lean_closure_set(v___f_2373_, 1, v_inst_2358_);
v___f_2374_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_2374_, 0, v___x_2372_);
lean_closure_set(v___f_2374_, 1, v_inst_2358_);
v___x_2375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2375_, 0, v___f_2373_);
lean_ctor_set(v___x_2375_, 1, v___f_2374_);
if (lean_obj_tag(v_e_2367_) == 7)
{
lean_object* v_binderName_2376_; lean_object* v_binderType_2377_; lean_object* v_body_2378_; uint8_t v_binderInfo_2379_; lean_object* v_toBind_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___f_2384_; lean_object* v___x_2385_; lean_object* v___f_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; 
v_binderName_2376_ = lean_ctor_get(v_e_2367_, 0);
lean_inc(v_binderName_2376_);
v_binderType_2377_ = lean_ctor_get(v_e_2367_, 1);
lean_inc_ref(v_binderType_2377_);
v_body_2378_ = lean_ctor_get(v_e_2367_, 2);
lean_inc_ref(v_body_2378_);
v_binderInfo_2379_ = lean_ctor_get_uint8(v_e_2367_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2367_, 3);
v_toBind_2380_ = lean_ctor_get(v_inst_2356_, 1);
lean_inc(v_toBind_2380_);
v___x_2381_ = lean_box(v_usedLetOnly_2361_);
v___x_2382_ = lean_box(v_skipConstInApp_2362_);
v___x_2383_ = lean_box(v_skipInstances_2363_);
lean_inc(v_x_2365_);
lean_inc(v_post_2360_);
lean_inc(v_pre_2359_);
lean_inc_ref(v_inst_2358_);
lean_inc(v_inst_2357_);
lean_inc_ref(v_inst_2356_);
lean_inc_ref(v_fvars_2366_);
v___f_2384_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__0___boxed), 14, 12);
lean_closure_set(v___f_2384_, 0, v_fvars_2366_);
lean_closure_set(v___f_2384_, 1, v_inst_2356_);
lean_closure_set(v___f_2384_, 2, v_inst_2357_);
lean_closure_set(v___f_2384_, 3, v_inst_2358_);
lean_closure_set(v___f_2384_, 4, v_pre_2359_);
lean_closure_set(v___f_2384_, 5, v_post_2360_);
lean_closure_set(v___f_2384_, 6, v___x_2381_);
lean_closure_set(v___f_2384_, 7, v___x_2382_);
lean_closure_set(v___f_2384_, 8, v___x_2383_);
lean_closure_set(v___f_2384_, 9, v_x_2364_);
lean_closure_set(v___f_2384_, 10, v_x_2365_);
lean_closure_set(v___f_2384_, 11, v_body_2378_);
v___x_2385_ = lean_box(v_binderInfo_2379_);
lean_inc(v_a_2368_);
v___f_2386_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_2386_, 0, v___x_2375_);
lean_closure_set(v___f_2386_, 1, v___x_2371_);
lean_closure_set(v___f_2386_, 2, v_binderName_2376_);
lean_closure_set(v___f_2386_, 3, v___x_2385_);
lean_closure_set(v___f_2386_, 4, v___f_2384_);
lean_closure_set(v___f_2386_, 5, v_a_2368_);
v___x_2387_ = lean_expr_instantiate_rev(v_binderType_2377_, v_fvars_2366_);
lean_dec_ref(v_fvars_2366_);
lean_dec_ref(v_binderType_2377_);
v___x_2388_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2356_, v_inst_2357_, v_inst_2358_, v_pre_2359_, v_post_2360_, v_usedLetOnly_2361_, v_skipConstInApp_2362_, v_skipInstances_2363_, v_x_2364_, v_x_2365_, v___x_2387_, v_a_2368_);
v___x_2389_ = lean_apply_4(v_toBind_2380_, lean_box(0), lean_box(0), v___x_2388_, v___f_2386_);
return v___x_2389_;
}
else
{
lean_object* v_toBind_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___f_2394_; lean_object* v___x_2395_; lean_object* v___f_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; 
lean_dec_ref_known(v___x_2375_, 2);
lean_dec_ref(v___x_2371_);
v_toBind_2390_ = lean_ctor_get(v_inst_2356_, 1);
lean_inc_n(v_toBind_2390_, 2);
v___x_2391_ = lean_box(v_usedLetOnly_2361_);
v___x_2392_ = lean_box(v_skipConstInApp_2362_);
v___x_2393_ = lean_box(v_skipInstances_2363_);
lean_inc(v_a_2368_);
lean_inc(v_x_2365_);
lean_inc(v_post_2360_);
lean_inc(v_pre_2359_);
lean_inc_ref(v_inst_2358_);
lean_inc_n(v_inst_2357_, 2);
lean_inc_ref(v_inst_2356_);
v___f_2394_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3___boxed), 12, 11);
lean_closure_set(v___f_2394_, 0, v_inst_2356_);
lean_closure_set(v___f_2394_, 1, v_inst_2357_);
lean_closure_set(v___f_2394_, 2, v_inst_2358_);
lean_closure_set(v___f_2394_, 3, v_pre_2359_);
lean_closure_set(v___f_2394_, 4, v_post_2360_);
lean_closure_set(v___f_2394_, 5, v___x_2391_);
lean_closure_set(v___f_2394_, 6, v___x_2392_);
lean_closure_set(v___f_2394_, 7, v___x_2393_);
lean_closure_set(v___f_2394_, 8, v_x_2364_);
lean_closure_set(v___f_2394_, 9, v_x_2365_);
lean_closure_set(v___f_2394_, 10, v_a_2368_);
v___x_2395_ = lean_box(v_usedLetOnly_2361_);
lean_inc_ref(v_fvars_2366_);
v___f_2396_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__3___boxed), 6, 5);
lean_closure_set(v___f_2396_, 0, v_fvars_2366_);
lean_closure_set(v___f_2396_, 1, v___x_2395_);
lean_closure_set(v___f_2396_, 2, v_inst_2357_);
lean_closure_set(v___f_2396_, 3, v_toBind_2390_);
lean_closure_set(v___f_2396_, 4, v___f_2394_);
v___x_2397_ = lean_expr_instantiate_rev(v_e_2367_, v_fvars_2366_);
lean_dec_ref(v_fvars_2366_);
lean_dec_ref(v_e_2367_);
v___x_2398_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2356_, v_inst_2357_, v_inst_2358_, v_pre_2359_, v_post_2360_, v_usedLetOnly_2361_, v_skipConstInApp_2362_, v_skipInstances_2363_, v_x_2364_, v_x_2365_, v___x_2397_, v_a_2368_);
v___x_2399_ = lean_apply_4(v_toBind_2390_, lean_box(0), lean_box(0), v___x_2398_, v___f_2396_);
return v___x_2399_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__0(lean_object* v_fvars_2400_, lean_object* v_inst_2401_, lean_object* v_inst_2402_, lean_object* v_inst_2403_, lean_object* v_pre_2404_, lean_object* v_post_2405_, uint8_t v_usedLetOnly_2406_, uint8_t v_skipConstInApp_2407_, uint8_t v_skipInstances_2408_, lean_object* v_x_2409_, lean_object* v_x_2410_, lean_object* v_body_2411_, lean_object* v_x_2412_, lean_object* v___y_2413_){
_start:
{
lean_object* v___x_2414_; lean_object* v___x_2415_; 
v___x_2414_ = lean_array_push(v_fvars_2400_, v_x_2412_);
v___x_2415_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(v_inst_2401_, v_inst_2402_, v_inst_2403_, v_pre_2404_, v_post_2405_, v_usedLetOnly_2406_, v_skipConstInApp_2407_, v_skipInstances_2408_, v_x_2409_, v_x_2410_, v___x_2414_, v_body_2411_, v___y_2413_);
return v___x_2415_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__0___boxed(lean_object* v_fvars_2416_, lean_object* v_inst_2417_, lean_object* v_inst_2418_, lean_object* v_inst_2419_, lean_object* v_pre_2420_, lean_object* v_post_2421_, lean_object* v_usedLetOnly_2422_, lean_object* v_skipConstInApp_2423_, lean_object* v_skipInstances_2424_, lean_object* v_x_2425_, lean_object* v_x_2426_, lean_object* v_body_2427_, lean_object* v_x_2428_, lean_object* v___y_2429_){
_start:
{
uint8_t v_usedLetOnly_boxed_2430_; uint8_t v_skipConstInApp_boxed_2431_; uint8_t v_skipInstances_boxed_2432_; lean_object* v_res_2433_; 
v_usedLetOnly_boxed_2430_ = lean_unbox(v_usedLetOnly_2422_);
v_skipConstInApp_boxed_2431_ = lean_unbox(v_skipConstInApp_2423_);
v_skipInstances_boxed_2432_ = lean_unbox(v_skipInstances_2424_);
v_res_2433_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__0(v_fvars_2416_, v_inst_2417_, v_inst_2418_, v_inst_2419_, v_pre_2420_, v_post_2421_, v_usedLetOnly_boxed_2430_, v_skipConstInApp_boxed_2431_, v_skipInstances_boxed_2432_, v_x_2425_, v_x_2426_, v_body_2427_, v_x_2428_, v___y_2429_);
lean_dec(v___y_2429_);
return v_res_2433_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(lean_object* v_inst_2434_, lean_object* v_inst_2435_, lean_object* v_inst_2436_, lean_object* v_pre_2437_, lean_object* v_post_2438_, uint8_t v_usedLetOnly_2439_, uint8_t v_skipConstInApp_2440_, uint8_t v_skipInstances_2441_, lean_object* v_x_2442_, lean_object* v_x_2443_, lean_object* v_fvars_2444_, lean_object* v_e_2445_, lean_object* v_a_2446_){
_start:
{
lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___f_2451_; lean_object* v___f_2452_; lean_object* v___x_2453_; 
v___x_2447_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0));
v___x_2448_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1));
lean_inc_ref(v_inst_2434_);
v___x_2449_ = l_Lean_MonadCacheT_instMonad___redArg(v_x_2442_, v___x_2447_, v___x_2448_, v_inst_2434_);
v___x_2450_ = l_Lean_MonadCacheT_instMonadControl___redArg(v_x_2442_, v___x_2447_, v___x_2448_);
lean_inc_ref_n(v_inst_2436_, 2);
lean_inc_ref(v___x_2450_);
v___f_2451_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_2451_, 0, v___x_2450_);
lean_closure_set(v___f_2451_, 1, v_inst_2436_);
v___f_2452_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_2452_, 0, v___x_2450_);
lean_closure_set(v___f_2452_, 1, v_inst_2436_);
v___x_2453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2453_, 0, v___f_2451_);
lean_ctor_set(v___x_2453_, 1, v___f_2452_);
if (lean_obj_tag(v_e_2445_) == 6)
{
lean_object* v_binderName_2454_; lean_object* v_binderType_2455_; lean_object* v_body_2456_; uint8_t v_binderInfo_2457_; lean_object* v_toBind_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___f_2462_; lean_object* v___x_2463_; lean_object* v___f_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; 
v_binderName_2454_ = lean_ctor_get(v_e_2445_, 0);
lean_inc(v_binderName_2454_);
v_binderType_2455_ = lean_ctor_get(v_e_2445_, 1);
lean_inc_ref(v_binderType_2455_);
v_body_2456_ = lean_ctor_get(v_e_2445_, 2);
lean_inc_ref(v_body_2456_);
v_binderInfo_2457_ = lean_ctor_get_uint8(v_e_2445_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2445_, 3);
v_toBind_2458_ = lean_ctor_get(v_inst_2434_, 1);
lean_inc(v_toBind_2458_);
v___x_2459_ = lean_box(v_usedLetOnly_2439_);
v___x_2460_ = lean_box(v_skipConstInApp_2440_);
v___x_2461_ = lean_box(v_skipInstances_2441_);
lean_inc(v_x_2443_);
lean_inc(v_post_2438_);
lean_inc(v_pre_2437_);
lean_inc_ref(v_inst_2436_);
lean_inc(v_inst_2435_);
lean_inc_ref(v_inst_2434_);
lean_inc_ref(v_fvars_2444_);
v___f_2462_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__0___boxed), 14, 12);
lean_closure_set(v___f_2462_, 0, v_fvars_2444_);
lean_closure_set(v___f_2462_, 1, v_inst_2434_);
lean_closure_set(v___f_2462_, 2, v_inst_2435_);
lean_closure_set(v___f_2462_, 3, v_inst_2436_);
lean_closure_set(v___f_2462_, 4, v_pre_2437_);
lean_closure_set(v___f_2462_, 5, v_post_2438_);
lean_closure_set(v___f_2462_, 6, v___x_2459_);
lean_closure_set(v___f_2462_, 7, v___x_2460_);
lean_closure_set(v___f_2462_, 8, v___x_2461_);
lean_closure_set(v___f_2462_, 9, v_x_2442_);
lean_closure_set(v___f_2462_, 10, v_x_2443_);
lean_closure_set(v___f_2462_, 11, v_body_2456_);
v___x_2463_ = lean_box(v_binderInfo_2457_);
lean_inc(v_a_2446_);
v___f_2464_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_2464_, 0, v___x_2453_);
lean_closure_set(v___f_2464_, 1, v___x_2449_);
lean_closure_set(v___f_2464_, 2, v_binderName_2454_);
lean_closure_set(v___f_2464_, 3, v___x_2463_);
lean_closure_set(v___f_2464_, 4, v___f_2462_);
lean_closure_set(v___f_2464_, 5, v_a_2446_);
v___x_2465_ = lean_expr_instantiate_rev(v_binderType_2455_, v_fvars_2444_);
lean_dec_ref(v_fvars_2444_);
lean_dec_ref(v_binderType_2455_);
v___x_2466_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2434_, v_inst_2435_, v_inst_2436_, v_pre_2437_, v_post_2438_, v_usedLetOnly_2439_, v_skipConstInApp_2440_, v_skipInstances_2441_, v_x_2442_, v_x_2443_, v___x_2465_, v_a_2446_);
v___x_2467_ = lean_apply_4(v_toBind_2458_, lean_box(0), lean_box(0), v___x_2466_, v___f_2464_);
return v___x_2467_;
}
else
{
lean_object* v_toBind_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___f_2472_; lean_object* v___x_2473_; lean_object* v___f_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; 
lean_dec_ref_known(v___x_2453_, 2);
lean_dec_ref(v___x_2449_);
v_toBind_2468_ = lean_ctor_get(v_inst_2434_, 1);
lean_inc_n(v_toBind_2468_, 2);
v___x_2469_ = lean_box(v_usedLetOnly_2439_);
v___x_2470_ = lean_box(v_skipConstInApp_2440_);
v___x_2471_ = lean_box(v_skipInstances_2441_);
lean_inc(v_a_2446_);
lean_inc(v_x_2443_);
lean_inc(v_post_2438_);
lean_inc(v_pre_2437_);
lean_inc_ref(v_inst_2436_);
lean_inc_n(v_inst_2435_, 2);
lean_inc_ref(v_inst_2434_);
v___f_2472_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3___boxed), 12, 11);
lean_closure_set(v___f_2472_, 0, v_inst_2434_);
lean_closure_set(v___f_2472_, 1, v_inst_2435_);
lean_closure_set(v___f_2472_, 2, v_inst_2436_);
lean_closure_set(v___f_2472_, 3, v_pre_2437_);
lean_closure_set(v___f_2472_, 4, v_post_2438_);
lean_closure_set(v___f_2472_, 5, v___x_2469_);
lean_closure_set(v___f_2472_, 6, v___x_2470_);
lean_closure_set(v___f_2472_, 7, v___x_2471_);
lean_closure_set(v___f_2472_, 8, v_x_2442_);
lean_closure_set(v___f_2472_, 9, v_x_2443_);
lean_closure_set(v___f_2472_, 10, v_a_2446_);
v___x_2473_ = lean_box(v_usedLetOnly_2439_);
lean_inc_ref(v_fvars_2444_);
v___f_2474_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__3___boxed), 6, 5);
lean_closure_set(v___f_2474_, 0, v_fvars_2444_);
lean_closure_set(v___f_2474_, 1, v___x_2473_);
lean_closure_set(v___f_2474_, 2, v_inst_2435_);
lean_closure_set(v___f_2474_, 3, v_toBind_2468_);
lean_closure_set(v___f_2474_, 4, v___f_2472_);
v___x_2475_ = lean_expr_instantiate_rev(v_e_2445_, v_fvars_2444_);
lean_dec_ref(v_fvars_2444_);
lean_dec_ref(v_e_2445_);
v___x_2476_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2434_, v_inst_2435_, v_inst_2436_, v_pre_2437_, v_post_2438_, v_usedLetOnly_2439_, v_skipConstInApp_2440_, v_skipInstances_2441_, v_x_2442_, v_x_2443_, v___x_2475_, v_a_2446_);
v___x_2477_ = lean_apply_4(v_toBind_2468_, lean_box(0), lean_box(0), v___x_2476_, v___f_2474_);
return v___x_2477_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__0(lean_object* v_fvars_2478_, lean_object* v_inst_2479_, lean_object* v_inst_2480_, lean_object* v_inst_2481_, lean_object* v_pre_2482_, lean_object* v_post_2483_, uint8_t v_usedLetOnly_2484_, uint8_t v_skipConstInApp_2485_, uint8_t v_skipInstances_2486_, lean_object* v_x_2487_, lean_object* v_x_2488_, lean_object* v_body_2489_, lean_object* v_x_2490_, lean_object* v___y_2491_){
_start:
{
lean_object* v___x_2492_; lean_object* v___x_2493_; 
v___x_2492_ = lean_array_push(v_fvars_2478_, v_x_2490_);
v___x_2493_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(v_inst_2479_, v_inst_2480_, v_inst_2481_, v_pre_2482_, v_post_2483_, v_usedLetOnly_2484_, v_skipConstInApp_2485_, v_skipInstances_2486_, v_x_2487_, v_x_2488_, v___x_2492_, v_body_2489_, v___y_2491_);
return v___x_2493_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__0___boxed(lean_object* v_fvars_2494_, lean_object* v_inst_2495_, lean_object* v_inst_2496_, lean_object* v_inst_2497_, lean_object* v_pre_2498_, lean_object* v_post_2499_, lean_object* v_usedLetOnly_2500_, lean_object* v_skipConstInApp_2501_, lean_object* v_skipInstances_2502_, lean_object* v_x_2503_, lean_object* v_x_2504_, lean_object* v_body_2505_, lean_object* v_x_2506_, lean_object* v___y_2507_){
_start:
{
uint8_t v_usedLetOnly_boxed_2508_; uint8_t v_skipConstInApp_boxed_2509_; uint8_t v_skipInstances_boxed_2510_; lean_object* v_res_2511_; 
v_usedLetOnly_boxed_2508_ = lean_unbox(v_usedLetOnly_2500_);
v_skipConstInApp_boxed_2509_ = lean_unbox(v_skipConstInApp_2501_);
v_skipInstances_boxed_2510_ = lean_unbox(v_skipInstances_2502_);
v_res_2511_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__0(v_fvars_2494_, v_inst_2495_, v_inst_2496_, v_inst_2497_, v_pre_2498_, v_post_2499_, v_usedLetOnly_boxed_2508_, v_skipConstInApp_boxed_2509_, v_skipInstances_boxed_2510_, v_x_2503_, v_x_2504_, v_body_2505_, v_x_2506_, v___y_2507_);
lean_dec(v___y_2507_);
return v_res_2511_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__2(lean_object* v___x_2512_, lean_object* v___x_2513_, lean_object* v_declName_2514_, lean_object* v___f_2515_, uint8_t v_nondep_2516_, lean_object* v_a_2517_, lean_object* v_value_2518_, lean_object* v_fvars_2519_, lean_object* v_inst_2520_, lean_object* v_inst_2521_, lean_object* v_inst_2522_, lean_object* v_pre_2523_, lean_object* v_post_2524_, uint8_t v_usedLetOnly_2525_, uint8_t v_skipConstInApp_2526_, uint8_t v_skipInstances_2527_, lean_object* v_x_2528_, lean_object* v_x_2529_, lean_object* v_toBind_2530_, lean_object* v_a_2531_){
_start:
{
lean_object* v___x_2532_; lean_object* v___f_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; 
v___x_2532_ = lean_box(v_nondep_2516_);
lean_inc(v_a_2517_);
v___f_2533_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_2533_, 0, v___x_2512_);
lean_closure_set(v___f_2533_, 1, v___x_2513_);
lean_closure_set(v___f_2533_, 2, v_declName_2514_);
lean_closure_set(v___f_2533_, 3, v_a_2531_);
lean_closure_set(v___f_2533_, 4, v___f_2515_);
lean_closure_set(v___f_2533_, 5, v___x_2532_);
lean_closure_set(v___f_2533_, 6, v_a_2517_);
v___x_2534_ = lean_expr_instantiate_rev(v_value_2518_, v_fvars_2519_);
v___x_2535_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2520_, v_inst_2521_, v_inst_2522_, v_pre_2523_, v_post_2524_, v_usedLetOnly_2525_, v_skipConstInApp_2526_, v_skipInstances_2527_, v_x_2528_, v_x_2529_, v___x_2534_, v_a_2517_);
v___x_2536_ = lean_apply_4(v_toBind_2530_, lean_box(0), lean_box(0), v___x_2535_, v___f_2533_);
return v___x_2536_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__2___boxed(lean_object** _args){
lean_object* v___x_2537_ = _args[0];
lean_object* v___x_2538_ = _args[1];
lean_object* v_declName_2539_ = _args[2];
lean_object* v___f_2540_ = _args[3];
lean_object* v_nondep_2541_ = _args[4];
lean_object* v_a_2542_ = _args[5];
lean_object* v_value_2543_ = _args[6];
lean_object* v_fvars_2544_ = _args[7];
lean_object* v_inst_2545_ = _args[8];
lean_object* v_inst_2546_ = _args[9];
lean_object* v_inst_2547_ = _args[10];
lean_object* v_pre_2548_ = _args[11];
lean_object* v_post_2549_ = _args[12];
lean_object* v_usedLetOnly_2550_ = _args[13];
lean_object* v_skipConstInApp_2551_ = _args[14];
lean_object* v_skipInstances_2552_ = _args[15];
lean_object* v_x_2553_ = _args[16];
lean_object* v_x_2554_ = _args[17];
lean_object* v_toBind_2555_ = _args[18];
lean_object* v_a_2556_ = _args[19];
_start:
{
uint8_t v_nondep_3815__boxed_2557_; uint8_t v_usedLetOnly_boxed_2558_; uint8_t v_skipConstInApp_boxed_2559_; uint8_t v_skipInstances_boxed_2560_; lean_object* v_res_2561_; 
v_nondep_3815__boxed_2557_ = lean_unbox(v_nondep_2541_);
v_usedLetOnly_boxed_2558_ = lean_unbox(v_usedLetOnly_2550_);
v_skipConstInApp_boxed_2559_ = lean_unbox(v_skipConstInApp_2551_);
v_skipInstances_boxed_2560_ = lean_unbox(v_skipInstances_2552_);
v_res_2561_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__2(v___x_2537_, v___x_2538_, v_declName_2539_, v___f_2540_, v_nondep_3815__boxed_2557_, v_a_2542_, v_value_2543_, v_fvars_2544_, v_inst_2545_, v_inst_2546_, v_inst_2547_, v_pre_2548_, v_post_2549_, v_usedLetOnly_boxed_2558_, v_skipConstInApp_boxed_2559_, v_skipInstances_boxed_2560_, v_x_2553_, v_x_2554_, v_toBind_2555_, v_a_2556_);
lean_dec_ref(v_fvars_2544_);
lean_dec_ref(v_value_2543_);
lean_dec(v_a_2542_);
return v_res_2561_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(lean_object* v_inst_2562_, lean_object* v_inst_2563_, lean_object* v_inst_2564_, lean_object* v_pre_2565_, lean_object* v_post_2566_, uint8_t v_usedLetOnly_2567_, uint8_t v_skipConstInApp_2568_, uint8_t v_skipInstances_2569_, lean_object* v_x_2570_, lean_object* v_x_2571_, lean_object* v_fvars_2572_, lean_object* v_e_2573_, lean_object* v_a_2574_){
_start:
{
lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___f_2579_; lean_object* v___f_2580_; lean_object* v___x_2581_; 
v___x_2575_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0));
v___x_2576_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1));
lean_inc_ref(v_inst_2562_);
v___x_2577_ = l_Lean_MonadCacheT_instMonad___redArg(v_x_2570_, v___x_2575_, v___x_2576_, v_inst_2562_);
v___x_2578_ = l_Lean_MonadCacheT_instMonadControl___redArg(v_x_2570_, v___x_2575_, v___x_2576_);
lean_inc_ref_n(v_inst_2564_, 2);
lean_inc_ref(v___x_2578_);
v___f_2579_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_2579_, 0, v___x_2578_);
lean_closure_set(v___f_2579_, 1, v_inst_2564_);
v___f_2580_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_2580_, 0, v___x_2578_);
lean_closure_set(v___f_2580_, 1, v_inst_2564_);
v___x_2581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2581_, 0, v___f_2579_);
lean_ctor_set(v___x_2581_, 1, v___f_2580_);
if (lean_obj_tag(v_e_2573_) == 8)
{
lean_object* v_declName_2582_; lean_object* v_type_2583_; lean_object* v_value_2584_; lean_object* v_body_2585_; uint8_t v_nondep_2586_; lean_object* v_toBind_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___f_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___f_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; 
v_declName_2582_ = lean_ctor_get(v_e_2573_, 0);
lean_inc(v_declName_2582_);
v_type_2583_ = lean_ctor_get(v_e_2573_, 1);
lean_inc_ref(v_type_2583_);
v_value_2584_ = lean_ctor_get(v_e_2573_, 2);
lean_inc_ref(v_value_2584_);
v_body_2585_ = lean_ctor_get(v_e_2573_, 3);
lean_inc_ref(v_body_2585_);
v_nondep_2586_ = lean_ctor_get_uint8(v_e_2573_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_2573_, 4);
v_toBind_2587_ = lean_ctor_get(v_inst_2562_, 1);
lean_inc_n(v_toBind_2587_, 2);
v___x_2588_ = lean_box(v_usedLetOnly_2567_);
v___x_2589_ = lean_box(v_skipConstInApp_2568_);
v___x_2590_ = lean_box(v_skipInstances_2569_);
lean_inc_n(v_x_2571_, 2);
lean_inc_n(v_post_2566_, 2);
lean_inc_n(v_pre_2565_, 2);
lean_inc_ref_n(v_inst_2564_, 2);
lean_inc_n(v_inst_2563_, 2);
lean_inc_ref_n(v_inst_2562_, 2);
lean_inc_ref_n(v_fvars_2572_, 2);
v___f_2591_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__0___boxed), 14, 12);
lean_closure_set(v___f_2591_, 0, v_fvars_2572_);
lean_closure_set(v___f_2591_, 1, v_inst_2562_);
lean_closure_set(v___f_2591_, 2, v_inst_2563_);
lean_closure_set(v___f_2591_, 3, v_inst_2564_);
lean_closure_set(v___f_2591_, 4, v_pre_2565_);
lean_closure_set(v___f_2591_, 5, v_post_2566_);
lean_closure_set(v___f_2591_, 6, v___x_2588_);
lean_closure_set(v___f_2591_, 7, v___x_2589_);
lean_closure_set(v___f_2591_, 8, v___x_2590_);
lean_closure_set(v___f_2591_, 9, v_x_2570_);
lean_closure_set(v___f_2591_, 10, v_x_2571_);
lean_closure_set(v___f_2591_, 11, v_body_2585_);
v___x_2592_ = lean_box(v_nondep_2586_);
v___x_2593_ = lean_box(v_usedLetOnly_2567_);
v___x_2594_ = lean_box(v_skipConstInApp_2568_);
v___x_2595_ = lean_box(v_skipInstances_2569_);
lean_inc(v_a_2574_);
v___f_2596_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__2___boxed), 20, 19);
lean_closure_set(v___f_2596_, 0, v___x_2581_);
lean_closure_set(v___f_2596_, 1, v___x_2577_);
lean_closure_set(v___f_2596_, 2, v_declName_2582_);
lean_closure_set(v___f_2596_, 3, v___f_2591_);
lean_closure_set(v___f_2596_, 4, v___x_2592_);
lean_closure_set(v___f_2596_, 5, v_a_2574_);
lean_closure_set(v___f_2596_, 6, v_value_2584_);
lean_closure_set(v___f_2596_, 7, v_fvars_2572_);
lean_closure_set(v___f_2596_, 8, v_inst_2562_);
lean_closure_set(v___f_2596_, 9, v_inst_2563_);
lean_closure_set(v___f_2596_, 10, v_inst_2564_);
lean_closure_set(v___f_2596_, 11, v_pre_2565_);
lean_closure_set(v___f_2596_, 12, v_post_2566_);
lean_closure_set(v___f_2596_, 13, v___x_2593_);
lean_closure_set(v___f_2596_, 14, v___x_2594_);
lean_closure_set(v___f_2596_, 15, v___x_2595_);
lean_closure_set(v___f_2596_, 16, v_x_2570_);
lean_closure_set(v___f_2596_, 17, v_x_2571_);
lean_closure_set(v___f_2596_, 18, v_toBind_2587_);
v___x_2597_ = lean_expr_instantiate_rev(v_type_2583_, v_fvars_2572_);
lean_dec_ref(v_fvars_2572_);
lean_dec_ref(v_type_2583_);
v___x_2598_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2562_, v_inst_2563_, v_inst_2564_, v_pre_2565_, v_post_2566_, v_usedLetOnly_2567_, v_skipConstInApp_2568_, v_skipInstances_2569_, v_x_2570_, v_x_2571_, v___x_2597_, v_a_2574_);
v___x_2599_ = lean_apply_4(v_toBind_2587_, lean_box(0), lean_box(0), v___x_2598_, v___f_2596_);
return v___x_2599_;
}
else
{
lean_object* v_toBind_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___f_2604_; lean_object* v___x_2605_; lean_object* v___f_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; 
lean_dec_ref_known(v___x_2581_, 2);
lean_dec_ref(v___x_2577_);
v_toBind_2600_ = lean_ctor_get(v_inst_2562_, 1);
lean_inc_n(v_toBind_2600_, 2);
v___x_2601_ = lean_box(v_usedLetOnly_2567_);
v___x_2602_ = lean_box(v_skipConstInApp_2568_);
v___x_2603_ = lean_box(v_skipInstances_2569_);
lean_inc(v_a_2574_);
lean_inc(v_x_2571_);
lean_inc(v_post_2566_);
lean_inc(v_pre_2565_);
lean_inc_ref(v_inst_2564_);
lean_inc_n(v_inst_2563_, 2);
lean_inc_ref(v_inst_2562_);
v___f_2604_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3___boxed), 12, 11);
lean_closure_set(v___f_2604_, 0, v_inst_2562_);
lean_closure_set(v___f_2604_, 1, v_inst_2563_);
lean_closure_set(v___f_2604_, 2, v_inst_2564_);
lean_closure_set(v___f_2604_, 3, v_pre_2565_);
lean_closure_set(v___f_2604_, 4, v_post_2566_);
lean_closure_set(v___f_2604_, 5, v___x_2601_);
lean_closure_set(v___f_2604_, 6, v___x_2602_);
lean_closure_set(v___f_2604_, 7, v___x_2603_);
lean_closure_set(v___f_2604_, 8, v_x_2570_);
lean_closure_set(v___f_2604_, 9, v_x_2571_);
lean_closure_set(v___f_2604_, 10, v_a_2574_);
v___x_2605_ = lean_box(v_usedLetOnly_2567_);
lean_inc_ref(v_fvars_2572_);
v___f_2606_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__4___boxed), 6, 5);
lean_closure_set(v___f_2606_, 0, v_fvars_2572_);
lean_closure_set(v___f_2606_, 1, v___x_2605_);
lean_closure_set(v___f_2606_, 2, v_inst_2563_);
lean_closure_set(v___f_2606_, 3, v_toBind_2600_);
lean_closure_set(v___f_2606_, 4, v___f_2604_);
v___x_2607_ = lean_expr_instantiate_rev(v_e_2573_, v_fvars_2572_);
lean_dec_ref(v_fvars_2572_);
lean_dec_ref(v_e_2573_);
v___x_2608_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2562_, v_inst_2563_, v_inst_2564_, v_pre_2565_, v_post_2566_, v_usedLetOnly_2567_, v_skipConstInApp_2568_, v_skipInstances_2569_, v_x_2570_, v_x_2571_, v___x_2607_, v_a_2574_);
v___x_2609_ = lean_apply_4(v_toBind_2600_, lean_box(0), lean_box(0), v___x_2608_, v___f_2606_);
return v___x_2609_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__8(lean_object* v_expr_2610_, lean_object* v_data_2611_, lean_object* v_inst_2612_, lean_object* v_inst_2613_, lean_object* v_inst_2614_, lean_object* v_pre_2615_, lean_object* v_post_2616_, uint8_t v_usedLetOnly_2617_, uint8_t v_skipConstInApp_2618_, uint8_t v_skipInstances_2619_, lean_object* v_x_2620_, lean_object* v_x_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v_a_2624_){
_start:
{
size_t v___x_2625_; size_t v___x_2626_; uint8_t v___x_2627_; 
v___x_2625_ = lean_ptr_addr(v_expr_2610_);
v___x_2626_ = lean_ptr_addr(v_a_2624_);
v___x_2627_ = lean_usize_dec_eq(v___x_2625_, v___x_2626_);
if (v___x_2627_ == 0)
{
lean_object* v___x_2628_; lean_object* v___x_2629_; 
lean_dec_ref(v___y_2623_);
v___x_2628_ = l_Lean_Expr_mdata___override(v_data_2611_, v_a_2624_);
v___x_2629_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2612_, v_inst_2613_, v_inst_2614_, v_pre_2615_, v_post_2616_, v_usedLetOnly_2617_, v_skipConstInApp_2618_, v_skipInstances_2619_, v_x_2620_, v_x_2621_, v___x_2628_, v___y_2622_);
return v___x_2629_;
}
else
{
lean_object* v___x_2630_; 
lean_dec_ref(v_a_2624_);
lean_dec(v_data_2611_);
v___x_2630_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2612_, v_inst_2613_, v_inst_2614_, v_pre_2615_, v_post_2616_, v_usedLetOnly_2617_, v_skipConstInApp_2618_, v_skipInstances_2619_, v_x_2620_, v_x_2621_, v___y_2623_, v___y_2622_);
return v___x_2630_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__8___boxed(lean_object* v_expr_2631_, lean_object* v_data_2632_, lean_object* v_inst_2633_, lean_object* v_inst_2634_, lean_object* v_inst_2635_, lean_object* v_pre_2636_, lean_object* v_post_2637_, lean_object* v_usedLetOnly_2638_, lean_object* v_skipConstInApp_2639_, lean_object* v_skipInstances_2640_, lean_object* v_x_2641_, lean_object* v_x_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v_a_2645_){
_start:
{
uint8_t v_usedLetOnly_boxed_2646_; uint8_t v_skipConstInApp_boxed_2647_; uint8_t v_skipInstances_boxed_2648_; lean_object* v_res_2649_; 
v_usedLetOnly_boxed_2646_ = lean_unbox(v_usedLetOnly_2638_);
v_skipConstInApp_boxed_2647_ = lean_unbox(v_skipConstInApp_2639_);
v_skipInstances_boxed_2648_ = lean_unbox(v_skipInstances_2640_);
v_res_2649_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__8(v_expr_2631_, v_data_2632_, v_inst_2633_, v_inst_2634_, v_inst_2635_, v_pre_2636_, v_post_2637_, v_usedLetOnly_boxed_2646_, v_skipConstInApp_boxed_2647_, v_skipInstances_boxed_2648_, v_x_2641_, v_x_2642_, v___y_2643_, v___y_2644_, v_a_2645_);
lean_dec(v___y_2643_);
lean_dec_ref(v_expr_2631_);
return v_res_2649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__10(lean_object* v_struct_2650_, lean_object* v_typeName_2651_, lean_object* v_idx_2652_, lean_object* v_inst_2653_, lean_object* v_inst_2654_, lean_object* v_inst_2655_, lean_object* v_pre_2656_, lean_object* v_post_2657_, uint8_t v_usedLetOnly_2658_, uint8_t v_skipConstInApp_2659_, uint8_t v_skipInstances_2660_, lean_object* v_x_2661_, lean_object* v_x_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v_a_2665_){
_start:
{
size_t v___x_2666_; size_t v___x_2667_; uint8_t v___x_2668_; 
v___x_2666_ = lean_ptr_addr(v_struct_2650_);
v___x_2667_ = lean_ptr_addr(v_a_2665_);
v___x_2668_ = lean_usize_dec_eq(v___x_2666_, v___x_2667_);
if (v___x_2668_ == 0)
{
lean_object* v___x_2669_; lean_object* v___x_2670_; 
lean_dec_ref(v___y_2664_);
v___x_2669_ = l_Lean_Expr_proj___override(v_typeName_2651_, v_idx_2652_, v_a_2665_);
v___x_2670_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2653_, v_inst_2654_, v_inst_2655_, v_pre_2656_, v_post_2657_, v_usedLetOnly_2658_, v_skipConstInApp_2659_, v_skipInstances_2660_, v_x_2661_, v_x_2662_, v___x_2669_, v___y_2663_);
return v___x_2670_;
}
else
{
lean_object* v___x_2671_; 
lean_dec_ref(v_a_2665_);
lean_dec(v_idx_2652_);
lean_dec(v_typeName_2651_);
v___x_2671_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2653_, v_inst_2654_, v_inst_2655_, v_pre_2656_, v_post_2657_, v_usedLetOnly_2658_, v_skipConstInApp_2659_, v_skipInstances_2660_, v_x_2661_, v_x_2662_, v___y_2664_, v___y_2663_);
return v___x_2671_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__10___boxed(lean_object* v_struct_2672_, lean_object* v_typeName_2673_, lean_object* v_idx_2674_, lean_object* v_inst_2675_, lean_object* v_inst_2676_, lean_object* v_inst_2677_, lean_object* v_pre_2678_, lean_object* v_post_2679_, lean_object* v_usedLetOnly_2680_, lean_object* v_skipConstInApp_2681_, lean_object* v_skipInstances_2682_, lean_object* v_x_2683_, lean_object* v_x_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v_a_2687_){
_start:
{
uint8_t v_usedLetOnly_boxed_2688_; uint8_t v_skipConstInApp_boxed_2689_; uint8_t v_skipInstances_boxed_2690_; lean_object* v_res_2691_; 
v_usedLetOnly_boxed_2688_ = lean_unbox(v_usedLetOnly_2680_);
v_skipConstInApp_boxed_2689_ = lean_unbox(v_skipConstInApp_2681_);
v_skipInstances_boxed_2690_ = lean_unbox(v_skipInstances_2682_);
v_res_2691_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__10(v_struct_2672_, v_typeName_2673_, v_idx_2674_, v_inst_2675_, v_inst_2676_, v_inst_2677_, v_pre_2678_, v_post_2679_, v_usedLetOnly_boxed_2688_, v_skipConstInApp_boxed_2689_, v_skipInstances_boxed_2690_, v_x_2683_, v_x_2684_, v___y_2685_, v___y_2686_, v_a_2687_);
lean_dec(v___y_2685_);
lean_dec_ref(v_struct_2672_);
return v_res_2691_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11(lean_object* v_toApplicative_2692_, lean_object* v_inst_2693_, lean_object* v_inst_2694_, lean_object* v_inst_2695_, lean_object* v_pre_2696_, lean_object* v_post_2697_, uint8_t v_usedLetOnly_2698_, uint8_t v_skipConstInApp_2699_, uint8_t v_skipInstances_2700_, lean_object* v_x_2701_, lean_object* v_x_2702_, lean_object* v___y_2703_, lean_object* v___f_2704_, lean_object* v_toBind_2705_, lean_object* v_e_2706_, lean_object* v_a_2707_){
_start:
{
lean_object* v___y_2709_; 
switch(lean_obj_tag(v_a_2707_))
{
case 0:
{
lean_object* v_e_2741_; lean_object* v_toPure_2742_; lean_object* v___x_2743_; 
lean_dec_ref(v_e_2706_);
lean_dec(v_toBind_2705_);
lean_dec(v___f_2704_);
lean_dec(v_x_2702_);
lean_dec(v_post_2697_);
lean_dec(v_pre_2696_);
lean_dec_ref(v_inst_2695_);
lean_dec(v_inst_2694_);
lean_dec_ref(v_inst_2693_);
v_e_2741_ = lean_ctor_get(v_a_2707_, 0);
lean_inc_ref(v_e_2741_);
lean_dec_ref_known(v_a_2707_, 1);
v_toPure_2742_ = lean_ctor_get(v_toApplicative_2692_, 1);
lean_inc(v_toPure_2742_);
lean_dec_ref(v_toApplicative_2692_);
v___x_2743_ = lean_apply_2(v_toPure_2742_, lean_box(0), v_e_2741_);
return v___x_2743_;
}
case 1:
{
lean_object* v_e_2744_; lean_object* v___x_2745_; 
lean_dec_ref(v_e_2706_);
lean_dec(v_toBind_2705_);
lean_dec(v___f_2704_);
lean_dec_ref(v_toApplicative_2692_);
v_e_2744_ = lean_ctor_get(v_a_2707_, 0);
lean_inc_ref(v_e_2744_);
lean_dec_ref_known(v_a_2707_, 1);
v___x_2745_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2693_, v_inst_2694_, v_inst_2695_, v_pre_2696_, v_post_2697_, v_usedLetOnly_2698_, v_skipConstInApp_2699_, v_skipInstances_2700_, v_x_2701_, v_x_2702_, v_e_2744_, v___y_2703_);
return v___x_2745_;
}
default: 
{
lean_object* v_e_x3f_2746_; 
lean_dec_ref(v_toApplicative_2692_);
v_e_x3f_2746_ = lean_ctor_get(v_a_2707_, 0);
lean_inc(v_e_x3f_2746_);
lean_dec_ref_known(v_a_2707_, 1);
if (lean_obj_tag(v_e_x3f_2746_) == 0)
{
v___y_2709_ = v_e_2706_;
goto v___jp_2708_;
}
else
{
lean_object* v_val_2747_; 
lean_dec_ref(v_e_2706_);
v_val_2747_ = lean_ctor_get(v_e_x3f_2746_, 0);
lean_inc(v_val_2747_);
lean_dec_ref_known(v_e_x3f_2746_, 1);
v___y_2709_ = v_val_2747_;
goto v___jp_2708_;
}
}
}
v___jp_2708_:
{
switch(lean_obj_tag(v___y_2709_))
{
case 7:
{
lean_object* v___x_2710_; lean_object* v___x_2711_; 
lean_dec(v_toBind_2705_);
lean_dec(v___f_2704_);
v___x_2710_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_2711_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(v_inst_2693_, v_inst_2694_, v_inst_2695_, v_pre_2696_, v_post_2697_, v_usedLetOnly_2698_, v_skipConstInApp_2699_, v_skipInstances_2700_, v_x_2701_, v_x_2702_, v___x_2710_, v___y_2709_, v___y_2703_);
return v___x_2711_;
}
case 6:
{
lean_object* v___x_2712_; lean_object* v___x_2713_; 
lean_dec(v_toBind_2705_);
lean_dec(v___f_2704_);
v___x_2712_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_2713_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(v_inst_2693_, v_inst_2694_, v_inst_2695_, v_pre_2696_, v_post_2697_, v_usedLetOnly_2698_, v_skipConstInApp_2699_, v_skipInstances_2700_, v_x_2701_, v_x_2702_, v___x_2712_, v___y_2709_, v___y_2703_);
return v___x_2713_;
}
case 8:
{
lean_object* v___x_2714_; lean_object* v___x_2715_; 
lean_dec(v_toBind_2705_);
lean_dec(v___f_2704_);
v___x_2714_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_2715_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(v_inst_2693_, v_inst_2694_, v_inst_2695_, v_pre_2696_, v_post_2697_, v_usedLetOnly_2698_, v_skipConstInApp_2699_, v_skipInstances_2700_, v_x_2701_, v_x_2702_, v___x_2714_, v___y_2709_, v___y_2703_);
return v___x_2715_;
}
case 5:
{
lean_object* v_dummy_2716_; lean_object* v_nargs_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_3361__overap_2721_; lean_object* v___x_2722_; 
lean_dec(v_toBind_2705_);
lean_dec(v_x_2702_);
lean_dec(v_post_2697_);
lean_dec(v_pre_2696_);
lean_dec_ref(v_inst_2695_);
lean_dec(v_inst_2694_);
lean_dec_ref(v_inst_2693_);
v_dummy_2716_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_2717_ = l_Lean_Expr_getAppNumArgs(v___y_2709_);
lean_inc(v_nargs_2717_);
v___x_2718_ = lean_mk_array(v_nargs_2717_, v_dummy_2716_);
v___x_2719_ = lean_unsigned_to_nat(1u);
v___x_2720_ = lean_nat_sub(v_nargs_2717_, v___x_2719_);
lean_dec(v_nargs_2717_);
v___x_3361__overap_2721_ = l_Lean_Expr_withAppAux___redArg(v___f_2704_, v___y_2709_, v___x_2718_, v___x_2720_);
lean_inc(v___y_2703_);
v___x_2722_ = lean_apply_1(v___x_3361__overap_2721_, v___y_2703_);
return v___x_2722_;
}
case 10:
{
lean_object* v_data_2723_; lean_object* v_expr_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___f_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; 
lean_dec(v___f_2704_);
v_data_2723_ = lean_ctor_get(v___y_2709_, 0);
lean_inc(v_data_2723_);
v_expr_2724_ = lean_ctor_get(v___y_2709_, 1);
lean_inc_ref_n(v_expr_2724_, 2);
v___x_2725_ = lean_box(v_usedLetOnly_2698_);
v___x_2726_ = lean_box(v_skipConstInApp_2699_);
v___x_2727_ = lean_box(v_skipInstances_2700_);
lean_inc(v___y_2703_);
lean_inc(v_x_2702_);
lean_inc(v_post_2697_);
lean_inc(v_pre_2696_);
lean_inc_ref(v_inst_2695_);
lean_inc(v_inst_2694_);
lean_inc_ref(v_inst_2693_);
v___f_2728_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__8___boxed), 15, 14);
lean_closure_set(v___f_2728_, 0, v_expr_2724_);
lean_closure_set(v___f_2728_, 1, v_data_2723_);
lean_closure_set(v___f_2728_, 2, v_inst_2693_);
lean_closure_set(v___f_2728_, 3, v_inst_2694_);
lean_closure_set(v___f_2728_, 4, v_inst_2695_);
lean_closure_set(v___f_2728_, 5, v_pre_2696_);
lean_closure_set(v___f_2728_, 6, v_post_2697_);
lean_closure_set(v___f_2728_, 7, v___x_2725_);
lean_closure_set(v___f_2728_, 8, v___x_2726_);
lean_closure_set(v___f_2728_, 9, v___x_2727_);
lean_closure_set(v___f_2728_, 10, v_x_2701_);
lean_closure_set(v___f_2728_, 11, v_x_2702_);
lean_closure_set(v___f_2728_, 12, v___y_2703_);
lean_closure_set(v___f_2728_, 13, v___y_2709_);
v___x_2729_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2693_, v_inst_2694_, v_inst_2695_, v_pre_2696_, v_post_2697_, v_usedLetOnly_2698_, v_skipConstInApp_2699_, v_skipInstances_2700_, v_x_2701_, v_x_2702_, v_expr_2724_, v___y_2703_);
v___x_2730_ = lean_apply_4(v_toBind_2705_, lean_box(0), lean_box(0), v___x_2729_, v___f_2728_);
return v___x_2730_;
}
case 11:
{
lean_object* v_typeName_2731_; lean_object* v_idx_2732_; lean_object* v_struct_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___f_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; 
lean_dec(v___f_2704_);
v_typeName_2731_ = lean_ctor_get(v___y_2709_, 0);
lean_inc(v_typeName_2731_);
v_idx_2732_ = lean_ctor_get(v___y_2709_, 1);
lean_inc(v_idx_2732_);
v_struct_2733_ = lean_ctor_get(v___y_2709_, 2);
lean_inc_ref_n(v_struct_2733_, 2);
v___x_2734_ = lean_box(v_usedLetOnly_2698_);
v___x_2735_ = lean_box(v_skipConstInApp_2699_);
v___x_2736_ = lean_box(v_skipInstances_2700_);
lean_inc(v___y_2703_);
lean_inc(v_x_2702_);
lean_inc(v_post_2697_);
lean_inc(v_pre_2696_);
lean_inc_ref(v_inst_2695_);
lean_inc(v_inst_2694_);
lean_inc_ref(v_inst_2693_);
v___f_2737_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__10___boxed), 16, 15);
lean_closure_set(v___f_2737_, 0, v_struct_2733_);
lean_closure_set(v___f_2737_, 1, v_typeName_2731_);
lean_closure_set(v___f_2737_, 2, v_idx_2732_);
lean_closure_set(v___f_2737_, 3, v_inst_2693_);
lean_closure_set(v___f_2737_, 4, v_inst_2694_);
lean_closure_set(v___f_2737_, 5, v_inst_2695_);
lean_closure_set(v___f_2737_, 6, v_pre_2696_);
lean_closure_set(v___f_2737_, 7, v_post_2697_);
lean_closure_set(v___f_2737_, 8, v___x_2734_);
lean_closure_set(v___f_2737_, 9, v___x_2735_);
lean_closure_set(v___f_2737_, 10, v___x_2736_);
lean_closure_set(v___f_2737_, 11, v_x_2701_);
lean_closure_set(v___f_2737_, 12, v_x_2702_);
lean_closure_set(v___f_2737_, 13, v___y_2703_);
lean_closure_set(v___f_2737_, 14, v___y_2709_);
v___x_2738_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2693_, v_inst_2694_, v_inst_2695_, v_pre_2696_, v_post_2697_, v_usedLetOnly_2698_, v_skipConstInApp_2699_, v_skipInstances_2700_, v_x_2701_, v_x_2702_, v_struct_2733_, v___y_2703_);
v___x_2739_ = lean_apply_4(v_toBind_2705_, lean_box(0), lean_box(0), v___x_2738_, v___f_2737_);
return v___x_2739_;
}
default: 
{
lean_object* v___x_2740_; 
lean_dec(v_toBind_2705_);
lean_dec(v___f_2704_);
v___x_2740_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2693_, v_inst_2694_, v_inst_2695_, v_pre_2696_, v_post_2697_, v_usedLetOnly_2698_, v_skipConstInApp_2699_, v_skipInstances_2700_, v_x_2701_, v_x_2702_, v___y_2709_, v___y_2703_);
return v___x_2740_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___boxed(lean_object* v_toApplicative_2748_, lean_object* v_inst_2749_, lean_object* v_inst_2750_, lean_object* v_inst_2751_, lean_object* v_pre_2752_, lean_object* v_post_2753_, lean_object* v_usedLetOnly_2754_, lean_object* v_skipConstInApp_2755_, lean_object* v_skipInstances_2756_, lean_object* v_x_2757_, lean_object* v_x_2758_, lean_object* v___y_2759_, lean_object* v___f_2760_, lean_object* v_toBind_2761_, lean_object* v_e_2762_, lean_object* v_a_2763_){
_start:
{
uint8_t v_usedLetOnly_boxed_2764_; uint8_t v_skipConstInApp_boxed_2765_; uint8_t v_skipInstances_boxed_2766_; lean_object* v_res_2767_; 
v_usedLetOnly_boxed_2764_ = lean_unbox(v_usedLetOnly_2754_);
v_skipConstInApp_boxed_2765_ = lean_unbox(v_skipConstInApp_2755_);
v_skipInstances_boxed_2766_ = lean_unbox(v_skipInstances_2756_);
v_res_2767_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11(v_toApplicative_2748_, v_inst_2749_, v_inst_2750_, v_inst_2751_, v_pre_2752_, v_post_2753_, v_usedLetOnly_boxed_2764_, v_skipConstInApp_boxed_2765_, v_skipInstances_boxed_2766_, v_x_2757_, v_x_2758_, v___y_2759_, v___f_2760_, v_toBind_2761_, v_e_2762_, v_a_2763_);
lean_dec(v___y_2759_);
return v_res_2767_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12(lean_object* v_toApplicative_2768_, lean_object* v_inst_2769_, lean_object* v_inst_2770_, lean_object* v_inst_2771_, lean_object* v_pre_2772_, lean_object* v_post_2773_, uint8_t v_usedLetOnly_2774_, uint8_t v_skipConstInApp_2775_, uint8_t v_skipInstances_2776_, lean_object* v_x_2777_, lean_object* v_x_2778_, lean_object* v___f_2779_, lean_object* v_toBind_2780_, lean_object* v_e_2781_, lean_object* v_____r_2782_, lean_object* v___y_2783_){
_start:
{
lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___f_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; 
v___x_2784_ = lean_box(v_usedLetOnly_2774_);
v___x_2785_ = lean_box(v_skipConstInApp_2775_);
v___x_2786_ = lean_box(v_skipInstances_2776_);
lean_inc_ref(v_e_2781_);
lean_inc(v_toBind_2780_);
lean_inc(v___y_2783_);
lean_inc(v_pre_2772_);
v___f_2787_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___boxed), 16, 15);
lean_closure_set(v___f_2787_, 0, v_toApplicative_2768_);
lean_closure_set(v___f_2787_, 1, v_inst_2769_);
lean_closure_set(v___f_2787_, 2, v_inst_2770_);
lean_closure_set(v___f_2787_, 3, v_inst_2771_);
lean_closure_set(v___f_2787_, 4, v_pre_2772_);
lean_closure_set(v___f_2787_, 5, v_post_2773_);
lean_closure_set(v___f_2787_, 6, v___x_2784_);
lean_closure_set(v___f_2787_, 7, v___x_2785_);
lean_closure_set(v___f_2787_, 8, v___x_2786_);
lean_closure_set(v___f_2787_, 9, v_x_2777_);
lean_closure_set(v___f_2787_, 10, v_x_2778_);
lean_closure_set(v___f_2787_, 11, v___y_2783_);
lean_closure_set(v___f_2787_, 12, v___f_2779_);
lean_closure_set(v___f_2787_, 13, v_toBind_2780_);
lean_closure_set(v___f_2787_, 14, v_e_2781_);
v___x_2788_ = lean_apply_1(v_pre_2772_, v_e_2781_);
v___x_2789_ = lean_apply_4(v_toBind_2780_, lean_box(0), lean_box(0), v___x_2788_, v___f_2787_);
return v___x_2789_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12___boxed(lean_object* v_toApplicative_2790_, lean_object* v_inst_2791_, lean_object* v_inst_2792_, lean_object* v_inst_2793_, lean_object* v_pre_2794_, lean_object* v_post_2795_, lean_object* v_usedLetOnly_2796_, lean_object* v_skipConstInApp_2797_, lean_object* v_skipInstances_2798_, lean_object* v_x_2799_, lean_object* v_x_2800_, lean_object* v___f_2801_, lean_object* v_toBind_2802_, lean_object* v_e_2803_, lean_object* v_____r_2804_, lean_object* v___y_2805_){
_start:
{
uint8_t v_usedLetOnly_boxed_2806_; uint8_t v_skipConstInApp_boxed_2807_; uint8_t v_skipInstances_boxed_2808_; lean_object* v_res_2809_; 
v_usedLetOnly_boxed_2806_ = lean_unbox(v_usedLetOnly_2796_);
v_skipConstInApp_boxed_2807_ = lean_unbox(v_skipConstInApp_2797_);
v_skipInstances_boxed_2808_ = lean_unbox(v_skipInstances_2798_);
v_res_2809_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12(v_toApplicative_2790_, v_inst_2791_, v_inst_2792_, v_inst_2793_, v_pre_2794_, v_post_2795_, v_usedLetOnly_boxed_2806_, v_skipConstInApp_boxed_2807_, v_skipInstances_boxed_2808_, v_x_2799_, v_x_2800_, v___f_2801_, v_toBind_2802_, v_e_2803_, v_____r_2804_, v___y_2805_);
lean_dec(v___y_2805_);
return v_res_2809_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(lean_object* v_inst_2810_, lean_object* v_inst_2811_, lean_object* v_inst_2812_, lean_object* v_pre_2813_, lean_object* v_post_2814_, uint8_t v_usedLetOnly_2815_, uint8_t v_skipConstInApp_2816_, uint8_t v_skipInstances_2817_, lean_object* v_x_2818_, lean_object* v_x_2819_, lean_object* v_e_2820_, lean_object* v_a_2821_){
_start:
{
lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___f_2826_; lean_object* v___f_2827_; lean_object* v___x_2828_; lean_object* v_toApplicative_2829_; lean_object* v_toBind_2830_; lean_object* v___f_2831_; lean_object* v___f_2832_; lean_object* v___f_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___f_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___f_2841_; lean_object* v___f_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; 
v___x_2822_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0));
v___x_2823_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1));
lean_inc_ref_n(v_inst_2810_, 3);
v___x_2824_ = l_Lean_MonadCacheT_instMonad___redArg(v_x_2818_, v___x_2822_, v___x_2823_, v_inst_2810_);
v___x_2825_ = l_Lean_MonadCacheT_instMonadControl___redArg(v_x_2818_, v___x_2822_, v___x_2823_);
lean_inc_ref_n(v_inst_2812_, 3);
lean_inc_ref(v___x_2825_);
v___f_2826_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_2826_, 0, v___x_2825_);
lean_closure_set(v___f_2826_, 1, v_inst_2812_);
v___f_2827_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_2827_, 0, v___x_2825_);
lean_closure_set(v___f_2827_, 1, v_inst_2812_);
v___x_2828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2828_, 0, v___f_2826_);
lean_ctor_set(v___x_2828_, 1, v___f_2827_);
v_toApplicative_2829_ = lean_ctor_get(v_inst_2810_, 0);
lean_inc_ref_n(v_toApplicative_2829_, 6);
v_toBind_2830_ = lean_ctor_get(v_inst_2810_, 1);
lean_inc_n(v_toBind_2830_, 6);
v___f_2831_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2831_, 0, v_toApplicative_2829_);
lean_inc_n(v_x_2819_, 3);
lean_inc_n(v_a_2821_, 3);
lean_inc_ref_n(v_e_2820_, 2);
v___f_2832_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_2832_, 0, v_toApplicative_2829_);
lean_closure_set(v___f_2832_, 1, v___x_2822_);
lean_closure_set(v___f_2832_, 2, v___x_2823_);
lean_closure_set(v___f_2832_, 3, v_e_2820_);
lean_closure_set(v___f_2832_, 4, v_a_2821_);
lean_closure_set(v___f_2832_, 5, v_x_2819_);
lean_closure_set(v___f_2832_, 6, v_toBind_2830_);
v___f_2833_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__3___boxed), 5, 4);
lean_closure_set(v___f_2833_, 0, v_toApplicative_2829_);
lean_closure_set(v___f_2833_, 1, v___x_2822_);
lean_closure_set(v___f_2833_, 2, v___x_2823_);
lean_closure_set(v___f_2833_, 3, v_e_2820_);
v___x_2834_ = lean_box(v_skipInstances_2817_);
v___x_2835_ = lean_box(v_usedLetOnly_2815_);
v___x_2836_ = lean_box(v_skipConstInApp_2816_);
lean_inc_ref(v___x_2824_);
lean_inc(v_post_2814_);
lean_inc(v_pre_2813_);
lean_inc_n(v_inst_2811_, 2);
v___f_2837_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__9___boxed), 17, 14);
lean_closure_set(v___f_2837_, 0, v___x_2834_);
lean_closure_set(v___f_2837_, 1, v_inst_2810_);
lean_closure_set(v___f_2837_, 2, v_inst_2811_);
lean_closure_set(v___f_2837_, 3, v_inst_2812_);
lean_closure_set(v___f_2837_, 4, v_pre_2813_);
lean_closure_set(v___f_2837_, 5, v_post_2814_);
lean_closure_set(v___f_2837_, 6, v___x_2835_);
lean_closure_set(v___f_2837_, 7, v___x_2836_);
lean_closure_set(v___f_2837_, 8, v_x_2818_);
lean_closure_set(v___f_2837_, 9, v_x_2819_);
lean_closure_set(v___f_2837_, 10, v___x_2824_);
lean_closure_set(v___f_2837_, 11, v_toBind_2830_);
lean_closure_set(v___f_2837_, 12, v_toApplicative_2829_);
lean_closure_set(v___f_2837_, 13, v___f_2831_);
v___x_2838_ = lean_box(v_usedLetOnly_2815_);
v___x_2839_ = lean_box(v_skipConstInApp_2816_);
v___x_2840_ = lean_box(v_skipInstances_2817_);
v___f_2841_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12___boxed), 16, 14);
lean_closure_set(v___f_2841_, 0, v_toApplicative_2829_);
lean_closure_set(v___f_2841_, 1, v_inst_2810_);
lean_closure_set(v___f_2841_, 2, v_inst_2811_);
lean_closure_set(v___f_2841_, 3, v_inst_2812_);
lean_closure_set(v___f_2841_, 4, v_pre_2813_);
lean_closure_set(v___f_2841_, 5, v_post_2814_);
lean_closure_set(v___f_2841_, 6, v___x_2838_);
lean_closure_set(v___f_2841_, 7, v___x_2839_);
lean_closure_set(v___f_2841_, 8, v___x_2840_);
lean_closure_set(v___f_2841_, 9, v_x_2818_);
lean_closure_set(v___f_2841_, 10, v_x_2819_);
lean_closure_set(v___f_2841_, 11, v___f_2837_);
lean_closure_set(v___f_2841_, 12, v_toBind_2830_);
lean_closure_set(v___f_2841_, 13, v_e_2820_);
v___f_2842_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14___boxed), 13, 12);
lean_closure_set(v___f_2842_, 0, v_inst_2811_);
lean_closure_set(v___f_2842_, 1, v_x_2818_);
lean_closure_set(v___f_2842_, 2, v___x_2822_);
lean_closure_set(v___f_2842_, 3, v___x_2823_);
lean_closure_set(v___f_2842_, 4, v_inst_2810_);
lean_closure_set(v___f_2842_, 5, v___f_2841_);
lean_closure_set(v___f_2842_, 6, v___x_2828_);
lean_closure_set(v___f_2842_, 7, v___x_2824_);
lean_closure_set(v___f_2842_, 8, v_a_2821_);
lean_closure_set(v___f_2842_, 9, v_toBind_2830_);
lean_closure_set(v___f_2842_, 10, v___f_2832_);
lean_closure_set(v___f_2842_, 11, v_toApplicative_2829_);
v___x_2843_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2843_, 0, lean_box(0));
lean_closure_set(v___x_2843_, 1, lean_box(0));
lean_closure_set(v___x_2843_, 2, v_a_2821_);
v___x_2844_ = lean_apply_2(v_x_2819_, lean_box(0), v___x_2843_);
v___x_2845_ = lean_apply_4(v_toBind_2830_, lean_box(0), lean_box(0), v___x_2844_, v___f_2833_);
v___x_2846_ = lean_apply_4(v_toBind_2830_, lean_box(0), lean_box(0), v___x_2845_, v___f_2842_);
return v___x_2846_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___lam__0(lean_object* v_toApplicative_2847_, lean_object* v_inst_2848_, lean_object* v_inst_2849_, lean_object* v_inst_2850_, lean_object* v_pre_2851_, lean_object* v_post_2852_, uint8_t v_usedLetOnly_2853_, uint8_t v_skipConstInApp_2854_, uint8_t v_skipInstances_2855_, lean_object* v_x_2856_, lean_object* v_x_2857_, lean_object* v_a_2858_, lean_object* v_e_2859_, lean_object* v_a_2860_){
_start:
{
lean_object* v___y_2862_; 
switch(lean_obj_tag(v_a_2860_))
{
case 0:
{
lean_object* v_e_2865_; lean_object* v_toPure_2866_; lean_object* v___x_2867_; 
lean_dec_ref(v_e_2859_);
lean_dec(v_x_2857_);
lean_dec(v_post_2852_);
lean_dec(v_pre_2851_);
lean_dec_ref(v_inst_2850_);
lean_dec(v_inst_2849_);
lean_dec_ref(v_inst_2848_);
v_e_2865_ = lean_ctor_get(v_a_2860_, 0);
lean_inc_ref(v_e_2865_);
lean_dec_ref_known(v_a_2860_, 1);
v_toPure_2866_ = lean_ctor_get(v_toApplicative_2847_, 1);
lean_inc(v_toPure_2866_);
lean_dec_ref(v_toApplicative_2847_);
v___x_2867_ = lean_apply_2(v_toPure_2866_, lean_box(0), v_e_2865_);
return v___x_2867_;
}
case 1:
{
lean_object* v_e_2868_; lean_object* v___x_2869_; 
lean_dec_ref(v_e_2859_);
lean_dec_ref(v_toApplicative_2847_);
v_e_2868_ = lean_ctor_get(v_a_2860_, 0);
lean_inc_ref(v_e_2868_);
lean_dec_ref_known(v_a_2860_, 1);
v___x_2869_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2848_, v_inst_2849_, v_inst_2850_, v_pre_2851_, v_post_2852_, v_usedLetOnly_2853_, v_skipConstInApp_2854_, v_skipInstances_2855_, v_x_2856_, v_x_2857_, v_e_2868_, v_a_2858_);
return v___x_2869_;
}
default: 
{
lean_object* v_e_x3f_2870_; 
lean_dec(v_x_2857_);
lean_dec(v_post_2852_);
lean_dec(v_pre_2851_);
lean_dec_ref(v_inst_2850_);
lean_dec(v_inst_2849_);
lean_dec_ref(v_inst_2848_);
v_e_x3f_2870_ = lean_ctor_get(v_a_2860_, 0);
lean_inc(v_e_x3f_2870_);
lean_dec_ref_known(v_a_2860_, 1);
if (lean_obj_tag(v_e_x3f_2870_) == 0)
{
v___y_2862_ = v_e_2859_;
goto v___jp_2861_;
}
else
{
lean_object* v_val_2871_; 
lean_dec_ref(v_e_2859_);
v_val_2871_ = lean_ctor_get(v_e_x3f_2870_, 0);
lean_inc(v_val_2871_);
lean_dec_ref_known(v_e_x3f_2870_, 1);
v___y_2862_ = v_val_2871_;
goto v___jp_2861_;
}
}
}
v___jp_2861_:
{
lean_object* v_toPure_2863_; lean_object* v___x_2864_; 
v_toPure_2863_ = lean_ctor_get(v_toApplicative_2847_, 1);
lean_inc(v_toPure_2863_);
lean_dec_ref(v_toApplicative_2847_);
v___x_2864_ = lean_apply_2(v_toPure_2863_, lean_box(0), v___y_2862_);
return v___x_2864_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___lam__0___boxed(lean_object* v_toApplicative_2872_, lean_object* v_inst_2873_, lean_object* v_inst_2874_, lean_object* v_inst_2875_, lean_object* v_pre_2876_, lean_object* v_post_2877_, lean_object* v_usedLetOnly_2878_, lean_object* v_skipConstInApp_2879_, lean_object* v_skipInstances_2880_, lean_object* v_x_2881_, lean_object* v_x_2882_, lean_object* v_a_2883_, lean_object* v_e_2884_, lean_object* v_a_2885_){
_start:
{
uint8_t v_usedLetOnly_boxed_2886_; uint8_t v_skipConstInApp_boxed_2887_; uint8_t v_skipInstances_boxed_2888_; lean_object* v_res_2889_; 
v_usedLetOnly_boxed_2886_ = lean_unbox(v_usedLetOnly_2878_);
v_skipConstInApp_boxed_2887_ = lean_unbox(v_skipConstInApp_2879_);
v_skipInstances_boxed_2888_ = lean_unbox(v_skipInstances_2880_);
v_res_2889_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___lam__0(v_toApplicative_2872_, v_inst_2873_, v_inst_2874_, v_inst_2875_, v_pre_2876_, v_post_2877_, v_usedLetOnly_boxed_2886_, v_skipConstInApp_boxed_2887_, v_skipInstances_boxed_2888_, v_x_2881_, v_x_2882_, v_a_2883_, v_e_2884_, v_a_2885_);
lean_dec(v_a_2883_);
return v_res_2889_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(lean_object* v_inst_2890_, lean_object* v_inst_2891_, lean_object* v_inst_2892_, lean_object* v_pre_2893_, lean_object* v_post_2894_, uint8_t v_usedLetOnly_2895_, uint8_t v_skipConstInApp_2896_, uint8_t v_skipInstances_2897_, lean_object* v_x_2898_, lean_object* v_x_2899_, lean_object* v_e_2900_, lean_object* v_a_2901_){
_start:
{
lean_object* v_toApplicative_2902_; lean_object* v_toBind_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___f_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; 
v_toApplicative_2902_ = lean_ctor_get(v_inst_2890_, 0);
lean_inc_ref(v_toApplicative_2902_);
v_toBind_2903_ = lean_ctor_get(v_inst_2890_, 1);
lean_inc(v_toBind_2903_);
v___x_2904_ = lean_box(v_usedLetOnly_2895_);
v___x_2905_ = lean_box(v_skipConstInApp_2896_);
v___x_2906_ = lean_box(v_skipInstances_2897_);
lean_inc_ref(v_e_2900_);
lean_inc(v_a_2901_);
lean_inc(v_post_2894_);
v___f_2907_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___lam__0___boxed), 14, 13);
lean_closure_set(v___f_2907_, 0, v_toApplicative_2902_);
lean_closure_set(v___f_2907_, 1, v_inst_2890_);
lean_closure_set(v___f_2907_, 2, v_inst_2891_);
lean_closure_set(v___f_2907_, 3, v_inst_2892_);
lean_closure_set(v___f_2907_, 4, v_pre_2893_);
lean_closure_set(v___f_2907_, 5, v_post_2894_);
lean_closure_set(v___f_2907_, 6, v___x_2904_);
lean_closure_set(v___f_2907_, 7, v___x_2905_);
lean_closure_set(v___f_2907_, 8, v___x_2906_);
lean_closure_set(v___f_2907_, 9, v_x_2898_);
lean_closure_set(v___f_2907_, 10, v_x_2899_);
lean_closure_set(v___f_2907_, 11, v_a_2901_);
lean_closure_set(v___f_2907_, 12, v_e_2900_);
v___x_2908_ = lean_apply_1(v_post_2894_, v_e_2900_);
v___x_2909_ = lean_apply_4(v_toBind_2903_, lean_box(0), lean_box(0), v___x_2908_, v___f_2907_);
return v___x_2909_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3(lean_object* v_inst_2910_, lean_object* v_inst_2911_, lean_object* v_inst_2912_, lean_object* v_pre_2913_, lean_object* v_post_2914_, uint8_t v_usedLetOnly_2915_, uint8_t v_skipConstInApp_2916_, uint8_t v_skipInstances_2917_, lean_object* v_x_2918_, lean_object* v_x_2919_, lean_object* v_a_2920_, lean_object* v_a_2921_){
_start:
{
lean_object* v___x_2922_; 
v___x_2922_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2910_, v_inst_2911_, v_inst_2912_, v_pre_2913_, v_post_2914_, v_usedLetOnly_2915_, v_skipConstInApp_2916_, v_skipInstances_2917_, v_x_2918_, v_x_2919_, v_a_2921_, v_a_2920_);
return v___x_2922_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___boxed(lean_object* v_inst_2923_, lean_object* v_inst_2924_, lean_object* v_inst_2925_, lean_object* v_pre_2926_, lean_object* v_post_2927_, lean_object* v_usedLetOnly_2928_, lean_object* v_skipConstInApp_2929_, lean_object* v_skipInstances_2930_, lean_object* v_x_2931_, lean_object* v_x_2932_, lean_object* v_e_2933_, lean_object* v_a_2934_){
_start:
{
uint8_t v_usedLetOnly_boxed_2935_; uint8_t v_skipConstInApp_boxed_2936_; uint8_t v_skipInstances_boxed_2937_; lean_object* v_res_2938_; 
v_usedLetOnly_boxed_2935_ = lean_unbox(v_usedLetOnly_2928_);
v_skipConstInApp_boxed_2936_ = lean_unbox(v_skipConstInApp_2929_);
v_skipInstances_boxed_2937_ = lean_unbox(v_skipInstances_2930_);
v_res_2938_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2923_, v_inst_2924_, v_inst_2925_, v_pre_2926_, v_post_2927_, v_usedLetOnly_boxed_2935_, v_skipConstInApp_boxed_2936_, v_skipInstances_boxed_2937_, v_x_2931_, v_x_2932_, v_e_2933_, v_a_2934_);
lean_dec(v_a_2934_);
return v_res_2938_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___boxed(lean_object* v_inst_2939_, lean_object* v_inst_2940_, lean_object* v_inst_2941_, lean_object* v_pre_2942_, lean_object* v_post_2943_, lean_object* v_usedLetOnly_2944_, lean_object* v_skipConstInApp_2945_, lean_object* v_skipInstances_2946_, lean_object* v_x_2947_, lean_object* v_x_2948_, lean_object* v_fvars_2949_, lean_object* v_e_2950_, lean_object* v_a_2951_){
_start:
{
uint8_t v_usedLetOnly_boxed_2952_; uint8_t v_skipConstInApp_boxed_2953_; uint8_t v_skipInstances_boxed_2954_; lean_object* v_res_2955_; 
v_usedLetOnly_boxed_2952_ = lean_unbox(v_usedLetOnly_2944_);
v_skipConstInApp_boxed_2953_ = lean_unbox(v_skipConstInApp_2945_);
v_skipInstances_boxed_2954_ = lean_unbox(v_skipInstances_2946_);
v_res_2955_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(v_inst_2939_, v_inst_2940_, v_inst_2941_, v_pre_2942_, v_post_2943_, v_usedLetOnly_boxed_2952_, v_skipConstInApp_boxed_2953_, v_skipInstances_boxed_2954_, v_x_2947_, v_x_2948_, v_fvars_2949_, v_e_2950_, v_a_2951_);
lean_dec(v_a_2951_);
return v_res_2955_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___boxed(lean_object* v_inst_2956_, lean_object* v_inst_2957_, lean_object* v_inst_2958_, lean_object* v_pre_2959_, lean_object* v_post_2960_, lean_object* v_usedLetOnly_2961_, lean_object* v_skipConstInApp_2962_, lean_object* v_skipInstances_2963_, lean_object* v_x_2964_, lean_object* v_x_2965_, lean_object* v_fvars_2966_, lean_object* v_e_2967_, lean_object* v_a_2968_){
_start:
{
uint8_t v_usedLetOnly_boxed_2969_; uint8_t v_skipConstInApp_boxed_2970_; uint8_t v_skipInstances_boxed_2971_; lean_object* v_res_2972_; 
v_usedLetOnly_boxed_2969_ = lean_unbox(v_usedLetOnly_2961_);
v_skipConstInApp_boxed_2970_ = lean_unbox(v_skipConstInApp_2962_);
v_skipInstances_boxed_2971_ = lean_unbox(v_skipInstances_2963_);
v_res_2972_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(v_inst_2956_, v_inst_2957_, v_inst_2958_, v_pre_2959_, v_post_2960_, v_usedLetOnly_boxed_2969_, v_skipConstInApp_boxed_2970_, v_skipInstances_boxed_2971_, v_x_2964_, v_x_2965_, v_fvars_2966_, v_e_2967_, v_a_2968_);
lean_dec(v_a_2968_);
return v_res_2972_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___boxed(lean_object* v_inst_2973_, lean_object* v_inst_2974_, lean_object* v_inst_2975_, lean_object* v_pre_2976_, lean_object* v_post_2977_, lean_object* v_usedLetOnly_2978_, lean_object* v_skipConstInApp_2979_, lean_object* v_skipInstances_2980_, lean_object* v_x_2981_, lean_object* v_x_2982_, lean_object* v_fvars_2983_, lean_object* v_e_2984_, lean_object* v_a_2985_){
_start:
{
uint8_t v_usedLetOnly_boxed_2986_; uint8_t v_skipConstInApp_boxed_2987_; uint8_t v_skipInstances_boxed_2988_; lean_object* v_res_2989_; 
v_usedLetOnly_boxed_2986_ = lean_unbox(v_usedLetOnly_2978_);
v_skipConstInApp_boxed_2987_ = lean_unbox(v_skipConstInApp_2979_);
v_skipInstances_boxed_2988_ = lean_unbox(v_skipInstances_2980_);
v_res_2989_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(v_inst_2973_, v_inst_2974_, v_inst_2975_, v_pre_2976_, v_post_2977_, v_usedLetOnly_boxed_2986_, v_skipConstInApp_boxed_2987_, v_skipInstances_boxed_2988_, v_x_2981_, v_x_2982_, v_fvars_2983_, v_e_2984_, v_a_2985_);
lean_dec(v_a_2985_);
return v_res_2989_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit(lean_object* v_m_2990_, lean_object* v_inst_2991_, lean_object* v_inst_2992_, lean_object* v_inst_2993_, lean_object* v_pre_2994_, lean_object* v_post_2995_, uint8_t v_usedLetOnly_2996_, uint8_t v_skipConstInApp_2997_, uint8_t v_skipInstances_2998_, lean_object* v_x_2999_, lean_object* v_x_3000_, lean_object* v_e_3001_, lean_object* v_a_3002_){
_start:
{
lean_object* v___x_3003_; 
v___x_3003_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2991_, v_inst_2992_, v_inst_2993_, v_pre_2994_, v_post_2995_, v_usedLetOnly_2996_, v_skipConstInApp_2997_, v_skipInstances_2998_, v_x_2999_, v_x_3000_, v_e_3001_, v_a_3002_);
return v___x_3003_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___boxed(lean_object* v_m_3004_, lean_object* v_inst_3005_, lean_object* v_inst_3006_, lean_object* v_inst_3007_, lean_object* v_pre_3008_, lean_object* v_post_3009_, lean_object* v_usedLetOnly_3010_, lean_object* v_skipConstInApp_3011_, lean_object* v_skipInstances_3012_, lean_object* v_x_3013_, lean_object* v_x_3014_, lean_object* v_e_3015_, lean_object* v_a_3016_){
_start:
{
uint8_t v_usedLetOnly_boxed_3017_; uint8_t v_skipConstInApp_boxed_3018_; uint8_t v_skipInstances_boxed_3019_; lean_object* v_res_3020_; 
v_usedLetOnly_boxed_3017_ = lean_unbox(v_usedLetOnly_3010_);
v_skipConstInApp_boxed_3018_ = lean_unbox(v_skipConstInApp_3011_);
v_skipInstances_boxed_3019_ = lean_unbox(v_skipInstances_3012_);
v_res_3020_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit(v_m_3004_, v_inst_3005_, v_inst_3006_, v_inst_3007_, v_pre_3008_, v_post_3009_, v_usedLetOnly_boxed_3017_, v_skipConstInApp_boxed_3018_, v_skipInstances_boxed_3019_, v_x_3013_, v_x_3014_, v_e_3015_, v_a_3016_);
lean_dec(v_a_3016_);
return v_res_3020_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet(lean_object* v_m_3021_, lean_object* v_inst_3022_, lean_object* v_inst_3023_, lean_object* v_inst_3024_, lean_object* v_pre_3025_, lean_object* v_post_3026_, uint8_t v_usedLetOnly_3027_, uint8_t v_skipConstInApp_3028_, uint8_t v_skipInstances_3029_, lean_object* v_x_3030_, lean_object* v_x_3031_, lean_object* v_fvars_3032_, lean_object* v_e_3033_, lean_object* v_a_3034_){
_start:
{
lean_object* v___x_3035_; 
v___x_3035_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(v_inst_3022_, v_inst_3023_, v_inst_3024_, v_pre_3025_, v_post_3026_, v_usedLetOnly_3027_, v_skipConstInApp_3028_, v_skipInstances_3029_, v_x_3030_, v_x_3031_, v_fvars_3032_, v_e_3033_, v_a_3034_);
return v___x_3035_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___boxed(lean_object* v_m_3036_, lean_object* v_inst_3037_, lean_object* v_inst_3038_, lean_object* v_inst_3039_, lean_object* v_pre_3040_, lean_object* v_post_3041_, lean_object* v_usedLetOnly_3042_, lean_object* v_skipConstInApp_3043_, lean_object* v_skipInstances_3044_, lean_object* v_x_3045_, lean_object* v_x_3046_, lean_object* v_fvars_3047_, lean_object* v_e_3048_, lean_object* v_a_3049_){
_start:
{
uint8_t v_usedLetOnly_boxed_3050_; uint8_t v_skipConstInApp_boxed_3051_; uint8_t v_skipInstances_boxed_3052_; lean_object* v_res_3053_; 
v_usedLetOnly_boxed_3050_ = lean_unbox(v_usedLetOnly_3042_);
v_skipConstInApp_boxed_3051_ = lean_unbox(v_skipConstInApp_3043_);
v_skipInstances_boxed_3052_ = lean_unbox(v_skipInstances_3044_);
v_res_3053_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet(v_m_3036_, v_inst_3037_, v_inst_3038_, v_inst_3039_, v_pre_3040_, v_post_3041_, v_usedLetOnly_boxed_3050_, v_skipConstInApp_boxed_3051_, v_skipInstances_boxed_3052_, v_x_3045_, v_x_3046_, v_fvars_3047_, v_e_3048_, v_a_3049_);
lean_dec(v_a_3049_);
return v_res_3053_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost(lean_object* v_m_3054_, lean_object* v_inst_3055_, lean_object* v_inst_3056_, lean_object* v_inst_3057_, lean_object* v_pre_3058_, lean_object* v_post_3059_, uint8_t v_usedLetOnly_3060_, uint8_t v_skipConstInApp_3061_, uint8_t v_skipInstances_3062_, lean_object* v_x_3063_, lean_object* v_x_3064_, lean_object* v_e_3065_, lean_object* v_a_3066_){
_start:
{
lean_object* v___x_3067_; 
v___x_3067_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_3055_, v_inst_3056_, v_inst_3057_, v_pre_3058_, v_post_3059_, v_usedLetOnly_3060_, v_skipConstInApp_3061_, v_skipInstances_3062_, v_x_3063_, v_x_3064_, v_e_3065_, v_a_3066_);
return v___x_3067_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___boxed(lean_object* v_m_3068_, lean_object* v_inst_3069_, lean_object* v_inst_3070_, lean_object* v_inst_3071_, lean_object* v_pre_3072_, lean_object* v_post_3073_, lean_object* v_usedLetOnly_3074_, lean_object* v_skipConstInApp_3075_, lean_object* v_skipInstances_3076_, lean_object* v_x_3077_, lean_object* v_x_3078_, lean_object* v_e_3079_, lean_object* v_a_3080_){
_start:
{
uint8_t v_usedLetOnly_boxed_3081_; uint8_t v_skipConstInApp_boxed_3082_; uint8_t v_skipInstances_boxed_3083_; lean_object* v_res_3084_; 
v_usedLetOnly_boxed_3081_ = lean_unbox(v_usedLetOnly_3074_);
v_skipConstInApp_boxed_3082_ = lean_unbox(v_skipConstInApp_3075_);
v_skipInstances_boxed_3083_ = lean_unbox(v_skipInstances_3076_);
v_res_3084_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost(v_m_3068_, v_inst_3069_, v_inst_3070_, v_inst_3071_, v_pre_3072_, v_post_3073_, v_usedLetOnly_boxed_3081_, v_skipConstInApp_boxed_3082_, v_skipInstances_boxed_3083_, v_x_3077_, v_x_3078_, v_e_3079_, v_a_3080_);
lean_dec(v_a_3080_);
return v_res_3084_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda(lean_object* v_m_3085_, lean_object* v_inst_3086_, lean_object* v_inst_3087_, lean_object* v_inst_3088_, lean_object* v_pre_3089_, lean_object* v_post_3090_, uint8_t v_usedLetOnly_3091_, uint8_t v_skipConstInApp_3092_, uint8_t v_skipInstances_3093_, lean_object* v_x_3094_, lean_object* v_x_3095_, lean_object* v_fvars_3096_, lean_object* v_e_3097_, lean_object* v_a_3098_){
_start:
{
lean_object* v___x_3099_; 
v___x_3099_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(v_inst_3086_, v_inst_3087_, v_inst_3088_, v_pre_3089_, v_post_3090_, v_usedLetOnly_3091_, v_skipConstInApp_3092_, v_skipInstances_3093_, v_x_3094_, v_x_3095_, v_fvars_3096_, v_e_3097_, v_a_3098_);
return v___x_3099_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___boxed(lean_object* v_m_3100_, lean_object* v_inst_3101_, lean_object* v_inst_3102_, lean_object* v_inst_3103_, lean_object* v_pre_3104_, lean_object* v_post_3105_, lean_object* v_usedLetOnly_3106_, lean_object* v_skipConstInApp_3107_, lean_object* v_skipInstances_3108_, lean_object* v_x_3109_, lean_object* v_x_3110_, lean_object* v_fvars_3111_, lean_object* v_e_3112_, lean_object* v_a_3113_){
_start:
{
uint8_t v_usedLetOnly_boxed_3114_; uint8_t v_skipConstInApp_boxed_3115_; uint8_t v_skipInstances_boxed_3116_; lean_object* v_res_3117_; 
v_usedLetOnly_boxed_3114_ = lean_unbox(v_usedLetOnly_3106_);
v_skipConstInApp_boxed_3115_ = lean_unbox(v_skipConstInApp_3107_);
v_skipInstances_boxed_3116_ = lean_unbox(v_skipInstances_3108_);
v_res_3117_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda(v_m_3100_, v_inst_3101_, v_inst_3102_, v_inst_3103_, v_pre_3104_, v_post_3105_, v_usedLetOnly_boxed_3114_, v_skipConstInApp_boxed_3115_, v_skipInstances_boxed_3116_, v_x_3109_, v_x_3110_, v_fvars_3111_, v_e_3112_, v_a_3113_);
lean_dec(v_a_3113_);
return v_res_3117_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall(lean_object* v_m_3118_, lean_object* v_inst_3119_, lean_object* v_inst_3120_, lean_object* v_inst_3121_, lean_object* v_pre_3122_, lean_object* v_post_3123_, uint8_t v_usedLetOnly_3124_, uint8_t v_skipConstInApp_3125_, uint8_t v_skipInstances_3126_, lean_object* v_x_3127_, lean_object* v_x_3128_, lean_object* v_fvars_3129_, lean_object* v_e_3130_, lean_object* v_a_3131_){
_start:
{
lean_object* v___x_3132_; 
v___x_3132_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(v_inst_3119_, v_inst_3120_, v_inst_3121_, v_pre_3122_, v_post_3123_, v_usedLetOnly_3124_, v_skipConstInApp_3125_, v_skipInstances_3126_, v_x_3127_, v_x_3128_, v_fvars_3129_, v_e_3130_, v_a_3131_);
return v___x_3132_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___boxed(lean_object* v_m_3133_, lean_object* v_inst_3134_, lean_object* v_inst_3135_, lean_object* v_inst_3136_, lean_object* v_pre_3137_, lean_object* v_post_3138_, lean_object* v_usedLetOnly_3139_, lean_object* v_skipConstInApp_3140_, lean_object* v_skipInstances_3141_, lean_object* v_x_3142_, lean_object* v_x_3143_, lean_object* v_fvars_3144_, lean_object* v_e_3145_, lean_object* v_a_3146_){
_start:
{
uint8_t v_usedLetOnly_boxed_3147_; uint8_t v_skipConstInApp_boxed_3148_; uint8_t v_skipInstances_boxed_3149_; lean_object* v_res_3150_; 
v_usedLetOnly_boxed_3147_ = lean_unbox(v_usedLetOnly_3139_);
v_skipConstInApp_boxed_3148_ = lean_unbox(v_skipConstInApp_3140_);
v_skipInstances_boxed_3149_ = lean_unbox(v_skipInstances_3141_);
v_res_3150_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall(v_m_3133_, v_inst_3134_, v_inst_3135_, v_inst_3136_, v_pre_3137_, v_post_3138_, v_usedLetOnly_boxed_3147_, v_skipConstInApp_boxed_3148_, v_skipInstances_boxed_3149_, v_x_3142_, v_x_3143_, v_fvars_3144_, v_e_3145_, v_a_3146_);
lean_dec(v_a_3146_);
return v_res_3150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__0(lean_object* v_x_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_){
_start:
{
lean_object* v___x_3157_; lean_object* v___x_3158_; 
v___x_3157_ = lean_apply_1(v_x_3151_, lean_box(0));
v___x_3158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3158_, 0, v___x_3157_);
return v___x_3158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__0___boxed(lean_object* v_x_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_){
_start:
{
lean_object* v_res_3165_; 
v_res_3165_ = l_Lean_Meta_transformWithCache___redArg___lam__0(v_x_3159_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_);
lean_dec(v___y_3163_);
lean_dec_ref(v___y_3162_);
lean_dec(v___y_3161_);
lean_dec_ref(v___y_3160_);
return v_res_3165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__1(lean_object* v_inst_3166_, lean_object* v_00_u03b1_3167_, lean_object* v_x_3168_){
_start:
{
lean_object* v___f_3169_; lean_object* v___x_3170_; 
v___f_3169_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_3169_, 0, v_x_3168_);
v___x_3170_ = lean_apply_2(v_inst_3166_, lean_box(0), v___f_3169_);
return v___x_3170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__4(lean_object* v_toPure_3171_, lean_object* v_x_3172_, lean_object* v_toBind_3173_, lean_object* v_inst_3174_, lean_object* v_inst_3175_, lean_object* v_inst_3176_, lean_object* v_pre_3177_, lean_object* v_post_3178_, uint8_t v_usedLetOnly_3179_, uint8_t v_skipConstInApp_3180_, uint8_t v_skipInstances_3181_, lean_object* v_x_3182_, lean_object* v_input_3183_, lean_object* v_ref_3184_){
_start:
{
lean_object* v___f_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; 
lean_inc(v_toBind_3173_);
lean_inc(v_x_3172_);
lean_inc(v_ref_3184_);
v___f_3185_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__4), 5, 4);
lean_closure_set(v___f_3185_, 0, v_toPure_3171_);
lean_closure_set(v___f_3185_, 1, v_ref_3184_);
lean_closure_set(v___f_3185_, 2, v_x_3172_);
lean_closure_set(v___f_3185_, 3, v_toBind_3173_);
v___x_3186_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_3174_, v_inst_3175_, v_inst_3176_, v_pre_3177_, v_post_3178_, v_usedLetOnly_3179_, v_skipConstInApp_3180_, v_skipInstances_3181_, v_x_3182_, v_x_3172_, v_input_3183_, v_ref_3184_);
lean_dec(v_ref_3184_);
v___x_3187_ = lean_apply_4(v_toBind_3173_, lean_box(0), lean_box(0), v___x_3186_, v___f_3185_);
return v___x_3187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__4___boxed(lean_object* v_toPure_3188_, lean_object* v_x_3189_, lean_object* v_toBind_3190_, lean_object* v_inst_3191_, lean_object* v_inst_3192_, lean_object* v_inst_3193_, lean_object* v_pre_3194_, lean_object* v_post_3195_, lean_object* v_usedLetOnly_3196_, lean_object* v_skipConstInApp_3197_, lean_object* v_skipInstances_3198_, lean_object* v_x_3199_, lean_object* v_input_3200_, lean_object* v_ref_3201_){
_start:
{
uint8_t v_usedLetOnly_boxed_3202_; uint8_t v_skipConstInApp_boxed_3203_; uint8_t v_skipInstances_boxed_3204_; lean_object* v_res_3205_; 
v_usedLetOnly_boxed_3202_ = lean_unbox(v_usedLetOnly_3196_);
v_skipConstInApp_boxed_3203_ = lean_unbox(v_skipConstInApp_3197_);
v_skipInstances_boxed_3204_ = lean_unbox(v_skipInstances_3198_);
v_res_3205_ = l_Lean_Meta_transformWithCache___redArg___lam__4(v_toPure_3188_, v_x_3189_, v_toBind_3190_, v_inst_3191_, v_inst_3192_, v_inst_3193_, v_pre_3194_, v_post_3195_, v_usedLetOnly_boxed_3202_, v_skipConstInApp_boxed_3203_, v_skipInstances_boxed_3204_, v_x_3199_, v_input_3200_, v_ref_3201_);
return v_res_3205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg(lean_object* v_inst_3206_, lean_object* v_inst_3207_, lean_object* v_inst_3208_, lean_object* v_input_3209_, lean_object* v_cache_3210_, lean_object* v_pre_3211_, lean_object* v_post_3212_, uint8_t v_usedLetOnly_3213_, uint8_t v_skipConstInApp_3214_, uint8_t v_skipInstances_3215_){
_start:
{
lean_object* v_x_3216_; lean_object* v_toApplicative_3217_; lean_object* v_toBind_3218_; lean_object* v_toPure_3219_; lean_object* v_x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___f_3226_; lean_object* v___x_3227_; 
v_x_3216_ = lean_box(0);
v_toApplicative_3217_ = lean_ctor_get(v_inst_3206_, 0);
v_toBind_3218_ = lean_ctor_get(v_inst_3206_, 1);
lean_inc_n(v_toBind_3218_, 2);
v_toPure_3219_ = lean_ctor_get(v_toApplicative_3217_, 1);
lean_inc(v_toPure_3219_);
lean_inc_n(v_inst_3207_, 2);
v_x_3220_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__1), 3, 1);
lean_closure_set(v_x_3220_, 0, v_inst_3207_);
v___x_3221_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_3221_, 0, lean_box(0));
lean_closure_set(v___x_3221_, 1, lean_box(0));
lean_closure_set(v___x_3221_, 2, v_cache_3210_);
v___x_3222_ = l_Lean_Meta_transformWithCache___redArg___lam__1(v_inst_3207_, lean_box(0), v___x_3221_);
v___x_3223_ = lean_box(v_usedLetOnly_3213_);
v___x_3224_ = lean_box(v_skipConstInApp_3214_);
v___x_3225_ = lean_box(v_skipInstances_3215_);
v___f_3226_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__4___boxed), 14, 13);
lean_closure_set(v___f_3226_, 0, v_toPure_3219_);
lean_closure_set(v___f_3226_, 1, v_x_3220_);
lean_closure_set(v___f_3226_, 2, v_toBind_3218_);
lean_closure_set(v___f_3226_, 3, v_inst_3206_);
lean_closure_set(v___f_3226_, 4, v_inst_3207_);
lean_closure_set(v___f_3226_, 5, v_inst_3208_);
lean_closure_set(v___f_3226_, 6, v_pre_3211_);
lean_closure_set(v___f_3226_, 7, v_post_3212_);
lean_closure_set(v___f_3226_, 8, v___x_3223_);
lean_closure_set(v___f_3226_, 9, v___x_3224_);
lean_closure_set(v___f_3226_, 10, v___x_3225_);
lean_closure_set(v___f_3226_, 11, v_x_3216_);
lean_closure_set(v___f_3226_, 12, v_input_3209_);
v___x_3227_ = lean_apply_4(v_toBind_3218_, lean_box(0), lean_box(0), v___x_3222_, v___f_3226_);
return v___x_3227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___boxed(lean_object* v_inst_3228_, lean_object* v_inst_3229_, lean_object* v_inst_3230_, lean_object* v_input_3231_, lean_object* v_cache_3232_, lean_object* v_pre_3233_, lean_object* v_post_3234_, lean_object* v_usedLetOnly_3235_, lean_object* v_skipConstInApp_3236_, lean_object* v_skipInstances_3237_){
_start:
{
uint8_t v_usedLetOnly_boxed_3238_; uint8_t v_skipConstInApp_boxed_3239_; uint8_t v_skipInstances_boxed_3240_; lean_object* v_res_3241_; 
v_usedLetOnly_boxed_3238_ = lean_unbox(v_usedLetOnly_3235_);
v_skipConstInApp_boxed_3239_ = lean_unbox(v_skipConstInApp_3236_);
v_skipInstances_boxed_3240_ = lean_unbox(v_skipInstances_3237_);
v_res_3241_ = l_Lean_Meta_transformWithCache___redArg(v_inst_3228_, v_inst_3229_, v_inst_3230_, v_input_3231_, v_cache_3232_, v_pre_3233_, v_post_3234_, v_usedLetOnly_boxed_3238_, v_skipConstInApp_boxed_3239_, v_skipInstances_boxed_3240_);
return v_res_3241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache(lean_object* v_m_3242_, lean_object* v_inst_3243_, lean_object* v_inst_3244_, lean_object* v_inst_3245_, lean_object* v_input_3246_, lean_object* v_cache_3247_, lean_object* v_pre_3248_, lean_object* v_post_3249_, uint8_t v_usedLetOnly_3250_, uint8_t v_skipConstInApp_3251_, uint8_t v_skipInstances_3252_){
_start:
{
lean_object* v_x_3253_; lean_object* v_toApplicative_3254_; lean_object* v_toBind_3255_; lean_object* v_toPure_3256_; lean_object* v_x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___f_3263_; lean_object* v___x_3264_; 
v_x_3253_ = lean_box(0);
v_toApplicative_3254_ = lean_ctor_get(v_inst_3243_, 0);
v_toBind_3255_ = lean_ctor_get(v_inst_3243_, 1);
lean_inc_n(v_toBind_3255_, 2);
v_toPure_3256_ = lean_ctor_get(v_toApplicative_3254_, 1);
lean_inc(v_toPure_3256_);
lean_inc_n(v_inst_3244_, 2);
v_x_3257_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__1), 3, 1);
lean_closure_set(v_x_3257_, 0, v_inst_3244_);
v___x_3258_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_3258_, 0, lean_box(0));
lean_closure_set(v___x_3258_, 1, lean_box(0));
lean_closure_set(v___x_3258_, 2, v_cache_3247_);
v___x_3259_ = l_Lean_Meta_transformWithCache___redArg___lam__1(v_inst_3244_, lean_box(0), v___x_3258_);
v___x_3260_ = lean_box(v_usedLetOnly_3250_);
v___x_3261_ = lean_box(v_skipConstInApp_3251_);
v___x_3262_ = lean_box(v_skipInstances_3252_);
v___f_3263_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__4___boxed), 14, 13);
lean_closure_set(v___f_3263_, 0, v_toPure_3256_);
lean_closure_set(v___f_3263_, 1, v_x_3257_);
lean_closure_set(v___f_3263_, 2, v_toBind_3255_);
lean_closure_set(v___f_3263_, 3, v_inst_3243_);
lean_closure_set(v___f_3263_, 4, v_inst_3244_);
lean_closure_set(v___f_3263_, 5, v_inst_3245_);
lean_closure_set(v___f_3263_, 6, v_pre_3248_);
lean_closure_set(v___f_3263_, 7, v_post_3249_);
lean_closure_set(v___f_3263_, 8, v___x_3260_);
lean_closure_set(v___f_3263_, 9, v___x_3261_);
lean_closure_set(v___f_3263_, 10, v___x_3262_);
lean_closure_set(v___f_3263_, 11, v_x_3253_);
lean_closure_set(v___f_3263_, 12, v_input_3246_);
v___x_3264_ = lean_apply_4(v_toBind_3255_, lean_box(0), lean_box(0), v___x_3259_, v___f_3263_);
return v___x_3264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___boxed(lean_object* v_m_3265_, lean_object* v_inst_3266_, lean_object* v_inst_3267_, lean_object* v_inst_3268_, lean_object* v_input_3269_, lean_object* v_cache_3270_, lean_object* v_pre_3271_, lean_object* v_post_3272_, lean_object* v_usedLetOnly_3273_, lean_object* v_skipConstInApp_3274_, lean_object* v_skipInstances_3275_){
_start:
{
uint8_t v_usedLetOnly_boxed_3276_; uint8_t v_skipConstInApp_boxed_3277_; uint8_t v_skipInstances_boxed_3278_; lean_object* v_res_3279_; 
v_usedLetOnly_boxed_3276_ = lean_unbox(v_usedLetOnly_3273_);
v_skipConstInApp_boxed_3277_ = lean_unbox(v_skipConstInApp_3274_);
v_skipInstances_boxed_3278_ = lean_unbox(v_skipInstances_3275_);
v_res_3279_ = l_Lean_Meta_transformWithCache(v_m_3265_, v_inst_3266_, v_inst_3267_, v_inst_3268_, v_input_3269_, v_cache_3270_, v_pre_3271_, v_post_3272_, v_usedLetOnly_boxed_3276_, v_skipConstInApp_boxed_3277_, v_skipInstances_boxed_3278_);
return v_res_3279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___redArg___lam__5(lean_object* v_toPure_3280_, lean_object* v_x_3281_, lean_object* v_toBind_3282_, lean_object* v_inst_3283_, lean_object* v_inst_3284_, lean_object* v_inst_3285_, lean_object* v_pre_3286_, lean_object* v_post_3287_, uint8_t v_usedLetOnly_3288_, uint8_t v_skipConstInApp_3289_, uint8_t v___x_3290_, lean_object* v_x_3291_, lean_object* v_input_3292_, lean_object* v_ref_3293_){
_start:
{
lean_object* v___f_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; 
lean_inc(v_toBind_3282_);
lean_inc(v_x_3281_);
lean_inc(v_ref_3293_);
v___f_3294_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__4), 5, 4);
lean_closure_set(v___f_3294_, 0, v_toPure_3280_);
lean_closure_set(v___f_3294_, 1, v_ref_3293_);
lean_closure_set(v___f_3294_, 2, v_x_3281_);
lean_closure_set(v___f_3294_, 3, v_toBind_3282_);
v___x_3295_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_3283_, v_inst_3284_, v_inst_3285_, v_pre_3286_, v_post_3287_, v_usedLetOnly_3288_, v_skipConstInApp_3289_, v___x_3290_, v_x_3291_, v_x_3281_, v_input_3292_, v_ref_3293_);
lean_dec(v_ref_3293_);
v___x_3296_ = lean_apply_4(v_toBind_3282_, lean_box(0), lean_box(0), v___x_3295_, v___f_3294_);
return v___x_3296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___redArg___lam__5___boxed(lean_object* v_toPure_3297_, lean_object* v_x_3298_, lean_object* v_toBind_3299_, lean_object* v_inst_3300_, lean_object* v_inst_3301_, lean_object* v_inst_3302_, lean_object* v_pre_3303_, lean_object* v_post_3304_, lean_object* v_usedLetOnly_3305_, lean_object* v_skipConstInApp_3306_, lean_object* v___x_3307_, lean_object* v_x_3308_, lean_object* v_input_3309_, lean_object* v_ref_3310_){
_start:
{
uint8_t v_usedLetOnly_boxed_3311_; uint8_t v_skipConstInApp_boxed_3312_; uint8_t v___x_114__boxed_3313_; lean_object* v_res_3314_; 
v_usedLetOnly_boxed_3311_ = lean_unbox(v_usedLetOnly_3305_);
v_skipConstInApp_boxed_3312_ = lean_unbox(v_skipConstInApp_3306_);
v___x_114__boxed_3313_ = lean_unbox(v___x_3307_);
v_res_3314_ = l_Lean_Meta_transform___redArg___lam__5(v_toPure_3297_, v_x_3298_, v_toBind_3299_, v_inst_3300_, v_inst_3301_, v_inst_3302_, v_pre_3303_, v_post_3304_, v_usedLetOnly_boxed_3311_, v_skipConstInApp_boxed_3312_, v___x_114__boxed_3313_, v_x_3308_, v_input_3309_, v_ref_3310_);
return v_res_3314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___redArg(lean_object* v_inst_3315_, lean_object* v_inst_3316_, lean_object* v_inst_3317_, lean_object* v_input_3318_, lean_object* v_pre_3319_, lean_object* v_post_3320_, uint8_t v_usedLetOnly_3321_, uint8_t v_skipConstInApp_3322_){
_start:
{
lean_object* v_toApplicative_3323_; lean_object* v_toBind_3324_; lean_object* v_x_3325_; lean_object* v_toPure_3326_; lean_object* v_x_3327_; uint8_t v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___f_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___f_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; 
v_toApplicative_3323_ = lean_ctor_get(v_inst_3315_, 0);
v_toBind_3324_ = lean_ctor_get(v_inst_3315_, 1);
lean_inc_n(v_toBind_3324_, 3);
v_x_3325_ = lean_box(0);
v_toPure_3326_ = lean_ctor_get(v_toApplicative_3323_, 1);
lean_inc_n(v_toPure_3326_, 2);
lean_inc_n(v_inst_3316_, 2);
v_x_3327_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__1), 3, 1);
lean_closure_set(v_x_3327_, 0, v_inst_3316_);
v___x_3328_ = 0;
v___x_3329_ = lean_obj_once(&l_Lean_Core_transform___redArg___closed__2, &l_Lean_Core_transform___redArg___closed__2_once, _init_l_Lean_Core_transform___redArg___closed__2);
v___x_3330_ = l_Lean_Meta_transformWithCache___redArg___lam__1(v_inst_3316_, lean_box(0), v___x_3329_);
v___f_3331_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__2), 2, 1);
lean_closure_set(v___f_3331_, 0, v_toPure_3326_);
v___x_3332_ = lean_box(v_usedLetOnly_3321_);
v___x_3333_ = lean_box(v_skipConstInApp_3322_);
v___x_3334_ = lean_box(v___x_3328_);
v___f_3335_ = lean_alloc_closure((void*)(l_Lean_Meta_transform___redArg___lam__5___boxed), 14, 13);
lean_closure_set(v___f_3335_, 0, v_toPure_3326_);
lean_closure_set(v___f_3335_, 1, v_x_3327_);
lean_closure_set(v___f_3335_, 2, v_toBind_3324_);
lean_closure_set(v___f_3335_, 3, v_inst_3315_);
lean_closure_set(v___f_3335_, 4, v_inst_3316_);
lean_closure_set(v___f_3335_, 5, v_inst_3317_);
lean_closure_set(v___f_3335_, 6, v_pre_3319_);
lean_closure_set(v___f_3335_, 7, v_post_3320_);
lean_closure_set(v___f_3335_, 8, v___x_3332_);
lean_closure_set(v___f_3335_, 9, v___x_3333_);
lean_closure_set(v___f_3335_, 10, v___x_3334_);
lean_closure_set(v___f_3335_, 11, v_x_3325_);
lean_closure_set(v___f_3335_, 12, v_input_3318_);
v___x_3336_ = lean_apply_4(v_toBind_3324_, lean_box(0), lean_box(0), v___x_3330_, v___f_3335_);
v___x_3337_ = lean_apply_4(v_toBind_3324_, lean_box(0), lean_box(0), v___x_3336_, v___f_3331_);
return v___x_3337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___redArg___boxed(lean_object* v_inst_3338_, lean_object* v_inst_3339_, lean_object* v_inst_3340_, lean_object* v_input_3341_, lean_object* v_pre_3342_, lean_object* v_post_3343_, lean_object* v_usedLetOnly_3344_, lean_object* v_skipConstInApp_3345_){
_start:
{
uint8_t v_usedLetOnly_boxed_3346_; uint8_t v_skipConstInApp_boxed_3347_; lean_object* v_res_3348_; 
v_usedLetOnly_boxed_3346_ = lean_unbox(v_usedLetOnly_3344_);
v_skipConstInApp_boxed_3347_ = lean_unbox(v_skipConstInApp_3345_);
v_res_3348_ = l_Lean_Meta_transform___redArg(v_inst_3338_, v_inst_3339_, v_inst_3340_, v_input_3341_, v_pre_3342_, v_post_3343_, v_usedLetOnly_boxed_3346_, v_skipConstInApp_boxed_3347_);
return v_res_3348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform(lean_object* v_m_3349_, lean_object* v_inst_3350_, lean_object* v_inst_3351_, lean_object* v_inst_3352_, lean_object* v_input_3353_, lean_object* v_pre_3354_, lean_object* v_post_3355_, uint8_t v_usedLetOnly_3356_, uint8_t v_skipConstInApp_3357_){
_start:
{
lean_object* v___x_3358_; 
v___x_3358_ = l_Lean_Meta_transform___redArg(v_inst_3350_, v_inst_3351_, v_inst_3352_, v_input_3353_, v_pre_3354_, v_post_3355_, v_usedLetOnly_3356_, v_skipConstInApp_3357_);
return v___x_3358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___boxed(lean_object* v_m_3359_, lean_object* v_inst_3360_, lean_object* v_inst_3361_, lean_object* v_inst_3362_, lean_object* v_input_3363_, lean_object* v_pre_3364_, lean_object* v_post_3365_, lean_object* v_usedLetOnly_3366_, lean_object* v_skipConstInApp_3367_){
_start:
{
uint8_t v_usedLetOnly_boxed_3368_; uint8_t v_skipConstInApp_boxed_3369_; lean_object* v_res_3370_; 
v_usedLetOnly_boxed_3368_ = lean_unbox(v_usedLetOnly_3366_);
v_skipConstInApp_boxed_3369_ = lean_unbox(v_skipConstInApp_3367_);
v_res_3370_ = l_Lean_Meta_transform(v_m_3359_, v_inst_3360_, v_inst_3361_, v_inst_3362_, v_input_3363_, v_pre_3364_, v_post_3365_, v_usedLetOnly_boxed_3368_, v_skipConstInApp_boxed_3369_);
return v_res_3370_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(lean_object* v_e_3371_, lean_object* v___y_3372_){
_start:
{
uint8_t v___x_3374_; 
v___x_3374_ = l_Lean_Expr_hasMVar(v_e_3371_);
if (v___x_3374_ == 0)
{
lean_object* v___x_3375_; 
v___x_3375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3375_, 0, v_e_3371_);
return v___x_3375_;
}
else
{
lean_object* v___x_3376_; lean_object* v_mctx_3377_; lean_object* v___x_3378_; lean_object* v_fst_3379_; lean_object* v_snd_3380_; lean_object* v___x_3381_; lean_object* v_cache_3382_; lean_object* v_zetaDeltaFVarIds_3383_; lean_object* v_postponed_3384_; lean_object* v_diag_3385_; lean_object* v___x_3387_; uint8_t v_isShared_3388_; uint8_t v_isSharedCheck_3394_; 
v___x_3376_ = lean_st_ref_get(v___y_3372_);
v_mctx_3377_ = lean_ctor_get(v___x_3376_, 0);
lean_inc_ref(v_mctx_3377_);
lean_dec(v___x_3376_);
v___x_3378_ = l_Lean_instantiateMVarsCore(v_mctx_3377_, v_e_3371_);
v_fst_3379_ = lean_ctor_get(v___x_3378_, 0);
lean_inc(v_fst_3379_);
v_snd_3380_ = lean_ctor_get(v___x_3378_, 1);
lean_inc(v_snd_3380_);
lean_dec_ref(v___x_3378_);
v___x_3381_ = lean_st_ref_take(v___y_3372_);
v_cache_3382_ = lean_ctor_get(v___x_3381_, 1);
v_zetaDeltaFVarIds_3383_ = lean_ctor_get(v___x_3381_, 2);
v_postponed_3384_ = lean_ctor_get(v___x_3381_, 3);
v_diag_3385_ = lean_ctor_get(v___x_3381_, 4);
v_isSharedCheck_3394_ = !lean_is_exclusive(v___x_3381_);
if (v_isSharedCheck_3394_ == 0)
{
lean_object* v_unused_3395_; 
v_unused_3395_ = lean_ctor_get(v___x_3381_, 0);
lean_dec(v_unused_3395_);
v___x_3387_ = v___x_3381_;
v_isShared_3388_ = v_isSharedCheck_3394_;
goto v_resetjp_3386_;
}
else
{
lean_inc(v_diag_3385_);
lean_inc(v_postponed_3384_);
lean_inc(v_zetaDeltaFVarIds_3383_);
lean_inc(v_cache_3382_);
lean_dec(v___x_3381_);
v___x_3387_ = lean_box(0);
v_isShared_3388_ = v_isSharedCheck_3394_;
goto v_resetjp_3386_;
}
v_resetjp_3386_:
{
lean_object* v___x_3390_; 
if (v_isShared_3388_ == 0)
{
lean_ctor_set(v___x_3387_, 0, v_snd_3380_);
v___x_3390_ = v___x_3387_;
goto v_reusejp_3389_;
}
else
{
lean_object* v_reuseFailAlloc_3393_; 
v_reuseFailAlloc_3393_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3393_, 0, v_snd_3380_);
lean_ctor_set(v_reuseFailAlloc_3393_, 1, v_cache_3382_);
lean_ctor_set(v_reuseFailAlloc_3393_, 2, v_zetaDeltaFVarIds_3383_);
lean_ctor_set(v_reuseFailAlloc_3393_, 3, v_postponed_3384_);
lean_ctor_set(v_reuseFailAlloc_3393_, 4, v_diag_3385_);
v___x_3390_ = v_reuseFailAlloc_3393_;
goto v_reusejp_3389_;
}
v_reusejp_3389_:
{
lean_object* v___x_3391_; lean_object* v___x_3392_; 
v___x_3391_ = lean_st_ref_put(v___y_3372_, v___x_3390_);
v___x_3392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3392_, 0, v_fst_3379_);
return v___x_3392_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg___boxed(lean_object* v_e_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_){
_start:
{
lean_object* v_res_3399_; 
v_res_3399_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(v_e_3396_, v___y_3397_);
lean_dec(v___y_3397_);
return v_res_3399_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0(lean_object* v_e_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_){
_start:
{
lean_object* v___x_3406_; 
v___x_3406_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(v_e_3400_, v___y_3402_);
return v___x_3406_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___boxed(lean_object* v_e_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_){
_start:
{
lean_object* v_res_3413_; 
v_res_3413_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0(v_e_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_);
lean_dec(v___y_3411_);
lean_dec_ref(v___y_3410_);
lean_dec(v___y_3409_);
lean_dec_ref(v___y_3408_);
return v_res_3413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__0(uint8_t v_zetaHave_3414_, lean_object* v___x_3415_, uint8_t v_zetaDelta_3416_, lean_object* v_fvarId_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_){
_start:
{
lean_object* v___x_3423_; 
v___x_3423_ = l_Lean_FVarId_findDecl_x3f___redArg(v_fvarId_3417_, v___y_3418_);
if (lean_obj_tag(v___x_3423_) == 0)
{
lean_object* v_a_3424_; lean_object* v___x_3426_; uint8_t v_isShared_3427_; uint8_t v_isSharedCheck_3452_; 
v_a_3424_ = lean_ctor_get(v___x_3423_, 0);
v_isSharedCheck_3452_ = !lean_is_exclusive(v___x_3423_);
if (v_isSharedCheck_3452_ == 0)
{
v___x_3426_ = v___x_3423_;
v_isShared_3427_ = v_isSharedCheck_3452_;
goto v_resetjp_3425_;
}
else
{
lean_inc(v_a_3424_);
lean_dec(v___x_3423_);
v___x_3426_ = lean_box(0);
v_isShared_3427_ = v_isSharedCheck_3452_;
goto v_resetjp_3425_;
}
v_resetjp_3425_:
{
if (lean_obj_tag(v_a_3424_) == 1)
{
lean_object* v_val_3428_; lean_object* v___x_3430_; uint8_t v_isShared_3431_; uint8_t v_isSharedCheck_3447_; 
v_val_3428_ = lean_ctor_get(v_a_3424_, 0);
v_isSharedCheck_3447_ = !lean_is_exclusive(v_a_3424_);
if (v_isSharedCheck_3447_ == 0)
{
v___x_3430_ = v_a_3424_;
v_isShared_3431_ = v_isSharedCheck_3447_;
goto v_resetjp_3429_;
}
else
{
lean_inc(v_val_3428_);
lean_dec(v_a_3424_);
v___x_3430_ = lean_box(0);
v_isShared_3431_ = v_isSharedCheck_3447_;
goto v_resetjp_3429_;
}
v_resetjp_3429_:
{
uint8_t v___y_3433_; 
if (v_zetaDelta_3416_ == 0)
{
lean_object* v___x_3441_; uint8_t v___x_3442_; 
v___x_3441_ = l_Lean_LocalDecl_index(v_val_3428_);
v___x_3442_ = lean_nat_dec_lt(v___x_3441_, v___x_3415_);
lean_dec(v___x_3441_);
if (v___x_3442_ == 0)
{
lean_del_object(v___x_3430_);
goto v___jp_3438_;
}
else
{
lean_object* v___x_3443_; lean_object* v___x_3445_; 
lean_dec(v_val_3428_);
lean_del_object(v___x_3426_);
v___x_3443_ = lean_box(0);
if (v_isShared_3431_ == 0)
{
lean_ctor_set_tag(v___x_3430_, 0);
lean_ctor_set(v___x_3430_, 0, v___x_3443_);
v___x_3445_ = v___x_3430_;
goto v_reusejp_3444_;
}
else
{
lean_object* v_reuseFailAlloc_3446_; 
v_reuseFailAlloc_3446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3446_, 0, v___x_3443_);
v___x_3445_ = v_reuseFailAlloc_3446_;
goto v_reusejp_3444_;
}
v_reusejp_3444_:
{
return v___x_3445_;
}
}
}
else
{
lean_del_object(v___x_3430_);
goto v___jp_3438_;
}
v___jp_3432_:
{
lean_object* v___x_3434_; lean_object* v___x_3436_; 
v___x_3434_ = l_Lean_LocalDecl_value_x3f(v_val_3428_, v___y_3433_);
lean_dec(v_val_3428_);
if (v_isShared_3427_ == 0)
{
lean_ctor_set(v___x_3426_, 0, v___x_3434_);
v___x_3436_ = v___x_3426_;
goto v_reusejp_3435_;
}
else
{
lean_object* v_reuseFailAlloc_3437_; 
v_reuseFailAlloc_3437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3437_, 0, v___x_3434_);
v___x_3436_ = v_reuseFailAlloc_3437_;
goto v_reusejp_3435_;
}
v_reusejp_3435_:
{
return v___x_3436_;
}
}
v___jp_3438_:
{
if (v_zetaHave_3414_ == 0)
{
v___y_3433_ = v_zetaHave_3414_;
goto v___jp_3432_;
}
else
{
lean_object* v___x_3439_; uint8_t v___x_3440_; 
v___x_3439_ = l_Lean_LocalDecl_index(v_val_3428_);
v___x_3440_ = lean_nat_dec_le(v___x_3415_, v___x_3439_);
lean_dec(v___x_3439_);
v___y_3433_ = v___x_3440_;
goto v___jp_3432_;
}
}
}
}
else
{
lean_object* v___x_3448_; lean_object* v___x_3450_; 
lean_dec(v_a_3424_);
v___x_3448_ = lean_box(0);
if (v_isShared_3427_ == 0)
{
lean_ctor_set(v___x_3426_, 0, v___x_3448_);
v___x_3450_ = v___x_3426_;
goto v_reusejp_3449_;
}
else
{
lean_object* v_reuseFailAlloc_3451_; 
v_reuseFailAlloc_3451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3451_, 0, v___x_3448_);
v___x_3450_ = v_reuseFailAlloc_3451_;
goto v_reusejp_3449_;
}
v_reusejp_3449_:
{
return v___x_3450_;
}
}
}
}
else
{
lean_object* v_a_3453_; lean_object* v___x_3455_; uint8_t v_isShared_3456_; uint8_t v_isSharedCheck_3460_; 
v_a_3453_ = lean_ctor_get(v___x_3423_, 0);
v_isSharedCheck_3460_ = !lean_is_exclusive(v___x_3423_);
if (v_isSharedCheck_3460_ == 0)
{
v___x_3455_ = v___x_3423_;
v_isShared_3456_ = v_isSharedCheck_3460_;
goto v_resetjp_3454_;
}
else
{
lean_inc(v_a_3453_);
lean_dec(v___x_3423_);
v___x_3455_ = lean_box(0);
v_isShared_3456_ = v_isSharedCheck_3460_;
goto v_resetjp_3454_;
}
v_resetjp_3454_:
{
lean_object* v___x_3458_; 
if (v_isShared_3456_ == 0)
{
v___x_3458_ = v___x_3455_;
goto v_reusejp_3457_;
}
else
{
lean_object* v_reuseFailAlloc_3459_; 
v_reuseFailAlloc_3459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3459_, 0, v_a_3453_);
v___x_3458_ = v_reuseFailAlloc_3459_;
goto v_reusejp_3457_;
}
v_reusejp_3457_:
{
return v___x_3458_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__0___boxed(lean_object* v_zetaHave_3461_, lean_object* v___x_3462_, lean_object* v_zetaDelta_3463_, lean_object* v_fvarId_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_){
_start:
{
uint8_t v_zetaHave_boxed_3470_; uint8_t v_zetaDelta_boxed_3471_; lean_object* v_res_3472_; 
v_zetaHave_boxed_3470_ = lean_unbox(v_zetaHave_3461_);
v_zetaDelta_boxed_3471_ = lean_unbox(v_zetaDelta_3463_);
v_res_3472_ = l_Lean_Meta_zetaReduce___lam__0(v_zetaHave_boxed_3470_, v___x_3462_, v_zetaDelta_boxed_3471_, v_fvarId_3464_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_);
lean_dec(v___y_3468_);
lean_dec_ref(v___y_3467_);
lean_dec(v___y_3466_);
lean_dec_ref(v___y_3465_);
lean_dec(v___x_3462_);
return v_res_3472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__1(lean_object* v_e_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_){
_start:
{
lean_object* v___x_3479_; lean_object* v___x_3480_; 
v___x_3479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3479_, 0, v_e_3473_);
v___x_3480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3480_, 0, v___x_3479_);
return v___x_3480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__1___boxed(lean_object* v_e_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_){
_start:
{
lean_object* v_res_3487_; 
v_res_3487_ = l_Lean_Meta_zetaReduce___lam__1(v_e_3481_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_);
lean_dec(v___y_3485_);
lean_dec_ref(v___y_3484_);
lean_dec(v___y_3483_);
lean_dec_ref(v___y_3482_);
return v_res_3487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__2(lean_object* v___f_3488_, lean_object* v_e_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_){
_start:
{
if (lean_obj_tag(v_e_3489_) == 1)
{
lean_object* v_fvarId_3495_; lean_object* v___x_3496_; 
v_fvarId_3495_ = lean_ctor_get(v_e_3489_, 0);
lean_inc(v___y_3493_);
lean_inc_ref(v___y_3492_);
lean_inc(v___y_3491_);
lean_inc_ref(v___y_3490_);
lean_inc(v_fvarId_3495_);
v___x_3496_ = lean_apply_6(v___f_3488_, v_fvarId_3495_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_, lean_box(0));
if (lean_obj_tag(v___x_3496_) == 0)
{
lean_object* v_a_3497_; lean_object* v___x_3499_; uint8_t v_isShared_3500_; uint8_t v_isSharedCheck_3522_; 
v_a_3497_ = lean_ctor_get(v___x_3496_, 0);
v_isSharedCheck_3522_ = !lean_is_exclusive(v___x_3496_);
if (v_isSharedCheck_3522_ == 0)
{
v___x_3499_ = v___x_3496_;
v_isShared_3500_ = v_isSharedCheck_3522_;
goto v_resetjp_3498_;
}
else
{
lean_inc(v_a_3497_);
lean_dec(v___x_3496_);
v___x_3499_ = lean_box(0);
v_isShared_3500_ = v_isSharedCheck_3522_;
goto v_resetjp_3498_;
}
v_resetjp_3498_:
{
if (lean_obj_tag(v_a_3497_) == 1)
{
lean_object* v_val_3501_; lean_object* v___x_3503_; uint8_t v_isShared_3504_; uint8_t v_isSharedCheck_3517_; 
lean_del_object(v___x_3499_);
lean_dec_ref_known(v_e_3489_, 1);
v_val_3501_ = lean_ctor_get(v_a_3497_, 0);
v_isSharedCheck_3517_ = !lean_is_exclusive(v_a_3497_);
if (v_isSharedCheck_3517_ == 0)
{
v___x_3503_ = v_a_3497_;
v_isShared_3504_ = v_isSharedCheck_3517_;
goto v_resetjp_3502_;
}
else
{
lean_inc(v_val_3501_);
lean_dec(v_a_3497_);
v___x_3503_ = lean_box(0);
v_isShared_3504_ = v_isSharedCheck_3517_;
goto v_resetjp_3502_;
}
v_resetjp_3502_:
{
lean_object* v___x_3505_; lean_object* v_a_3506_; lean_object* v___x_3508_; uint8_t v_isShared_3509_; uint8_t v_isSharedCheck_3516_; 
v___x_3505_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(v_val_3501_, v___y_3491_);
v_a_3506_ = lean_ctor_get(v___x_3505_, 0);
v_isSharedCheck_3516_ = !lean_is_exclusive(v___x_3505_);
if (v_isSharedCheck_3516_ == 0)
{
v___x_3508_ = v___x_3505_;
v_isShared_3509_ = v_isSharedCheck_3516_;
goto v_resetjp_3507_;
}
else
{
lean_inc(v_a_3506_);
lean_dec(v___x_3505_);
v___x_3508_ = lean_box(0);
v_isShared_3509_ = v_isSharedCheck_3516_;
goto v_resetjp_3507_;
}
v_resetjp_3507_:
{
lean_object* v___x_3511_; 
if (v_isShared_3504_ == 0)
{
lean_ctor_set(v___x_3503_, 0, v_a_3506_);
v___x_3511_ = v___x_3503_;
goto v_reusejp_3510_;
}
else
{
lean_object* v_reuseFailAlloc_3515_; 
v_reuseFailAlloc_3515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3515_, 0, v_a_3506_);
v___x_3511_ = v_reuseFailAlloc_3515_;
goto v_reusejp_3510_;
}
v_reusejp_3510_:
{
lean_object* v___x_3513_; 
if (v_isShared_3509_ == 0)
{
lean_ctor_set(v___x_3508_, 0, v___x_3511_);
v___x_3513_ = v___x_3508_;
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
}
else
{
lean_object* v___x_3518_; lean_object* v___x_3520_; 
lean_dec(v_a_3497_);
v___x_3518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3518_, 0, v_e_3489_);
if (v_isShared_3500_ == 0)
{
lean_ctor_set(v___x_3499_, 0, v___x_3518_);
v___x_3520_ = v___x_3499_;
goto v_reusejp_3519_;
}
else
{
lean_object* v_reuseFailAlloc_3521_; 
v_reuseFailAlloc_3521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3521_, 0, v___x_3518_);
v___x_3520_ = v_reuseFailAlloc_3521_;
goto v_reusejp_3519_;
}
v_reusejp_3519_:
{
return v___x_3520_;
}
}
}
}
else
{
lean_object* v_a_3523_; lean_object* v___x_3525_; uint8_t v_isShared_3526_; uint8_t v_isSharedCheck_3530_; 
lean_dec_ref_known(v_e_3489_, 1);
v_a_3523_ = lean_ctor_get(v___x_3496_, 0);
v_isSharedCheck_3530_ = !lean_is_exclusive(v___x_3496_);
if (v_isSharedCheck_3530_ == 0)
{
v___x_3525_ = v___x_3496_;
v_isShared_3526_ = v_isSharedCheck_3530_;
goto v_resetjp_3524_;
}
else
{
lean_inc(v_a_3523_);
lean_dec(v___x_3496_);
v___x_3525_ = lean_box(0);
v_isShared_3526_ = v_isSharedCheck_3530_;
goto v_resetjp_3524_;
}
v_resetjp_3524_:
{
lean_object* v___x_3528_; 
if (v_isShared_3526_ == 0)
{
v___x_3528_ = v___x_3525_;
goto v_reusejp_3527_;
}
else
{
lean_object* v_reuseFailAlloc_3529_; 
v_reuseFailAlloc_3529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3529_, 0, v_a_3523_);
v___x_3528_ = v_reuseFailAlloc_3529_;
goto v_reusejp_3527_;
}
v_reusejp_3527_:
{
return v___x_3528_;
}
}
}
}
else
{
lean_object* v___x_3531_; lean_object* v___x_3532_; 
lean_dec_ref(v_e_3489_);
lean_dec_ref(v___f_3488_);
v___x_3531_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_3532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3532_, 0, v___x_3531_);
return v___x_3532_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__2___boxed(lean_object* v___f_3533_, lean_object* v_e_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_){
_start:
{
lean_object* v_res_3540_; 
v_res_3540_ = l_Lean_Meta_zetaReduce___lam__2(v___f_3533_, v_e_3534_, v___y_3535_, v___y_3536_, v___y_3537_, v___y_3538_);
lean_dec(v___y_3538_);
lean_dec_ref(v___y_3537_);
lean_dec(v___y_3536_);
lean_dec_ref(v___y_3535_);
return v_res_3540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__4(lean_object* v___f_3541_, lean_object* v_e_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_){
_start:
{
lean_object* v___x_3548_; 
v___x_3548_ = l_Lean_Expr_getAppFn(v_e_3542_);
if (lean_obj_tag(v___x_3548_) == 1)
{
lean_object* v_fvarId_3549_; lean_object* v___x_3550_; 
v_fvarId_3549_ = lean_ctor_get(v___x_3548_, 0);
lean_inc(v_fvarId_3549_);
lean_dec_ref_known(v___x_3548_, 1);
lean_inc(v___y_3546_);
lean_inc_ref(v___y_3545_);
lean_inc(v___y_3544_);
lean_inc_ref(v___y_3543_);
v___x_3550_ = lean_apply_6(v___f_3541_, v_fvarId_3549_, v___y_3543_, v___y_3544_, v___y_3545_, v___y_3546_, lean_box(0));
if (lean_obj_tag(v___x_3550_) == 0)
{
lean_object* v_a_3551_; lean_object* v___x_3553_; uint8_t v_isShared_3554_; uint8_t v_isSharedCheck_3583_; 
v_a_3551_ = lean_ctor_get(v___x_3550_, 0);
v_isSharedCheck_3583_ = !lean_is_exclusive(v___x_3550_);
if (v_isSharedCheck_3583_ == 0)
{
v___x_3553_ = v___x_3550_;
v_isShared_3554_ = v_isSharedCheck_3583_;
goto v_resetjp_3552_;
}
else
{
lean_inc(v_a_3551_);
lean_dec(v___x_3550_);
v___x_3553_ = lean_box(0);
v_isShared_3554_ = v_isSharedCheck_3583_;
goto v_resetjp_3552_;
}
v_resetjp_3552_:
{
if (lean_obj_tag(v_a_3551_) == 1)
{
lean_object* v_val_3555_; lean_object* v___x_3557_; uint8_t v_isShared_3558_; uint8_t v_isSharedCheck_3578_; 
lean_del_object(v___x_3553_);
v_val_3555_ = lean_ctor_get(v_a_3551_, 0);
v_isSharedCheck_3578_ = !lean_is_exclusive(v_a_3551_);
if (v_isSharedCheck_3578_ == 0)
{
v___x_3557_ = v_a_3551_;
v_isShared_3558_ = v_isSharedCheck_3578_;
goto v_resetjp_3556_;
}
else
{
lean_inc(v_val_3555_);
lean_dec(v_a_3551_);
v___x_3557_ = lean_box(0);
v_isShared_3558_ = v_isSharedCheck_3578_;
goto v_resetjp_3556_;
}
v_resetjp_3556_:
{
lean_object* v___x_3559_; lean_object* v_a_3560_; lean_object* v___x_3562_; uint8_t v_isShared_3563_; uint8_t v_isSharedCheck_3577_; 
v___x_3559_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(v_val_3555_, v___y_3544_);
v_a_3560_ = lean_ctor_get(v___x_3559_, 0);
v_isSharedCheck_3577_ = !lean_is_exclusive(v___x_3559_);
if (v_isSharedCheck_3577_ == 0)
{
v___x_3562_ = v___x_3559_;
v_isShared_3563_ = v_isSharedCheck_3577_;
goto v_resetjp_3561_;
}
else
{
lean_inc(v_a_3560_);
lean_dec(v___x_3559_);
v___x_3562_ = lean_box(0);
v_isShared_3563_ = v_isSharedCheck_3577_;
goto v_resetjp_3561_;
}
v_resetjp_3561_:
{
lean_object* v_dummy_3564_; lean_object* v_nargs_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3572_; 
v_dummy_3564_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_3565_ = l_Lean_Expr_getAppNumArgs(v_e_3542_);
lean_inc(v_nargs_3565_);
v___x_3566_ = lean_mk_array(v_nargs_3565_, v_dummy_3564_);
v___x_3567_ = lean_unsigned_to_nat(1u);
v___x_3568_ = lean_nat_sub(v_nargs_3565_, v___x_3567_);
lean_dec(v_nargs_3565_);
v___x_3569_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3542_, v___x_3566_, v___x_3568_);
v___x_3570_ = l_Lean_Expr_beta(v_a_3560_, v___x_3569_);
if (v_isShared_3558_ == 0)
{
lean_ctor_set(v___x_3557_, 0, v___x_3570_);
v___x_3572_ = v___x_3557_;
goto v_reusejp_3571_;
}
else
{
lean_object* v_reuseFailAlloc_3576_; 
v_reuseFailAlloc_3576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3576_, 0, v___x_3570_);
v___x_3572_ = v_reuseFailAlloc_3576_;
goto v_reusejp_3571_;
}
v_reusejp_3571_:
{
lean_object* v___x_3574_; 
if (v_isShared_3563_ == 0)
{
lean_ctor_set(v___x_3562_, 0, v___x_3572_);
v___x_3574_ = v___x_3562_;
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
}
else
{
lean_object* v___x_3579_; lean_object* v___x_3581_; 
lean_dec(v_a_3551_);
lean_dec_ref(v_e_3542_);
v___x_3579_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
if (v_isShared_3554_ == 0)
{
lean_ctor_set(v___x_3553_, 0, v___x_3579_);
v___x_3581_ = v___x_3553_;
goto v_reusejp_3580_;
}
else
{
lean_object* v_reuseFailAlloc_3582_; 
v_reuseFailAlloc_3582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3582_, 0, v___x_3579_);
v___x_3581_ = v_reuseFailAlloc_3582_;
goto v_reusejp_3580_;
}
v_reusejp_3580_:
{
return v___x_3581_;
}
}
}
}
else
{
lean_object* v_a_3584_; lean_object* v___x_3586_; uint8_t v_isShared_3587_; uint8_t v_isSharedCheck_3591_; 
lean_dec_ref(v_e_3542_);
v_a_3584_ = lean_ctor_get(v___x_3550_, 0);
v_isSharedCheck_3591_ = !lean_is_exclusive(v___x_3550_);
if (v_isSharedCheck_3591_ == 0)
{
v___x_3586_ = v___x_3550_;
v_isShared_3587_ = v_isSharedCheck_3591_;
goto v_resetjp_3585_;
}
else
{
lean_inc(v_a_3584_);
lean_dec(v___x_3550_);
v___x_3586_ = lean_box(0);
v_isShared_3587_ = v_isSharedCheck_3591_;
goto v_resetjp_3585_;
}
v_resetjp_3585_:
{
lean_object* v___x_3589_; 
if (v_isShared_3587_ == 0)
{
v___x_3589_ = v___x_3586_;
goto v_reusejp_3588_;
}
else
{
lean_object* v_reuseFailAlloc_3590_; 
v_reuseFailAlloc_3590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3590_, 0, v_a_3584_);
v___x_3589_ = v_reuseFailAlloc_3590_;
goto v_reusejp_3588_;
}
v_reusejp_3588_:
{
return v___x_3589_;
}
}
}
}
else
{
lean_object* v___x_3592_; lean_object* v___x_3593_; 
lean_dec_ref(v___x_3548_);
lean_dec_ref(v_e_3542_);
lean_dec_ref(v___f_3541_);
v___x_3592_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_3593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3593_, 0, v___x_3592_);
return v___x_3593_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__4___boxed(lean_object* v___f_3594_, lean_object* v_e_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_){
_start:
{
lean_object* v_res_3601_; 
v_res_3601_ = l_Lean_Meta_zetaReduce___lam__4(v___f_3594_, v_e_3595_, v___y_3596_, v___y_3597_, v___y_3598_, v___y_3599_);
lean_dec(v___y_3599_);
lean_dec_ref(v___y_3598_);
lean_dec(v___y_3597_);
lean_dec_ref(v___y_3596_);
return v_res_3601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0(lean_object* v_00_u03b1_3602_, lean_object* v_x_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_){
_start:
{
lean_object* v___x_3609_; lean_object* v___x_3610_; 
v___x_3609_ = lean_apply_1(v_x_3603_, lean_box(0));
v___x_3610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3610_, 0, v___x_3609_);
return v___x_3610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0___boxed(lean_object* v_00_u03b1_3611_, lean_object* v_x_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_){
_start:
{
lean_object* v_res_3618_; 
v_res_3618_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0(v_00_u03b1_3611_, v_x_3612_, v___y_3613_, v___y_3614_, v___y_3615_, v___y_3616_);
lean_dec(v___y_3616_);
lean_dec_ref(v___y_3615_);
lean_dec(v___y_3614_);
lean_dec_ref(v___y_3613_);
return v_res_3618_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__2(lean_object* v___x_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_){
_start:
{
lean_object* v___x_3625_; 
v___x_3625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3625_, 0, v___x_3619_);
return v___x_3625_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__2___boxed(lean_object* v___x_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_){
_start:
{
lean_object* v_res_3632_; 
v_res_3632_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__2(v___x_3626_, v___y_3627_, v___y_3628_, v___y_3629_, v___y_3630_);
lean_dec(v___y_3630_);
lean_dec_ref(v___y_3629_);
lean_dec(v___y_3628_);
lean_dec_ref(v___y_3627_);
return v_res_3632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0(lean_object* v_k_3633_, lean_object* v___y_3634_, lean_object* v_b_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_){
_start:
{
lean_object* v___x_3641_; 
lean_inc(v___y_3639_);
lean_inc_ref(v___y_3638_);
lean_inc(v___y_3637_);
lean_inc_ref(v___y_3636_);
lean_inc(v___y_3634_);
v___x_3641_ = lean_apply_7(v_k_3633_, v_b_3635_, v___y_3634_, v___y_3636_, v___y_3637_, v___y_3638_, v___y_3639_, lean_box(0));
return v___x_3641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0___boxed(lean_object* v_k_3642_, lean_object* v___y_3643_, lean_object* v_b_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_){
_start:
{
lean_object* v_res_3650_; 
v_res_3650_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0(v_k_3642_, v___y_3643_, v_b_3644_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_);
lean_dec(v___y_3648_);
lean_dec_ref(v___y_3647_);
lean_dec(v___y_3646_);
lean_dec_ref(v___y_3645_);
lean_dec(v___y_3643_);
return v_res_3650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(lean_object* v_name_3651_, uint8_t v_bi_3652_, lean_object* v_type_3653_, lean_object* v_k_3654_, uint8_t v_kind_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_){
_start:
{
lean_object* v___f_3662_; lean_object* v___x_3663_; 
lean_inc(v___y_3656_);
v___f_3662_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3662_, 0, v_k_3654_);
lean_closure_set(v___f_3662_, 1, v___y_3656_);
v___x_3663_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3651_, v_bi_3652_, v_type_3653_, v___f_3662_, v_kind_3655_, v___y_3657_, v___y_3658_, v___y_3659_, v___y_3660_);
if (lean_obj_tag(v___x_3663_) == 0)
{
return v___x_3663_;
}
else
{
lean_object* v_a_3664_; lean_object* v___x_3666_; uint8_t v_isShared_3667_; uint8_t v_isSharedCheck_3671_; 
v_a_3664_ = lean_ctor_get(v___x_3663_, 0);
v_isSharedCheck_3671_ = !lean_is_exclusive(v___x_3663_);
if (v_isSharedCheck_3671_ == 0)
{
v___x_3666_ = v___x_3663_;
v_isShared_3667_ = v_isSharedCheck_3671_;
goto v_resetjp_3665_;
}
else
{
lean_inc(v_a_3664_);
lean_dec(v___x_3663_);
v___x_3666_ = lean_box(0);
v_isShared_3667_ = v_isSharedCheck_3671_;
goto v_resetjp_3665_;
}
v_resetjp_3665_:
{
lean_object* v___x_3669_; 
if (v_isShared_3667_ == 0)
{
v___x_3669_ = v___x_3666_;
goto v_reusejp_3668_;
}
else
{
lean_object* v_reuseFailAlloc_3670_; 
v_reuseFailAlloc_3670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3670_, 0, v_a_3664_);
v___x_3669_ = v_reuseFailAlloc_3670_;
goto v_reusejp_3668_;
}
v_reusejp_3668_:
{
return v___x_3669_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___boxed(lean_object* v_name_3672_, lean_object* v_bi_3673_, lean_object* v_type_3674_, lean_object* v_k_3675_, lean_object* v_kind_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_, lean_object* v___y_3682_){
_start:
{
uint8_t v_bi_boxed_3683_; uint8_t v_kind_boxed_3684_; lean_object* v_res_3685_; 
v_bi_boxed_3683_ = lean_unbox(v_bi_3673_);
v_kind_boxed_3684_ = lean_unbox(v_kind_3676_);
v_res_3685_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_name_3672_, v_bi_boxed_3683_, v_type_3674_, v_k_3675_, v_kind_boxed_3684_, v___y_3677_, v___y_3678_, v___y_3679_, v___y_3680_, v___y_3681_);
lean_dec(v___y_3681_);
lean_dec_ref(v___y_3680_);
lean_dec(v___y_3679_);
lean_dec_ref(v___y_3678_);
lean_dec(v___y_3677_);
return v_res_3685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg(lean_object* v_name_3686_, lean_object* v_type_3687_, lean_object* v_val_3688_, lean_object* v_k_3689_, uint8_t v_nondep_3690_, uint8_t v_kind_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_){
_start:
{
lean_object* v___f_3698_; lean_object* v___x_3699_; 
lean_inc(v___y_3692_);
v___f_3698_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3698_, 0, v_k_3689_);
lean_closure_set(v___f_3698_, 1, v___y_3692_);
v___x_3699_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_3686_, v_type_3687_, v_val_3688_, v___f_3698_, v_nondep_3690_, v_kind_3691_, v___y_3693_, v___y_3694_, v___y_3695_, v___y_3696_);
if (lean_obj_tag(v___x_3699_) == 0)
{
return v___x_3699_;
}
else
{
lean_object* v_a_3700_; lean_object* v___x_3702_; uint8_t v_isShared_3703_; uint8_t v_isSharedCheck_3707_; 
v_a_3700_ = lean_ctor_get(v___x_3699_, 0);
v_isSharedCheck_3707_ = !lean_is_exclusive(v___x_3699_);
if (v_isSharedCheck_3707_ == 0)
{
v___x_3702_ = v___x_3699_;
v_isShared_3703_ = v_isSharedCheck_3707_;
goto v_resetjp_3701_;
}
else
{
lean_inc(v_a_3700_);
lean_dec(v___x_3699_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg___boxed(lean_object* v_name_3708_, lean_object* v_type_3709_, lean_object* v_val_3710_, lean_object* v_k_3711_, lean_object* v_nondep_3712_, lean_object* v_kind_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_){
_start:
{
uint8_t v_nondep_boxed_3720_; uint8_t v_kind_boxed_3721_; lean_object* v_res_3722_; 
v_nondep_boxed_3720_ = lean_unbox(v_nondep_3712_);
v_kind_boxed_3721_ = lean_unbox(v_kind_3713_);
v_res_3722_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg(v_name_3708_, v_type_3709_, v_val_3710_, v_k_3711_, v_nondep_boxed_3720_, v_kind_boxed_3721_, v___y_3714_, v___y_3715_, v___y_3716_, v___y_3717_, v___y_3718_);
lean_dec(v___y_3718_);
lean_dec_ref(v___y_3717_);
lean_dec(v___y_3716_);
lean_dec_ref(v___y_3715_);
lean_dec(v___y_3714_);
return v_res_3722_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0(lean_object* v_00_u03b1_3723_, lean_object* v_x_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_){
_start:
{
lean_object* v___x_3730_; lean_object* v___x_3731_; 
v___x_3730_ = lean_apply_1(v_x_3724_, lean_box(0));
v___x_3731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3731_, 0, v___x_3730_);
return v___x_3731_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0___boxed(lean_object* v_00_u03b1_3732_, lean_object* v_x_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_){
_start:
{
lean_object* v_res_3739_; 
v_res_3739_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0(v_00_u03b1_3732_, v_x_3733_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_);
lean_dec(v___y_3737_);
lean_dec_ref(v___y_3736_);
lean_dec(v___y_3735_);
lean_dec_ref(v___y_3734_);
return v_res_3739_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg(lean_object* v_ref_3740_){
_start:
{
lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; 
v___x_3742_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5);
v___x_3743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3743_, 0, v_ref_3740_);
lean_ctor_set(v___x_3743_, 1, v___x_3742_);
v___x_3744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3744_, 0, v___x_3743_);
return v___x_3744_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg___boxed(lean_object* v_ref_3745_, lean_object* v___y_3746_){
_start:
{
lean_object* v_res_3747_; 
v_res_3747_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg(v_ref_3745_);
return v_res_3747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg(lean_object* v_x_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_){
_start:
{
lean_object* v___y_3756_; lean_object* v_fileName_3765_; lean_object* v_fileMap_3766_; lean_object* v_options_3767_; lean_object* v_currRecDepth_3768_; lean_object* v_maxRecDepth_3769_; lean_object* v_ref_3770_; lean_object* v_currNamespace_3771_; lean_object* v_openDecls_3772_; lean_object* v_initHeartbeats_3773_; lean_object* v_maxHeartbeats_3774_; lean_object* v_quotContext_3775_; lean_object* v_currMacroScope_3776_; uint8_t v_diag_3777_; lean_object* v_cancelTk_x3f_3778_; uint8_t v_suppressElabErrors_3779_; lean_object* v_inheritedTraceOptions_3780_; lean_object* v___x_3786_; uint8_t v___x_3787_; 
v_fileName_3765_ = lean_ctor_get(v___y_3752_, 0);
v_fileMap_3766_ = lean_ctor_get(v___y_3752_, 1);
v_options_3767_ = lean_ctor_get(v___y_3752_, 2);
v_currRecDepth_3768_ = lean_ctor_get(v___y_3752_, 3);
v_maxRecDepth_3769_ = lean_ctor_get(v___y_3752_, 4);
v_ref_3770_ = lean_ctor_get(v___y_3752_, 5);
v_currNamespace_3771_ = lean_ctor_get(v___y_3752_, 6);
v_openDecls_3772_ = lean_ctor_get(v___y_3752_, 7);
v_initHeartbeats_3773_ = lean_ctor_get(v___y_3752_, 8);
v_maxHeartbeats_3774_ = lean_ctor_get(v___y_3752_, 9);
v_quotContext_3775_ = lean_ctor_get(v___y_3752_, 10);
v_currMacroScope_3776_ = lean_ctor_get(v___y_3752_, 11);
v_diag_3777_ = lean_ctor_get_uint8(v___y_3752_, sizeof(void*)*14);
v_cancelTk_x3f_3778_ = lean_ctor_get(v___y_3752_, 12);
v_suppressElabErrors_3779_ = lean_ctor_get_uint8(v___y_3752_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3780_ = lean_ctor_get(v___y_3752_, 13);
v___x_3786_ = lean_unsigned_to_nat(0u);
v___x_3787_ = lean_nat_dec_eq(v_maxRecDepth_3769_, v___x_3786_);
if (v___x_3787_ == 0)
{
uint8_t v___x_3788_; 
v___x_3788_ = lean_nat_dec_eq(v_currRecDepth_3768_, v_maxRecDepth_3769_);
if (v___x_3788_ == 0)
{
goto v___jp_3781_;
}
else
{
lean_object* v___x_3789_; 
lean_dec_ref(v_x_3748_);
lean_inc(v_ref_3770_);
v___x_3789_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg(v_ref_3770_);
v___y_3756_ = v___x_3789_;
goto v___jp_3755_;
}
}
else
{
goto v___jp_3781_;
}
v___jp_3755_:
{
if (lean_obj_tag(v___y_3756_) == 0)
{
return v___y_3756_;
}
else
{
lean_object* v_a_3757_; lean_object* v___x_3759_; uint8_t v_isShared_3760_; uint8_t v_isSharedCheck_3764_; 
v_a_3757_ = lean_ctor_get(v___y_3756_, 0);
v_isSharedCheck_3764_ = !lean_is_exclusive(v___y_3756_);
if (v_isSharedCheck_3764_ == 0)
{
v___x_3759_ = v___y_3756_;
v_isShared_3760_ = v_isSharedCheck_3764_;
goto v_resetjp_3758_;
}
else
{
lean_inc(v_a_3757_);
lean_dec(v___y_3756_);
v___x_3759_ = lean_box(0);
v_isShared_3760_ = v_isSharedCheck_3764_;
goto v_resetjp_3758_;
}
v_resetjp_3758_:
{
lean_object* v___x_3762_; 
if (v_isShared_3760_ == 0)
{
v___x_3762_ = v___x_3759_;
goto v_reusejp_3761_;
}
else
{
lean_object* v_reuseFailAlloc_3763_; 
v_reuseFailAlloc_3763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3763_, 0, v_a_3757_);
v___x_3762_ = v_reuseFailAlloc_3763_;
goto v_reusejp_3761_;
}
v_reusejp_3761_:
{
return v___x_3762_;
}
}
}
}
v___jp_3781_:
{
lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; 
v___x_3782_ = lean_unsigned_to_nat(1u);
v___x_3783_ = lean_nat_add(v_currRecDepth_3768_, v___x_3782_);
lean_inc_ref(v_inheritedTraceOptions_3780_);
lean_inc(v_cancelTk_x3f_3778_);
lean_inc(v_currMacroScope_3776_);
lean_inc(v_quotContext_3775_);
lean_inc(v_maxHeartbeats_3774_);
lean_inc(v_initHeartbeats_3773_);
lean_inc(v_openDecls_3772_);
lean_inc(v_currNamespace_3771_);
lean_inc(v_ref_3770_);
lean_inc(v_maxRecDepth_3769_);
lean_inc_ref(v_options_3767_);
lean_inc_ref(v_fileMap_3766_);
lean_inc_ref(v_fileName_3765_);
v___x_3784_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3784_, 0, v_fileName_3765_);
lean_ctor_set(v___x_3784_, 1, v_fileMap_3766_);
lean_ctor_set(v___x_3784_, 2, v_options_3767_);
lean_ctor_set(v___x_3784_, 3, v___x_3783_);
lean_ctor_set(v___x_3784_, 4, v_maxRecDepth_3769_);
lean_ctor_set(v___x_3784_, 5, v_ref_3770_);
lean_ctor_set(v___x_3784_, 6, v_currNamespace_3771_);
lean_ctor_set(v___x_3784_, 7, v_openDecls_3772_);
lean_ctor_set(v___x_3784_, 8, v_initHeartbeats_3773_);
lean_ctor_set(v___x_3784_, 9, v_maxHeartbeats_3774_);
lean_ctor_set(v___x_3784_, 10, v_quotContext_3775_);
lean_ctor_set(v___x_3784_, 11, v_currMacroScope_3776_);
lean_ctor_set(v___x_3784_, 12, v_cancelTk_x3f_3778_);
lean_ctor_set(v___x_3784_, 13, v_inheritedTraceOptions_3780_);
lean_ctor_set_uint8(v___x_3784_, sizeof(void*)*14, v_diag_3777_);
lean_ctor_set_uint8(v___x_3784_, sizeof(void*)*14 + 1, v_suppressElabErrors_3779_);
lean_inc(v___y_3753_);
lean_inc(v___y_3751_);
lean_inc_ref(v___y_3750_);
lean_inc(v___y_3749_);
v___x_3785_ = lean_apply_6(v_x_3748_, v___y_3749_, v___y_3750_, v___y_3751_, v___x_3784_, v___y_3753_, lean_box(0));
v___y_3756_ = v___x_3785_;
goto v___jp_3755_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg___boxed(lean_object* v_x_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_){
_start:
{
lean_object* v_res_3797_; 
v_res_3797_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg(v_x_3790_, v___y_3791_, v___y_3792_, v___y_3793_, v___y_3794_, v___y_3795_);
lean_dec(v___y_3795_);
lean_dec_ref(v___y_3794_);
lean_dec(v___y_3793_);
lean_dec_ref(v___y_3792_);
lean_dec(v___y_3791_);
return v_res_3797_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___lam__0(lean_object* v_fvars_3798_, lean_object* v_pre_3799_, lean_object* v_post_3800_, uint8_t v_usedLetOnly_3801_, uint8_t v_skipConstInApp_3802_, uint8_t v_skipInstances_3803_, lean_object* v_body_3804_, lean_object* v_x_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_){
_start:
{
lean_object* v___x_3812_; lean_object* v___x_3813_; 
v___x_3812_ = lean_array_push(v_fvars_3798_, v_x_3805_);
v___x_3813_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6(v_pre_3799_, v_post_3800_, v_usedLetOnly_3801_, v_skipConstInApp_3802_, v_skipInstances_3803_, v___x_3812_, v_body_3804_, v___y_3806_, v___y_3807_, v___y_3808_, v___y_3809_, v___y_3810_);
return v___x_3813_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___lam__0___boxed(lean_object* v_fvars_3814_, lean_object* v_pre_3815_, lean_object* v_post_3816_, lean_object* v_usedLetOnly_3817_, lean_object* v_skipConstInApp_3818_, lean_object* v_skipInstances_3819_, lean_object* v_body_3820_, lean_object* v_x_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_){
_start:
{
uint8_t v_usedLetOnly_boxed_3828_; uint8_t v_skipConstInApp_boxed_3829_; uint8_t v_skipInstances_boxed_3830_; lean_object* v_res_3831_; 
v_usedLetOnly_boxed_3828_ = lean_unbox(v_usedLetOnly_3817_);
v_skipConstInApp_boxed_3829_ = lean_unbox(v_skipConstInApp_3818_);
v_skipInstances_boxed_3830_ = lean_unbox(v_skipInstances_3819_);
v_res_3831_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___lam__0(v_fvars_3814_, v_pre_3815_, v_post_3816_, v_usedLetOnly_boxed_3828_, v_skipConstInApp_boxed_3829_, v_skipInstances_boxed_3830_, v_body_3820_, v_x_3821_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_);
lean_dec(v___y_3826_);
lean_dec_ref(v___y_3825_);
lean_dec(v___y_3824_);
lean_dec_ref(v___y_3823_);
lean_dec(v___y_3822_);
return v_res_3831_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(lean_object* v_pre_3832_, lean_object* v_post_3833_, uint8_t v_usedLetOnly_3834_, uint8_t v_skipConstInApp_3835_, uint8_t v_skipInstances_3836_, lean_object* v_e_3837_, lean_object* v_a_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_){
_start:
{
lean_object* v___x_3844_; 
lean_inc_ref(v_post_3833_);
lean_inc(v___y_3842_);
lean_inc_ref(v___y_3841_);
lean_inc(v___y_3840_);
lean_inc_ref(v___y_3839_);
lean_inc_ref(v_e_3837_);
v___x_3844_ = lean_apply_6(v_post_3833_, v_e_3837_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_, lean_box(0));
if (lean_obj_tag(v___x_3844_) == 0)
{
lean_object* v_a_3845_; lean_object* v___x_3847_; uint8_t v_isShared_3848_; uint8_t v_isSharedCheck_3863_; 
v_a_3845_ = lean_ctor_get(v___x_3844_, 0);
v_isSharedCheck_3863_ = !lean_is_exclusive(v___x_3844_);
if (v_isSharedCheck_3863_ == 0)
{
v___x_3847_ = v___x_3844_;
v_isShared_3848_ = v_isSharedCheck_3863_;
goto v_resetjp_3846_;
}
else
{
lean_inc(v_a_3845_);
lean_dec(v___x_3844_);
v___x_3847_ = lean_box(0);
v_isShared_3848_ = v_isSharedCheck_3863_;
goto v_resetjp_3846_;
}
v_resetjp_3846_:
{
switch(lean_obj_tag(v_a_3845_))
{
case 0:
{
lean_object* v_e_3849_; lean_object* v___x_3851_; 
lean_dec_ref(v_e_3837_);
lean_dec_ref(v_post_3833_);
lean_dec_ref(v_pre_3832_);
v_e_3849_ = lean_ctor_get(v_a_3845_, 0);
lean_inc_ref(v_e_3849_);
lean_dec_ref_known(v_a_3845_, 1);
if (v_isShared_3848_ == 0)
{
lean_ctor_set(v___x_3847_, 0, v_e_3849_);
v___x_3851_ = v___x_3847_;
goto v_reusejp_3850_;
}
else
{
lean_object* v_reuseFailAlloc_3852_; 
v_reuseFailAlloc_3852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3852_, 0, v_e_3849_);
v___x_3851_ = v_reuseFailAlloc_3852_;
goto v_reusejp_3850_;
}
v_reusejp_3850_:
{
return v___x_3851_;
}
}
case 1:
{
lean_object* v_e_3853_; lean_object* v___x_3854_; 
lean_del_object(v___x_3847_);
lean_dec_ref(v_e_3837_);
v_e_3853_ = lean_ctor_get(v_a_3845_, 0);
lean_inc_ref(v_e_3853_);
lean_dec_ref_known(v_a_3845_, 1);
v___x_3854_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3832_, v_post_3833_, v_usedLetOnly_3834_, v_skipConstInApp_3835_, v_skipInstances_3836_, v_e_3853_, v_a_3838_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_);
return v___x_3854_;
}
default: 
{
lean_object* v_e_x3f_3855_; 
lean_dec_ref(v_post_3833_);
lean_dec_ref(v_pre_3832_);
v_e_x3f_3855_ = lean_ctor_get(v_a_3845_, 0);
lean_inc(v_e_x3f_3855_);
lean_dec_ref_known(v_a_3845_, 1);
if (lean_obj_tag(v_e_x3f_3855_) == 0)
{
lean_object* v___x_3857_; 
if (v_isShared_3848_ == 0)
{
lean_ctor_set(v___x_3847_, 0, v_e_3837_);
v___x_3857_ = v___x_3847_;
goto v_reusejp_3856_;
}
else
{
lean_object* v_reuseFailAlloc_3858_; 
v_reuseFailAlloc_3858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3858_, 0, v_e_3837_);
v___x_3857_ = v_reuseFailAlloc_3858_;
goto v_reusejp_3856_;
}
v_reusejp_3856_:
{
return v___x_3857_;
}
}
else
{
lean_object* v_val_3859_; lean_object* v___x_3861_; 
lean_dec_ref(v_e_3837_);
v_val_3859_ = lean_ctor_get(v_e_x3f_3855_, 0);
lean_inc(v_val_3859_);
lean_dec_ref_known(v_e_x3f_3855_, 1);
if (v_isShared_3848_ == 0)
{
lean_ctor_set(v___x_3847_, 0, v_val_3859_);
v___x_3861_ = v___x_3847_;
goto v_reusejp_3860_;
}
else
{
lean_object* v_reuseFailAlloc_3862_; 
v_reuseFailAlloc_3862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3862_, 0, v_val_3859_);
v___x_3861_ = v_reuseFailAlloc_3862_;
goto v_reusejp_3860_;
}
v_reusejp_3860_:
{
return v___x_3861_;
}
}
}
}
}
}
else
{
lean_object* v_a_3864_; lean_object* v___x_3866_; uint8_t v_isShared_3867_; uint8_t v_isSharedCheck_3871_; 
lean_dec_ref(v_e_3837_);
lean_dec_ref(v_post_3833_);
lean_dec_ref(v_pre_3832_);
v_a_3864_ = lean_ctor_get(v___x_3844_, 0);
v_isSharedCheck_3871_ = !lean_is_exclusive(v___x_3844_);
if (v_isSharedCheck_3871_ == 0)
{
v___x_3866_ = v___x_3844_;
v_isShared_3867_ = v_isSharedCheck_3871_;
goto v_resetjp_3865_;
}
else
{
lean_inc(v_a_3864_);
lean_dec(v___x_3844_);
v___x_3866_ = lean_box(0);
v_isShared_3867_ = v_isSharedCheck_3871_;
goto v_resetjp_3865_;
}
v_resetjp_3865_:
{
lean_object* v___x_3869_; 
if (v_isShared_3867_ == 0)
{
v___x_3869_ = v___x_3866_;
goto v_reusejp_3868_;
}
else
{
lean_object* v_reuseFailAlloc_3870_; 
v_reuseFailAlloc_3870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3870_, 0, v_a_3864_);
v___x_3869_ = v_reuseFailAlloc_3870_;
goto v_reusejp_3868_;
}
v_reusejp_3868_:
{
return v___x_3869_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6(lean_object* v_pre_3872_, lean_object* v_post_3873_, uint8_t v_usedLetOnly_3874_, uint8_t v_skipConstInApp_3875_, uint8_t v_skipInstances_3876_, lean_object* v_fvars_3877_, lean_object* v_e_3878_, lean_object* v_a_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_){
_start:
{
if (lean_obj_tag(v_e_3878_) == 6)
{
lean_object* v_binderName_3885_; lean_object* v_binderType_3886_; lean_object* v_body_3887_; uint8_t v_binderInfo_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; 
v_binderName_3885_ = lean_ctor_get(v_e_3878_, 0);
lean_inc(v_binderName_3885_);
v_binderType_3886_ = lean_ctor_get(v_e_3878_, 1);
lean_inc_ref(v_binderType_3886_);
v_body_3887_ = lean_ctor_get(v_e_3878_, 2);
lean_inc_ref(v_body_3887_);
v_binderInfo_3888_ = lean_ctor_get_uint8(v_e_3878_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_3878_, 3);
v___x_3889_ = lean_expr_instantiate_rev(v_binderType_3886_, v_fvars_3877_);
lean_dec_ref(v_binderType_3886_);
lean_inc_ref(v_post_3873_);
lean_inc_ref(v_pre_3872_);
v___x_3890_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3872_, v_post_3873_, v_usedLetOnly_3874_, v_skipConstInApp_3875_, v_skipInstances_3876_, v___x_3889_, v_a_3879_, v___y_3880_, v___y_3881_, v___y_3882_, v___y_3883_);
if (lean_obj_tag(v___x_3890_) == 0)
{
lean_object* v_a_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___f_3895_; uint8_t v___x_3896_; lean_object* v___x_3897_; 
v_a_3891_ = lean_ctor_get(v___x_3890_, 0);
lean_inc(v_a_3891_);
lean_dec_ref_known(v___x_3890_, 1);
v___x_3892_ = lean_box(v_usedLetOnly_3874_);
v___x_3893_ = lean_box(v_skipConstInApp_3875_);
v___x_3894_ = lean_box(v_skipInstances_3876_);
v___f_3895_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___lam__0___boxed), 14, 7);
lean_closure_set(v___f_3895_, 0, v_fvars_3877_);
lean_closure_set(v___f_3895_, 1, v_pre_3872_);
lean_closure_set(v___f_3895_, 2, v_post_3873_);
lean_closure_set(v___f_3895_, 3, v___x_3892_);
lean_closure_set(v___f_3895_, 4, v___x_3893_);
lean_closure_set(v___f_3895_, 5, v___x_3894_);
lean_closure_set(v___f_3895_, 6, v_body_3887_);
v___x_3896_ = 0;
v___x_3897_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_binderName_3885_, v_binderInfo_3888_, v_a_3891_, v___f_3895_, v___x_3896_, v_a_3879_, v___y_3880_, v___y_3881_, v___y_3882_, v___y_3883_);
return v___x_3897_;
}
else
{
lean_dec_ref(v_body_3887_);
lean_dec(v_binderName_3885_);
lean_dec_ref(v_fvars_3877_);
lean_dec_ref(v_post_3873_);
lean_dec_ref(v_pre_3872_);
return v___x_3890_;
}
}
else
{
lean_object* v___x_3898_; lean_object* v___x_3899_; 
v___x_3898_ = lean_expr_instantiate_rev(v_e_3878_, v_fvars_3877_);
lean_dec_ref(v_e_3878_);
lean_inc_ref(v_post_3873_);
lean_inc_ref(v_pre_3872_);
v___x_3899_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3872_, v_post_3873_, v_usedLetOnly_3874_, v_skipConstInApp_3875_, v_skipInstances_3876_, v___x_3898_, v_a_3879_, v___y_3880_, v___y_3881_, v___y_3882_, v___y_3883_);
if (lean_obj_tag(v___x_3899_) == 0)
{
lean_object* v_a_3900_; uint8_t v___x_3901_; uint8_t v___x_3902_; uint8_t v___x_3903_; lean_object* v___x_3904_; 
v_a_3900_ = lean_ctor_get(v___x_3899_, 0);
lean_inc(v_a_3900_);
lean_dec_ref_known(v___x_3899_, 1);
v___x_3901_ = 0;
v___x_3902_ = 1;
v___x_3903_ = 1;
v___x_3904_ = l_Lean_Meta_mkLambdaFVars(v_fvars_3877_, v_a_3900_, v___x_3901_, v_usedLetOnly_3874_, v___x_3901_, v___x_3902_, v___x_3903_, v___y_3880_, v___y_3881_, v___y_3882_, v___y_3883_);
lean_dec_ref(v_fvars_3877_);
if (lean_obj_tag(v___x_3904_) == 0)
{
lean_object* v_a_3905_; lean_object* v___x_3906_; 
v_a_3905_ = lean_ctor_get(v___x_3904_, 0);
lean_inc(v_a_3905_);
lean_dec_ref_known(v___x_3904_, 1);
v___x_3906_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_3872_, v_post_3873_, v_usedLetOnly_3874_, v_skipConstInApp_3875_, v_skipInstances_3876_, v_a_3905_, v_a_3879_, v___y_3880_, v___y_3881_, v___y_3882_, v___y_3883_);
return v___x_3906_;
}
else
{
lean_dec_ref(v_post_3873_);
lean_dec_ref(v_pre_3872_);
return v___x_3904_;
}
}
else
{
lean_dec_ref(v_fvars_3877_);
lean_dec_ref(v_post_3873_);
lean_dec_ref(v_pre_3872_);
return v___x_3899_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___lam__0(lean_object* v_fvars_3907_, lean_object* v_pre_3908_, lean_object* v_post_3909_, uint8_t v_usedLetOnly_3910_, uint8_t v_skipConstInApp_3911_, uint8_t v_skipInstances_3912_, lean_object* v_body_3913_, lean_object* v_x_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_){
_start:
{
lean_object* v___x_3921_; lean_object* v___x_3922_; 
v___x_3921_ = lean_array_push(v_fvars_3907_, v_x_3914_);
v___x_3922_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7(v_pre_3908_, v_post_3909_, v_usedLetOnly_3910_, v_skipConstInApp_3911_, v_skipInstances_3912_, v___x_3921_, v_body_3913_, v___y_3915_, v___y_3916_, v___y_3917_, v___y_3918_, v___y_3919_);
return v___x_3922_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___lam__0___boxed(lean_object* v_fvars_3923_, lean_object* v_pre_3924_, lean_object* v_post_3925_, lean_object* v_usedLetOnly_3926_, lean_object* v_skipConstInApp_3927_, lean_object* v_skipInstances_3928_, lean_object* v_body_3929_, lean_object* v_x_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_){
_start:
{
uint8_t v_usedLetOnly_boxed_3937_; uint8_t v_skipConstInApp_boxed_3938_; uint8_t v_skipInstances_boxed_3939_; lean_object* v_res_3940_; 
v_usedLetOnly_boxed_3937_ = lean_unbox(v_usedLetOnly_3926_);
v_skipConstInApp_boxed_3938_ = lean_unbox(v_skipConstInApp_3927_);
v_skipInstances_boxed_3939_ = lean_unbox(v_skipInstances_3928_);
v_res_3940_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___lam__0(v_fvars_3923_, v_pre_3924_, v_post_3925_, v_usedLetOnly_boxed_3937_, v_skipConstInApp_boxed_3938_, v_skipInstances_boxed_3939_, v_body_3929_, v_x_3930_, v___y_3931_, v___y_3932_, v___y_3933_, v___y_3934_, v___y_3935_);
lean_dec(v___y_3935_);
lean_dec_ref(v___y_3934_);
lean_dec(v___y_3933_);
lean_dec_ref(v___y_3932_);
lean_dec(v___y_3931_);
return v_res_3940_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7(lean_object* v_pre_3941_, lean_object* v_post_3942_, uint8_t v_usedLetOnly_3943_, uint8_t v_skipConstInApp_3944_, uint8_t v_skipInstances_3945_, lean_object* v_fvars_3946_, lean_object* v_e_3947_, lean_object* v_a_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_){
_start:
{
if (lean_obj_tag(v_e_3947_) == 8)
{
lean_object* v_declName_3954_; lean_object* v_type_3955_; lean_object* v_value_3956_; lean_object* v_body_3957_; uint8_t v_nondep_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; 
v_declName_3954_ = lean_ctor_get(v_e_3947_, 0);
lean_inc(v_declName_3954_);
v_type_3955_ = lean_ctor_get(v_e_3947_, 1);
lean_inc_ref(v_type_3955_);
v_value_3956_ = lean_ctor_get(v_e_3947_, 2);
lean_inc_ref(v_value_3956_);
v_body_3957_ = lean_ctor_get(v_e_3947_, 3);
lean_inc_ref(v_body_3957_);
v_nondep_3958_ = lean_ctor_get_uint8(v_e_3947_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_3947_, 4);
v___x_3959_ = lean_expr_instantiate_rev(v_type_3955_, v_fvars_3946_);
lean_dec_ref(v_type_3955_);
lean_inc_ref(v_post_3942_);
lean_inc_ref(v_pre_3941_);
v___x_3960_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3941_, v_post_3942_, v_usedLetOnly_3943_, v_skipConstInApp_3944_, v_skipInstances_3945_, v___x_3959_, v_a_3948_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_);
if (lean_obj_tag(v___x_3960_) == 0)
{
lean_object* v_a_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; 
v_a_3961_ = lean_ctor_get(v___x_3960_, 0);
lean_inc(v_a_3961_);
lean_dec_ref_known(v___x_3960_, 1);
v___x_3962_ = lean_expr_instantiate_rev(v_value_3956_, v_fvars_3946_);
lean_dec_ref(v_value_3956_);
lean_inc_ref(v_post_3942_);
lean_inc_ref(v_pre_3941_);
v___x_3963_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3941_, v_post_3942_, v_usedLetOnly_3943_, v_skipConstInApp_3944_, v_skipInstances_3945_, v___x_3962_, v_a_3948_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_);
if (lean_obj_tag(v___x_3963_) == 0)
{
lean_object* v_a_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___f_3968_; uint8_t v___x_3969_; lean_object* v___x_3970_; 
v_a_3964_ = lean_ctor_get(v___x_3963_, 0);
lean_inc(v_a_3964_);
lean_dec_ref_known(v___x_3963_, 1);
v___x_3965_ = lean_box(v_usedLetOnly_3943_);
v___x_3966_ = lean_box(v_skipConstInApp_3944_);
v___x_3967_ = lean_box(v_skipInstances_3945_);
v___f_3968_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___lam__0___boxed), 14, 7);
lean_closure_set(v___f_3968_, 0, v_fvars_3946_);
lean_closure_set(v___f_3968_, 1, v_pre_3941_);
lean_closure_set(v___f_3968_, 2, v_post_3942_);
lean_closure_set(v___f_3968_, 3, v___x_3965_);
lean_closure_set(v___f_3968_, 4, v___x_3966_);
lean_closure_set(v___f_3968_, 5, v___x_3967_);
lean_closure_set(v___f_3968_, 6, v_body_3957_);
v___x_3969_ = 0;
v___x_3970_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg(v_declName_3954_, v_a_3961_, v_a_3964_, v___f_3968_, v_nondep_3958_, v___x_3969_, v_a_3948_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_);
return v___x_3970_;
}
else
{
lean_dec(v_a_3961_);
lean_dec_ref(v_body_3957_);
lean_dec(v_declName_3954_);
lean_dec_ref(v_fvars_3946_);
lean_dec_ref(v_post_3942_);
lean_dec_ref(v_pre_3941_);
return v___x_3963_;
}
}
else
{
lean_dec_ref(v_body_3957_);
lean_dec_ref(v_value_3956_);
lean_dec(v_declName_3954_);
lean_dec_ref(v_fvars_3946_);
lean_dec_ref(v_post_3942_);
lean_dec_ref(v_pre_3941_);
return v___x_3960_;
}
}
else
{
lean_object* v___x_3971_; lean_object* v___x_3972_; 
v___x_3971_ = lean_expr_instantiate_rev(v_e_3947_, v_fvars_3946_);
lean_dec_ref(v_e_3947_);
lean_inc_ref(v_post_3942_);
lean_inc_ref(v_pre_3941_);
v___x_3972_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3941_, v_post_3942_, v_usedLetOnly_3943_, v_skipConstInApp_3944_, v_skipInstances_3945_, v___x_3971_, v_a_3948_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_);
if (lean_obj_tag(v___x_3972_) == 0)
{
lean_object* v_a_3973_; uint8_t v___x_3974_; uint8_t v___x_3975_; lean_object* v___x_3976_; 
v_a_3973_ = lean_ctor_get(v___x_3972_, 0);
lean_inc(v_a_3973_);
lean_dec_ref_known(v___x_3972_, 1);
v___x_3974_ = 0;
v___x_3975_ = 1;
v___x_3976_ = l_Lean_Meta_mkLetFVars(v_fvars_3946_, v_a_3973_, v_usedLetOnly_3943_, v___x_3974_, v___x_3975_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_);
lean_dec_ref(v_fvars_3946_);
if (lean_obj_tag(v___x_3976_) == 0)
{
lean_object* v_a_3977_; lean_object* v___x_3978_; 
v_a_3977_ = lean_ctor_get(v___x_3976_, 0);
lean_inc(v_a_3977_);
lean_dec_ref_known(v___x_3976_, 1);
v___x_3978_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_3941_, v_post_3942_, v_usedLetOnly_3943_, v_skipConstInApp_3944_, v_skipInstances_3945_, v_a_3977_, v_a_3948_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_);
return v___x_3978_;
}
else
{
lean_dec_ref(v_post_3942_);
lean_dec_ref(v_pre_3941_);
return v___x_3976_;
}
}
else
{
lean_dec_ref(v_fvars_3946_);
lean_dec_ref(v_post_3942_);
lean_dec_ref(v_pre_3941_);
return v___x_3972_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__2(lean_object* v_pre_3979_, lean_object* v_post_3980_, uint8_t v_usedLetOnly_3981_, uint8_t v_skipConstInApp_3982_, uint8_t v_skipInstances_3983_, size_t v_sz_3984_, size_t v_i_3985_, lean_object* v_bs_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_){
_start:
{
uint8_t v___x_3993_; 
v___x_3993_ = lean_usize_dec_lt(v_i_3985_, v_sz_3984_);
if (v___x_3993_ == 0)
{
lean_object* v___x_3994_; 
lean_dec_ref(v_post_3980_);
lean_dec_ref(v_pre_3979_);
v___x_3994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3994_, 0, v_bs_3986_);
return v___x_3994_;
}
else
{
lean_object* v_v_3995_; lean_object* v___x_3996_; 
v_v_3995_ = lean_array_uget_borrowed(v_bs_3986_, v_i_3985_);
lean_inc(v_v_3995_);
lean_inc_ref(v_post_3980_);
lean_inc_ref(v_pre_3979_);
v___x_3996_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3979_, v_post_3980_, v_usedLetOnly_3981_, v_skipConstInApp_3982_, v_skipInstances_3983_, v_v_3995_, v___y_3987_, v___y_3988_, v___y_3989_, v___y_3990_, v___y_3991_);
if (lean_obj_tag(v___x_3996_) == 0)
{
lean_object* v_a_3997_; lean_object* v___x_3998_; lean_object* v_bs_x27_3999_; size_t v___x_4000_; size_t v___x_4001_; lean_object* v___x_4002_; 
v_a_3997_ = lean_ctor_get(v___x_3996_, 0);
lean_inc(v_a_3997_);
lean_dec_ref_known(v___x_3996_, 1);
v___x_3998_ = lean_unsigned_to_nat(0u);
v_bs_x27_3999_ = lean_array_uset(v_bs_3986_, v_i_3985_, v___x_3998_);
v___x_4000_ = ((size_t)1ULL);
v___x_4001_ = lean_usize_add(v_i_3985_, v___x_4000_);
v___x_4002_ = lean_array_uset(v_bs_x27_3999_, v_i_3985_, v_a_3997_);
v_i_3985_ = v___x_4001_;
v_bs_3986_ = v___x_4002_;
goto _start;
}
else
{
lean_object* v_a_4004_; lean_object* v___x_4006_; uint8_t v_isShared_4007_; uint8_t v_isSharedCheck_4011_; 
lean_dec_ref(v_bs_3986_);
lean_dec_ref(v_post_3980_);
lean_dec_ref(v_pre_3979_);
v_a_4004_ = lean_ctor_get(v___x_3996_, 0);
v_isSharedCheck_4011_ = !lean_is_exclusive(v___x_3996_);
if (v_isSharedCheck_4011_ == 0)
{
v___x_4006_ = v___x_3996_;
v_isShared_4007_ = v_isSharedCheck_4011_;
goto v_resetjp_4005_;
}
else
{
lean_inc(v_a_4004_);
lean_dec(v___x_3996_);
v___x_4006_ = lean_box(0);
v_isShared_4007_ = v_isSharedCheck_4011_;
goto v_resetjp_4005_;
}
v_resetjp_4005_:
{
lean_object* v___x_4009_; 
if (v_isShared_4007_ == 0)
{
v___x_4009_ = v___x_4006_;
goto v_reusejp_4008_;
}
else
{
lean_object* v_reuseFailAlloc_4010_; 
v_reuseFailAlloc_4010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4010_, 0, v_a_4004_);
v___x_4009_ = v_reuseFailAlloc_4010_;
goto v_reusejp_4008_;
}
v_reusejp_4008_:
{
return v___x_4009_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0(lean_object* v_pre_4012_, lean_object* v_post_4013_, uint8_t v_usedLetOnly_4014_, uint8_t v_skipConstInApp_4015_, uint8_t v_skipInstances_4016_, lean_object* v___x_4017_, lean_object* v___y_4018_, lean_object* v_b_4019_, lean_object* v_a_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_){
_start:
{
lean_object* v___x_4026_; 
v___x_4026_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4012_, v_post_4013_, v_usedLetOnly_4014_, v_skipConstInApp_4015_, v_skipInstances_4016_, v___x_4017_, v___y_4018_, v___y_4021_, v___y_4022_, v___y_4023_, v___y_4024_);
if (lean_obj_tag(v___x_4026_) == 0)
{
lean_object* v_a_4027_; lean_object* v___x_4029_; uint8_t v_isShared_4030_; uint8_t v_isSharedCheck_4036_; 
v_a_4027_ = lean_ctor_get(v___x_4026_, 0);
v_isSharedCheck_4036_ = !lean_is_exclusive(v___x_4026_);
if (v_isSharedCheck_4036_ == 0)
{
v___x_4029_ = v___x_4026_;
v_isShared_4030_ = v_isSharedCheck_4036_;
goto v_resetjp_4028_;
}
else
{
lean_inc(v_a_4027_);
lean_dec(v___x_4026_);
v___x_4029_ = lean_box(0);
v_isShared_4030_ = v_isSharedCheck_4036_;
goto v_resetjp_4028_;
}
v_resetjp_4028_:
{
lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4034_; 
v___x_4031_ = lean_array_fset(v_b_4019_, v_a_4020_, v_a_4027_);
v___x_4032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4032_, 0, v___x_4031_);
if (v_isShared_4030_ == 0)
{
lean_ctor_set(v___x_4029_, 0, v___x_4032_);
v___x_4034_ = v___x_4029_;
goto v_reusejp_4033_;
}
else
{
lean_object* v_reuseFailAlloc_4035_; 
v_reuseFailAlloc_4035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4035_, 0, v___x_4032_);
v___x_4034_ = v_reuseFailAlloc_4035_;
goto v_reusejp_4033_;
}
v_reusejp_4033_:
{
return v___x_4034_;
}
}
}
else
{
lean_object* v_a_4037_; lean_object* v___x_4039_; uint8_t v_isShared_4040_; uint8_t v_isSharedCheck_4044_; 
lean_dec_ref(v_b_4019_);
v_a_4037_ = lean_ctor_get(v___x_4026_, 0);
v_isSharedCheck_4044_ = !lean_is_exclusive(v___x_4026_);
if (v_isSharedCheck_4044_ == 0)
{
v___x_4039_ = v___x_4026_;
v_isShared_4040_ = v_isSharedCheck_4044_;
goto v_resetjp_4038_;
}
else
{
lean_inc(v_a_4037_);
lean_dec(v___x_4026_);
v___x_4039_ = lean_box(0);
v_isShared_4040_ = v_isSharedCheck_4044_;
goto v_resetjp_4038_;
}
v_resetjp_4038_:
{
lean_object* v___x_4042_; 
if (v_isShared_4040_ == 0)
{
v___x_4042_ = v___x_4039_;
goto v_reusejp_4041_;
}
else
{
lean_object* v_reuseFailAlloc_4043_; 
v_reuseFailAlloc_4043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4043_, 0, v_a_4037_);
v___x_4042_ = v_reuseFailAlloc_4043_;
goto v_reusejp_4041_;
}
v_reusejp_4041_:
{
return v___x_4042_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed(lean_object* v_pre_4045_, lean_object* v_post_4046_, lean_object* v_usedLetOnly_4047_, lean_object* v_skipConstInApp_4048_, lean_object* v_skipInstances_4049_, lean_object* v___x_4050_, lean_object* v___y_4051_, lean_object* v_b_4052_, lean_object* v_a_4053_, lean_object* v___y_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_){
_start:
{
uint8_t v_usedLetOnly_boxed_4059_; uint8_t v_skipConstInApp_boxed_4060_; uint8_t v_skipInstances_boxed_4061_; lean_object* v_res_4062_; 
v_usedLetOnly_boxed_4059_ = lean_unbox(v_usedLetOnly_4047_);
v_skipConstInApp_boxed_4060_ = lean_unbox(v_skipConstInApp_4048_);
v_skipInstances_boxed_4061_ = lean_unbox(v_skipInstances_4049_);
v_res_4062_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0(v_pre_4045_, v_post_4046_, v_usedLetOnly_boxed_4059_, v_skipConstInApp_boxed_4060_, v_skipInstances_boxed_4061_, v___x_4050_, v___y_4051_, v_b_4052_, v_a_4053_, v___y_4054_, v___y_4055_, v___y_4056_, v___y_4057_);
lean_dec(v___y_4057_);
lean_dec_ref(v___y_4056_);
lean_dec(v___y_4055_);
lean_dec_ref(v___y_4054_);
lean_dec(v_a_4053_);
lean_dec(v___y_4051_);
return v_res_4062_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg(lean_object* v_upperBound_4063_, lean_object* v___x_4064_, lean_object* v_pre_4065_, lean_object* v_post_4066_, uint8_t v_usedLetOnly_4067_, uint8_t v_skipConstInApp_4068_, uint8_t v_skipInstances_4069_, lean_object* v_a_4070_, lean_object* v_b_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_){
_start:
{
lean_object* v___y_4079_; uint8_t v___x_4102_; 
v___x_4102_ = lean_nat_dec_lt(v_a_4070_, v_upperBound_4063_);
if (v___x_4102_ == 0)
{
lean_object* v___x_4103_; 
lean_dec(v_a_4070_);
lean_dec_ref(v_post_4066_);
lean_dec_ref(v_pre_4065_);
v___x_4103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4103_, 0, v_b_4071_);
return v___x_4103_;
}
else
{
lean_object* v___x_4104_; lean_object* v___x_4105_; uint8_t v___x_4106_; 
v___x_4104_ = lean_array_fget_borrowed(v_b_4071_, v_a_4070_);
v___x_4105_ = lean_array_get_size(v___x_4064_);
v___x_4106_ = lean_nat_dec_lt(v_a_4070_, v___x_4105_);
if (v___x_4106_ == 0)
{
lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___f_4110_; 
lean_inc(v___x_4104_);
v___x_4107_ = lean_box(v_usedLetOnly_4067_);
v___x_4108_ = lean_box(v_skipConstInApp_4068_);
v___x_4109_ = lean_box(v_skipInstances_4069_);
lean_inc(v_a_4070_);
lean_inc(v___y_4072_);
lean_inc_ref(v_post_4066_);
lean_inc_ref(v_pre_4065_);
v___f_4110_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_4110_, 0, v_pre_4065_);
lean_closure_set(v___f_4110_, 1, v_post_4066_);
lean_closure_set(v___f_4110_, 2, v___x_4107_);
lean_closure_set(v___f_4110_, 3, v___x_4108_);
lean_closure_set(v___f_4110_, 4, v___x_4109_);
lean_closure_set(v___f_4110_, 5, v___x_4104_);
lean_closure_set(v___f_4110_, 6, v___y_4072_);
lean_closure_set(v___f_4110_, 7, v_b_4071_);
lean_closure_set(v___f_4110_, 8, v_a_4070_);
v___y_4079_ = v___f_4110_;
goto v___jp_4078_;
}
else
{
lean_object* v___x_4111_; uint8_t v_isInstance_4112_; 
v___x_4111_ = lean_array_fget_borrowed(v___x_4064_, v_a_4070_);
v_isInstance_4112_ = lean_ctor_get_uint8(v___x_4111_, sizeof(void*)*1 + 4);
if (v_isInstance_4112_ == 0)
{
lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___f_4116_; 
lean_inc(v___x_4104_);
v___x_4113_ = lean_box(v_usedLetOnly_4067_);
v___x_4114_ = lean_box(v_skipConstInApp_4068_);
v___x_4115_ = lean_box(v_skipInstances_4069_);
lean_inc(v_a_4070_);
lean_inc(v___y_4072_);
lean_inc_ref(v_post_4066_);
lean_inc_ref(v_pre_4065_);
v___f_4116_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_4116_, 0, v_pre_4065_);
lean_closure_set(v___f_4116_, 1, v_post_4066_);
lean_closure_set(v___f_4116_, 2, v___x_4113_);
lean_closure_set(v___f_4116_, 3, v___x_4114_);
lean_closure_set(v___f_4116_, 4, v___x_4115_);
lean_closure_set(v___f_4116_, 5, v___x_4104_);
lean_closure_set(v___f_4116_, 6, v___y_4072_);
lean_closure_set(v___f_4116_, 7, v_b_4071_);
lean_closure_set(v___f_4116_, 8, v_a_4070_);
v___y_4079_ = v___f_4116_;
goto v___jp_4078_;
}
else
{
lean_object* v___x_4117_; lean_object* v___f_4118_; 
v___x_4117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4117_, 0, v_b_4071_);
v___f_4118_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_4118_, 0, v___x_4117_);
v___y_4079_ = v___f_4118_;
goto v___jp_4078_;
}
}
}
v___jp_4078_:
{
lean_object* v___x_4080_; 
lean_inc(v___y_4076_);
lean_inc_ref(v___y_4075_);
lean_inc(v___y_4074_);
lean_inc_ref(v___y_4073_);
v___x_4080_ = lean_apply_5(v___y_4079_, v___y_4073_, v___y_4074_, v___y_4075_, v___y_4076_, lean_box(0));
if (lean_obj_tag(v___x_4080_) == 0)
{
lean_object* v_a_4081_; lean_object* v___x_4083_; uint8_t v_isShared_4084_; uint8_t v_isSharedCheck_4093_; 
v_a_4081_ = lean_ctor_get(v___x_4080_, 0);
v_isSharedCheck_4093_ = !lean_is_exclusive(v___x_4080_);
if (v_isSharedCheck_4093_ == 0)
{
v___x_4083_ = v___x_4080_;
v_isShared_4084_ = v_isSharedCheck_4093_;
goto v_resetjp_4082_;
}
else
{
lean_inc(v_a_4081_);
lean_dec(v___x_4080_);
v___x_4083_ = lean_box(0);
v_isShared_4084_ = v_isSharedCheck_4093_;
goto v_resetjp_4082_;
}
v_resetjp_4082_:
{
if (lean_obj_tag(v_a_4081_) == 0)
{
lean_object* v_a_4085_; lean_object* v___x_4087_; 
lean_dec(v_a_4070_);
lean_dec_ref(v_post_4066_);
lean_dec_ref(v_pre_4065_);
v_a_4085_ = lean_ctor_get(v_a_4081_, 0);
lean_inc(v_a_4085_);
lean_dec_ref_known(v_a_4081_, 1);
if (v_isShared_4084_ == 0)
{
lean_ctor_set(v___x_4083_, 0, v_a_4085_);
v___x_4087_ = v___x_4083_;
goto v_reusejp_4086_;
}
else
{
lean_object* v_reuseFailAlloc_4088_; 
v_reuseFailAlloc_4088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4088_, 0, v_a_4085_);
v___x_4087_ = v_reuseFailAlloc_4088_;
goto v_reusejp_4086_;
}
v_reusejp_4086_:
{
return v___x_4087_;
}
}
else
{
lean_object* v_a_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; 
lean_del_object(v___x_4083_);
v_a_4089_ = lean_ctor_get(v_a_4081_, 0);
lean_inc(v_a_4089_);
lean_dec_ref_known(v_a_4081_, 1);
v___x_4090_ = lean_unsigned_to_nat(1u);
v___x_4091_ = lean_nat_add(v_a_4070_, v___x_4090_);
lean_dec(v_a_4070_);
v_a_4070_ = v___x_4091_;
v_b_4071_ = v_a_4089_;
goto _start;
}
}
}
else
{
lean_object* v_a_4094_; lean_object* v___x_4096_; uint8_t v_isShared_4097_; uint8_t v_isSharedCheck_4101_; 
lean_dec(v_a_4070_);
lean_dec_ref(v_post_4066_);
lean_dec_ref(v_pre_4065_);
v_a_4094_ = lean_ctor_get(v___x_4080_, 0);
v_isSharedCheck_4101_ = !lean_is_exclusive(v___x_4080_);
if (v_isSharedCheck_4101_ == 0)
{
v___x_4096_ = v___x_4080_;
v_isShared_4097_ = v_isSharedCheck_4101_;
goto v_resetjp_4095_;
}
else
{
lean_inc(v_a_4094_);
lean_dec(v___x_4080_);
v___x_4096_ = lean_box(0);
v_isShared_4097_ = v_isSharedCheck_4101_;
goto v_resetjp_4095_;
}
v_resetjp_4095_:
{
lean_object* v___x_4099_; 
if (v_isShared_4097_ == 0)
{
v___x_4099_ = v___x_4096_;
goto v_reusejp_4098_;
}
else
{
lean_object* v_reuseFailAlloc_4100_; 
v_reuseFailAlloc_4100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4100_, 0, v_a_4094_);
v___x_4099_ = v_reuseFailAlloc_4100_;
goto v_reusejp_4098_;
}
v_reusejp_4098_:
{
return v___x_4099_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__8(uint8_t v_skipInstances_4119_, lean_object* v_pre_4120_, lean_object* v_post_4121_, uint8_t v_usedLetOnly_4122_, uint8_t v_skipConstInApp_4123_, lean_object* v_x_4124_, lean_object* v_x_4125_, lean_object* v_x_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_){
_start:
{
lean_object* v_f_4134_; lean_object* v___y_4135_; lean_object* v___y_4136_; lean_object* v___y_4137_; lean_object* v___y_4138_; lean_object* v___y_4139_; 
if (lean_obj_tag(v_x_4124_) == 5)
{
lean_object* v_fn_4182_; lean_object* v_arg_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; 
v_fn_4182_ = lean_ctor_get(v_x_4124_, 0);
lean_inc_ref(v_fn_4182_);
v_arg_4183_ = lean_ctor_get(v_x_4124_, 1);
lean_inc_ref(v_arg_4183_);
lean_dec_ref_known(v_x_4124_, 2);
v___x_4184_ = lean_array_set(v_x_4125_, v_x_4126_, v_arg_4183_);
v___x_4185_ = lean_unsigned_to_nat(1u);
v___x_4186_ = lean_nat_sub(v_x_4126_, v___x_4185_);
lean_dec(v_x_4126_);
v_x_4124_ = v_fn_4182_;
v_x_4125_ = v___x_4184_;
v_x_4126_ = v___x_4186_;
goto _start;
}
else
{
lean_dec(v_x_4126_);
if (v_skipConstInApp_4123_ == 0)
{
goto v___jp_4179_;
}
else
{
uint8_t v___x_4188_; 
v___x_4188_ = l_Lean_Expr_isConst(v_x_4124_);
if (v___x_4188_ == 0)
{
goto v___jp_4179_;
}
else
{
v_f_4134_ = v_x_4124_;
v___y_4135_ = v___y_4127_;
v___y_4136_ = v___y_4128_;
v___y_4137_ = v___y_4129_;
v___y_4138_ = v___y_4130_;
v___y_4139_ = v___y_4131_;
goto v___jp_4133_;
}
}
}
v___jp_4133_:
{
if (v_skipInstances_4119_ == 0)
{
size_t v_sz_4140_; size_t v___x_4141_; lean_object* v___x_4142_; 
v_sz_4140_ = lean_array_size(v_x_4125_);
v___x_4141_ = ((size_t)0ULL);
lean_inc_ref(v_post_4121_);
lean_inc_ref(v_pre_4120_);
v___x_4142_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__2(v_pre_4120_, v_post_4121_, v_usedLetOnly_4122_, v_skipConstInApp_4123_, v_skipInstances_4119_, v_sz_4140_, v___x_4141_, v_x_4125_, v___y_4135_, v___y_4136_, v___y_4137_, v___y_4138_, v___y_4139_);
if (lean_obj_tag(v___x_4142_) == 0)
{
lean_object* v_a_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; 
v_a_4143_ = lean_ctor_get(v___x_4142_, 0);
lean_inc(v_a_4143_);
lean_dec_ref_known(v___x_4142_, 1);
v___x_4144_ = l_Lean_mkAppN(v_f_4134_, v_a_4143_);
lean_dec(v_a_4143_);
v___x_4145_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4120_, v_post_4121_, v_usedLetOnly_4122_, v_skipConstInApp_4123_, v_skipInstances_4119_, v___x_4144_, v___y_4135_, v___y_4136_, v___y_4137_, v___y_4138_, v___y_4139_);
return v___x_4145_;
}
else
{
lean_object* v_a_4146_; lean_object* v___x_4148_; uint8_t v_isShared_4149_; uint8_t v_isSharedCheck_4153_; 
lean_dec_ref(v_f_4134_);
lean_dec_ref(v_post_4121_);
lean_dec_ref(v_pre_4120_);
v_a_4146_ = lean_ctor_get(v___x_4142_, 0);
v_isSharedCheck_4153_ = !lean_is_exclusive(v___x_4142_);
if (v_isSharedCheck_4153_ == 0)
{
v___x_4148_ = v___x_4142_;
v_isShared_4149_ = v_isSharedCheck_4153_;
goto v_resetjp_4147_;
}
else
{
lean_inc(v_a_4146_);
lean_dec(v___x_4142_);
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
else
{
lean_object* v___x_4154_; lean_object* v___x_4155_; 
v___x_4154_ = lean_array_get_size(v_x_4125_);
lean_inc_ref(v_f_4134_);
v___x_4155_ = l_Lean_Meta_getFunInfoNArgs(v_f_4134_, v___x_4154_, v___y_4136_, v___y_4137_, v___y_4138_, v___y_4139_);
if (lean_obj_tag(v___x_4155_) == 0)
{
lean_object* v_a_4156_; lean_object* v_paramInfo_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; 
v_a_4156_ = lean_ctor_get(v___x_4155_, 0);
lean_inc(v_a_4156_);
lean_dec_ref_known(v___x_4155_, 1);
v_paramInfo_4157_ = lean_ctor_get(v_a_4156_, 0);
lean_inc_ref(v_paramInfo_4157_);
lean_dec(v_a_4156_);
v___x_4158_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_4121_);
lean_inc_ref(v_pre_4120_);
v___x_4159_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg(v___x_4154_, v_paramInfo_4157_, v_pre_4120_, v_post_4121_, v_usedLetOnly_4122_, v_skipConstInApp_4123_, v_skipInstances_4119_, v___x_4158_, v_x_4125_, v___y_4135_, v___y_4136_, v___y_4137_, v___y_4138_, v___y_4139_);
lean_dec_ref(v_paramInfo_4157_);
if (lean_obj_tag(v___x_4159_) == 0)
{
lean_object* v_a_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; 
v_a_4160_ = lean_ctor_get(v___x_4159_, 0);
lean_inc(v_a_4160_);
lean_dec_ref_known(v___x_4159_, 1);
v___x_4161_ = l_Lean_mkAppN(v_f_4134_, v_a_4160_);
lean_dec(v_a_4160_);
v___x_4162_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4120_, v_post_4121_, v_usedLetOnly_4122_, v_skipConstInApp_4123_, v_skipInstances_4119_, v___x_4161_, v___y_4135_, v___y_4136_, v___y_4137_, v___y_4138_, v___y_4139_);
return v___x_4162_;
}
else
{
lean_object* v_a_4163_; lean_object* v___x_4165_; uint8_t v_isShared_4166_; uint8_t v_isSharedCheck_4170_; 
lean_dec_ref(v_f_4134_);
lean_dec_ref(v_post_4121_);
lean_dec_ref(v_pre_4120_);
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
lean_object* v_a_4171_; lean_object* v___x_4173_; uint8_t v_isShared_4174_; uint8_t v_isSharedCheck_4178_; 
lean_dec_ref(v_f_4134_);
lean_dec_ref(v_x_4125_);
lean_dec_ref(v_post_4121_);
lean_dec_ref(v_pre_4120_);
v_a_4171_ = lean_ctor_get(v___x_4155_, 0);
v_isSharedCheck_4178_ = !lean_is_exclusive(v___x_4155_);
if (v_isSharedCheck_4178_ == 0)
{
v___x_4173_ = v___x_4155_;
v_isShared_4174_ = v_isSharedCheck_4178_;
goto v_resetjp_4172_;
}
else
{
lean_inc(v_a_4171_);
lean_dec(v___x_4155_);
v___x_4173_ = lean_box(0);
v_isShared_4174_ = v_isSharedCheck_4178_;
goto v_resetjp_4172_;
}
v_resetjp_4172_:
{
lean_object* v___x_4176_; 
if (v_isShared_4174_ == 0)
{
v___x_4176_ = v___x_4173_;
goto v_reusejp_4175_;
}
else
{
lean_object* v_reuseFailAlloc_4177_; 
v_reuseFailAlloc_4177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4177_, 0, v_a_4171_);
v___x_4176_ = v_reuseFailAlloc_4177_;
goto v_reusejp_4175_;
}
v_reusejp_4175_:
{
return v___x_4176_;
}
}
}
}
}
v___jp_4179_:
{
lean_object* v___x_4180_; 
lean_inc_ref(v_post_4121_);
lean_inc_ref(v_pre_4120_);
v___x_4180_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4120_, v_post_4121_, v_usedLetOnly_4122_, v_skipConstInApp_4123_, v_skipInstances_4119_, v_x_4124_, v___y_4127_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_);
if (lean_obj_tag(v___x_4180_) == 0)
{
lean_object* v_a_4181_; 
v_a_4181_ = lean_ctor_get(v___x_4180_, 0);
lean_inc(v_a_4181_);
lean_dec_ref_known(v___x_4180_, 1);
v_f_4134_ = v_a_4181_;
v___y_4135_ = v___y_4127_;
v___y_4136_ = v___y_4128_;
v___y_4137_ = v___y_4129_;
v___y_4138_ = v___y_4130_;
v___y_4139_ = v___y_4131_;
goto v___jp_4133_;
}
else
{
lean_dec_ref(v_x_4125_);
lean_dec_ref(v_post_4121_);
lean_dec_ref(v_pre_4120_);
return v___x_4180_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1(lean_object* v___x_4189_, lean_object* v_pre_4190_, lean_object* v_e_4191_, lean_object* v_post_4192_, uint8_t v_usedLetOnly_4193_, uint8_t v_skipConstInApp_4194_, uint8_t v_skipInstances_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_){
_start:
{
lean_object* v___x_4202_; 
v___x_4202_ = l_Lean_Core_checkSystem(v___x_4189_, v___y_4199_, v___y_4200_);
if (lean_obj_tag(v___x_4202_) == 0)
{
lean_object* v___x_4203_; 
lean_dec_ref_known(v___x_4202_, 1);
lean_inc_ref(v_pre_4190_);
lean_inc(v___y_4200_);
lean_inc_ref(v___y_4199_);
lean_inc(v___y_4198_);
lean_inc_ref(v___y_4197_);
lean_inc_ref(v_e_4191_);
v___x_4203_ = lean_apply_6(v_pre_4190_, v_e_4191_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_, lean_box(0));
if (lean_obj_tag(v___x_4203_) == 0)
{
lean_object* v_a_4204_; lean_object* v___x_4206_; uint8_t v_isShared_4207_; uint8_t v_isSharedCheck_4252_; 
v_a_4204_ = lean_ctor_get(v___x_4203_, 0);
v_isSharedCheck_4252_ = !lean_is_exclusive(v___x_4203_);
if (v_isSharedCheck_4252_ == 0)
{
v___x_4206_ = v___x_4203_;
v_isShared_4207_ = v_isSharedCheck_4252_;
goto v_resetjp_4205_;
}
else
{
lean_inc(v_a_4204_);
lean_dec(v___x_4203_);
v___x_4206_ = lean_box(0);
v_isShared_4207_ = v_isSharedCheck_4252_;
goto v_resetjp_4205_;
}
v_resetjp_4205_:
{
lean_object* v___y_4209_; 
switch(lean_obj_tag(v_a_4204_))
{
case 0:
{
lean_object* v_e_4244_; lean_object* v___x_4246_; 
lean_dec_ref(v_post_4192_);
lean_dec_ref(v_e_4191_);
lean_dec_ref(v_pre_4190_);
v_e_4244_ = lean_ctor_get(v_a_4204_, 0);
lean_inc_ref(v_e_4244_);
lean_dec_ref_known(v_a_4204_, 1);
if (v_isShared_4207_ == 0)
{
lean_ctor_set(v___x_4206_, 0, v_e_4244_);
v___x_4246_ = v___x_4206_;
goto v_reusejp_4245_;
}
else
{
lean_object* v_reuseFailAlloc_4247_; 
v_reuseFailAlloc_4247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4247_, 0, v_e_4244_);
v___x_4246_ = v_reuseFailAlloc_4247_;
goto v_reusejp_4245_;
}
v_reusejp_4245_:
{
return v___x_4246_;
}
}
case 1:
{
lean_object* v_e_4248_; lean_object* v___x_4249_; 
lean_del_object(v___x_4206_);
lean_dec_ref(v_e_4191_);
v_e_4248_ = lean_ctor_get(v_a_4204_, 0);
lean_inc_ref(v_e_4248_);
lean_dec_ref_known(v_a_4204_, 1);
v___x_4249_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4190_, v_post_4192_, v_usedLetOnly_4193_, v_skipConstInApp_4194_, v_skipInstances_4195_, v_e_4248_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_);
return v___x_4249_;
}
default: 
{
lean_object* v_e_x3f_4250_; 
lean_del_object(v___x_4206_);
v_e_x3f_4250_ = lean_ctor_get(v_a_4204_, 0);
lean_inc(v_e_x3f_4250_);
lean_dec_ref_known(v_a_4204_, 1);
if (lean_obj_tag(v_e_x3f_4250_) == 0)
{
v___y_4209_ = v_e_4191_;
goto v___jp_4208_;
}
else
{
lean_object* v_val_4251_; 
lean_dec_ref(v_e_4191_);
v_val_4251_ = lean_ctor_get(v_e_x3f_4250_, 0);
lean_inc(v_val_4251_);
lean_dec_ref_known(v_e_x3f_4250_, 1);
v___y_4209_ = v_val_4251_;
goto v___jp_4208_;
}
}
}
v___jp_4208_:
{
switch(lean_obj_tag(v___y_4209_))
{
case 7:
{
lean_object* v___x_4210_; lean_object* v___x_4211_; 
v___x_4210_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_4211_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5(v_pre_4190_, v_post_4192_, v_usedLetOnly_4193_, v_skipConstInApp_4194_, v_skipInstances_4195_, v___x_4210_, v___y_4209_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_);
return v___x_4211_;
}
case 6:
{
lean_object* v___x_4212_; lean_object* v___x_4213_; 
v___x_4212_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_4213_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6(v_pre_4190_, v_post_4192_, v_usedLetOnly_4193_, v_skipConstInApp_4194_, v_skipInstances_4195_, v___x_4212_, v___y_4209_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_);
return v___x_4213_;
}
case 8:
{
lean_object* v___x_4214_; lean_object* v___x_4215_; 
v___x_4214_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_4215_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7(v_pre_4190_, v_post_4192_, v_usedLetOnly_4193_, v_skipConstInApp_4194_, v_skipInstances_4195_, v___x_4214_, v___y_4209_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_);
return v___x_4215_;
}
case 5:
{
lean_object* v_dummy_4216_; lean_object* v_nargs_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v___x_4220_; lean_object* v___x_4221_; 
v_dummy_4216_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_4217_ = l_Lean_Expr_getAppNumArgs(v___y_4209_);
lean_inc(v_nargs_4217_);
v___x_4218_ = lean_mk_array(v_nargs_4217_, v_dummy_4216_);
v___x_4219_ = lean_unsigned_to_nat(1u);
v___x_4220_ = lean_nat_sub(v_nargs_4217_, v___x_4219_);
lean_dec(v_nargs_4217_);
v___x_4221_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__8(v_skipInstances_4195_, v_pre_4190_, v_post_4192_, v_usedLetOnly_4193_, v_skipConstInApp_4194_, v___y_4209_, v___x_4218_, v___x_4220_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_);
return v___x_4221_;
}
case 10:
{
lean_object* v_data_4222_; lean_object* v_expr_4223_; lean_object* v___x_4224_; 
v_data_4222_ = lean_ctor_get(v___y_4209_, 0);
v_expr_4223_ = lean_ctor_get(v___y_4209_, 1);
lean_inc_ref(v_expr_4223_);
lean_inc_ref(v_post_4192_);
lean_inc_ref(v_pre_4190_);
v___x_4224_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4190_, v_post_4192_, v_usedLetOnly_4193_, v_skipConstInApp_4194_, v_skipInstances_4195_, v_expr_4223_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_);
if (lean_obj_tag(v___x_4224_) == 0)
{
lean_object* v_a_4225_; size_t v___x_4226_; size_t v___x_4227_; uint8_t v___x_4228_; 
v_a_4225_ = lean_ctor_get(v___x_4224_, 0);
lean_inc(v_a_4225_);
lean_dec_ref_known(v___x_4224_, 1);
v___x_4226_ = lean_ptr_addr(v_expr_4223_);
v___x_4227_ = lean_ptr_addr(v_a_4225_);
v___x_4228_ = lean_usize_dec_eq(v___x_4226_, v___x_4227_);
if (v___x_4228_ == 0)
{
lean_object* v___x_4229_; lean_object* v___x_4230_; 
lean_inc(v_data_4222_);
lean_dec_ref_known(v___y_4209_, 2);
v___x_4229_ = l_Lean_Expr_mdata___override(v_data_4222_, v_a_4225_);
v___x_4230_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4190_, v_post_4192_, v_usedLetOnly_4193_, v_skipConstInApp_4194_, v_skipInstances_4195_, v___x_4229_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_);
return v___x_4230_;
}
else
{
lean_object* v___x_4231_; 
lean_dec(v_a_4225_);
v___x_4231_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4190_, v_post_4192_, v_usedLetOnly_4193_, v_skipConstInApp_4194_, v_skipInstances_4195_, v___y_4209_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_);
return v___x_4231_;
}
}
else
{
lean_dec_ref_known(v___y_4209_, 2);
lean_dec_ref(v_post_4192_);
lean_dec_ref(v_pre_4190_);
return v___x_4224_;
}
}
case 11:
{
lean_object* v_typeName_4232_; lean_object* v_idx_4233_; lean_object* v_struct_4234_; lean_object* v___x_4235_; 
v_typeName_4232_ = lean_ctor_get(v___y_4209_, 0);
v_idx_4233_ = lean_ctor_get(v___y_4209_, 1);
v_struct_4234_ = lean_ctor_get(v___y_4209_, 2);
lean_inc_ref(v_struct_4234_);
lean_inc_ref(v_post_4192_);
lean_inc_ref(v_pre_4190_);
v___x_4235_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4190_, v_post_4192_, v_usedLetOnly_4193_, v_skipConstInApp_4194_, v_skipInstances_4195_, v_struct_4234_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_);
if (lean_obj_tag(v___x_4235_) == 0)
{
lean_object* v_a_4236_; size_t v___x_4237_; size_t v___x_4238_; uint8_t v___x_4239_; 
v_a_4236_ = lean_ctor_get(v___x_4235_, 0);
lean_inc(v_a_4236_);
lean_dec_ref_known(v___x_4235_, 1);
v___x_4237_ = lean_ptr_addr(v_struct_4234_);
v___x_4238_ = lean_ptr_addr(v_a_4236_);
v___x_4239_ = lean_usize_dec_eq(v___x_4237_, v___x_4238_);
if (v___x_4239_ == 0)
{
lean_object* v___x_4240_; lean_object* v___x_4241_; 
lean_inc(v_idx_4233_);
lean_inc(v_typeName_4232_);
lean_dec_ref_known(v___y_4209_, 3);
v___x_4240_ = l_Lean_Expr_proj___override(v_typeName_4232_, v_idx_4233_, v_a_4236_);
v___x_4241_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4190_, v_post_4192_, v_usedLetOnly_4193_, v_skipConstInApp_4194_, v_skipInstances_4195_, v___x_4240_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_);
return v___x_4241_;
}
else
{
lean_object* v___x_4242_; 
lean_dec(v_a_4236_);
v___x_4242_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4190_, v_post_4192_, v_usedLetOnly_4193_, v_skipConstInApp_4194_, v_skipInstances_4195_, v___y_4209_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_);
return v___x_4242_;
}
}
else
{
lean_dec_ref_known(v___y_4209_, 3);
lean_dec_ref(v_post_4192_);
lean_dec_ref(v_pre_4190_);
return v___x_4235_;
}
}
default: 
{
lean_object* v___x_4243_; 
v___x_4243_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4190_, v_post_4192_, v_usedLetOnly_4193_, v_skipConstInApp_4194_, v_skipInstances_4195_, v___y_4209_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_);
return v___x_4243_;
}
}
}
}
}
else
{
lean_object* v_a_4253_; lean_object* v___x_4255_; uint8_t v_isShared_4256_; uint8_t v_isSharedCheck_4260_; 
lean_dec_ref(v_post_4192_);
lean_dec_ref(v_e_4191_);
lean_dec_ref(v_pre_4190_);
v_a_4253_ = lean_ctor_get(v___x_4203_, 0);
v_isSharedCheck_4260_ = !lean_is_exclusive(v___x_4203_);
if (v_isSharedCheck_4260_ == 0)
{
v___x_4255_ = v___x_4203_;
v_isShared_4256_ = v_isSharedCheck_4260_;
goto v_resetjp_4254_;
}
else
{
lean_inc(v_a_4253_);
lean_dec(v___x_4203_);
v___x_4255_ = lean_box(0);
v_isShared_4256_ = v_isSharedCheck_4260_;
goto v_resetjp_4254_;
}
v_resetjp_4254_:
{
lean_object* v___x_4258_; 
if (v_isShared_4256_ == 0)
{
v___x_4258_ = v___x_4255_;
goto v_reusejp_4257_;
}
else
{
lean_object* v_reuseFailAlloc_4259_; 
v_reuseFailAlloc_4259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4259_, 0, v_a_4253_);
v___x_4258_ = v_reuseFailAlloc_4259_;
goto v_reusejp_4257_;
}
v_reusejp_4257_:
{
return v___x_4258_;
}
}
}
}
else
{
lean_object* v_a_4261_; lean_object* v___x_4263_; uint8_t v_isShared_4264_; uint8_t v_isSharedCheck_4268_; 
lean_dec_ref(v_post_4192_);
lean_dec_ref(v_e_4191_);
lean_dec_ref(v_pre_4190_);
v_a_4261_ = lean_ctor_get(v___x_4202_, 0);
v_isSharedCheck_4268_ = !lean_is_exclusive(v___x_4202_);
if (v_isSharedCheck_4268_ == 0)
{
v___x_4263_ = v___x_4202_;
v_isShared_4264_ = v_isSharedCheck_4268_;
goto v_resetjp_4262_;
}
else
{
lean_inc(v_a_4261_);
lean_dec(v___x_4202_);
v___x_4263_ = lean_box(0);
v_isShared_4264_ = v_isSharedCheck_4268_;
goto v_resetjp_4262_;
}
v_resetjp_4262_:
{
lean_object* v___x_4266_; 
if (v_isShared_4264_ == 0)
{
v___x_4266_ = v___x_4263_;
goto v_reusejp_4265_;
}
else
{
lean_object* v_reuseFailAlloc_4267_; 
v_reuseFailAlloc_4267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4267_, 0, v_a_4261_);
v___x_4266_ = v_reuseFailAlloc_4267_;
goto v_reusejp_4265_;
}
v_reusejp_4265_:
{
return v___x_4266_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1___boxed(lean_object* v___x_4269_, lean_object* v_pre_4270_, lean_object* v_e_4271_, lean_object* v_post_4272_, lean_object* v_usedLetOnly_4273_, lean_object* v_skipConstInApp_4274_, lean_object* v_skipInstances_4275_, lean_object* v___y_4276_, lean_object* v___y_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_){
_start:
{
uint8_t v_usedLetOnly_boxed_4282_; uint8_t v_skipConstInApp_boxed_4283_; uint8_t v_skipInstances_boxed_4284_; lean_object* v_res_4285_; 
v_usedLetOnly_boxed_4282_ = lean_unbox(v_usedLetOnly_4273_);
v_skipConstInApp_boxed_4283_ = lean_unbox(v_skipConstInApp_4274_);
v_skipInstances_boxed_4284_ = lean_unbox(v_skipInstances_4275_);
v_res_4285_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1(v___x_4269_, v_pre_4270_, v_e_4271_, v_post_4272_, v_usedLetOnly_boxed_4282_, v_skipConstInApp_boxed_4283_, v_skipInstances_boxed_4284_, v___y_4276_, v___y_4277_, v___y_4278_, v___y_4279_, v___y_4280_);
lean_dec(v___y_4280_);
lean_dec_ref(v___y_4279_);
lean_dec(v___y_4278_);
lean_dec_ref(v___y_4277_);
lean_dec(v___y_4276_);
return v_res_4285_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(lean_object* v_pre_4286_, lean_object* v_post_4287_, uint8_t v_usedLetOnly_4288_, uint8_t v_skipConstInApp_4289_, uint8_t v_skipInstances_4290_, lean_object* v_e_4291_, lean_object* v_a_4292_, lean_object* v___y_4293_, lean_object* v___y_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_){
_start:
{
lean_object* v___x_4298_; lean_object* v___x_4299_; 
lean_inc(v_a_4292_);
v___x_4298_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_4298_, 0, lean_box(0));
lean_closure_set(v___x_4298_, 1, lean_box(0));
lean_closure_set(v___x_4298_, 2, v_a_4292_);
v___x_4299_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0(lean_box(0), v___x_4298_, v___y_4293_, v___y_4294_, v___y_4295_, v___y_4296_);
if (lean_obj_tag(v___x_4299_) == 0)
{
lean_object* v_a_4300_; lean_object* v___x_4302_; uint8_t v_isShared_4303_; uint8_t v_isSharedCheck_4334_; 
v_a_4300_ = lean_ctor_get(v___x_4299_, 0);
v_isSharedCheck_4334_ = !lean_is_exclusive(v___x_4299_);
if (v_isSharedCheck_4334_ == 0)
{
v___x_4302_ = v___x_4299_;
v_isShared_4303_ = v_isSharedCheck_4334_;
goto v_resetjp_4301_;
}
else
{
lean_inc(v_a_4300_);
lean_dec(v___x_4299_);
v___x_4302_ = lean_box(0);
v_isShared_4303_ = v_isSharedCheck_4334_;
goto v_resetjp_4301_;
}
v_resetjp_4301_:
{
lean_object* v___x_4304_; 
v___x_4304_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg(v_a_4300_, v_e_4291_);
lean_dec(v_a_4300_);
if (lean_obj_tag(v___x_4304_) == 0)
{
lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___f_4309_; lean_object* v___x_4310_; 
lean_del_object(v___x_4302_);
v___x_4305_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__19___closed__0));
v___x_4306_ = lean_box(v_usedLetOnly_4288_);
v___x_4307_ = lean_box(v_skipConstInApp_4289_);
v___x_4308_ = lean_box(v_skipInstances_4290_);
lean_inc_ref(v_e_4291_);
v___f_4309_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1___boxed), 13, 7);
lean_closure_set(v___f_4309_, 0, v___x_4305_);
lean_closure_set(v___f_4309_, 1, v_pre_4286_);
lean_closure_set(v___f_4309_, 2, v_e_4291_);
lean_closure_set(v___f_4309_, 3, v_post_4287_);
lean_closure_set(v___f_4309_, 4, v___x_4306_);
lean_closure_set(v___f_4309_, 5, v___x_4307_);
lean_closure_set(v___f_4309_, 6, v___x_4308_);
v___x_4310_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg(v___f_4309_, v_a_4292_, v___y_4293_, v___y_4294_, v___y_4295_, v___y_4296_);
if (lean_obj_tag(v___x_4310_) == 0)
{
lean_object* v_a_4311_; lean_object* v___f_4312_; lean_object* v___x_4313_; 
v_a_4311_ = lean_ctor_get(v___x_4310_, 0);
lean_inc_n(v_a_4311_, 2);
lean_dec_ref_known(v___x_4310_, 1);
lean_inc(v_a_4292_);
v___f_4312_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_4312_, 0, v_a_4292_);
lean_closure_set(v___f_4312_, 1, v_e_4291_);
lean_closure_set(v___f_4312_, 2, v_a_4311_);
v___x_4313_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0(lean_box(0), v___f_4312_, v___y_4293_, v___y_4294_, v___y_4295_, v___y_4296_);
if (lean_obj_tag(v___x_4313_) == 0)
{
lean_object* v___x_4315_; uint8_t v_isShared_4316_; uint8_t v_isSharedCheck_4320_; 
v_isSharedCheck_4320_ = !lean_is_exclusive(v___x_4313_);
if (v_isSharedCheck_4320_ == 0)
{
lean_object* v_unused_4321_; 
v_unused_4321_ = lean_ctor_get(v___x_4313_, 0);
lean_dec(v_unused_4321_);
v___x_4315_ = v___x_4313_;
v_isShared_4316_ = v_isSharedCheck_4320_;
goto v_resetjp_4314_;
}
else
{
lean_dec(v___x_4313_);
v___x_4315_ = lean_box(0);
v_isShared_4316_ = v_isSharedCheck_4320_;
goto v_resetjp_4314_;
}
v_resetjp_4314_:
{
lean_object* v___x_4318_; 
if (v_isShared_4316_ == 0)
{
lean_ctor_set(v___x_4315_, 0, v_a_4311_);
v___x_4318_ = v___x_4315_;
goto v_reusejp_4317_;
}
else
{
lean_object* v_reuseFailAlloc_4319_; 
v_reuseFailAlloc_4319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4319_, 0, v_a_4311_);
v___x_4318_ = v_reuseFailAlloc_4319_;
goto v_reusejp_4317_;
}
v_reusejp_4317_:
{
return v___x_4318_;
}
}
}
else
{
lean_object* v_a_4322_; lean_object* v___x_4324_; uint8_t v_isShared_4325_; uint8_t v_isSharedCheck_4329_; 
lean_dec(v_a_4311_);
v_a_4322_ = lean_ctor_get(v___x_4313_, 0);
v_isSharedCheck_4329_ = !lean_is_exclusive(v___x_4313_);
if (v_isSharedCheck_4329_ == 0)
{
v___x_4324_ = v___x_4313_;
v_isShared_4325_ = v_isSharedCheck_4329_;
goto v_resetjp_4323_;
}
else
{
lean_inc(v_a_4322_);
lean_dec(v___x_4313_);
v___x_4324_ = lean_box(0);
v_isShared_4325_ = v_isSharedCheck_4329_;
goto v_resetjp_4323_;
}
v_resetjp_4323_:
{
lean_object* v___x_4327_; 
if (v_isShared_4325_ == 0)
{
v___x_4327_ = v___x_4324_;
goto v_reusejp_4326_;
}
else
{
lean_object* v_reuseFailAlloc_4328_; 
v_reuseFailAlloc_4328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4328_, 0, v_a_4322_);
v___x_4327_ = v_reuseFailAlloc_4328_;
goto v_reusejp_4326_;
}
v_reusejp_4326_:
{
return v___x_4327_;
}
}
}
}
else
{
lean_dec_ref(v_e_4291_);
return v___x_4310_;
}
}
else
{
lean_object* v_val_4330_; lean_object* v___x_4332_; 
lean_dec_ref(v_e_4291_);
lean_dec_ref(v_post_4287_);
lean_dec_ref(v_pre_4286_);
v_val_4330_ = lean_ctor_get(v___x_4304_, 0);
lean_inc(v_val_4330_);
lean_dec_ref_known(v___x_4304_, 1);
if (v_isShared_4303_ == 0)
{
lean_ctor_set(v___x_4302_, 0, v_val_4330_);
v___x_4332_ = v___x_4302_;
goto v_reusejp_4331_;
}
else
{
lean_object* v_reuseFailAlloc_4333_; 
v_reuseFailAlloc_4333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4333_, 0, v_val_4330_);
v___x_4332_ = v_reuseFailAlloc_4333_;
goto v_reusejp_4331_;
}
v_reusejp_4331_:
{
return v___x_4332_;
}
}
}
}
else
{
lean_object* v_a_4335_; lean_object* v___x_4337_; uint8_t v_isShared_4338_; uint8_t v_isSharedCheck_4342_; 
lean_dec_ref(v_e_4291_);
lean_dec_ref(v_post_4287_);
lean_dec_ref(v_pre_4286_);
v_a_4335_ = lean_ctor_get(v___x_4299_, 0);
v_isSharedCheck_4342_ = !lean_is_exclusive(v___x_4299_);
if (v_isSharedCheck_4342_ == 0)
{
v___x_4337_ = v___x_4299_;
v_isShared_4338_ = v_isSharedCheck_4342_;
goto v_resetjp_4336_;
}
else
{
lean_inc(v_a_4335_);
lean_dec(v___x_4299_);
v___x_4337_ = lean_box(0);
v_isShared_4338_ = v_isSharedCheck_4342_;
goto v_resetjp_4336_;
}
v_resetjp_4336_:
{
lean_object* v___x_4340_; 
if (v_isShared_4338_ == 0)
{
v___x_4340_ = v___x_4337_;
goto v_reusejp_4339_;
}
else
{
lean_object* v_reuseFailAlloc_4341_; 
v_reuseFailAlloc_4341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4341_, 0, v_a_4335_);
v___x_4340_ = v_reuseFailAlloc_4341_;
goto v_reusejp_4339_;
}
v_reusejp_4339_:
{
return v___x_4340_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___lam__0___boxed(lean_object* v_fvars_4343_, lean_object* v_pre_4344_, lean_object* v_post_4345_, lean_object* v_usedLetOnly_4346_, lean_object* v_skipConstInApp_4347_, lean_object* v_skipInstances_4348_, lean_object* v_body_4349_, lean_object* v_x_4350_, lean_object* v___y_4351_, lean_object* v___y_4352_, lean_object* v___y_4353_, lean_object* v___y_4354_, lean_object* v___y_4355_, lean_object* v___y_4356_){
_start:
{
uint8_t v_usedLetOnly_boxed_4357_; uint8_t v_skipConstInApp_boxed_4358_; uint8_t v_skipInstances_boxed_4359_; lean_object* v_res_4360_; 
v_usedLetOnly_boxed_4357_ = lean_unbox(v_usedLetOnly_4346_);
v_skipConstInApp_boxed_4358_ = lean_unbox(v_skipConstInApp_4347_);
v_skipInstances_boxed_4359_ = lean_unbox(v_skipInstances_4348_);
v_res_4360_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___lam__0(v_fvars_4343_, v_pre_4344_, v_post_4345_, v_usedLetOnly_boxed_4357_, v_skipConstInApp_boxed_4358_, v_skipInstances_boxed_4359_, v_body_4349_, v_x_4350_, v___y_4351_, v___y_4352_, v___y_4353_, v___y_4354_, v___y_4355_);
lean_dec(v___y_4355_);
lean_dec_ref(v___y_4354_);
lean_dec(v___y_4353_);
lean_dec_ref(v___y_4352_);
lean_dec(v___y_4351_);
return v_res_4360_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5(lean_object* v_pre_4361_, lean_object* v_post_4362_, uint8_t v_usedLetOnly_4363_, uint8_t v_skipConstInApp_4364_, uint8_t v_skipInstances_4365_, lean_object* v_fvars_4366_, lean_object* v_e_4367_, lean_object* v_a_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_, lean_object* v___y_4371_, lean_object* v___y_4372_){
_start:
{
if (lean_obj_tag(v_e_4367_) == 7)
{
lean_object* v_binderName_4374_; lean_object* v_binderType_4375_; lean_object* v_body_4376_; uint8_t v_binderInfo_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; 
v_binderName_4374_ = lean_ctor_get(v_e_4367_, 0);
lean_inc(v_binderName_4374_);
v_binderType_4375_ = lean_ctor_get(v_e_4367_, 1);
lean_inc_ref(v_binderType_4375_);
v_body_4376_ = lean_ctor_get(v_e_4367_, 2);
lean_inc_ref(v_body_4376_);
v_binderInfo_4377_ = lean_ctor_get_uint8(v_e_4367_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_4367_, 3);
v___x_4378_ = lean_expr_instantiate_rev(v_binderType_4375_, v_fvars_4366_);
lean_dec_ref(v_binderType_4375_);
lean_inc_ref(v_post_4362_);
lean_inc_ref(v_pre_4361_);
v___x_4379_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4361_, v_post_4362_, v_usedLetOnly_4363_, v_skipConstInApp_4364_, v_skipInstances_4365_, v___x_4378_, v_a_4368_, v___y_4369_, v___y_4370_, v___y_4371_, v___y_4372_);
if (lean_obj_tag(v___x_4379_) == 0)
{
lean_object* v_a_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; lean_object* v___x_4383_; lean_object* v___f_4384_; uint8_t v___x_4385_; lean_object* v___x_4386_; 
v_a_4380_ = lean_ctor_get(v___x_4379_, 0);
lean_inc(v_a_4380_);
lean_dec_ref_known(v___x_4379_, 1);
v___x_4381_ = lean_box(v_usedLetOnly_4363_);
v___x_4382_ = lean_box(v_skipConstInApp_4364_);
v___x_4383_ = lean_box(v_skipInstances_4365_);
v___f_4384_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___lam__0___boxed), 14, 7);
lean_closure_set(v___f_4384_, 0, v_fvars_4366_);
lean_closure_set(v___f_4384_, 1, v_pre_4361_);
lean_closure_set(v___f_4384_, 2, v_post_4362_);
lean_closure_set(v___f_4384_, 3, v___x_4381_);
lean_closure_set(v___f_4384_, 4, v___x_4382_);
lean_closure_set(v___f_4384_, 5, v___x_4383_);
lean_closure_set(v___f_4384_, 6, v_body_4376_);
v___x_4385_ = 0;
v___x_4386_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_binderName_4374_, v_binderInfo_4377_, v_a_4380_, v___f_4384_, v___x_4385_, v_a_4368_, v___y_4369_, v___y_4370_, v___y_4371_, v___y_4372_);
return v___x_4386_;
}
else
{
lean_dec_ref(v_body_4376_);
lean_dec(v_binderName_4374_);
lean_dec_ref(v_fvars_4366_);
lean_dec_ref(v_post_4362_);
lean_dec_ref(v_pre_4361_);
return v___x_4379_;
}
}
else
{
lean_object* v___x_4387_; lean_object* v___x_4388_; 
v___x_4387_ = lean_expr_instantiate_rev(v_e_4367_, v_fvars_4366_);
lean_dec_ref(v_e_4367_);
lean_inc_ref(v_post_4362_);
lean_inc_ref(v_pre_4361_);
v___x_4388_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4361_, v_post_4362_, v_usedLetOnly_4363_, v_skipConstInApp_4364_, v_skipInstances_4365_, v___x_4387_, v_a_4368_, v___y_4369_, v___y_4370_, v___y_4371_, v___y_4372_);
if (lean_obj_tag(v___x_4388_) == 0)
{
lean_object* v_a_4389_; uint8_t v___x_4390_; uint8_t v___x_4391_; uint8_t v___x_4392_; lean_object* v___x_4393_; 
v_a_4389_ = lean_ctor_get(v___x_4388_, 0);
lean_inc(v_a_4389_);
lean_dec_ref_known(v___x_4388_, 1);
v___x_4390_ = 0;
v___x_4391_ = 1;
v___x_4392_ = 1;
v___x_4393_ = l_Lean_Meta_mkForallFVars(v_fvars_4366_, v_a_4389_, v___x_4390_, v_usedLetOnly_4363_, v___x_4391_, v___x_4392_, v___y_4369_, v___y_4370_, v___y_4371_, v___y_4372_);
lean_dec_ref(v_fvars_4366_);
if (lean_obj_tag(v___x_4393_) == 0)
{
lean_object* v_a_4394_; lean_object* v___x_4395_; 
v_a_4394_ = lean_ctor_get(v___x_4393_, 0);
lean_inc(v_a_4394_);
lean_dec_ref_known(v___x_4393_, 1);
v___x_4395_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4361_, v_post_4362_, v_usedLetOnly_4363_, v_skipConstInApp_4364_, v_skipInstances_4365_, v_a_4394_, v_a_4368_, v___y_4369_, v___y_4370_, v___y_4371_, v___y_4372_);
return v___x_4395_;
}
else
{
lean_dec_ref(v_post_4362_);
lean_dec_ref(v_pre_4361_);
return v___x_4393_;
}
}
else
{
lean_dec_ref(v_fvars_4366_);
lean_dec_ref(v_post_4362_);
lean_dec_ref(v_pre_4361_);
return v___x_4388_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___lam__0(lean_object* v_fvars_4396_, lean_object* v_pre_4397_, lean_object* v_post_4398_, uint8_t v_usedLetOnly_4399_, uint8_t v_skipConstInApp_4400_, uint8_t v_skipInstances_4401_, lean_object* v_body_4402_, lean_object* v_x_4403_, lean_object* v___y_4404_, lean_object* v___y_4405_, lean_object* v___y_4406_, lean_object* v___y_4407_, lean_object* v___y_4408_){
_start:
{
lean_object* v___x_4410_; lean_object* v___x_4411_; 
v___x_4410_ = lean_array_push(v_fvars_4396_, v_x_4403_);
v___x_4411_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5(v_pre_4397_, v_post_4398_, v_usedLetOnly_4399_, v_skipConstInApp_4400_, v_skipInstances_4401_, v___x_4410_, v_body_4402_, v___y_4404_, v___y_4405_, v___y_4406_, v___y_4407_, v___y_4408_);
return v___x_4411_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3___boxed(lean_object* v_pre_4412_, lean_object* v_post_4413_, lean_object* v_usedLetOnly_4414_, lean_object* v_skipConstInApp_4415_, lean_object* v_skipInstances_4416_, lean_object* v_e_4417_, lean_object* v_a_4418_, lean_object* v___y_4419_, lean_object* v___y_4420_, lean_object* v___y_4421_, lean_object* v___y_4422_, lean_object* v___y_4423_){
_start:
{
uint8_t v_usedLetOnly_boxed_4424_; uint8_t v_skipConstInApp_boxed_4425_; uint8_t v_skipInstances_boxed_4426_; lean_object* v_res_4427_; 
v_usedLetOnly_boxed_4424_ = lean_unbox(v_usedLetOnly_4414_);
v_skipConstInApp_boxed_4425_ = lean_unbox(v_skipConstInApp_4415_);
v_skipInstances_boxed_4426_ = lean_unbox(v_skipInstances_4416_);
v_res_4427_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4412_, v_post_4413_, v_usedLetOnly_boxed_4424_, v_skipConstInApp_boxed_4425_, v_skipInstances_boxed_4426_, v_e_4417_, v_a_4418_, v___y_4419_, v___y_4420_, v___y_4421_, v___y_4422_);
lean_dec(v___y_4422_);
lean_dec_ref(v___y_4421_);
lean_dec(v___y_4420_);
lean_dec_ref(v___y_4419_);
lean_dec(v_a_4418_);
return v_res_4427_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__2___boxed(lean_object* v_pre_4428_, lean_object* v_post_4429_, lean_object* v_usedLetOnly_4430_, lean_object* v_skipConstInApp_4431_, lean_object* v_skipInstances_4432_, lean_object* v_sz_4433_, lean_object* v_i_4434_, lean_object* v_bs_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_, lean_object* v___y_4441_){
_start:
{
uint8_t v_usedLetOnly_boxed_4442_; uint8_t v_skipConstInApp_boxed_4443_; uint8_t v_skipInstances_boxed_4444_; size_t v_sz_boxed_4445_; size_t v_i_boxed_4446_; lean_object* v_res_4447_; 
v_usedLetOnly_boxed_4442_ = lean_unbox(v_usedLetOnly_4430_);
v_skipConstInApp_boxed_4443_ = lean_unbox(v_skipConstInApp_4431_);
v_skipInstances_boxed_4444_ = lean_unbox(v_skipInstances_4432_);
v_sz_boxed_4445_ = lean_unbox_usize(v_sz_4433_);
lean_dec(v_sz_4433_);
v_i_boxed_4446_ = lean_unbox_usize(v_i_4434_);
lean_dec(v_i_4434_);
v_res_4447_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__2(v_pre_4428_, v_post_4429_, v_usedLetOnly_boxed_4442_, v_skipConstInApp_boxed_4443_, v_skipInstances_boxed_4444_, v_sz_boxed_4445_, v_i_boxed_4446_, v_bs_4435_, v___y_4436_, v___y_4437_, v___y_4438_, v___y_4439_, v___y_4440_);
lean_dec(v___y_4440_);
lean_dec_ref(v___y_4439_);
lean_dec(v___y_4438_);
lean_dec_ref(v___y_4437_);
lean_dec(v___y_4436_);
return v_res_4447_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___boxed(lean_object* v_pre_4448_, lean_object* v_post_4449_, lean_object* v_usedLetOnly_4450_, lean_object* v_skipConstInApp_4451_, lean_object* v_skipInstances_4452_, lean_object* v_e_4453_, lean_object* v_a_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_){
_start:
{
uint8_t v_usedLetOnly_boxed_4460_; uint8_t v_skipConstInApp_boxed_4461_; uint8_t v_skipInstances_boxed_4462_; lean_object* v_res_4463_; 
v_usedLetOnly_boxed_4460_ = lean_unbox(v_usedLetOnly_4450_);
v_skipConstInApp_boxed_4461_ = lean_unbox(v_skipConstInApp_4451_);
v_skipInstances_boxed_4462_ = lean_unbox(v_skipInstances_4452_);
v_res_4463_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4448_, v_post_4449_, v_usedLetOnly_boxed_4460_, v_skipConstInApp_boxed_4461_, v_skipInstances_boxed_4462_, v_e_4453_, v_a_4454_, v___y_4455_, v___y_4456_, v___y_4457_, v___y_4458_);
lean_dec(v___y_4458_);
lean_dec_ref(v___y_4457_);
lean_dec(v___y_4456_);
lean_dec_ref(v___y_4455_);
lean_dec(v_a_4454_);
return v_res_4463_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___boxed(lean_object* v_pre_4464_, lean_object* v_post_4465_, lean_object* v_usedLetOnly_4466_, lean_object* v_skipConstInApp_4467_, lean_object* v_skipInstances_4468_, lean_object* v_fvars_4469_, lean_object* v_e_4470_, lean_object* v_a_4471_, lean_object* v___y_4472_, lean_object* v___y_4473_, lean_object* v___y_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_){
_start:
{
uint8_t v_usedLetOnly_boxed_4477_; uint8_t v_skipConstInApp_boxed_4478_; uint8_t v_skipInstances_boxed_4479_; lean_object* v_res_4480_; 
v_usedLetOnly_boxed_4477_ = lean_unbox(v_usedLetOnly_4466_);
v_skipConstInApp_boxed_4478_ = lean_unbox(v_skipConstInApp_4467_);
v_skipInstances_boxed_4479_ = lean_unbox(v_skipInstances_4468_);
v_res_4480_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5(v_pre_4464_, v_post_4465_, v_usedLetOnly_boxed_4477_, v_skipConstInApp_boxed_4478_, v_skipInstances_boxed_4479_, v_fvars_4469_, v_e_4470_, v_a_4471_, v___y_4472_, v___y_4473_, v___y_4474_, v___y_4475_);
lean_dec(v___y_4475_);
lean_dec_ref(v___y_4474_);
lean_dec(v___y_4473_);
lean_dec_ref(v___y_4472_);
lean_dec(v_a_4471_);
return v_res_4480_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___boxed(lean_object* v_pre_4481_, lean_object* v_post_4482_, lean_object* v_usedLetOnly_4483_, lean_object* v_skipConstInApp_4484_, lean_object* v_skipInstances_4485_, lean_object* v_fvars_4486_, lean_object* v_e_4487_, lean_object* v_a_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_, lean_object* v___y_4493_){
_start:
{
uint8_t v_usedLetOnly_boxed_4494_; uint8_t v_skipConstInApp_boxed_4495_; uint8_t v_skipInstances_boxed_4496_; lean_object* v_res_4497_; 
v_usedLetOnly_boxed_4494_ = lean_unbox(v_usedLetOnly_4483_);
v_skipConstInApp_boxed_4495_ = lean_unbox(v_skipConstInApp_4484_);
v_skipInstances_boxed_4496_ = lean_unbox(v_skipInstances_4485_);
v_res_4497_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6(v_pre_4481_, v_post_4482_, v_usedLetOnly_boxed_4494_, v_skipConstInApp_boxed_4495_, v_skipInstances_boxed_4496_, v_fvars_4486_, v_e_4487_, v_a_4488_, v___y_4489_, v___y_4490_, v___y_4491_, v___y_4492_);
lean_dec(v___y_4492_);
lean_dec_ref(v___y_4491_);
lean_dec(v___y_4490_);
lean_dec_ref(v___y_4489_);
lean_dec(v_a_4488_);
return v_res_4497_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___boxed(lean_object* v_pre_4498_, lean_object* v_post_4499_, lean_object* v_usedLetOnly_4500_, lean_object* v_skipConstInApp_4501_, lean_object* v_skipInstances_4502_, lean_object* v_fvars_4503_, lean_object* v_e_4504_, lean_object* v_a_4505_, lean_object* v___y_4506_, lean_object* v___y_4507_, lean_object* v___y_4508_, lean_object* v___y_4509_, lean_object* v___y_4510_){
_start:
{
uint8_t v_usedLetOnly_boxed_4511_; uint8_t v_skipConstInApp_boxed_4512_; uint8_t v_skipInstances_boxed_4513_; lean_object* v_res_4514_; 
v_usedLetOnly_boxed_4511_ = lean_unbox(v_usedLetOnly_4500_);
v_skipConstInApp_boxed_4512_ = lean_unbox(v_skipConstInApp_4501_);
v_skipInstances_boxed_4513_ = lean_unbox(v_skipInstances_4502_);
v_res_4514_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7(v_pre_4498_, v_post_4499_, v_usedLetOnly_boxed_4511_, v_skipConstInApp_boxed_4512_, v_skipInstances_boxed_4513_, v_fvars_4503_, v_e_4504_, v_a_4505_, v___y_4506_, v___y_4507_, v___y_4508_, v___y_4509_);
lean_dec(v___y_4509_);
lean_dec_ref(v___y_4508_);
lean_dec(v___y_4507_);
lean_dec_ref(v___y_4506_);
lean_dec(v_a_4505_);
return v_res_4514_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_upperBound_4515_, lean_object* v___x_4516_, lean_object* v_pre_4517_, lean_object* v_post_4518_, lean_object* v_usedLetOnly_4519_, lean_object* v_skipConstInApp_4520_, lean_object* v_skipInstances_4521_, lean_object* v_a_4522_, lean_object* v_b_4523_, lean_object* v___y_4524_, lean_object* v___y_4525_, lean_object* v___y_4526_, lean_object* v___y_4527_, lean_object* v___y_4528_, lean_object* v___y_4529_){
_start:
{
uint8_t v_usedLetOnly_boxed_4530_; uint8_t v_skipConstInApp_boxed_4531_; uint8_t v_skipInstances_boxed_4532_; lean_object* v_res_4533_; 
v_usedLetOnly_boxed_4530_ = lean_unbox(v_usedLetOnly_4519_);
v_skipConstInApp_boxed_4531_ = lean_unbox(v_skipConstInApp_4520_);
v_skipInstances_boxed_4532_ = lean_unbox(v_skipInstances_4521_);
v_res_4533_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg(v_upperBound_4515_, v___x_4516_, v_pre_4517_, v_post_4518_, v_usedLetOnly_boxed_4530_, v_skipConstInApp_boxed_4531_, v_skipInstances_boxed_4532_, v_a_4522_, v_b_4523_, v___y_4524_, v___y_4525_, v___y_4526_, v___y_4527_, v___y_4528_);
lean_dec(v___y_4528_);
lean_dec_ref(v___y_4527_);
lean_dec(v___y_4526_);
lean_dec_ref(v___y_4525_);
lean_dec(v___y_4524_);
lean_dec_ref(v___x_4516_);
lean_dec(v_upperBound_4515_);
return v_res_4533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__8___boxed(lean_object* v_skipInstances_4534_, lean_object* v_pre_4535_, lean_object* v_post_4536_, lean_object* v_usedLetOnly_4537_, lean_object* v_skipConstInApp_4538_, lean_object* v_x_4539_, lean_object* v_x_4540_, lean_object* v_x_4541_, lean_object* v___y_4542_, lean_object* v___y_4543_, lean_object* v___y_4544_, lean_object* v___y_4545_, lean_object* v___y_4546_, lean_object* v___y_4547_){
_start:
{
uint8_t v_skipInstances_boxed_4548_; uint8_t v_usedLetOnly_boxed_4549_; uint8_t v_skipConstInApp_boxed_4550_; lean_object* v_res_4551_; 
v_skipInstances_boxed_4548_ = lean_unbox(v_skipInstances_4534_);
v_usedLetOnly_boxed_4549_ = lean_unbox(v_usedLetOnly_4537_);
v_skipConstInApp_boxed_4550_ = lean_unbox(v_skipConstInApp_4538_);
v_res_4551_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__8(v_skipInstances_boxed_4548_, v_pre_4535_, v_post_4536_, v_usedLetOnly_boxed_4549_, v_skipConstInApp_boxed_4550_, v_x_4539_, v_x_4540_, v_x_4541_, v___y_4542_, v___y_4543_, v___y_4544_, v___y_4545_, v___y_4546_);
lean_dec(v___y_4546_);
lean_dec_ref(v___y_4545_);
lean_dec(v___y_4544_);
lean_dec_ref(v___y_4543_);
lean_dec(v___y_4542_);
return v_res_4551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(lean_object* v_input_4552_, lean_object* v_pre_4553_, lean_object* v_post_4554_, uint8_t v_usedLetOnly_4555_, uint8_t v_skipConstInApp_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_, lean_object* v___y_4559_, lean_object* v___y_4560_){
_start:
{
lean_object* v___x_4562_; lean_object* v___x_4563_; lean_object* v_a_4564_; uint8_t v___x_4565_; lean_object* v___x_4566_; 
v___x_4562_ = lean_obj_once(&l_Lean_Core_transform___redArg___closed__2, &l_Lean_Core_transform___redArg___closed__2_once, _init_l_Lean_Core_transform___redArg___closed__2);
v___x_4563_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0(lean_box(0), v___x_4562_, v___y_4557_, v___y_4558_, v___y_4559_, v___y_4560_);
v_a_4564_ = lean_ctor_get(v___x_4563_, 0);
lean_inc(v_a_4564_);
lean_dec_ref(v___x_4563_);
v___x_4565_ = 0;
v___x_4566_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4553_, v_post_4554_, v_usedLetOnly_4555_, v_skipConstInApp_4556_, v___x_4565_, v_input_4552_, v_a_4564_, v___y_4557_, v___y_4558_, v___y_4559_, v___y_4560_);
if (lean_obj_tag(v___x_4566_) == 0)
{
lean_object* v_a_4567_; lean_object* v___x_4568_; lean_object* v___x_4569_; lean_object* v___x_4571_; uint8_t v_isShared_4572_; uint8_t v_isSharedCheck_4576_; 
v_a_4567_ = lean_ctor_get(v___x_4566_, 0);
lean_inc(v_a_4567_);
lean_dec_ref_known(v___x_4566_, 1);
v___x_4568_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_4568_, 0, lean_box(0));
lean_closure_set(v___x_4568_, 1, lean_box(0));
lean_closure_set(v___x_4568_, 2, v_a_4564_);
v___x_4569_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0(lean_box(0), v___x_4568_, v___y_4557_, v___y_4558_, v___y_4559_, v___y_4560_);
v_isSharedCheck_4576_ = !lean_is_exclusive(v___x_4569_);
if (v_isSharedCheck_4576_ == 0)
{
lean_object* v_unused_4577_; 
v_unused_4577_ = lean_ctor_get(v___x_4569_, 0);
lean_dec(v_unused_4577_);
v___x_4571_ = v___x_4569_;
v_isShared_4572_ = v_isSharedCheck_4576_;
goto v_resetjp_4570_;
}
else
{
lean_dec(v___x_4569_);
v___x_4571_ = lean_box(0);
v_isShared_4572_ = v_isSharedCheck_4576_;
goto v_resetjp_4570_;
}
v_resetjp_4570_:
{
lean_object* v___x_4574_; 
if (v_isShared_4572_ == 0)
{
lean_ctor_set(v___x_4571_, 0, v_a_4567_);
v___x_4574_ = v___x_4571_;
goto v_reusejp_4573_;
}
else
{
lean_object* v_reuseFailAlloc_4575_; 
v_reuseFailAlloc_4575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4575_, 0, v_a_4567_);
v___x_4574_ = v_reuseFailAlloc_4575_;
goto v_reusejp_4573_;
}
v_reusejp_4573_:
{
return v___x_4574_;
}
}
}
else
{
lean_dec(v_a_4564_);
return v___x_4566_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___boxed(lean_object* v_input_4578_, lean_object* v_pre_4579_, lean_object* v_post_4580_, lean_object* v_usedLetOnly_4581_, lean_object* v_skipConstInApp_4582_, lean_object* v___y_4583_, lean_object* v___y_4584_, lean_object* v___y_4585_, lean_object* v___y_4586_, lean_object* v___y_4587_){
_start:
{
uint8_t v_usedLetOnly_boxed_4588_; uint8_t v_skipConstInApp_boxed_4589_; lean_object* v_res_4590_; 
v_usedLetOnly_boxed_4588_ = lean_unbox(v_usedLetOnly_4581_);
v_skipConstInApp_boxed_4589_ = lean_unbox(v_skipConstInApp_4582_);
v_res_4590_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(v_input_4578_, v_pre_4579_, v_post_4580_, v_usedLetOnly_boxed_4588_, v_skipConstInApp_boxed_4589_, v___y_4583_, v___y_4584_, v___y_4585_, v___y_4586_);
lean_dec(v___y_4586_);
lean_dec_ref(v___y_4585_);
lean_dec(v___y_4584_);
lean_dec_ref(v___y_4583_);
return v_res_4590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce(lean_object* v_e_4592_, uint8_t v_zetaDelta_4593_, uint8_t v_zetaHave_4594_, uint8_t v_beta_4595_, lean_object* v_a_4596_, lean_object* v_a_4597_, lean_object* v_a_4598_, lean_object* v_a_4599_){
_start:
{
lean_object* v_lctx_4601_; lean_object* v___x_4602_; lean_object* v___x_4603_; lean_object* v___x_4604_; lean_object* v___f_4605_; uint8_t v___x_4606_; 
v_lctx_4601_ = lean_ctor_get(v_a_4596_, 2);
lean_inc_ref(v_lctx_4601_);
v___x_4602_ = lean_local_ctx_num_indices(v_lctx_4601_);
v___x_4603_ = lean_box(v_zetaHave_4594_);
v___x_4604_ = lean_box(v_zetaDelta_4593_);
v___f_4605_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaReduce___lam__0___boxed), 9, 3);
lean_closure_set(v___f_4605_, 0, v___x_4603_);
lean_closure_set(v___f_4605_, 1, v___x_4602_);
lean_closure_set(v___f_4605_, 2, v___x_4604_);
v___x_4606_ = 1;
if (v_beta_4595_ == 0)
{
lean_object* v___f_4607_; lean_object* v___f_4608_; lean_object* v___x_4609_; 
v___f_4607_ = ((lean_object*)(l_Lean_Meta_zetaReduce___closed__0));
v___f_4608_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaReduce___lam__2___boxed), 7, 1);
lean_closure_set(v___f_4608_, 0, v___f_4605_);
v___x_4609_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(v_e_4592_, v___f_4608_, v___f_4607_, v___x_4606_, v_beta_4595_, v_a_4596_, v_a_4597_, v_a_4598_, v_a_4599_);
return v___x_4609_;
}
else
{
lean_object* v___f_4610_; lean_object* v___f_4611_; uint8_t v___x_4612_; lean_object* v___x_4613_; 
v___f_4610_ = ((lean_object*)(l_Lean_Meta_zetaReduce___closed__0));
v___f_4611_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaReduce___lam__4___boxed), 7, 1);
lean_closure_set(v___f_4611_, 0, v___f_4605_);
v___x_4612_ = 0;
v___x_4613_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(v_e_4592_, v___f_4611_, v___f_4610_, v___x_4606_, v___x_4612_, v_a_4596_, v_a_4597_, v_a_4598_, v_a_4599_);
return v___x_4613_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___boxed(lean_object* v_e_4614_, lean_object* v_zetaDelta_4615_, lean_object* v_zetaHave_4616_, lean_object* v_beta_4617_, lean_object* v_a_4618_, lean_object* v_a_4619_, lean_object* v_a_4620_, lean_object* v_a_4621_, lean_object* v_a_4622_){
_start:
{
uint8_t v_zetaDelta_boxed_4623_; uint8_t v_zetaHave_boxed_4624_; uint8_t v_beta_boxed_4625_; lean_object* v_res_4626_; 
v_zetaDelta_boxed_4623_ = lean_unbox(v_zetaDelta_4615_);
v_zetaHave_boxed_4624_ = lean_unbox(v_zetaHave_4616_);
v_beta_boxed_4625_ = lean_unbox(v_beta_4617_);
v_res_4626_ = l_Lean_Meta_zetaReduce(v_e_4614_, v_zetaDelta_boxed_4623_, v_zetaHave_boxed_4624_, v_beta_boxed_4625_, v_a_4618_, v_a_4619_, v_a_4620_, v_a_4621_);
lean_dec(v_a_4621_);
lean_dec_ref(v_a_4620_);
lean_dec(v_a_4619_);
lean_dec_ref(v_a_4618_);
return v_res_4626_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4(lean_object* v_upperBound_4627_, lean_object* v___x_4628_, lean_object* v_pre_4629_, lean_object* v_post_4630_, uint8_t v_usedLetOnly_4631_, uint8_t v_skipConstInApp_4632_, uint8_t v_skipInstances_4633_, lean_object* v___x_4634_, lean_object* v_inst_4635_, lean_object* v_R_4636_, lean_object* v_a_4637_, lean_object* v_b_4638_, lean_object* v_c_4639_, lean_object* v___y_4640_, lean_object* v___y_4641_, lean_object* v___y_4642_, lean_object* v___y_4643_, lean_object* v___y_4644_){
_start:
{
lean_object* v___x_4646_; 
v___x_4646_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg(v_upperBound_4627_, v___x_4628_, v_pre_4629_, v_post_4630_, v_usedLetOnly_4631_, v_skipConstInApp_4632_, v_skipInstances_4633_, v_a_4637_, v_b_4638_, v___y_4640_, v___y_4641_, v___y_4642_, v___y_4643_, v___y_4644_);
return v___x_4646_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___boxed(lean_object** _args){
lean_object* v_upperBound_4647_ = _args[0];
lean_object* v___x_4648_ = _args[1];
lean_object* v_pre_4649_ = _args[2];
lean_object* v_post_4650_ = _args[3];
lean_object* v_usedLetOnly_4651_ = _args[4];
lean_object* v_skipConstInApp_4652_ = _args[5];
lean_object* v_skipInstances_4653_ = _args[6];
lean_object* v___x_4654_ = _args[7];
lean_object* v_inst_4655_ = _args[8];
lean_object* v_R_4656_ = _args[9];
lean_object* v_a_4657_ = _args[10];
lean_object* v_b_4658_ = _args[11];
lean_object* v_c_4659_ = _args[12];
lean_object* v___y_4660_ = _args[13];
lean_object* v___y_4661_ = _args[14];
lean_object* v___y_4662_ = _args[15];
lean_object* v___y_4663_ = _args[16];
lean_object* v___y_4664_ = _args[17];
lean_object* v___y_4665_ = _args[18];
_start:
{
uint8_t v_usedLetOnly_boxed_4666_; uint8_t v_skipConstInApp_boxed_4667_; uint8_t v_skipInstances_boxed_4668_; lean_object* v_res_4669_; 
v_usedLetOnly_boxed_4666_ = lean_unbox(v_usedLetOnly_4651_);
v_skipConstInApp_boxed_4667_ = lean_unbox(v_skipConstInApp_4652_);
v_skipInstances_boxed_4668_ = lean_unbox(v_skipInstances_4653_);
v_res_4669_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4(v_upperBound_4647_, v___x_4648_, v_pre_4649_, v_post_4650_, v_usedLetOnly_boxed_4666_, v_skipConstInApp_boxed_4667_, v_skipInstances_boxed_4668_, v___x_4654_, v_inst_4655_, v_R_4656_, v_a_4657_, v_b_4658_, v_c_4659_, v___y_4660_, v___y_4661_, v___y_4662_, v___y_4663_, v___y_4664_);
lean_dec(v___y_4664_);
lean_dec_ref(v___y_4663_);
lean_dec(v___y_4662_);
lean_dec_ref(v___y_4661_);
lean_dec(v___y_4660_);
lean_dec(v___x_4654_);
lean_dec_ref(v___x_4648_);
lean_dec(v_upperBound_4647_);
return v_res_4669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6(lean_object* v_00_u03b1_4670_, lean_object* v_name_4671_, uint8_t v_bi_4672_, lean_object* v_type_4673_, lean_object* v_k_4674_, uint8_t v_kind_4675_, lean_object* v___y_4676_, lean_object* v___y_4677_, lean_object* v___y_4678_, lean_object* v___y_4679_, lean_object* v___y_4680_){
_start:
{
lean_object* v___x_4682_; 
v___x_4682_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_name_4671_, v_bi_4672_, v_type_4673_, v_k_4674_, v_kind_4675_, v___y_4676_, v___y_4677_, v___y_4678_, v___y_4679_, v___y_4680_);
return v___x_4682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___boxed(lean_object* v_00_u03b1_4683_, lean_object* v_name_4684_, lean_object* v_bi_4685_, lean_object* v_type_4686_, lean_object* v_k_4687_, lean_object* v_kind_4688_, lean_object* v___y_4689_, lean_object* v___y_4690_, lean_object* v___y_4691_, lean_object* v___y_4692_, lean_object* v___y_4693_, lean_object* v___y_4694_){
_start:
{
uint8_t v_bi_boxed_4695_; uint8_t v_kind_boxed_4696_; lean_object* v_res_4697_; 
v_bi_boxed_4695_ = lean_unbox(v_bi_4685_);
v_kind_boxed_4696_ = lean_unbox(v_kind_4688_);
v_res_4697_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6(v_00_u03b1_4683_, v_name_4684_, v_bi_boxed_4695_, v_type_4686_, v_k_4687_, v_kind_boxed_4696_, v___y_4689_, v___y_4690_, v___y_4691_, v___y_4692_, v___y_4693_);
lean_dec(v___y_4693_);
lean_dec_ref(v___y_4692_);
lean_dec(v___y_4691_);
lean_dec_ref(v___y_4690_);
lean_dec(v___y_4689_);
return v_res_4697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9(lean_object* v_00_u03b1_4698_, lean_object* v_name_4699_, lean_object* v_type_4700_, lean_object* v_val_4701_, lean_object* v_k_4702_, uint8_t v_nondep_4703_, uint8_t v_kind_4704_, lean_object* v___y_4705_, lean_object* v___y_4706_, lean_object* v___y_4707_, lean_object* v___y_4708_, lean_object* v___y_4709_){
_start:
{
lean_object* v___x_4711_; 
v___x_4711_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg(v_name_4699_, v_type_4700_, v_val_4701_, v_k_4702_, v_nondep_4703_, v_kind_4704_, v___y_4705_, v___y_4706_, v___y_4707_, v___y_4708_, v___y_4709_);
return v___x_4711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___boxed(lean_object* v_00_u03b1_4712_, lean_object* v_name_4713_, lean_object* v_type_4714_, lean_object* v_val_4715_, lean_object* v_k_4716_, lean_object* v_nondep_4717_, lean_object* v_kind_4718_, lean_object* v___y_4719_, lean_object* v___y_4720_, lean_object* v___y_4721_, lean_object* v___y_4722_, lean_object* v___y_4723_, lean_object* v___y_4724_){
_start:
{
uint8_t v_nondep_boxed_4725_; uint8_t v_kind_boxed_4726_; lean_object* v_res_4727_; 
v_nondep_boxed_4725_ = lean_unbox(v_nondep_4717_);
v_kind_boxed_4726_ = lean_unbox(v_kind_4718_);
v_res_4727_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9(v_00_u03b1_4712_, v_name_4713_, v_type_4714_, v_val_4715_, v_k_4716_, v_nondep_boxed_4725_, v_kind_boxed_4726_, v___y_4719_, v___y_4720_, v___y_4721_, v___y_4722_, v___y_4723_);
lean_dec(v___y_4723_);
lean_dec_ref(v___y_4722_);
lean_dec(v___y_4721_);
lean_dec_ref(v___y_4720_);
lean_dec(v___y_4719_);
return v_res_4727_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12(lean_object* v_00_u03b1_4728_, lean_object* v_ref_4729_, lean_object* v___y_4730_, lean_object* v___y_4731_, lean_object* v___y_4732_, lean_object* v___y_4733_){
_start:
{
lean_object* v___x_4735_; 
v___x_4735_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg(v_ref_4729_);
return v___x_4735_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___boxed(lean_object* v_00_u03b1_4736_, lean_object* v_ref_4737_, lean_object* v___y_4738_, lean_object* v___y_4739_, lean_object* v___y_4740_, lean_object* v___y_4741_, lean_object* v___y_4742_){
_start:
{
lean_object* v_res_4743_; 
v_res_4743_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12(v_00_u03b1_4736_, v_ref_4737_, v___y_4738_, v___y_4739_, v___y_4740_, v___y_4741_);
lean_dec(v___y_4741_);
lean_dec_ref(v___y_4740_);
lean_dec(v___y_4739_);
lean_dec_ref(v___y_4738_);
return v_res_4743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9(lean_object* v_00_u03b1_4744_, lean_object* v_x_4745_, lean_object* v___y_4746_, lean_object* v___y_4747_, lean_object* v___y_4748_, lean_object* v___y_4749_, lean_object* v___y_4750_){
_start:
{
lean_object* v___x_4752_; 
v___x_4752_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg(v_x_4745_, v___y_4746_, v___y_4747_, v___y_4748_, v___y_4749_, v___y_4750_);
return v___x_4752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___boxed(lean_object* v_00_u03b1_4753_, lean_object* v_x_4754_, lean_object* v___y_4755_, lean_object* v___y_4756_, lean_object* v___y_4757_, lean_object* v___y_4758_, lean_object* v___y_4759_, lean_object* v___y_4760_){
_start:
{
lean_object* v_res_4761_; 
v_res_4761_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9(v_00_u03b1_4753_, v_x_4754_, v___y_4755_, v___y_4756_, v___y_4757_, v___y_4758_, v___y_4759_);
lean_dec(v___y_4759_);
lean_dec_ref(v___y_4758_);
lean_dec(v___y_4757_);
lean_dec_ref(v___y_4756_);
lean_dec(v___y_4755_);
return v_res_4761_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0_spec__0(lean_object* v_a_4762_, lean_object* v_as_4763_, size_t v_i_4764_, size_t v_stop_4765_){
_start:
{
uint8_t v___x_4766_; 
v___x_4766_ = lean_usize_dec_eq(v_i_4764_, v_stop_4765_);
if (v___x_4766_ == 0)
{
lean_object* v___x_4767_; uint8_t v___x_4768_; 
v___x_4767_ = lean_array_uget_borrowed(v_as_4763_, v_i_4764_);
v___x_4768_ = l_Lean_instBEqFVarId_beq(v_a_4762_, v___x_4767_);
if (v___x_4768_ == 0)
{
size_t v___x_4769_; size_t v___x_4770_; 
v___x_4769_ = ((size_t)1ULL);
v___x_4770_ = lean_usize_add(v_i_4764_, v___x_4769_);
v_i_4764_ = v___x_4770_;
goto _start;
}
else
{
return v___x_4768_;
}
}
else
{
uint8_t v___x_4772_; 
v___x_4772_ = 0;
return v___x_4772_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0_spec__0___boxed(lean_object* v_a_4773_, lean_object* v_as_4774_, lean_object* v_i_4775_, lean_object* v_stop_4776_){
_start:
{
size_t v_i_boxed_4777_; size_t v_stop_boxed_4778_; uint8_t v_res_4779_; lean_object* v_r_4780_; 
v_i_boxed_4777_ = lean_unbox_usize(v_i_4775_);
lean_dec(v_i_4775_);
v_stop_boxed_4778_ = lean_unbox_usize(v_stop_4776_);
lean_dec(v_stop_4776_);
v_res_4779_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0_spec__0(v_a_4773_, v_as_4774_, v_i_boxed_4777_, v_stop_boxed_4778_);
lean_dec_ref(v_as_4774_);
lean_dec(v_a_4773_);
v_r_4780_ = lean_box(v_res_4779_);
return v_r_4780_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0(lean_object* v_as_4781_, lean_object* v_a_4782_){
_start:
{
lean_object* v___x_4783_; lean_object* v___x_4784_; uint8_t v___x_4785_; 
v___x_4783_ = lean_unsigned_to_nat(0u);
v___x_4784_ = lean_array_get_size(v_as_4781_);
v___x_4785_ = lean_nat_dec_lt(v___x_4783_, v___x_4784_);
if (v___x_4785_ == 0)
{
return v___x_4785_;
}
else
{
if (v___x_4785_ == 0)
{
return v___x_4785_;
}
else
{
size_t v___x_4786_; size_t v___x_4787_; uint8_t v___x_4788_; 
v___x_4786_ = ((size_t)0ULL);
v___x_4787_ = lean_usize_of_nat(v___x_4784_);
v___x_4788_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0_spec__0(v_a_4782_, v_as_4781_, v___x_4786_, v___x_4787_);
return v___x_4788_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0___boxed(lean_object* v_as_4789_, lean_object* v_a_4790_){
_start:
{
uint8_t v_res_4791_; lean_object* v_r_4792_; 
v_res_4791_ = l_Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0(v_as_4789_, v_a_4790_);
lean_dec(v_a_4790_);
lean_dec_ref(v_as_4789_);
v_r_4792_ = lean_box(v_res_4791_);
return v_r_4792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaFVars___lam__1(lean_object* v_fvars_4793_, lean_object* v_e_4794_, lean_object* v___y_4795_, lean_object* v___y_4796_, lean_object* v___y_4797_, lean_object* v___y_4798_){
_start:
{
lean_object* v___x_4803_; 
v___x_4803_ = l_Lean_Expr_getAppFn(v_e_4794_);
if (lean_obj_tag(v___x_4803_) == 1)
{
lean_object* v_fvarId_4804_; uint8_t v___x_4805_; 
v_fvarId_4804_ = lean_ctor_get(v___x_4803_, 0);
lean_inc(v_fvarId_4804_);
lean_dec_ref_known(v___x_4803_, 1);
v___x_4805_ = l_Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0(v_fvars_4793_, v_fvarId_4804_);
if (v___x_4805_ == 0)
{
lean_dec(v_fvarId_4804_);
lean_dec_ref(v_e_4794_);
goto v___jp_4800_;
}
else
{
uint8_t v___x_4806_; lean_object* v___x_4807_; 
v___x_4806_ = 0;
v___x_4807_ = l_Lean_FVarId_getValue_x3f___redArg(v_fvarId_4804_, v___x_4806_, v___y_4795_, v___y_4797_, v___y_4798_);
if (lean_obj_tag(v___x_4807_) == 0)
{
lean_object* v_a_4808_; 
v_a_4808_ = lean_ctor_get(v___x_4807_, 0);
lean_inc(v_a_4808_);
lean_dec_ref_known(v___x_4807_, 1);
if (lean_obj_tag(v_a_4808_) == 1)
{
lean_object* v_val_4809_; lean_object* v___x_4811_; uint8_t v_isShared_4812_; uint8_t v_isSharedCheck_4832_; 
v_val_4809_ = lean_ctor_get(v_a_4808_, 0);
v_isSharedCheck_4832_ = !lean_is_exclusive(v_a_4808_);
if (v_isSharedCheck_4832_ == 0)
{
v___x_4811_ = v_a_4808_;
v_isShared_4812_ = v_isSharedCheck_4832_;
goto v_resetjp_4810_;
}
else
{
lean_inc(v_val_4809_);
lean_dec(v_a_4808_);
v___x_4811_ = lean_box(0);
v_isShared_4812_ = v_isSharedCheck_4832_;
goto v_resetjp_4810_;
}
v_resetjp_4810_:
{
lean_object* v___x_4813_; lean_object* v_a_4814_; lean_object* v___x_4816_; uint8_t v_isShared_4817_; uint8_t v_isSharedCheck_4831_; 
v___x_4813_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(v_val_4809_, v___y_4796_);
v_a_4814_ = lean_ctor_get(v___x_4813_, 0);
v_isSharedCheck_4831_ = !lean_is_exclusive(v___x_4813_);
if (v_isSharedCheck_4831_ == 0)
{
v___x_4816_ = v___x_4813_;
v_isShared_4817_ = v_isSharedCheck_4831_;
goto v_resetjp_4815_;
}
else
{
lean_inc(v_a_4814_);
lean_dec(v___x_4813_);
v___x_4816_ = lean_box(0);
v_isShared_4817_ = v_isSharedCheck_4831_;
goto v_resetjp_4815_;
}
v_resetjp_4815_:
{
lean_object* v_dummy_4818_; lean_object* v_nargs_4819_; lean_object* v___x_4820_; lean_object* v___x_4821_; lean_object* v___x_4822_; lean_object* v___x_4823_; lean_object* v___x_4824_; lean_object* v___x_4826_; 
v_dummy_4818_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_4819_ = l_Lean_Expr_getAppNumArgs(v_e_4794_);
lean_inc(v_nargs_4819_);
v___x_4820_ = lean_mk_array(v_nargs_4819_, v_dummy_4818_);
v___x_4821_ = lean_unsigned_to_nat(1u);
v___x_4822_ = lean_nat_sub(v_nargs_4819_, v___x_4821_);
lean_dec(v_nargs_4819_);
v___x_4823_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_4794_, v___x_4820_, v___x_4822_);
v___x_4824_ = l_Lean_Expr_beta(v_a_4814_, v___x_4823_);
if (v_isShared_4812_ == 0)
{
lean_ctor_set(v___x_4811_, 0, v___x_4824_);
v___x_4826_ = v___x_4811_;
goto v_reusejp_4825_;
}
else
{
lean_object* v_reuseFailAlloc_4830_; 
v_reuseFailAlloc_4830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4830_, 0, v___x_4824_);
v___x_4826_ = v_reuseFailAlloc_4830_;
goto v_reusejp_4825_;
}
v_reusejp_4825_:
{
lean_object* v___x_4828_; 
if (v_isShared_4817_ == 0)
{
lean_ctor_set(v___x_4816_, 0, v___x_4826_);
v___x_4828_ = v___x_4816_;
goto v_reusejp_4827_;
}
else
{
lean_object* v_reuseFailAlloc_4829_; 
v_reuseFailAlloc_4829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4829_, 0, v___x_4826_);
v___x_4828_ = v_reuseFailAlloc_4829_;
goto v_reusejp_4827_;
}
v_reusejp_4827_:
{
return v___x_4828_;
}
}
}
}
}
else
{
lean_dec(v_a_4808_);
lean_dec_ref(v_e_4794_);
goto v___jp_4800_;
}
}
else
{
lean_object* v_a_4833_; lean_object* v___x_4835_; uint8_t v_isShared_4836_; uint8_t v_isSharedCheck_4840_; 
lean_dec_ref(v_e_4794_);
v_a_4833_ = lean_ctor_get(v___x_4807_, 0);
v_isSharedCheck_4840_ = !lean_is_exclusive(v___x_4807_);
if (v_isSharedCheck_4840_ == 0)
{
v___x_4835_ = v___x_4807_;
v_isShared_4836_ = v_isSharedCheck_4840_;
goto v_resetjp_4834_;
}
else
{
lean_inc(v_a_4833_);
lean_dec(v___x_4807_);
v___x_4835_ = lean_box(0);
v_isShared_4836_ = v_isSharedCheck_4840_;
goto v_resetjp_4834_;
}
v_resetjp_4834_:
{
lean_object* v___x_4838_; 
if (v_isShared_4836_ == 0)
{
v___x_4838_ = v___x_4835_;
goto v_reusejp_4837_;
}
else
{
lean_object* v_reuseFailAlloc_4839_; 
v_reuseFailAlloc_4839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4839_, 0, v_a_4833_);
v___x_4838_ = v_reuseFailAlloc_4839_;
goto v_reusejp_4837_;
}
v_reusejp_4837_:
{
return v___x_4838_;
}
}
}
}
}
else
{
lean_object* v___x_4841_; lean_object* v___x_4842_; 
lean_dec_ref(v___x_4803_);
lean_dec_ref(v_e_4794_);
v___x_4841_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_4842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4842_, 0, v___x_4841_);
return v___x_4842_;
}
v___jp_4800_:
{
lean_object* v___x_4801_; lean_object* v___x_4802_; 
v___x_4801_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_4802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4802_, 0, v___x_4801_);
return v___x_4802_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaFVars___lam__1___boxed(lean_object* v_fvars_4843_, lean_object* v_e_4844_, lean_object* v___y_4845_, lean_object* v___y_4846_, lean_object* v___y_4847_, lean_object* v___y_4848_, lean_object* v___y_4849_){
_start:
{
lean_object* v_res_4850_; 
v_res_4850_ = l_Lean_Meta_zetaDeltaFVars___lam__1(v_fvars_4843_, v_e_4844_, v___y_4845_, v___y_4846_, v___y_4847_, v___y_4848_);
lean_dec(v___y_4848_);
lean_dec_ref(v___y_4847_);
lean_dec(v___y_4846_);
lean_dec_ref(v___y_4845_);
lean_dec_ref(v_fvars_4843_);
return v_res_4850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaFVars(lean_object* v_e_4851_, lean_object* v_fvars_4852_, lean_object* v_a_4853_, lean_object* v_a_4854_, lean_object* v_a_4855_, lean_object* v_a_4856_){
_start:
{
lean_object* v___f_4858_; lean_object* v_pre_4859_; uint8_t v___x_4860_; lean_object* v___x_4861_; 
v___f_4858_ = ((lean_object*)(l_Lean_Meta_zetaReduce___closed__0));
v_pre_4859_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaDeltaFVars___lam__1___boxed), 7, 1);
lean_closure_set(v_pre_4859_, 0, v_fvars_4852_);
v___x_4860_ = 0;
v___x_4861_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(v_e_4851_, v_pre_4859_, v___f_4858_, v___x_4860_, v___x_4860_, v_a_4853_, v_a_4854_, v_a_4855_, v_a_4856_);
return v___x_4861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaFVars___boxed(lean_object* v_e_4862_, lean_object* v_fvars_4863_, lean_object* v_a_4864_, lean_object* v_a_4865_, lean_object* v_a_4866_, lean_object* v_a_4867_, lean_object* v_a_4868_){
_start:
{
lean_object* v_res_4869_; 
v_res_4869_ = l_Lean_Meta_zetaDeltaFVars(v_e_4862_, v_fvars_4863_, v_a_4864_, v_a_4865_, v_a_4866_, v_a_4867_);
lean_dec(v_a_4867_);
lean_dec_ref(v_a_4866_);
lean_dec(v_a_4865_);
lean_dec_ref(v_a_4864_);
return v_res_4869_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_4870_; 
v___x_4870_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4870_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_4871_; lean_object* v___x_4872_; 
v___x_4871_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__0, &l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__0);
v___x_4872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4872_, 0, v___x_4871_);
return v___x_4872_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_4873_; lean_object* v___x_4874_; 
v___x_4873_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__1, &l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__1);
v___x_4874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4874_, 0, v___x_4873_);
lean_ctor_set(v___x_4874_, 1, v___x_4873_);
return v___x_4874_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(lean_object* v_env_4875_, lean_object* v___y_4876_){
_start:
{
lean_object* v___x_4878_; lean_object* v_nextMacroScope_4879_; lean_object* v_ngen_4880_; lean_object* v_auxDeclNGen_4881_; lean_object* v_traceState_4882_; lean_object* v_messages_4883_; lean_object* v_infoState_4884_; lean_object* v_snapshotTasks_4885_; lean_object* v___x_4887_; uint8_t v_isShared_4888_; uint8_t v_isSharedCheck_4896_; 
v___x_4878_ = lean_st_ref_take(v___y_4876_);
v_nextMacroScope_4879_ = lean_ctor_get(v___x_4878_, 1);
v_ngen_4880_ = lean_ctor_get(v___x_4878_, 2);
v_auxDeclNGen_4881_ = lean_ctor_get(v___x_4878_, 3);
v_traceState_4882_ = lean_ctor_get(v___x_4878_, 4);
v_messages_4883_ = lean_ctor_get(v___x_4878_, 6);
v_infoState_4884_ = lean_ctor_get(v___x_4878_, 7);
v_snapshotTasks_4885_ = lean_ctor_get(v___x_4878_, 8);
v_isSharedCheck_4896_ = !lean_is_exclusive(v___x_4878_);
if (v_isSharedCheck_4896_ == 0)
{
lean_object* v_unused_4897_; lean_object* v_unused_4898_; 
v_unused_4897_ = lean_ctor_get(v___x_4878_, 5);
lean_dec(v_unused_4897_);
v_unused_4898_ = lean_ctor_get(v___x_4878_, 0);
lean_dec(v_unused_4898_);
v___x_4887_ = v___x_4878_;
v_isShared_4888_ = v_isSharedCheck_4896_;
goto v_resetjp_4886_;
}
else
{
lean_inc(v_snapshotTasks_4885_);
lean_inc(v_infoState_4884_);
lean_inc(v_messages_4883_);
lean_inc(v_traceState_4882_);
lean_inc(v_auxDeclNGen_4881_);
lean_inc(v_ngen_4880_);
lean_inc(v_nextMacroScope_4879_);
lean_dec(v___x_4878_);
v___x_4887_ = lean_box(0);
v_isShared_4888_ = v_isSharedCheck_4896_;
goto v_resetjp_4886_;
}
v_resetjp_4886_:
{
lean_object* v___x_4889_; lean_object* v___x_4891_; 
v___x_4889_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2, &l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2);
if (v_isShared_4888_ == 0)
{
lean_ctor_set(v___x_4887_, 5, v___x_4889_);
lean_ctor_set(v___x_4887_, 0, v_env_4875_);
v___x_4891_ = v___x_4887_;
goto v_reusejp_4890_;
}
else
{
lean_object* v_reuseFailAlloc_4895_; 
v_reuseFailAlloc_4895_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4895_, 0, v_env_4875_);
lean_ctor_set(v_reuseFailAlloc_4895_, 1, v_nextMacroScope_4879_);
lean_ctor_set(v_reuseFailAlloc_4895_, 2, v_ngen_4880_);
lean_ctor_set(v_reuseFailAlloc_4895_, 3, v_auxDeclNGen_4881_);
lean_ctor_set(v_reuseFailAlloc_4895_, 4, v_traceState_4882_);
lean_ctor_set(v_reuseFailAlloc_4895_, 5, v___x_4889_);
lean_ctor_set(v_reuseFailAlloc_4895_, 6, v_messages_4883_);
lean_ctor_set(v_reuseFailAlloc_4895_, 7, v_infoState_4884_);
lean_ctor_set(v_reuseFailAlloc_4895_, 8, v_snapshotTasks_4885_);
v___x_4891_ = v_reuseFailAlloc_4895_;
goto v_reusejp_4890_;
}
v_reusejp_4890_:
{
lean_object* v___x_4892_; lean_object* v___x_4893_; lean_object* v___x_4894_; 
v___x_4892_ = lean_st_ref_put(v___y_4876_, v___x_4891_);
v___x_4893_ = lean_box(0);
v___x_4894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4894_, 0, v___x_4893_);
return v___x_4894_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___boxed(lean_object* v_env_4899_, lean_object* v___y_4900_, lean_object* v___y_4901_){
_start:
{
lean_object* v_res_4902_; 
v_res_4902_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_4899_, v___y_4900_);
lean_dec(v___y_4900_);
return v_res_4902_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0(lean_object* v_env_4903_, lean_object* v___y_4904_, lean_object* v___y_4905_){
_start:
{
lean_object* v___x_4907_; 
v___x_4907_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_4903_, v___y_4905_);
return v___x_4907_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___boxed(lean_object* v_env_4908_, lean_object* v___y_4909_, lean_object* v___y_4910_, lean_object* v___y_4911_){
_start:
{
lean_object* v_res_4912_; 
v_res_4912_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0(v_env_4908_, v___y_4909_, v___y_4910_);
lean_dec(v___y_4910_);
lean_dec_ref(v___y_4909_);
return v_res_4912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___lam__1(lean_object* v_env_4913_, lean_object* v___x_4914_, uint8_t v___x_4915_, lean_object* v_e_4916_, lean_object* v___y_4917_, lean_object* v___y_4918_){
_start:
{
if (lean_obj_tag(v_e_4916_) == 4)
{
lean_object* v_declName_4920_; lean_object* v_us_4921_; uint8_t v___x_4922_; uint8_t v___x_4923_; 
v_declName_4920_ = lean_ctor_get(v_e_4916_, 0);
v_us_4921_ = lean_ctor_get(v_e_4916_, 1);
v___x_4922_ = 1;
lean_inc(v_declName_4920_);
v___x_4923_ = l_Lean_Environment_contains(v_env_4913_, v_declName_4920_, v___x_4922_);
if (v___x_4923_ == 0)
{
lean_object* v___x_4924_; 
lean_inc(v_declName_4920_);
v___x_4924_ = l_Lean_Environment_find_x3f(v___x_4914_, v_declName_4920_, v___x_4915_);
if (lean_obj_tag(v___x_4924_) == 1)
{
lean_object* v_val_4925_; lean_object* v___x_4927_; uint8_t v_isShared_4928_; uint8_t v_isSharedCheck_4954_; 
v_val_4925_ = lean_ctor_get(v___x_4924_, 0);
v_isSharedCheck_4954_ = !lean_is_exclusive(v___x_4924_);
if (v_isSharedCheck_4954_ == 0)
{
v___x_4927_ = v___x_4924_;
v_isShared_4928_ = v_isSharedCheck_4954_;
goto v_resetjp_4926_;
}
else
{
lean_inc(v_val_4925_);
lean_dec(v___x_4924_);
v___x_4927_ = lean_box(0);
v_isShared_4928_ = v_isSharedCheck_4954_;
goto v_resetjp_4926_;
}
v_resetjp_4926_:
{
uint8_t v___x_4929_; 
v___x_4929_ = l_Lean_ConstantInfo_hasValue(v_val_4925_, v___x_4922_);
if (v___x_4929_ == 0)
{
lean_object* v___x_4931_; 
lean_dec(v_val_4925_);
if (v_isShared_4928_ == 0)
{
lean_ctor_set_tag(v___x_4927_, 0);
lean_ctor_set(v___x_4927_, 0, v_e_4916_);
v___x_4931_ = v___x_4927_;
goto v_reusejp_4930_;
}
else
{
lean_object* v_reuseFailAlloc_4933_; 
v_reuseFailAlloc_4933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4933_, 0, v_e_4916_);
v___x_4931_ = v_reuseFailAlloc_4933_;
goto v_reusejp_4930_;
}
v_reusejp_4930_:
{
lean_object* v___x_4932_; 
v___x_4932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4932_, 0, v___x_4931_);
return v___x_4932_;
}
}
else
{
lean_object* v___x_4934_; 
lean_inc(v_us_4921_);
lean_dec_ref_known(v_e_4916_, 2);
v___x_4934_ = l_Lean_Core_instantiateValueLevelParams(v_val_4925_, v_us_4921_, v___x_4922_, v___y_4917_, v___y_4918_);
lean_dec(v_val_4925_);
if (lean_obj_tag(v___x_4934_) == 0)
{
lean_object* v_a_4935_; lean_object* v___x_4937_; uint8_t v_isShared_4938_; uint8_t v_isSharedCheck_4945_; 
v_a_4935_ = lean_ctor_get(v___x_4934_, 0);
v_isSharedCheck_4945_ = !lean_is_exclusive(v___x_4934_);
if (v_isSharedCheck_4945_ == 0)
{
v___x_4937_ = v___x_4934_;
v_isShared_4938_ = v_isSharedCheck_4945_;
goto v_resetjp_4936_;
}
else
{
lean_inc(v_a_4935_);
lean_dec(v___x_4934_);
v___x_4937_ = lean_box(0);
v_isShared_4938_ = v_isSharedCheck_4945_;
goto v_resetjp_4936_;
}
v_resetjp_4936_:
{
lean_object* v___x_4940_; 
if (v_isShared_4928_ == 0)
{
lean_ctor_set(v___x_4927_, 0, v_a_4935_);
v___x_4940_ = v___x_4927_;
goto v_reusejp_4939_;
}
else
{
lean_object* v_reuseFailAlloc_4944_; 
v_reuseFailAlloc_4944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4944_, 0, v_a_4935_);
v___x_4940_ = v_reuseFailAlloc_4944_;
goto v_reusejp_4939_;
}
v_reusejp_4939_:
{
lean_object* v___x_4942_; 
if (v_isShared_4938_ == 0)
{
lean_ctor_set(v___x_4937_, 0, v___x_4940_);
v___x_4942_ = v___x_4937_;
goto v_reusejp_4941_;
}
else
{
lean_object* v_reuseFailAlloc_4943_; 
v_reuseFailAlloc_4943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4943_, 0, v___x_4940_);
v___x_4942_ = v_reuseFailAlloc_4943_;
goto v_reusejp_4941_;
}
v_reusejp_4941_:
{
return v___x_4942_;
}
}
}
}
else
{
lean_object* v_a_4946_; lean_object* v___x_4948_; uint8_t v_isShared_4949_; uint8_t v_isSharedCheck_4953_; 
lean_del_object(v___x_4927_);
v_a_4946_ = lean_ctor_get(v___x_4934_, 0);
v_isSharedCheck_4953_ = !lean_is_exclusive(v___x_4934_);
if (v_isSharedCheck_4953_ == 0)
{
v___x_4948_ = v___x_4934_;
v_isShared_4949_ = v_isSharedCheck_4953_;
goto v_resetjp_4947_;
}
else
{
lean_inc(v_a_4946_);
lean_dec(v___x_4934_);
v___x_4948_ = lean_box(0);
v_isShared_4949_ = v_isSharedCheck_4953_;
goto v_resetjp_4947_;
}
v_resetjp_4947_:
{
lean_object* v___x_4951_; 
if (v_isShared_4949_ == 0)
{
v___x_4951_ = v___x_4948_;
goto v_reusejp_4950_;
}
else
{
lean_object* v_reuseFailAlloc_4952_; 
v_reuseFailAlloc_4952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4952_, 0, v_a_4946_);
v___x_4951_ = v_reuseFailAlloc_4952_;
goto v_reusejp_4950_;
}
v_reusejp_4950_:
{
return v___x_4951_;
}
}
}
}
}
}
else
{
lean_object* v___x_4955_; lean_object* v___x_4956_; 
lean_dec(v___x_4924_);
v___x_4955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4955_, 0, v_e_4916_);
v___x_4956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4956_, 0, v___x_4955_);
return v___x_4956_;
}
}
else
{
lean_object* v___x_4957_; lean_object* v___x_4958_; 
lean_dec_ref(v___x_4914_);
v___x_4957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4957_, 0, v_e_4916_);
v___x_4958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4958_, 0, v___x_4957_);
return v___x_4958_;
}
}
else
{
lean_object* v___x_4959_; lean_object* v___x_4960_; 
lean_dec_ref(v_e_4916_);
lean_dec_ref(v___x_4914_);
lean_dec_ref(v_env_4913_);
v___x_4959_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_4960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4960_, 0, v___x_4959_);
return v___x_4960_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___lam__1___boxed(lean_object* v_env_4961_, lean_object* v___x_4962_, lean_object* v___x_4963_, lean_object* v_e_4964_, lean_object* v___y_4965_, lean_object* v___y_4966_, lean_object* v___y_4967_){
_start:
{
uint8_t v___x_1992__boxed_4968_; lean_object* v_res_4969_; 
v___x_1992__boxed_4968_ = lean_unbox(v___x_4963_);
v_res_4969_ = l_Lean_Meta_unfoldDeclsFrom___lam__1(v_env_4961_, v___x_4962_, v___x_1992__boxed_4968_, v_e_4964_, v___y_4965_, v___y_4966_);
lean_dec(v___y_4966_);
lean_dec_ref(v___y_4965_);
return v_res_4969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___lam__0(lean_object* v_biggerEnv_4970_, lean_object* v_e_4971_, lean_object* v___f_4972_, lean_object* v___y_4973_, lean_object* v___y_4974_){
_start:
{
lean_object* v___x_4976_; uint8_t v___x_4977_; lean_object* v___x_4978_; lean_object* v___x_4979_; lean_object* v_env_4980_; lean_object* v___x_4981_; lean_object* v___f_4982_; lean_object* v___x_4983_; 
v___x_4976_ = lean_st_ref_get(v___y_4974_);
v___x_4977_ = 0;
v___x_4978_ = l_Lean_Environment_setExporting(v_biggerEnv_4970_, v___x_4977_);
lean_inc_ref(v___x_4978_);
v___x_4979_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v___x_4978_, v___y_4974_);
lean_dec_ref(v___x_4979_);
v_env_4980_ = lean_ctor_get(v___x_4976_, 0);
lean_inc_ref(v_env_4980_);
lean_dec(v___x_4976_);
v___x_4981_ = lean_box(v___x_4977_);
v___f_4982_ = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDeclsFrom___lam__1___boxed), 7, 3);
lean_closure_set(v___f_4982_, 0, v_env_4980_);
lean_closure_set(v___f_4982_, 1, v___x_4978_);
lean_closure_set(v___f_4982_, 2, v___x_4981_);
v___x_4983_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_4971_, v___f_4982_, v___f_4972_, v___y_4973_, v___y_4974_);
return v___x_4983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___lam__0___boxed(lean_object* v_biggerEnv_4984_, lean_object* v_e_4985_, lean_object* v___f_4986_, lean_object* v___y_4987_, lean_object* v___y_4988_, lean_object* v___y_4989_){
_start:
{
lean_object* v_res_4990_; 
v_res_4990_ = l_Lean_Meta_unfoldDeclsFrom___lam__0(v_biggerEnv_4984_, v_e_4985_, v___f_4986_, v___y_4987_, v___y_4988_);
lean_dec(v___y_4988_);
lean_dec_ref(v___y_4987_);
return v_res_4990_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg(lean_object* v_env_4991_, lean_object* v_x_4992_, lean_object* v___y_4993_, lean_object* v___y_4994_){
_start:
{
lean_object* v___x_4996_; lean_object* v_env_4997_; lean_object* v_a_4999_; lean_object* v___x_5009_; lean_object* v___x_5010_; 
v___x_4996_ = lean_st_ref_get(v___y_4994_);
v_env_4997_ = lean_ctor_get(v___x_4996_, 0);
lean_inc_ref(v_env_4997_);
lean_dec(v___x_4996_);
v___x_5009_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_4991_, v___y_4994_);
lean_dec_ref(v___x_5009_);
lean_inc(v___y_4994_);
lean_inc_ref(v___y_4993_);
v___x_5010_ = lean_apply_3(v_x_4992_, v___y_4993_, v___y_4994_, lean_box(0));
if (lean_obj_tag(v___x_5010_) == 0)
{
lean_object* v_a_5011_; lean_object* v___x_5012_; lean_object* v___x_5014_; uint8_t v_isShared_5015_; uint8_t v_isSharedCheck_5019_; 
v_a_5011_ = lean_ctor_get(v___x_5010_, 0);
lean_inc(v_a_5011_);
lean_dec_ref_known(v___x_5010_, 1);
v___x_5012_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_4997_, v___y_4994_);
v_isSharedCheck_5019_ = !lean_is_exclusive(v___x_5012_);
if (v_isSharedCheck_5019_ == 0)
{
lean_object* v_unused_5020_; 
v_unused_5020_ = lean_ctor_get(v___x_5012_, 0);
lean_dec(v_unused_5020_);
v___x_5014_ = v___x_5012_;
v_isShared_5015_ = v_isSharedCheck_5019_;
goto v_resetjp_5013_;
}
else
{
lean_dec(v___x_5012_);
v___x_5014_ = lean_box(0);
v_isShared_5015_ = v_isSharedCheck_5019_;
goto v_resetjp_5013_;
}
v_resetjp_5013_:
{
lean_object* v___x_5017_; 
if (v_isShared_5015_ == 0)
{
lean_ctor_set(v___x_5014_, 0, v_a_5011_);
v___x_5017_ = v___x_5014_;
goto v_reusejp_5016_;
}
else
{
lean_object* v_reuseFailAlloc_5018_; 
v_reuseFailAlloc_5018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5018_, 0, v_a_5011_);
v___x_5017_ = v_reuseFailAlloc_5018_;
goto v_reusejp_5016_;
}
v_reusejp_5016_:
{
return v___x_5017_;
}
}
}
else
{
lean_object* v_a_5021_; 
v_a_5021_ = lean_ctor_get(v___x_5010_, 0);
lean_inc(v_a_5021_);
lean_dec_ref_known(v___x_5010_, 1);
v_a_4999_ = v_a_5021_;
goto v___jp_4998_;
}
v___jp_4998_:
{
lean_object* v___x_5000_; lean_object* v___x_5002_; uint8_t v_isShared_5003_; uint8_t v_isSharedCheck_5007_; 
v___x_5000_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_4997_, v___y_4994_);
v_isSharedCheck_5007_ = !lean_is_exclusive(v___x_5000_);
if (v_isSharedCheck_5007_ == 0)
{
lean_object* v_unused_5008_; 
v_unused_5008_ = lean_ctor_get(v___x_5000_, 0);
lean_dec(v_unused_5008_);
v___x_5002_ = v___x_5000_;
v_isShared_5003_ = v_isSharedCheck_5007_;
goto v_resetjp_5001_;
}
else
{
lean_dec(v___x_5000_);
v___x_5002_ = lean_box(0);
v_isShared_5003_ = v_isSharedCheck_5007_;
goto v_resetjp_5001_;
}
v_resetjp_5001_:
{
lean_object* v___x_5005_; 
if (v_isShared_5003_ == 0)
{
lean_ctor_set_tag(v___x_5002_, 1);
lean_ctor_set(v___x_5002_, 0, v_a_4999_);
v___x_5005_ = v___x_5002_;
goto v_reusejp_5004_;
}
else
{
lean_object* v_reuseFailAlloc_5006_; 
v_reuseFailAlloc_5006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5006_, 0, v_a_4999_);
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
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg___boxed(lean_object* v_env_5022_, lean_object* v_x_5023_, lean_object* v___y_5024_, lean_object* v___y_5025_, lean_object* v___y_5026_){
_start:
{
lean_object* v_res_5027_; 
v_res_5027_ = l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg(v_env_5022_, v_x_5023_, v___y_5024_, v___y_5025_);
lean_dec(v___y_5025_);
lean_dec_ref(v___y_5024_);
return v_res_5027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom(lean_object* v_biggerEnv_5028_, lean_object* v_e_5029_, lean_object* v_a_5030_, lean_object* v_a_5031_){
_start:
{
lean_object* v___x_5033_; lean_object* v_env_5034_; lean_object* v___f_5035_; lean_object* v___f_5036_; lean_object* v___x_5037_; lean_object* v___x_5038_; 
v___x_5033_ = lean_st_ref_get(v_a_5031_);
v_env_5034_ = lean_ctor_get(v___x_5033_, 0);
lean_inc_ref(v_env_5034_);
lean_dec(v___x_5033_);
v___f_5035_ = ((lean_object*)(l_Lean_Core_betaReduce___closed__1));
v___f_5036_ = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDeclsFrom___lam__0___boxed), 6, 3);
lean_closure_set(v___f_5036_, 0, v_biggerEnv_5028_);
lean_closure_set(v___f_5036_, 1, v_e_5029_);
lean_closure_set(v___f_5036_, 2, v___f_5035_);
v___x_5037_ = l_Lean_Environment_unlockAsync(v_env_5034_);
v___x_5038_ = l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg(v___x_5037_, v___f_5036_, v_a_5030_, v_a_5031_);
return v___x_5038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___boxed(lean_object* v_biggerEnv_5039_, lean_object* v_e_5040_, lean_object* v_a_5041_, lean_object* v_a_5042_, lean_object* v_a_5043_){
_start:
{
lean_object* v_res_5044_; 
v_res_5044_ = l_Lean_Meta_unfoldDeclsFrom(v_biggerEnv_5039_, v_e_5040_, v_a_5041_, v_a_5042_);
lean_dec(v_a_5042_);
lean_dec_ref(v_a_5041_);
return v_res_5044_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1(lean_object* v_00_u03b1_5045_, lean_object* v_env_5046_, lean_object* v_x_5047_, lean_object* v___y_5048_, lean_object* v___y_5049_){
_start:
{
lean_object* v___x_5051_; 
v___x_5051_ = l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg(v_env_5046_, v_x_5047_, v___y_5048_, v___y_5049_);
return v___x_5051_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___boxed(lean_object* v_00_u03b1_5052_, lean_object* v_env_5053_, lean_object* v_x_5054_, lean_object* v___y_5055_, lean_object* v___y_5056_, lean_object* v___y_5057_){
_start:
{
lean_object* v_res_5058_; 
v_res_5058_ = l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1(v_00_u03b1_5052_, v_env_5053_, v_x_5054_, v___y_5055_, v___y_5056_);
lean_dec(v___y_5056_);
lean_dec_ref(v___y_5055_);
return v_res_5058_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0(lean_object* v_af_5059_, lean_object* v_axs_5060_, lean_object* v_numSectionVars_5061_, lean_object* v_as_5062_, size_t v_i_5063_, size_t v_stop_5064_){
_start:
{
uint8_t v___x_5065_; 
v___x_5065_ = lean_usize_dec_eq(v_i_5063_, v_stop_5064_);
if (v___x_5065_ == 0)
{
uint8_t v___x_5066_; uint8_t v___y_5068_; lean_object* v___x_5072_; lean_object* v___x_5073_; uint8_t v___x_5074_; 
v___x_5066_ = 1;
v___x_5072_ = lean_array_uget_borrowed(v_as_5062_, v_i_5063_);
v___x_5073_ = l_Lean_Expr_constName_x21(v_af_5059_);
v___x_5074_ = lean_name_eq(v___x_5073_, v___x_5072_);
lean_dec(v___x_5073_);
if (v___x_5074_ == 0)
{
v___y_5068_ = v___x_5074_;
goto v___jp_5067_;
}
else
{
lean_object* v___x_5075_; uint8_t v___x_5076_; 
v___x_5075_ = lean_array_get_size(v_axs_5060_);
v___x_5076_ = lean_nat_dec_le(v___x_5075_, v_numSectionVars_5061_);
v___y_5068_ = v___x_5076_;
goto v___jp_5067_;
}
v___jp_5067_:
{
if (v___y_5068_ == 0)
{
size_t v___x_5069_; size_t v___x_5070_; 
v___x_5069_ = ((size_t)1ULL);
v___x_5070_ = lean_usize_add(v_i_5063_, v___x_5069_);
v_i_5063_ = v___x_5070_;
goto _start;
}
else
{
return v___x_5066_;
}
}
}
else
{
uint8_t v___x_5077_; 
v___x_5077_ = 0;
return v___x_5077_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0___boxed(lean_object* v_af_5078_, lean_object* v_axs_5079_, lean_object* v_numSectionVars_5080_, lean_object* v_as_5081_, lean_object* v_i_5082_, lean_object* v_stop_5083_){
_start:
{
size_t v_i_boxed_5084_; size_t v_stop_boxed_5085_; uint8_t v_res_5086_; lean_object* v_r_5087_; 
v_i_boxed_5084_ = lean_unbox_usize(v_i_5082_);
lean_dec(v_i_5082_);
v_stop_boxed_5085_ = lean_unbox_usize(v_stop_5083_);
lean_dec(v_stop_5083_);
v_res_5086_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0(v_af_5078_, v_axs_5079_, v_numSectionVars_5080_, v_as_5081_, v_i_boxed_5084_, v_stop_boxed_5085_);
lean_dec_ref(v_as_5081_);
lean_dec(v_numSectionVars_5080_);
lean_dec_ref(v_axs_5079_);
lean_dec_ref(v_af_5078_);
v_r_5087_ = lean_box(v_res_5086_);
return v_r_5087_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1_spec__1(lean_object* v_fnNames_5088_, lean_object* v_numSectionVars_5089_, lean_object* v_x_5090_, lean_object* v_x_5091_, lean_object* v_x_5092_){
_start:
{
if (lean_obj_tag(v_x_5090_) == 5)
{
lean_object* v_fn_5093_; lean_object* v_arg_5094_; lean_object* v___x_5095_; lean_object* v___x_5096_; lean_object* v___x_5097_; 
v_fn_5093_ = lean_ctor_get(v_x_5090_, 0);
lean_inc_ref(v_fn_5093_);
v_arg_5094_ = lean_ctor_get(v_x_5090_, 1);
lean_inc_ref(v_arg_5094_);
lean_dec_ref_known(v_x_5090_, 2);
v___x_5095_ = lean_array_set(v_x_5091_, v_x_5092_, v_arg_5094_);
v___x_5096_ = lean_unsigned_to_nat(1u);
v___x_5097_ = lean_nat_sub(v_x_5092_, v___x_5096_);
lean_dec(v_x_5092_);
v_x_5090_ = v_fn_5093_;
v_x_5091_ = v___x_5095_;
v_x_5092_ = v___x_5097_;
goto _start;
}
else
{
uint8_t v___x_5099_; 
lean_dec(v_x_5092_);
v___x_5099_ = l_Lean_Expr_isConst(v_x_5090_);
if (v___x_5099_ == 0)
{
lean_dec_ref(v_x_5091_);
lean_dec_ref(v_x_5090_);
return v___x_5099_;
}
else
{
lean_object* v___x_5100_; lean_object* v___x_5101_; uint8_t v___x_5102_; 
v___x_5100_ = lean_unsigned_to_nat(0u);
v___x_5101_ = lean_array_get_size(v_fnNames_5088_);
v___x_5102_ = lean_nat_dec_lt(v___x_5100_, v___x_5101_);
if (v___x_5102_ == 0)
{
lean_dec_ref(v_x_5091_);
lean_dec_ref(v_x_5090_);
return v___x_5102_;
}
else
{
if (v___x_5102_ == 0)
{
lean_dec_ref(v_x_5091_);
lean_dec_ref(v_x_5090_);
return v___x_5102_;
}
else
{
size_t v___x_5103_; size_t v___x_5104_; uint8_t v___x_5105_; 
v___x_5103_ = ((size_t)0ULL);
v___x_5104_ = lean_usize_of_nat(v___x_5101_);
v___x_5105_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0(v_x_5090_, v_x_5091_, v_numSectionVars_5089_, v_fnNames_5088_, v___x_5103_, v___x_5104_);
lean_dec_ref(v_x_5091_);
lean_dec_ref(v_x_5090_);
return v___x_5105_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1_spec__1___boxed(lean_object* v_fnNames_5106_, lean_object* v_numSectionVars_5107_, lean_object* v_x_5108_, lean_object* v_x_5109_, lean_object* v_x_5110_){
_start:
{
uint8_t v_res_5111_; lean_object* v_r_5112_; 
v_res_5111_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1_spec__1(v_fnNames_5106_, v_numSectionVars_5107_, v_x_5108_, v_x_5109_, v_x_5110_);
lean_dec(v_numSectionVars_5107_);
lean_dec_ref(v_fnNames_5106_);
v_r_5112_ = lean_box(v_res_5111_);
return v_r_5112_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1(lean_object* v_numSectionVars_5113_, lean_object* v_fnNames_5114_, lean_object* v_x_5115_, lean_object* v_x_5116_, lean_object* v_x_5117_){
_start:
{
if (lean_obj_tag(v_x_5115_) == 5)
{
lean_object* v_fn_5118_; lean_object* v_arg_5119_; lean_object* v___x_5120_; lean_object* v___x_5121_; lean_object* v___x_5122_; uint8_t v___x_5123_; 
v_fn_5118_ = lean_ctor_get(v_x_5115_, 0);
lean_inc_ref(v_fn_5118_);
v_arg_5119_ = lean_ctor_get(v_x_5115_, 1);
lean_inc_ref(v_arg_5119_);
lean_dec_ref_known(v_x_5115_, 2);
v___x_5120_ = lean_array_set(v_x_5116_, v_x_5117_, v_arg_5119_);
v___x_5121_ = lean_unsigned_to_nat(1u);
v___x_5122_ = lean_nat_sub(v_x_5117_, v___x_5121_);
v___x_5123_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1_spec__1(v_fnNames_5114_, v_numSectionVars_5113_, v_fn_5118_, v___x_5120_, v___x_5122_);
return v___x_5123_;
}
else
{
uint8_t v___x_5124_; 
v___x_5124_ = l_Lean_Expr_isConst(v_x_5115_);
if (v___x_5124_ == 0)
{
lean_dec_ref(v_x_5116_);
lean_dec_ref(v_x_5115_);
return v___x_5124_;
}
else
{
lean_object* v___x_5125_; lean_object* v___x_5126_; uint8_t v___x_5127_; 
v___x_5125_ = lean_unsigned_to_nat(0u);
v___x_5126_ = lean_array_get_size(v_fnNames_5114_);
v___x_5127_ = lean_nat_dec_lt(v___x_5125_, v___x_5126_);
if (v___x_5127_ == 0)
{
lean_dec_ref(v_x_5116_);
lean_dec_ref(v_x_5115_);
return v___x_5127_;
}
else
{
if (v___x_5127_ == 0)
{
lean_dec_ref(v_x_5116_);
lean_dec_ref(v_x_5115_);
return v___x_5127_;
}
else
{
size_t v___x_5128_; size_t v___x_5129_; uint8_t v___x_5130_; 
v___x_5128_ = ((size_t)0ULL);
v___x_5129_ = lean_usize_of_nat(v___x_5126_);
v___x_5130_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0(v_x_5115_, v_x_5116_, v_numSectionVars_5113_, v_fnNames_5114_, v___x_5128_, v___x_5129_);
lean_dec_ref(v_x_5116_);
lean_dec_ref(v_x_5115_);
return v___x_5130_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1___boxed(lean_object* v_numSectionVars_5131_, lean_object* v_fnNames_5132_, lean_object* v_x_5133_, lean_object* v_x_5134_, lean_object* v_x_5135_){
_start:
{
uint8_t v_res_5136_; lean_object* v_r_5137_; 
v_res_5136_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1(v_numSectionVars_5131_, v_fnNames_5132_, v_x_5133_, v_x_5134_, v_x_5135_);
lean_dec(v_x_5135_);
lean_dec_ref(v_fnNames_5132_);
lean_dec(v_numSectionVars_5131_);
v_r_5137_ = lean_box(v_res_5136_);
return v_r_5137_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg(lean_object* v_fnNames_5138_, lean_object* v_numSectionVars_5139_, lean_object* v_a_5140_){
_start:
{
lean_object* v_dummy_5141_; lean_object* v_nargs_5142_; lean_object* v___x_5143_; lean_object* v___x_5144_; lean_object* v___x_5145_; uint8_t v___x_5146_; 
v_dummy_5141_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_5142_ = l_Lean_Expr_getAppNumArgs(v_a_5140_);
lean_inc(v_nargs_5142_);
v___x_5143_ = lean_mk_array(v_nargs_5142_, v_dummy_5141_);
v___x_5144_ = lean_unsigned_to_nat(1u);
v___x_5145_ = lean_nat_sub(v_nargs_5142_, v___x_5144_);
lean_dec(v_nargs_5142_);
v___x_5146_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1(v_numSectionVars_5139_, v_fnNames_5138_, v_a_5140_, v___x_5143_, v___x_5145_);
lean_dec(v___x_5145_);
return v___x_5146_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg___boxed(lean_object* v_fnNames_5147_, lean_object* v_numSectionVars_5148_, lean_object* v_a_5149_){
_start:
{
uint8_t v_res_5150_; lean_object* v_r_5151_; 
v_res_5150_ = l___private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg(v_fnNames_5147_, v_numSectionVars_5148_, v_a_5149_);
lean_dec(v_numSectionVars_5148_);
lean_dec_ref(v_fnNames_5147_);
v_r_5151_ = lean_box(v_res_5150_);
return v_r_5151_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__0(lean_object* v_fnNames_5152_, lean_object* v_numSectionVars_5153_, lean_object* v_as_5154_, size_t v_i_5155_, size_t v_stop_5156_){
_start:
{
uint8_t v___x_5157_; 
v___x_5157_ = lean_usize_dec_eq(v_i_5155_, v_stop_5156_);
if (v___x_5157_ == 0)
{
lean_object* v___x_5158_; uint8_t v___x_5159_; 
v___x_5158_ = lean_array_uget_borrowed(v_as_5154_, v_i_5155_);
lean_inc(v___x_5158_);
v___x_5159_ = l___private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg(v_fnNames_5152_, v_numSectionVars_5153_, v___x_5158_);
if (v___x_5159_ == 0)
{
size_t v___x_5160_; size_t v___x_5161_; 
v___x_5160_ = ((size_t)1ULL);
v___x_5161_ = lean_usize_add(v_i_5155_, v___x_5160_);
v_i_5155_ = v___x_5161_;
goto _start;
}
else
{
return v___x_5159_;
}
}
else
{
uint8_t v___x_5163_; 
v___x_5163_ = 0;
return v___x_5163_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__0___boxed(lean_object* v_fnNames_5164_, lean_object* v_numSectionVars_5165_, lean_object* v_as_5166_, lean_object* v_i_5167_, lean_object* v_stop_5168_){
_start:
{
size_t v_i_boxed_5169_; size_t v_stop_boxed_5170_; uint8_t v_res_5171_; lean_object* v_r_5172_; 
v_i_boxed_5169_ = lean_unbox_usize(v_i_5167_);
lean_dec(v_i_5167_);
v_stop_boxed_5170_ = lean_unbox_usize(v_stop_5168_);
lean_dec(v_stop_5168_);
v_res_5171_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__0(v_fnNames_5164_, v_numSectionVars_5165_, v_as_5166_, v_i_boxed_5169_, v_stop_boxed_5170_);
lean_dec_ref(v_as_5166_);
lean_dec(v_numSectionVars_5165_);
lean_dec_ref(v_fnNames_5164_);
v_r_5172_ = lean_box(v_res_5171_);
return v_r_5172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__1(lean_object* v_fnNames_5173_, lean_object* v_numSectionVars_5174_, lean_object* v___x_5175_, lean_object* v_x_5176_, lean_object* v_x_5177_, lean_object* v___y_5178_, lean_object* v___y_5179_){
_start:
{
if (lean_obj_tag(v_x_5176_) == 5)
{
lean_object* v_fn_5184_; lean_object* v_arg_5185_; lean_object* v___x_5186_; 
v_fn_5184_ = lean_ctor_get(v_x_5176_, 0);
lean_inc_ref(v_fn_5184_);
v_arg_5185_ = lean_ctor_get(v_x_5176_, 1);
lean_inc_ref(v_arg_5185_);
lean_dec_ref_known(v_x_5176_, 2);
v___x_5186_ = lean_array_push(v_x_5177_, v_arg_5185_);
v_x_5176_ = v_fn_5184_;
v_x_5177_ = v___x_5186_;
goto _start;
}
else
{
uint8_t v___x_5188_; 
v___x_5188_ = l_Lean_Expr_isConst(v_x_5176_);
if (v___x_5188_ == 0)
{
lean_dec_ref(v_x_5177_);
lean_dec_ref(v_x_5176_);
lean_dec_ref(v___x_5175_);
goto v___jp_5181_;
}
else
{
lean_object* v___x_5189_; lean_object* v___x_5190_; uint8_t v___x_5191_; 
v___x_5189_ = lean_unsigned_to_nat(0u);
v___x_5190_ = lean_array_get_size(v_x_5177_);
v___x_5191_ = lean_nat_dec_lt(v___x_5189_, v___x_5190_);
if (v___x_5191_ == 0)
{
lean_dec_ref(v_x_5177_);
lean_dec_ref(v_x_5176_);
lean_dec_ref(v___x_5175_);
goto v___jp_5181_;
}
else
{
if (v___x_5191_ == 0)
{
lean_dec_ref(v_x_5177_);
lean_dec_ref(v_x_5176_);
lean_dec_ref(v___x_5175_);
goto v___jp_5181_;
}
else
{
size_t v___x_5192_; size_t v___x_5193_; uint8_t v___x_5194_; 
v___x_5192_ = ((size_t)0ULL);
v___x_5193_ = lean_usize_of_nat(v___x_5190_);
v___x_5194_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__0(v_fnNames_5173_, v_numSectionVars_5174_, v_x_5177_, v___x_5192_, v___x_5193_);
if (v___x_5194_ == 0)
{
lean_dec_ref(v_x_5177_);
lean_dec_ref(v_x_5176_);
lean_dec_ref(v___x_5175_);
goto v___jp_5181_;
}
else
{
lean_object* v___x_5195_; uint8_t v___x_5196_; lean_object* v___x_5197_; 
v___x_5195_ = l_Lean_Expr_constName_x21(v_x_5176_);
v___x_5196_ = 0;
v___x_5197_ = l_Lean_Environment_find_x3f(v___x_5175_, v___x_5195_, v___x_5196_);
if (lean_obj_tag(v___x_5197_) == 1)
{
lean_object* v_val_5198_; 
v_val_5198_ = lean_ctor_get(v___x_5197_, 0);
lean_inc(v_val_5198_);
lean_dec_ref_known(v___x_5197_, 1);
if (lean_obj_tag(v_val_5198_) == 2)
{
lean_object* v___x_5199_; lean_object* v___x_5200_; lean_object* v___x_5202_; uint8_t v_isShared_5203_; uint8_t v_isSharedCheck_5224_; 
v___x_5199_ = l_Lean_Expr_constLevels_x21(v_x_5176_);
lean_dec_ref(v_x_5176_);
v___x_5200_ = l_Lean_Core_instantiateValueLevelParams(v_val_5198_, v___x_5199_, v___x_5191_, v___y_5178_, v___y_5179_);
v_isSharedCheck_5224_ = !lean_is_exclusive(v_val_5198_);
if (v_isSharedCheck_5224_ == 0)
{
lean_object* v_unused_5225_; 
v_unused_5225_ = lean_ctor_get(v_val_5198_, 0);
lean_dec(v_unused_5225_);
v___x_5202_ = v_val_5198_;
v_isShared_5203_ = v_isSharedCheck_5224_;
goto v_resetjp_5201_;
}
else
{
lean_dec(v_val_5198_);
v___x_5202_ = lean_box(0);
v_isShared_5203_ = v_isSharedCheck_5224_;
goto v_resetjp_5201_;
}
v_resetjp_5201_:
{
if (lean_obj_tag(v___x_5200_) == 0)
{
lean_object* v_a_5204_; lean_object* v___x_5206_; uint8_t v_isShared_5207_; uint8_t v_isSharedCheck_5215_; 
v_a_5204_ = lean_ctor_get(v___x_5200_, 0);
v_isSharedCheck_5215_ = !lean_is_exclusive(v___x_5200_);
if (v_isSharedCheck_5215_ == 0)
{
v___x_5206_ = v___x_5200_;
v_isShared_5207_ = v_isSharedCheck_5215_;
goto v_resetjp_5205_;
}
else
{
lean_inc(v_a_5204_);
lean_dec(v___x_5200_);
v___x_5206_ = lean_box(0);
v_isShared_5207_ = v_isSharedCheck_5215_;
goto v_resetjp_5205_;
}
v_resetjp_5205_:
{
lean_object* v___x_5208_; lean_object* v___x_5210_; 
v___x_5208_ = l_Lean_Expr_betaRev(v_a_5204_, v_x_5177_, v___x_5196_, v___x_5196_);
lean_dec_ref(v_x_5177_);
if (v_isShared_5203_ == 0)
{
lean_ctor_set_tag(v___x_5202_, 1);
lean_ctor_set(v___x_5202_, 0, v___x_5208_);
v___x_5210_ = v___x_5202_;
goto v_reusejp_5209_;
}
else
{
lean_object* v_reuseFailAlloc_5214_; 
v_reuseFailAlloc_5214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5214_, 0, v___x_5208_);
v___x_5210_ = v_reuseFailAlloc_5214_;
goto v_reusejp_5209_;
}
v_reusejp_5209_:
{
lean_object* v___x_5212_; 
if (v_isShared_5207_ == 0)
{
lean_ctor_set(v___x_5206_, 0, v___x_5210_);
v___x_5212_ = v___x_5206_;
goto v_reusejp_5211_;
}
else
{
lean_object* v_reuseFailAlloc_5213_; 
v_reuseFailAlloc_5213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5213_, 0, v___x_5210_);
v___x_5212_ = v_reuseFailAlloc_5213_;
goto v_reusejp_5211_;
}
v_reusejp_5211_:
{
return v___x_5212_;
}
}
}
}
else
{
lean_object* v_a_5216_; lean_object* v___x_5218_; uint8_t v_isShared_5219_; uint8_t v_isSharedCheck_5223_; 
lean_del_object(v___x_5202_);
lean_dec_ref(v_x_5177_);
v_a_5216_ = lean_ctor_get(v___x_5200_, 0);
v_isSharedCheck_5223_ = !lean_is_exclusive(v___x_5200_);
if (v_isSharedCheck_5223_ == 0)
{
v___x_5218_ = v___x_5200_;
v_isShared_5219_ = v_isSharedCheck_5223_;
goto v_resetjp_5217_;
}
else
{
lean_inc(v_a_5216_);
lean_dec(v___x_5200_);
v___x_5218_ = lean_box(0);
v_isShared_5219_ = v_isSharedCheck_5223_;
goto v_resetjp_5217_;
}
v_resetjp_5217_:
{
lean_object* v___x_5221_; 
if (v_isShared_5219_ == 0)
{
v___x_5221_ = v___x_5218_;
goto v_reusejp_5220_;
}
else
{
lean_object* v_reuseFailAlloc_5222_; 
v_reuseFailAlloc_5222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5222_, 0, v_a_5216_);
v___x_5221_ = v_reuseFailAlloc_5222_;
goto v_reusejp_5220_;
}
v_reusejp_5220_:
{
return v___x_5221_;
}
}
}
}
}
else
{
lean_dec(v_val_5198_);
lean_dec_ref(v_x_5177_);
lean_dec_ref(v_x_5176_);
goto v___jp_5181_;
}
}
else
{
lean_dec(v___x_5197_);
lean_dec_ref(v_x_5177_);
lean_dec_ref(v_x_5176_);
goto v___jp_5181_;
}
}
}
}
}
}
v___jp_5181_:
{
lean_object* v___x_5182_; lean_object* v___x_5183_; 
v___x_5182_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_5183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5183_, 0, v___x_5182_);
return v___x_5183_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__1___boxed(lean_object* v_fnNames_5226_, lean_object* v_numSectionVars_5227_, lean_object* v___x_5228_, lean_object* v_x_5229_, lean_object* v_x_5230_, lean_object* v___y_5231_, lean_object* v___y_5232_, lean_object* v___y_5233_){
_start:
{
lean_object* v_res_5234_; 
v_res_5234_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__1(v_fnNames_5226_, v_numSectionVars_5227_, v___x_5228_, v_x_5229_, v_x_5230_, v___y_5231_, v___y_5232_);
lean_dec(v___y_5232_);
lean_dec_ref(v___y_5231_);
lean_dec(v_numSectionVars_5227_);
lean_dec_ref(v_fnNames_5226_);
return v_res_5234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___lam__1(lean_object* v_fnNames_5235_, lean_object* v_numSectionVars_5236_, lean_object* v_env_5237_, lean_object* v_e_5238_, lean_object* v___y_5239_, lean_object* v___y_5240_){
_start:
{
lean_object* v___x_5242_; lean_object* v___x_5243_; lean_object* v___x_5244_; 
v___x_5242_ = l_Lean_Expr_getAppNumArgs(v_e_5238_);
v___x_5243_ = lean_mk_empty_array_with_capacity(v___x_5242_);
lean_dec(v___x_5242_);
v___x_5244_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__1(v_fnNames_5235_, v_numSectionVars_5236_, v_env_5237_, v_e_5238_, v___x_5243_, v___y_5239_, v___y_5240_);
return v___x_5244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___lam__1___boxed(lean_object* v_fnNames_5245_, lean_object* v_numSectionVars_5246_, lean_object* v_env_5247_, lean_object* v_e_5248_, lean_object* v___y_5249_, lean_object* v___y_5250_, lean_object* v___y_5251_){
_start:
{
lean_object* v_res_5252_; 
v_res_5252_ = l_Lean_Meta_unfoldIfArgIsAppOf___lam__1(v_fnNames_5245_, v_numSectionVars_5246_, v_env_5247_, v_e_5248_, v___y_5249_, v___y_5250_);
lean_dec(v___y_5250_);
lean_dec_ref(v___y_5249_);
lean_dec(v_numSectionVars_5246_);
lean_dec_ref(v_fnNames_5245_);
return v_res_5252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___lam__0(lean_object* v_fnNames_5253_, lean_object* v_numSectionVars_5254_, lean_object* v_e_5255_, lean_object* v___f_5256_, lean_object* v___y_5257_, lean_object* v___y_5258_){
_start:
{
lean_object* v___x_5260_; lean_object* v_env_5261_; lean_object* v___f_5262_; lean_object* v___x_5263_; 
v___x_5260_ = lean_st_ref_get(v___y_5258_);
v_env_5261_ = lean_ctor_get(v___x_5260_, 0);
lean_inc_ref(v_env_5261_);
lean_dec(v___x_5260_);
v___f_5262_ = lean_alloc_closure((void*)(l_Lean_Meta_unfoldIfArgIsAppOf___lam__1___boxed), 7, 3);
lean_closure_set(v___f_5262_, 0, v_fnNames_5253_);
lean_closure_set(v___f_5262_, 1, v_numSectionVars_5254_);
lean_closure_set(v___f_5262_, 2, v_env_5261_);
v___x_5263_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_5255_, v___f_5262_, v___f_5256_, v___y_5257_, v___y_5258_);
return v___x_5263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___lam__0___boxed(lean_object* v_fnNames_5264_, lean_object* v_numSectionVars_5265_, lean_object* v_e_5266_, lean_object* v___f_5267_, lean_object* v___y_5268_, lean_object* v___y_5269_, lean_object* v___y_5270_){
_start:
{
lean_object* v_res_5271_; 
v_res_5271_ = l_Lean_Meta_unfoldIfArgIsAppOf___lam__0(v_fnNames_5264_, v_numSectionVars_5265_, v_e_5266_, v___f_5267_, v___y_5268_, v___y_5269_);
lean_dec(v___y_5269_);
lean_dec_ref(v___y_5268_);
return v_res_5271_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0(lean_object* v___y_5272_, uint8_t v_isExporting_5273_, lean_object* v___x_5274_, lean_object* v_a_x3f_5275_){
_start:
{
lean_object* v___x_5277_; lean_object* v_env_5278_; lean_object* v_nextMacroScope_5279_; lean_object* v_ngen_5280_; lean_object* v_auxDeclNGen_5281_; lean_object* v_traceState_5282_; lean_object* v_messages_5283_; lean_object* v_infoState_5284_; lean_object* v_snapshotTasks_5285_; lean_object* v___x_5287_; uint8_t v_isShared_5288_; uint8_t v_isSharedCheck_5296_; 
v___x_5277_ = lean_st_ref_take(v___y_5272_);
v_env_5278_ = lean_ctor_get(v___x_5277_, 0);
v_nextMacroScope_5279_ = lean_ctor_get(v___x_5277_, 1);
v_ngen_5280_ = lean_ctor_get(v___x_5277_, 2);
v_auxDeclNGen_5281_ = lean_ctor_get(v___x_5277_, 3);
v_traceState_5282_ = lean_ctor_get(v___x_5277_, 4);
v_messages_5283_ = lean_ctor_get(v___x_5277_, 6);
v_infoState_5284_ = lean_ctor_get(v___x_5277_, 7);
v_snapshotTasks_5285_ = lean_ctor_get(v___x_5277_, 8);
v_isSharedCheck_5296_ = !lean_is_exclusive(v___x_5277_);
if (v_isSharedCheck_5296_ == 0)
{
lean_object* v_unused_5297_; 
v_unused_5297_ = lean_ctor_get(v___x_5277_, 5);
lean_dec(v_unused_5297_);
v___x_5287_ = v___x_5277_;
v_isShared_5288_ = v_isSharedCheck_5296_;
goto v_resetjp_5286_;
}
else
{
lean_inc(v_snapshotTasks_5285_);
lean_inc(v_infoState_5284_);
lean_inc(v_messages_5283_);
lean_inc(v_traceState_5282_);
lean_inc(v_auxDeclNGen_5281_);
lean_inc(v_ngen_5280_);
lean_inc(v_nextMacroScope_5279_);
lean_inc(v_env_5278_);
lean_dec(v___x_5277_);
v___x_5287_ = lean_box(0);
v_isShared_5288_ = v_isSharedCheck_5296_;
goto v_resetjp_5286_;
}
v_resetjp_5286_:
{
lean_object* v___x_5289_; lean_object* v___x_5291_; 
v___x_5289_ = l_Lean_Environment_setExporting(v_env_5278_, v_isExporting_5273_);
if (v_isShared_5288_ == 0)
{
lean_ctor_set(v___x_5287_, 5, v___x_5274_);
lean_ctor_set(v___x_5287_, 0, v___x_5289_);
v___x_5291_ = v___x_5287_;
goto v_reusejp_5290_;
}
else
{
lean_object* v_reuseFailAlloc_5295_; 
v_reuseFailAlloc_5295_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5295_, 0, v___x_5289_);
lean_ctor_set(v_reuseFailAlloc_5295_, 1, v_nextMacroScope_5279_);
lean_ctor_set(v_reuseFailAlloc_5295_, 2, v_ngen_5280_);
lean_ctor_set(v_reuseFailAlloc_5295_, 3, v_auxDeclNGen_5281_);
lean_ctor_set(v_reuseFailAlloc_5295_, 4, v_traceState_5282_);
lean_ctor_set(v_reuseFailAlloc_5295_, 5, v___x_5274_);
lean_ctor_set(v_reuseFailAlloc_5295_, 6, v_messages_5283_);
lean_ctor_set(v_reuseFailAlloc_5295_, 7, v_infoState_5284_);
lean_ctor_set(v_reuseFailAlloc_5295_, 8, v_snapshotTasks_5285_);
v___x_5291_ = v_reuseFailAlloc_5295_;
goto v_reusejp_5290_;
}
v_reusejp_5290_:
{
lean_object* v___x_5292_; lean_object* v___x_5293_; lean_object* v___x_5294_; 
v___x_5292_ = lean_st_ref_put(v___y_5272_, v___x_5291_);
v___x_5293_ = lean_box(0);
v___x_5294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5294_, 0, v___x_5293_);
return v___x_5294_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0___boxed(lean_object* v___y_5298_, lean_object* v_isExporting_5299_, lean_object* v___x_5300_, lean_object* v_a_x3f_5301_, lean_object* v___y_5302_){
_start:
{
uint8_t v_isExporting_boxed_5303_; lean_object* v_res_5304_; 
v_isExporting_boxed_5303_ = lean_unbox(v_isExporting_5299_);
v_res_5304_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0(v___y_5298_, v_isExporting_boxed_5303_, v___x_5300_, v_a_x3f_5301_);
lean_dec(v_a_x3f_5301_);
lean_dec(v___y_5298_);
return v_res_5304_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg(lean_object* v_x_5305_, uint8_t v_isExporting_5306_, lean_object* v___y_5307_, lean_object* v___y_5308_){
_start:
{
lean_object* v___x_5310_; lean_object* v_env_5311_; lean_object* v___x_5312_; uint8_t v_isModule_5313_; 
v___x_5310_ = lean_st_ref_get(v___y_5308_);
v_env_5311_ = lean_ctor_get(v___x_5310_, 0);
lean_inc_ref(v_env_5311_);
lean_dec(v___x_5310_);
v___x_5312_ = l_Lean_Environment_header(v_env_5311_);
v_isModule_5313_ = lean_ctor_get_uint8(v___x_5312_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_5312_);
if (v_isModule_5313_ == 0)
{
lean_object* v___x_5314_; 
lean_dec_ref(v_env_5311_);
lean_inc(v___y_5308_);
lean_inc_ref(v___y_5307_);
v___x_5314_ = lean_apply_3(v_x_5305_, v___y_5307_, v___y_5308_, lean_box(0));
return v___x_5314_;
}
else
{
uint8_t v_isExporting_5315_; 
v_isExporting_5315_ = lean_ctor_get_uint8(v_env_5311_, sizeof(void*)*8);
lean_dec_ref(v_env_5311_);
if (v_isExporting_5306_ == 0)
{
if (v_isExporting_5315_ == 0)
{
lean_object* v___x_5366_; 
lean_inc(v___y_5308_);
lean_inc_ref(v___y_5307_);
v___x_5366_ = lean_apply_3(v_x_5305_, v___y_5307_, v___y_5308_, lean_box(0));
return v___x_5366_;
}
else
{
goto v___jp_5316_;
}
}
else
{
if (v_isExporting_5315_ == 0)
{
goto v___jp_5316_;
}
else
{
lean_object* v___x_5367_; 
lean_inc(v___y_5308_);
lean_inc_ref(v___y_5307_);
v___x_5367_ = lean_apply_3(v_x_5305_, v___y_5307_, v___y_5308_, lean_box(0));
return v___x_5367_;
}
}
v___jp_5316_:
{
lean_object* v___x_5317_; lean_object* v_env_5318_; lean_object* v_nextMacroScope_5319_; lean_object* v_ngen_5320_; lean_object* v_auxDeclNGen_5321_; lean_object* v_traceState_5322_; lean_object* v_messages_5323_; lean_object* v_infoState_5324_; lean_object* v_snapshotTasks_5325_; lean_object* v___x_5327_; uint8_t v_isShared_5328_; uint8_t v_isSharedCheck_5364_; 
v___x_5317_ = lean_st_ref_take(v___y_5308_);
v_env_5318_ = lean_ctor_get(v___x_5317_, 0);
v_nextMacroScope_5319_ = lean_ctor_get(v___x_5317_, 1);
v_ngen_5320_ = lean_ctor_get(v___x_5317_, 2);
v_auxDeclNGen_5321_ = lean_ctor_get(v___x_5317_, 3);
v_traceState_5322_ = lean_ctor_get(v___x_5317_, 4);
v_messages_5323_ = lean_ctor_get(v___x_5317_, 6);
v_infoState_5324_ = lean_ctor_get(v___x_5317_, 7);
v_snapshotTasks_5325_ = lean_ctor_get(v___x_5317_, 8);
v_isSharedCheck_5364_ = !lean_is_exclusive(v___x_5317_);
if (v_isSharedCheck_5364_ == 0)
{
lean_object* v_unused_5365_; 
v_unused_5365_ = lean_ctor_get(v___x_5317_, 5);
lean_dec(v_unused_5365_);
v___x_5327_ = v___x_5317_;
v_isShared_5328_ = v_isSharedCheck_5364_;
goto v_resetjp_5326_;
}
else
{
lean_inc(v_snapshotTasks_5325_);
lean_inc(v_infoState_5324_);
lean_inc(v_messages_5323_);
lean_inc(v_traceState_5322_);
lean_inc(v_auxDeclNGen_5321_);
lean_inc(v_ngen_5320_);
lean_inc(v_nextMacroScope_5319_);
lean_inc(v_env_5318_);
lean_dec(v___x_5317_);
v___x_5327_ = lean_box(0);
v_isShared_5328_ = v_isSharedCheck_5364_;
goto v_resetjp_5326_;
}
v_resetjp_5326_:
{
lean_object* v___x_5329_; lean_object* v___x_5330_; lean_object* v___x_5332_; 
v___x_5329_ = l_Lean_Environment_setExporting(v_env_5318_, v_isExporting_5306_);
v___x_5330_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2, &l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2);
if (v_isShared_5328_ == 0)
{
lean_ctor_set(v___x_5327_, 5, v___x_5330_);
lean_ctor_set(v___x_5327_, 0, v___x_5329_);
v___x_5332_ = v___x_5327_;
goto v_reusejp_5331_;
}
else
{
lean_object* v_reuseFailAlloc_5363_; 
v_reuseFailAlloc_5363_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5363_, 0, v___x_5329_);
lean_ctor_set(v_reuseFailAlloc_5363_, 1, v_nextMacroScope_5319_);
lean_ctor_set(v_reuseFailAlloc_5363_, 2, v_ngen_5320_);
lean_ctor_set(v_reuseFailAlloc_5363_, 3, v_auxDeclNGen_5321_);
lean_ctor_set(v_reuseFailAlloc_5363_, 4, v_traceState_5322_);
lean_ctor_set(v_reuseFailAlloc_5363_, 5, v___x_5330_);
lean_ctor_set(v_reuseFailAlloc_5363_, 6, v_messages_5323_);
lean_ctor_set(v_reuseFailAlloc_5363_, 7, v_infoState_5324_);
lean_ctor_set(v_reuseFailAlloc_5363_, 8, v_snapshotTasks_5325_);
v___x_5332_ = v_reuseFailAlloc_5363_;
goto v_reusejp_5331_;
}
v_reusejp_5331_:
{
lean_object* v___x_5333_; lean_object* v_r_5334_; 
v___x_5333_ = lean_st_ref_put(v___y_5308_, v___x_5332_);
lean_inc(v___y_5308_);
lean_inc_ref(v___y_5307_);
v_r_5334_ = lean_apply_3(v_x_5305_, v___y_5307_, v___y_5308_, lean_box(0));
if (lean_obj_tag(v_r_5334_) == 0)
{
lean_object* v_a_5335_; lean_object* v___x_5337_; uint8_t v_isShared_5338_; uint8_t v_isSharedCheck_5351_; 
v_a_5335_ = lean_ctor_get(v_r_5334_, 0);
v_isSharedCheck_5351_ = !lean_is_exclusive(v_r_5334_);
if (v_isSharedCheck_5351_ == 0)
{
v___x_5337_ = v_r_5334_;
v_isShared_5338_ = v_isSharedCheck_5351_;
goto v_resetjp_5336_;
}
else
{
lean_inc(v_a_5335_);
lean_dec(v_r_5334_);
v___x_5337_ = lean_box(0);
v_isShared_5338_ = v_isSharedCheck_5351_;
goto v_resetjp_5336_;
}
v_resetjp_5336_:
{
lean_object* v___x_5340_; 
lean_inc(v_a_5335_);
if (v_isShared_5338_ == 0)
{
lean_ctor_set_tag(v___x_5337_, 1);
v___x_5340_ = v___x_5337_;
goto v_reusejp_5339_;
}
else
{
lean_object* v_reuseFailAlloc_5350_; 
v_reuseFailAlloc_5350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5350_, 0, v_a_5335_);
v___x_5340_ = v_reuseFailAlloc_5350_;
goto v_reusejp_5339_;
}
v_reusejp_5339_:
{
lean_object* v___x_5341_; lean_object* v___x_5343_; uint8_t v_isShared_5344_; uint8_t v_isSharedCheck_5348_; 
v___x_5341_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0(v___y_5308_, v_isExporting_5315_, v___x_5330_, v___x_5340_);
lean_dec_ref(v___x_5340_);
v_isSharedCheck_5348_ = !lean_is_exclusive(v___x_5341_);
if (v_isSharedCheck_5348_ == 0)
{
lean_object* v_unused_5349_; 
v_unused_5349_ = lean_ctor_get(v___x_5341_, 0);
lean_dec(v_unused_5349_);
v___x_5343_ = v___x_5341_;
v_isShared_5344_ = v_isSharedCheck_5348_;
goto v_resetjp_5342_;
}
else
{
lean_dec(v___x_5341_);
v___x_5343_ = lean_box(0);
v_isShared_5344_ = v_isSharedCheck_5348_;
goto v_resetjp_5342_;
}
v_resetjp_5342_:
{
lean_object* v___x_5346_; 
if (v_isShared_5344_ == 0)
{
lean_ctor_set(v___x_5343_, 0, v_a_5335_);
v___x_5346_ = v___x_5343_;
goto v_reusejp_5345_;
}
else
{
lean_object* v_reuseFailAlloc_5347_; 
v_reuseFailAlloc_5347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5347_, 0, v_a_5335_);
v___x_5346_ = v_reuseFailAlloc_5347_;
goto v_reusejp_5345_;
}
v_reusejp_5345_:
{
return v___x_5346_;
}
}
}
}
}
else
{
lean_object* v_a_5352_; lean_object* v___x_5353_; lean_object* v___x_5354_; lean_object* v___x_5356_; uint8_t v_isShared_5357_; uint8_t v_isSharedCheck_5361_; 
v_a_5352_ = lean_ctor_get(v_r_5334_, 0);
lean_inc(v_a_5352_);
lean_dec_ref_known(v_r_5334_, 1);
v___x_5353_ = lean_box(0);
v___x_5354_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0(v___y_5308_, v_isExporting_5315_, v___x_5330_, v___x_5353_);
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
lean_ctor_set_tag(v___x_5356_, 1);
lean_ctor_set(v___x_5356_, 0, v_a_5352_);
v___x_5359_ = v___x_5356_;
goto v_reusejp_5358_;
}
else
{
lean_object* v_reuseFailAlloc_5360_; 
v_reuseFailAlloc_5360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5360_, 0, v_a_5352_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___boxed(lean_object* v_x_5368_, lean_object* v_isExporting_5369_, lean_object* v___y_5370_, lean_object* v___y_5371_, lean_object* v___y_5372_){
_start:
{
uint8_t v_isExporting_boxed_5373_; lean_object* v_res_5374_; 
v_isExporting_boxed_5373_ = lean_unbox(v_isExporting_5369_);
v_res_5374_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg(v_x_5368_, v_isExporting_boxed_5373_, v___y_5370_, v___y_5371_);
lean_dec(v___y_5371_);
lean_dec_ref(v___y_5370_);
return v_res_5374_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg(lean_object* v_x_5375_, uint8_t v_when_5376_, lean_object* v___y_5377_, lean_object* v___y_5378_){
_start:
{
if (v_when_5376_ == 0)
{
lean_object* v___x_5380_; 
lean_inc(v___y_5378_);
lean_inc_ref(v___y_5377_);
v___x_5380_ = lean_apply_3(v_x_5375_, v___y_5377_, v___y_5378_, lean_box(0));
return v___x_5380_;
}
else
{
uint8_t v___x_5381_; lean_object* v___x_5382_; 
v___x_5381_ = 0;
v___x_5382_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg(v_x_5375_, v___x_5381_, v___y_5377_, v___y_5378_);
return v___x_5382_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg___boxed(lean_object* v_x_5383_, lean_object* v_when_5384_, lean_object* v___y_5385_, lean_object* v___y_5386_, lean_object* v___y_5387_){
_start:
{
uint8_t v_when_boxed_5388_; lean_object* v_res_5389_; 
v_when_boxed_5388_ = lean_unbox(v_when_5384_);
v_res_5389_ = l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg(v_x_5383_, v_when_boxed_5388_, v___y_5385_, v___y_5386_);
lean_dec(v___y_5386_);
lean_dec_ref(v___y_5385_);
return v_res_5389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf(lean_object* v_fnNames_5390_, lean_object* v_numSectionVars_5391_, lean_object* v_e_5392_, lean_object* v_a_5393_, lean_object* v_a_5394_){
_start:
{
lean_object* v___f_5396_; lean_object* v___f_5397_; uint8_t v___x_5398_; lean_object* v___x_5399_; 
v___f_5396_ = ((lean_object*)(l_Lean_Core_betaReduce___closed__1));
v___f_5397_ = lean_alloc_closure((void*)(l_Lean_Meta_unfoldIfArgIsAppOf___lam__0___boxed), 7, 4);
lean_closure_set(v___f_5397_, 0, v_fnNames_5390_);
lean_closure_set(v___f_5397_, 1, v_numSectionVars_5391_);
lean_closure_set(v___f_5397_, 2, v_e_5392_);
lean_closure_set(v___f_5397_, 3, v___f_5396_);
v___x_5398_ = 1;
v___x_5399_ = l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg(v___f_5397_, v___x_5398_, v_a_5393_, v_a_5394_);
return v___x_5399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___boxed(lean_object* v_fnNames_5400_, lean_object* v_numSectionVars_5401_, lean_object* v_e_5402_, lean_object* v_a_5403_, lean_object* v_a_5404_, lean_object* v_a_5405_){
_start:
{
lean_object* v_res_5406_; 
v_res_5406_ = l_Lean_Meta_unfoldIfArgIsAppOf(v_fnNames_5400_, v_numSectionVars_5401_, v_e_5402_, v_a_5403_, v_a_5404_);
lean_dec(v_a_5404_);
lean_dec_ref(v_a_5403_);
return v_res_5406_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2(lean_object* v_00_u03b1_5407_, lean_object* v_x_5408_, uint8_t v_isExporting_5409_, lean_object* v___y_5410_, lean_object* v___y_5411_){
_start:
{
lean_object* v___x_5413_; 
v___x_5413_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg(v_x_5408_, v_isExporting_5409_, v___y_5410_, v___y_5411_);
return v___x_5413_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___boxed(lean_object* v_00_u03b1_5414_, lean_object* v_x_5415_, lean_object* v_isExporting_5416_, lean_object* v___y_5417_, lean_object* v___y_5418_, lean_object* v___y_5419_){
_start:
{
uint8_t v_isExporting_boxed_5420_; lean_object* v_res_5421_; 
v_isExporting_boxed_5420_ = lean_unbox(v_isExporting_5416_);
v_res_5421_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2(v_00_u03b1_5414_, v_x_5415_, v_isExporting_boxed_5420_, v___y_5417_, v___y_5418_);
lean_dec(v___y_5418_);
lean_dec_ref(v___y_5417_);
return v_res_5421_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2(lean_object* v_00_u03b1_5422_, lean_object* v_x_5423_, uint8_t v_when_5424_, lean_object* v___y_5425_, lean_object* v___y_5426_){
_start:
{
lean_object* v___x_5428_; 
v___x_5428_ = l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg(v_x_5423_, v_when_5424_, v___y_5425_, v___y_5426_);
return v___x_5428_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___boxed(lean_object* v_00_u03b1_5429_, lean_object* v_x_5430_, lean_object* v_when_5431_, lean_object* v___y_5432_, lean_object* v___y_5433_, lean_object* v___y_5434_){
_start:
{
uint8_t v_when_boxed_5435_; lean_object* v_res_5436_; 
v_when_boxed_5435_ = lean_unbox(v_when_5431_);
v_res_5436_ = l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2(v_00_u03b1_5429_, v_x_5430_, v_when_boxed_5435_, v___y_5432_, v___y_5433_);
lean_dec(v___y_5433_);
lean_dec_ref(v___y_5432_);
return v_res_5436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___lam__0(lean_object* v_x_5437_, lean_object* v___y_5438_, lean_object* v___y_5439_){
_start:
{
lean_object* v___x_5441_; lean_object* v___x_5442_; 
v___x_5441_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_5442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5442_, 0, v___x_5441_);
return v___x_5442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___lam__0___boxed(lean_object* v_x_5443_, lean_object* v___y_5444_, lean_object* v___y_5445_, lean_object* v___y_5446_){
_start:
{
lean_object* v_res_5447_; 
v_res_5447_ = l_Lean_Meta_eraseInaccessibleAnnotations___lam__0(v_x_5443_, v___y_5444_, v___y_5445_);
lean_dec(v___y_5445_);
lean_dec_ref(v___y_5444_);
lean_dec_ref(v_x_5443_);
return v_res_5447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___lam__1(lean_object* v_e_5448_, lean_object* v___y_5449_, lean_object* v___y_5450_){
_start:
{
lean_object* v___y_5453_; lean_object* v___x_5456_; 
v___x_5456_ = l_Lean_inaccessible_x3f(v_e_5448_);
if (lean_obj_tag(v___x_5456_) == 1)
{
lean_object* v_val_5457_; 
lean_dec_ref(v_e_5448_);
v_val_5457_ = lean_ctor_get(v___x_5456_, 0);
lean_inc(v_val_5457_);
lean_dec_ref_known(v___x_5456_, 1);
v___y_5453_ = v_val_5457_;
goto v___jp_5452_;
}
else
{
lean_dec(v___x_5456_);
v___y_5453_ = v_e_5448_;
goto v___jp_5452_;
}
v___jp_5452_:
{
lean_object* v___x_5454_; lean_object* v___x_5455_; 
v___x_5454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5454_, 0, v___y_5453_);
v___x_5455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5455_, 0, v___x_5454_);
return v___x_5455_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___lam__1___boxed(lean_object* v_e_5458_, lean_object* v___y_5459_, lean_object* v___y_5460_, lean_object* v___y_5461_){
_start:
{
lean_object* v_res_5462_; 
v_res_5462_ = l_Lean_Meta_eraseInaccessibleAnnotations___lam__1(v_e_5458_, v___y_5459_, v___y_5460_);
lean_dec(v___y_5460_);
lean_dec_ref(v___y_5459_);
return v_res_5462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations(lean_object* v_e_5465_, lean_object* v_a_5466_, lean_object* v_a_5467_){
_start:
{
lean_object* v___f_5469_; lean_object* v___f_5470_; lean_object* v___x_5471_; 
v___f_5469_ = ((lean_object*)(l_Lean_Meta_eraseInaccessibleAnnotations___closed__0));
v___f_5470_ = ((lean_object*)(l_Lean_Meta_eraseInaccessibleAnnotations___closed__1));
v___x_5471_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_5465_, v___f_5469_, v___f_5470_, v_a_5466_, v_a_5467_);
return v___x_5471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___boxed(lean_object* v_e_5472_, lean_object* v_a_5473_, lean_object* v_a_5474_, lean_object* v_a_5475_){
_start:
{
lean_object* v_res_5476_; 
v_res_5476_ = l_Lean_Meta_eraseInaccessibleAnnotations(v_e_5472_, v_a_5473_, v_a_5474_);
lean_dec(v_a_5474_);
lean_dec_ref(v_a_5473_);
return v_res_5476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_erasePatternRefAnnotations___lam__1(lean_object* v_e_5477_, lean_object* v___y_5478_, lean_object* v___y_5479_){
_start:
{
lean_object* v___y_5482_; lean_object* v___x_5485_; 
v___x_5485_ = l_Lean_patternWithRef_x3f(v_e_5477_);
if (lean_obj_tag(v___x_5485_) == 1)
{
lean_object* v_val_5486_; lean_object* v_snd_5487_; 
lean_dec_ref(v_e_5477_);
v_val_5486_ = lean_ctor_get(v___x_5485_, 0);
lean_inc(v_val_5486_);
lean_dec_ref_known(v___x_5485_, 1);
v_snd_5487_ = lean_ctor_get(v_val_5486_, 1);
lean_inc(v_snd_5487_);
lean_dec(v_val_5486_);
v___y_5482_ = v_snd_5487_;
goto v___jp_5481_;
}
else
{
lean_dec(v___x_5485_);
v___y_5482_ = v_e_5477_;
goto v___jp_5481_;
}
v___jp_5481_:
{
lean_object* v___x_5483_; lean_object* v___x_5484_; 
v___x_5483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5483_, 0, v___y_5482_);
v___x_5484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5484_, 0, v___x_5483_);
return v___x_5484_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_erasePatternRefAnnotations___lam__1___boxed(lean_object* v_e_5488_, lean_object* v___y_5489_, lean_object* v___y_5490_, lean_object* v___y_5491_){
_start:
{
lean_object* v_res_5492_; 
v_res_5492_ = l_Lean_Meta_erasePatternRefAnnotations___lam__1(v_e_5488_, v___y_5489_, v___y_5490_);
lean_dec(v___y_5490_);
lean_dec_ref(v___y_5489_);
return v_res_5492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_erasePatternRefAnnotations(lean_object* v_e_5494_, lean_object* v_a_5495_, lean_object* v_a_5496_){
_start:
{
lean_object* v___f_5498_; lean_object* v___f_5499_; lean_object* v___x_5500_; 
v___f_5498_ = ((lean_object*)(l_Lean_Meta_eraseInaccessibleAnnotations___closed__0));
v___f_5499_ = ((lean_object*)(l_Lean_Meta_erasePatternRefAnnotations___closed__0));
v___x_5500_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_5494_, v___f_5498_, v___f_5499_, v_a_5495_, v_a_5496_);
return v___x_5500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_erasePatternRefAnnotations___boxed(lean_object* v_e_5501_, lean_object* v_a_5502_, lean_object* v_a_5503_, lean_object* v_a_5504_){
_start:
{
lean_object* v_res_5505_; 
v_res_5505_ = l_Lean_Meta_erasePatternRefAnnotations(v_e_5501_, v_a_5502_, v_a_5503_);
lean_dec(v_a_5503_);
lean_dec_ref(v_a_5502_);
return v_res_5505_;
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
