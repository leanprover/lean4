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
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
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
lean_object* v___y_1099_; lean_object* v___y_1109_; uint8_t v___y_1110_; lean_object* v___y_1111_; lean_object* v___y_1112_; lean_object* v___y_1113_; lean_object* v___y_1114_; lean_object* v___y_1115_; lean_object* v___y_1116_; lean_object* v___y_1117_; lean_object* v___y_1118_; uint8_t v___y_1119_; lean_object* v___y_1120_; lean_object* v___y_1121_; lean_object* v___y_1122_; lean_object* v___y_1123_; lean_object* v___y_1124_; uint8_t v___y_1125_; lean_object* v_fileName_1131_; lean_object* v_fileMap_1132_; lean_object* v_options_1133_; lean_object* v_currRecDepth_1134_; lean_object* v_maxRecDepth_1135_; lean_object* v_ref_1136_; lean_object* v_currNamespace_1137_; lean_object* v_openDecls_1138_; lean_object* v_initHeartbeats_1139_; lean_object* v_maxHeartbeats_1140_; lean_object* v_quotContext_1141_; lean_object* v_currMacroScope_1142_; uint8_t v_diag_1143_; lean_object* v_cancelTk_x3f_1144_; uint8_t v_suppressElabErrors_1145_; lean_object* v_inheritedTraceOptions_1146_; 
v_fileName_1131_ = lean_ctor_get(v___y_1095_, 0);
v_fileMap_1132_ = lean_ctor_get(v___y_1095_, 1);
v_options_1133_ = lean_ctor_get(v___y_1095_, 2);
v_currRecDepth_1134_ = lean_ctor_get(v___y_1095_, 3);
v_maxRecDepth_1135_ = lean_ctor_get(v___y_1095_, 4);
v_ref_1136_ = lean_ctor_get(v___y_1095_, 5);
v_currNamespace_1137_ = lean_ctor_get(v___y_1095_, 6);
v_openDecls_1138_ = lean_ctor_get(v___y_1095_, 7);
v_initHeartbeats_1139_ = lean_ctor_get(v___y_1095_, 8);
v_maxHeartbeats_1140_ = lean_ctor_get(v___y_1095_, 9);
v_quotContext_1141_ = lean_ctor_get(v___y_1095_, 10);
v_currMacroScope_1142_ = lean_ctor_get(v___y_1095_, 11);
v_diag_1143_ = lean_ctor_get_uint8(v___y_1095_, sizeof(void*)*14);
v_cancelTk_x3f_1144_ = lean_ctor_get(v___y_1095_, 12);
v_suppressElabErrors_1145_ = lean_ctor_get_uint8(v___y_1095_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1146_ = lean_ctor_get(v___y_1095_, 13);
if (lean_obj_tag(v_cancelTk_x3f_1144_) == 1)
{
lean_object* v_val_1152_; uint8_t v___x_1153_; 
v_val_1152_ = lean_ctor_get(v_cancelTk_x3f_1144_, 0);
v___x_1153_ = l_IO_CancelToken_isSet(v_val_1152_);
if (v___x_1153_ == 0)
{
goto v___jp_1147_;
}
else
{
lean_object* v___x_1154_; lean_object* v_a_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1162_; 
lean_dec_ref(v_x_1093_);
v___x_1154_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___redArg();
v_a_1155_ = lean_ctor_get(v___x_1154_, 0);
v_isSharedCheck_1162_ = !lean_is_exclusive(v___x_1154_);
if (v_isSharedCheck_1162_ == 0)
{
v___x_1157_ = v___x_1154_;
v_isShared_1158_ = v_isSharedCheck_1162_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_a_1155_);
lean_dec(v___x_1154_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1162_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v___x_1160_; 
if (v_isShared_1158_ == 0)
{
v___x_1160_ = v___x_1157_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v_a_1155_);
v___x_1160_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
return v___x_1160_;
}
}
}
}
else
{
goto v___jp_1147_;
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
if (v___y_1125_ == 0)
{
lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; 
v___x_1126_ = lean_unsigned_to_nat(1u);
v___x_1127_ = lean_nat_add(v___y_1121_, v___x_1126_);
lean_inc_ref(v___y_1115_);
lean_inc(v___y_1123_);
lean_inc(v___y_1112_);
lean_inc(v___y_1114_);
lean_inc(v___y_1118_);
lean_inc(v___y_1122_);
lean_inc(v___y_1120_);
lean_inc(v___y_1117_);
lean_inc(v___y_1113_);
lean_inc(v___y_1111_);
lean_inc_ref(v___y_1116_);
lean_inc_ref(v___y_1109_);
lean_inc_ref(v___y_1124_);
v___x_1128_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1128_, 0, v___y_1124_);
lean_ctor_set(v___x_1128_, 1, v___y_1109_);
lean_ctor_set(v___x_1128_, 2, v___y_1116_);
lean_ctor_set(v___x_1128_, 3, v___x_1127_);
lean_ctor_set(v___x_1128_, 4, v___y_1111_);
lean_ctor_set(v___x_1128_, 5, v___y_1113_);
lean_ctor_set(v___x_1128_, 6, v___y_1117_);
lean_ctor_set(v___x_1128_, 7, v___y_1120_);
lean_ctor_set(v___x_1128_, 8, v___y_1122_);
lean_ctor_set(v___x_1128_, 9, v___y_1118_);
lean_ctor_set(v___x_1128_, 10, v___y_1114_);
lean_ctor_set(v___x_1128_, 11, v___y_1112_);
lean_ctor_set(v___x_1128_, 12, v___y_1123_);
lean_ctor_set(v___x_1128_, 13, v___y_1115_);
lean_ctor_set_uint8(v___x_1128_, sizeof(void*)*14, v___y_1110_);
lean_ctor_set_uint8(v___x_1128_, sizeof(void*)*14 + 1, v___y_1119_);
lean_inc(v___y_1096_);
lean_inc(v___y_1094_);
v___x_1129_ = lean_apply_4(v_x_1093_, v___y_1094_, v___x_1128_, v___y_1096_, lean_box(0));
v___y_1099_ = v___x_1129_;
goto v___jp_1098_;
}
else
{
lean_object* v___x_1130_; 
lean_dec_ref(v_x_1093_);
lean_inc(v___y_1113_);
v___x_1130_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg(v___y_1113_);
v___y_1099_ = v___x_1130_;
goto v___jp_1098_;
}
}
v___jp_1147_:
{
lean_object* v___x_1148_; uint8_t v___x_1149_; uint8_t v___x_1150_; 
v___x_1148_ = lean_unsigned_to_nat(0u);
v___x_1149_ = lean_nat_dec_eq(v_maxRecDepth_1135_, v___x_1148_);
v___x_1150_ = lean_bool_not(v___x_1149_);
if (v___x_1150_ == 0)
{
v___y_1109_ = v_fileMap_1132_;
v___y_1110_ = v_diag_1143_;
v___y_1111_ = v_maxRecDepth_1135_;
v___y_1112_ = v_currMacroScope_1142_;
v___y_1113_ = v_ref_1136_;
v___y_1114_ = v_quotContext_1141_;
v___y_1115_ = v_inheritedTraceOptions_1146_;
v___y_1116_ = v_options_1133_;
v___y_1117_ = v_currNamespace_1137_;
v___y_1118_ = v_maxHeartbeats_1140_;
v___y_1119_ = v_suppressElabErrors_1145_;
v___y_1120_ = v_openDecls_1138_;
v___y_1121_ = v_currRecDepth_1134_;
v___y_1122_ = v_initHeartbeats_1139_;
v___y_1123_ = v_cancelTk_x3f_1144_;
v___y_1124_ = v_fileName_1131_;
v___y_1125_ = v___x_1150_;
goto v___jp_1108_;
}
else
{
uint8_t v___x_1151_; 
v___x_1151_ = lean_nat_dec_eq(v_currRecDepth_1134_, v_maxRecDepth_1135_);
v___y_1109_ = v_fileMap_1132_;
v___y_1110_ = v_diag_1143_;
v___y_1111_ = v_maxRecDepth_1135_;
v___y_1112_ = v_currMacroScope_1142_;
v___y_1113_ = v_ref_1136_;
v___y_1114_ = v_quotContext_1141_;
v___y_1115_ = v_inheritedTraceOptions_1146_;
v___y_1116_ = v_options_1133_;
v___y_1117_ = v_currNamespace_1137_;
v___y_1118_ = v_maxHeartbeats_1140_;
v___y_1119_ = v_suppressElabErrors_1145_;
v___y_1120_ = v_openDecls_1138_;
v___y_1121_ = v_currRecDepth_1134_;
v___y_1122_ = v_initHeartbeats_1139_;
v___y_1123_ = v_cancelTk_x3f_1144_;
v___y_1124_ = v_fileName_1131_;
v___y_1125_ = v___x_1151_;
goto v___jp_1108_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___redArg___boxed(lean_object* v_x_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_){
_start:
{
lean_object* v_res_1168_; 
v_res_1168_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___redArg(v_x_1163_, v___y_1164_, v___y_1165_, v___y_1166_);
lean_dec(v___y_1166_);
lean_dec_ref(v___y_1165_);
lean_dec(v___y_1164_);
return v_res_1168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_1169_, lean_object* v_x_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_){
_start:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; 
v___x_1174_ = lean_apply_1(v_x_1170_, lean_box(0));
v___x_1175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1175_, 0, v___x_1174_);
return v___x_1175_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_1176_, lean_object* v_x_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_){
_start:
{
lean_object* v_res_1181_; 
v_res_1181_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__0(v_00_u03b1_1176_, v_x_1177_, v___y_1178_, v___y_1179_);
lean_dec(v___y_1179_);
lean_dec_ref(v___y_1178_);
return v_res_1181_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___redArg(lean_object* v_a_1182_, lean_object* v_x_1183_){
_start:
{
if (lean_obj_tag(v_x_1183_) == 0)
{
uint8_t v___x_1184_; 
v___x_1184_ = 0;
return v___x_1184_;
}
else
{
lean_object* v_key_1185_; lean_object* v_tail_1186_; uint8_t v___x_1187_; 
v_key_1185_ = lean_ctor_get(v_x_1183_, 0);
v_tail_1186_ = lean_ctor_get(v_x_1183_, 2);
v___x_1187_ = l_Lean_ExprStructEq_beq(v_key_1185_, v_a_1182_);
if (v___x_1187_ == 0)
{
v_x_1183_ = v_tail_1186_;
goto _start;
}
else
{
return v___x_1187_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___redArg___boxed(lean_object* v_a_1189_, lean_object* v_x_1190_){
_start:
{
uint8_t v_res_1191_; lean_object* v_r_1192_; 
v_res_1191_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___redArg(v_a_1189_, v_x_1190_);
lean_dec(v_x_1190_);
lean_dec_ref(v_a_1189_);
v_r_1192_ = lean_box(v_res_1191_);
return v_r_1192_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(lean_object* v_x_1193_, lean_object* v_x_1194_){
_start:
{
if (lean_obj_tag(v_x_1194_) == 0)
{
return v_x_1193_;
}
else
{
lean_object* v_key_1195_; lean_object* v_value_1196_; lean_object* v_tail_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1220_; 
v_key_1195_ = lean_ctor_get(v_x_1194_, 0);
v_value_1196_ = lean_ctor_get(v_x_1194_, 1);
v_tail_1197_ = lean_ctor_get(v_x_1194_, 2);
v_isSharedCheck_1220_ = !lean_is_exclusive(v_x_1194_);
if (v_isSharedCheck_1220_ == 0)
{
v___x_1199_ = v_x_1194_;
v_isShared_1200_ = v_isSharedCheck_1220_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_tail_1197_);
lean_inc(v_value_1196_);
lean_inc(v_key_1195_);
lean_dec(v_x_1194_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1220_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v___x_1201_; uint64_t v___x_1202_; uint64_t v___x_1203_; uint64_t v___x_1204_; uint64_t v_fold_1205_; uint64_t v___x_1206_; uint64_t v___x_1207_; uint64_t v___x_1208_; size_t v___x_1209_; size_t v___x_1210_; size_t v___x_1211_; size_t v___x_1212_; size_t v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1216_; 
v___x_1201_ = lean_array_get_size(v_x_1193_);
v___x_1202_ = l_Lean_ExprStructEq_hash(v_key_1195_);
v___x_1203_ = 32ULL;
v___x_1204_ = lean_uint64_shift_right(v___x_1202_, v___x_1203_);
v_fold_1205_ = lean_uint64_xor(v___x_1202_, v___x_1204_);
v___x_1206_ = 16ULL;
v___x_1207_ = lean_uint64_shift_right(v_fold_1205_, v___x_1206_);
v___x_1208_ = lean_uint64_xor(v_fold_1205_, v___x_1207_);
v___x_1209_ = lean_uint64_to_usize(v___x_1208_);
v___x_1210_ = lean_usize_of_nat(v___x_1201_);
v___x_1211_ = ((size_t)1ULL);
v___x_1212_ = lean_usize_sub(v___x_1210_, v___x_1211_);
v___x_1213_ = lean_usize_land(v___x_1209_, v___x_1212_);
v___x_1214_ = lean_array_uget_borrowed(v_x_1193_, v___x_1213_);
lean_inc(v___x_1214_);
if (v_isShared_1200_ == 0)
{
lean_ctor_set(v___x_1199_, 2, v___x_1214_);
v___x_1216_ = v___x_1199_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v_key_1195_);
lean_ctor_set(v_reuseFailAlloc_1219_, 1, v_value_1196_);
lean_ctor_set(v_reuseFailAlloc_1219_, 2, v___x_1214_);
v___x_1216_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
lean_object* v___x_1217_; 
v___x_1217_ = lean_array_uset(v_x_1193_, v___x_1213_, v___x_1216_);
v_x_1193_ = v___x_1217_;
v_x_1194_ = v_tail_1197_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(lean_object* v_i_1221_, lean_object* v_source_1222_, lean_object* v_target_1223_){
_start:
{
lean_object* v___x_1224_; uint8_t v___x_1225_; 
v___x_1224_ = lean_array_get_size(v_source_1222_);
v___x_1225_ = lean_nat_dec_lt(v_i_1221_, v___x_1224_);
if (v___x_1225_ == 0)
{
lean_dec_ref(v_source_1222_);
lean_dec(v_i_1221_);
return v_target_1223_;
}
else
{
lean_object* v_es_1226_; lean_object* v___x_1227_; lean_object* v_source_1228_; lean_object* v_target_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; 
v_es_1226_ = lean_array_fget(v_source_1222_, v_i_1221_);
v___x_1227_ = lean_box(0);
v_source_1228_ = lean_array_fset(v_source_1222_, v_i_1221_, v___x_1227_);
v_target_1229_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_target_1223_, v_es_1226_);
v___x_1230_ = lean_unsigned_to_nat(1u);
v___x_1231_ = lean_nat_add(v_i_1221_, v___x_1230_);
lean_dec(v_i_1221_);
v_i_1221_ = v___x_1231_;
v_source_1222_ = v_source_1228_;
v_target_1223_ = v_target_1229_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11___redArg(lean_object* v_data_1233_){
_start:
{
lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v_nbuckets_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___x_1234_ = lean_array_get_size(v_data_1233_);
v___x_1235_ = lean_unsigned_to_nat(2u);
v_nbuckets_1236_ = lean_nat_mul(v___x_1234_, v___x_1235_);
v___x_1237_ = lean_unsigned_to_nat(0u);
v___x_1238_ = lean_box(0);
v___x_1239_ = lean_mk_array(v_nbuckets_1236_, v___x_1238_);
v___x_1240_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v___x_1237_, v_data_1233_, v___x_1239_);
return v___x_1240_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__12___redArg(lean_object* v_a_1241_, lean_object* v_b_1242_, lean_object* v_x_1243_){
_start:
{
if (lean_obj_tag(v_x_1243_) == 0)
{
lean_dec(v_b_1242_);
lean_dec_ref(v_a_1241_);
return v_x_1243_;
}
else
{
lean_object* v_key_1244_; lean_object* v_value_1245_; lean_object* v_tail_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1258_; 
v_key_1244_ = lean_ctor_get(v_x_1243_, 0);
v_value_1245_ = lean_ctor_get(v_x_1243_, 1);
v_tail_1246_ = lean_ctor_get(v_x_1243_, 2);
v_isSharedCheck_1258_ = !lean_is_exclusive(v_x_1243_);
if (v_isSharedCheck_1258_ == 0)
{
v___x_1248_ = v_x_1243_;
v_isShared_1249_ = v_isSharedCheck_1258_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_tail_1246_);
lean_inc(v_value_1245_);
lean_inc(v_key_1244_);
lean_dec(v_x_1243_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1258_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
uint8_t v___x_1250_; 
v___x_1250_ = l_Lean_ExprStructEq_beq(v_key_1244_, v_a_1241_);
if (v___x_1250_ == 0)
{
lean_object* v___x_1251_; lean_object* v___x_1253_; 
v___x_1251_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__12___redArg(v_a_1241_, v_b_1242_, v_tail_1246_);
if (v_isShared_1249_ == 0)
{
lean_ctor_set(v___x_1248_, 2, v___x_1251_);
v___x_1253_ = v___x_1248_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_key_1244_);
lean_ctor_set(v_reuseFailAlloc_1254_, 1, v_value_1245_);
lean_ctor_set(v_reuseFailAlloc_1254_, 2, v___x_1251_);
v___x_1253_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
return v___x_1253_;
}
}
else
{
lean_object* v___x_1256_; 
lean_dec(v_value_1245_);
lean_dec(v_key_1244_);
if (v_isShared_1249_ == 0)
{
lean_ctor_set(v___x_1248_, 1, v_b_1242_);
lean_ctor_set(v___x_1248_, 0, v_a_1241_);
v___x_1256_ = v___x_1248_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v_a_1241_);
lean_ctor_set(v_reuseFailAlloc_1257_, 1, v_b_1242_);
lean_ctor_set(v_reuseFailAlloc_1257_, 2, v_tail_1246_);
v___x_1256_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
return v___x_1256_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6___redArg(lean_object* v_m_1259_, lean_object* v_a_1260_, lean_object* v_b_1261_){
_start:
{
lean_object* v_size_1262_; lean_object* v_buckets_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1306_; 
v_size_1262_ = lean_ctor_get(v_m_1259_, 0);
v_buckets_1263_ = lean_ctor_get(v_m_1259_, 1);
v_isSharedCheck_1306_ = !lean_is_exclusive(v_m_1259_);
if (v_isSharedCheck_1306_ == 0)
{
v___x_1265_ = v_m_1259_;
v_isShared_1266_ = v_isSharedCheck_1306_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_buckets_1263_);
lean_inc(v_size_1262_);
lean_dec(v_m_1259_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1306_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v___x_1267_; uint64_t v___x_1268_; uint64_t v___x_1269_; uint64_t v___x_1270_; uint64_t v_fold_1271_; uint64_t v___x_1272_; uint64_t v___x_1273_; uint64_t v___x_1274_; size_t v___x_1275_; size_t v___x_1276_; size_t v___x_1277_; size_t v___x_1278_; size_t v___x_1279_; lean_object* v_bkt_1280_; uint8_t v___x_1281_; 
v___x_1267_ = lean_array_get_size(v_buckets_1263_);
v___x_1268_ = l_Lean_ExprStructEq_hash(v_a_1260_);
v___x_1269_ = 32ULL;
v___x_1270_ = lean_uint64_shift_right(v___x_1268_, v___x_1269_);
v_fold_1271_ = lean_uint64_xor(v___x_1268_, v___x_1270_);
v___x_1272_ = 16ULL;
v___x_1273_ = lean_uint64_shift_right(v_fold_1271_, v___x_1272_);
v___x_1274_ = lean_uint64_xor(v_fold_1271_, v___x_1273_);
v___x_1275_ = lean_uint64_to_usize(v___x_1274_);
v___x_1276_ = lean_usize_of_nat(v___x_1267_);
v___x_1277_ = ((size_t)1ULL);
v___x_1278_ = lean_usize_sub(v___x_1276_, v___x_1277_);
v___x_1279_ = lean_usize_land(v___x_1275_, v___x_1278_);
v_bkt_1280_ = lean_array_uget_borrowed(v_buckets_1263_, v___x_1279_);
v___x_1281_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___redArg(v_a_1260_, v_bkt_1280_);
if (v___x_1281_ == 0)
{
lean_object* v___x_1282_; lean_object* v_size_x27_1283_; lean_object* v___x_1284_; lean_object* v_buckets_x27_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; uint8_t v___x_1291_; 
v___x_1282_ = lean_unsigned_to_nat(1u);
v_size_x27_1283_ = lean_nat_add(v_size_1262_, v___x_1282_);
lean_dec(v_size_1262_);
lean_inc(v_bkt_1280_);
v___x_1284_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1284_, 0, v_a_1260_);
lean_ctor_set(v___x_1284_, 1, v_b_1261_);
lean_ctor_set(v___x_1284_, 2, v_bkt_1280_);
v_buckets_x27_1285_ = lean_array_uset(v_buckets_1263_, v___x_1279_, v___x_1284_);
v___x_1286_ = lean_unsigned_to_nat(4u);
v___x_1287_ = lean_nat_mul(v_size_x27_1283_, v___x_1286_);
v___x_1288_ = lean_unsigned_to_nat(3u);
v___x_1289_ = lean_nat_div(v___x_1287_, v___x_1288_);
lean_dec(v___x_1287_);
v___x_1290_ = lean_array_get_size(v_buckets_x27_1285_);
v___x_1291_ = lean_nat_dec_le(v___x_1289_, v___x_1290_);
lean_dec(v___x_1289_);
if (v___x_1291_ == 0)
{
lean_object* v_val_1292_; lean_object* v___x_1294_; 
v_val_1292_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11___redArg(v_buckets_x27_1285_);
if (v_isShared_1266_ == 0)
{
lean_ctor_set(v___x_1265_, 1, v_val_1292_);
lean_ctor_set(v___x_1265_, 0, v_size_x27_1283_);
v___x_1294_ = v___x_1265_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_size_x27_1283_);
lean_ctor_set(v_reuseFailAlloc_1295_, 1, v_val_1292_);
v___x_1294_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
return v___x_1294_;
}
}
else
{
lean_object* v___x_1297_; 
if (v_isShared_1266_ == 0)
{
lean_ctor_set(v___x_1265_, 1, v_buckets_x27_1285_);
lean_ctor_set(v___x_1265_, 0, v_size_x27_1283_);
v___x_1297_ = v___x_1265_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v_size_x27_1283_);
lean_ctor_set(v_reuseFailAlloc_1298_, 1, v_buckets_x27_1285_);
v___x_1297_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
return v___x_1297_;
}
}
}
else
{
lean_object* v___x_1299_; lean_object* v_buckets_x27_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1304_; 
lean_inc(v_bkt_1280_);
v___x_1299_ = lean_box(0);
v_buckets_x27_1300_ = lean_array_uset(v_buckets_1263_, v___x_1279_, v___x_1299_);
v___x_1301_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__12___redArg(v_a_1260_, v_b_1261_, v_bkt_1280_);
v___x_1302_ = lean_array_uset(v_buckets_x27_1300_, v___x_1279_, v___x_1301_);
if (v_isShared_1266_ == 0)
{
lean_ctor_set(v___x_1265_, 1, v___x_1302_);
v___x_1304_ = v___x_1265_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v_size_1262_);
lean_ctor_set(v_reuseFailAlloc_1305_, 1, v___x_1302_);
v___x_1304_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
return v___x_1304_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__2(lean_object* v_a_1307_, lean_object* v_e_1308_, lean_object* v_a_1309_){
_start:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; 
v___x_1311_ = lean_st_ref_take(v_a_1307_);
v___x_1312_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6___redArg(v___x_1311_, v_e_1308_, v_a_1309_);
v___x_1313_ = lean_st_ref_set(v_a_1307_, v___x_1312_);
v___x_1314_ = lean_box(0);
return v___x_1314_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__2___boxed(lean_object* v_a_1315_, lean_object* v_e_1316_, lean_object* v_a_1317_, lean_object* v___y_1318_){
_start:
{
lean_object* v_res_1319_; 
v_res_1319_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__2(v_a_1315_, v_e_1316_, v_a_1317_);
lean_dec(v_a_1315_);
return v_res_1319_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___redArg(lean_object* v_a_1320_, lean_object* v_x_1321_){
_start:
{
if (lean_obj_tag(v_x_1321_) == 0)
{
lean_object* v___x_1322_; 
v___x_1322_ = lean_box(0);
return v___x_1322_;
}
else
{
lean_object* v_key_1323_; lean_object* v_value_1324_; lean_object* v_tail_1325_; uint8_t v___x_1326_; 
v_key_1323_ = lean_ctor_get(v_x_1321_, 0);
v_value_1324_ = lean_ctor_get(v_x_1321_, 1);
v_tail_1325_ = lean_ctor_get(v_x_1321_, 2);
v___x_1326_ = l_Lean_ExprStructEq_beq(v_key_1323_, v_a_1320_);
if (v___x_1326_ == 0)
{
v_x_1321_ = v_tail_1325_;
goto _start;
}
else
{
lean_object* v___x_1328_; 
lean_inc(v_value_1324_);
v___x_1328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1328_, 0, v_value_1324_);
return v___x_1328_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___redArg___boxed(lean_object* v_a_1329_, lean_object* v_x_1330_){
_start:
{
lean_object* v_res_1331_; 
v_res_1331_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___redArg(v_a_1329_, v_x_1330_);
lean_dec(v_x_1330_);
lean_dec_ref(v_a_1329_);
return v_res_1331_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg(lean_object* v_m_1332_, lean_object* v_a_1333_){
_start:
{
lean_object* v_buckets_1334_; lean_object* v___x_1335_; uint64_t v___x_1336_; uint64_t v___x_1337_; uint64_t v___x_1338_; uint64_t v_fold_1339_; uint64_t v___x_1340_; uint64_t v___x_1341_; uint64_t v___x_1342_; size_t v___x_1343_; size_t v___x_1344_; size_t v___x_1345_; size_t v___x_1346_; size_t v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; 
v_buckets_1334_ = lean_ctor_get(v_m_1332_, 1);
v___x_1335_ = lean_array_get_size(v_buckets_1334_);
v___x_1336_ = l_Lean_ExprStructEq_hash(v_a_1333_);
v___x_1337_ = 32ULL;
v___x_1338_ = lean_uint64_shift_right(v___x_1336_, v___x_1337_);
v_fold_1339_ = lean_uint64_xor(v___x_1336_, v___x_1338_);
v___x_1340_ = 16ULL;
v___x_1341_ = lean_uint64_shift_right(v_fold_1339_, v___x_1340_);
v___x_1342_ = lean_uint64_xor(v_fold_1339_, v___x_1341_);
v___x_1343_ = lean_uint64_to_usize(v___x_1342_);
v___x_1344_ = lean_usize_of_nat(v___x_1335_);
v___x_1345_ = ((size_t)1ULL);
v___x_1346_ = lean_usize_sub(v___x_1344_, v___x_1345_);
v___x_1347_ = lean_usize_land(v___x_1343_, v___x_1346_);
v___x_1348_ = lean_array_uget_borrowed(v_buckets_1334_, v___x_1347_);
v___x_1349_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___redArg(v_a_1333_, v___x_1348_);
return v___x_1349_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_m_1350_, lean_object* v_a_1351_){
_start:
{
lean_object* v_res_1352_; 
v_res_1352_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg(v_m_1350_, v_a_1351_);
lean_dec_ref(v_a_1351_);
lean_dec_ref(v_m_1350_);
return v_res_1352_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1(lean_object* v_pre_1353_, lean_object* v_post_1354_, size_t v_sz_1355_, size_t v_i_1356_, lean_object* v_bs_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_){
_start:
{
uint8_t v___x_1362_; 
v___x_1362_ = lean_usize_dec_lt(v_i_1356_, v_sz_1355_);
if (v___x_1362_ == 0)
{
lean_object* v___x_1363_; 
lean_dec_ref(v_post_1354_);
lean_dec_ref(v_pre_1353_);
v___x_1363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1363_, 0, v_bs_1357_);
return v___x_1363_;
}
else
{
lean_object* v_v_1364_; lean_object* v___x_1365_; 
v_v_1364_ = lean_array_uget_borrowed(v_bs_1357_, v_i_1356_);
lean_inc(v_v_1364_);
lean_inc_ref(v_post_1354_);
lean_inc_ref(v_pre_1353_);
v___x_1365_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1353_, v_post_1354_, v_v_1364_, v___y_1358_, v___y_1359_, v___y_1360_);
if (lean_obj_tag(v___x_1365_) == 0)
{
lean_object* v_a_1366_; lean_object* v___x_1367_; lean_object* v_bs_x27_1368_; size_t v___x_1369_; size_t v___x_1370_; lean_object* v___x_1371_; 
v_a_1366_ = lean_ctor_get(v___x_1365_, 0);
lean_inc(v_a_1366_);
lean_dec_ref_known(v___x_1365_, 1);
v___x_1367_ = lean_unsigned_to_nat(0u);
v_bs_x27_1368_ = lean_array_uset(v_bs_1357_, v_i_1356_, v___x_1367_);
v___x_1369_ = ((size_t)1ULL);
v___x_1370_ = lean_usize_add(v_i_1356_, v___x_1369_);
v___x_1371_ = lean_array_uset(v_bs_x27_1368_, v_i_1356_, v_a_1366_);
v_i_1356_ = v___x_1370_;
v_bs_1357_ = v___x_1371_;
goto _start;
}
else
{
lean_object* v_a_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1380_; 
lean_dec_ref(v_bs_1357_);
lean_dec_ref(v_post_1354_);
lean_dec_ref(v_pre_1353_);
v_a_1373_ = lean_ctor_get(v___x_1365_, 0);
v_isSharedCheck_1380_ = !lean_is_exclusive(v___x_1365_);
if (v_isSharedCheck_1380_ == 0)
{
v___x_1375_ = v___x_1365_;
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_a_1373_);
lean_dec(v___x_1365_);
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
v_reuseFailAlloc_1379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v_a_1373_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__4(lean_object* v_pre_1381_, lean_object* v_post_1382_, lean_object* v_x_1383_, lean_object* v_x_1384_, lean_object* v_x_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_){
_start:
{
if (lean_obj_tag(v_x_1383_) == 5)
{
lean_object* v_fn_1390_; lean_object* v_arg_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; 
v_fn_1390_ = lean_ctor_get(v_x_1383_, 0);
lean_inc_ref(v_fn_1390_);
v_arg_1391_ = lean_ctor_get(v_x_1383_, 1);
lean_inc_ref(v_arg_1391_);
lean_dec_ref_known(v_x_1383_, 2);
v___x_1392_ = lean_array_set(v_x_1384_, v_x_1385_, v_arg_1391_);
v___x_1393_ = lean_unsigned_to_nat(1u);
v___x_1394_ = lean_nat_sub(v_x_1385_, v___x_1393_);
lean_dec(v_x_1385_);
v_x_1383_ = v_fn_1390_;
v_x_1384_ = v___x_1392_;
v_x_1385_ = v___x_1394_;
goto _start;
}
else
{
lean_object* v___x_1396_; 
lean_dec(v_x_1385_);
lean_inc_ref(v_post_1382_);
lean_inc_ref(v_pre_1381_);
v___x_1396_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1381_, v_post_1382_, v_x_1383_, v___y_1386_, v___y_1387_, v___y_1388_);
if (lean_obj_tag(v___x_1396_) == 0)
{
lean_object* v_a_1397_; size_t v_sz_1398_; size_t v___x_1399_; lean_object* v___x_1400_; 
v_a_1397_ = lean_ctor_get(v___x_1396_, 0);
lean_inc(v_a_1397_);
lean_dec_ref_known(v___x_1396_, 1);
v_sz_1398_ = lean_array_size(v_x_1384_);
v___x_1399_ = ((size_t)0ULL);
lean_inc_ref(v_post_1382_);
lean_inc_ref(v_pre_1381_);
v___x_1400_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1(v_pre_1381_, v_post_1382_, v_sz_1398_, v___x_1399_, v_x_1384_, v___y_1386_, v___y_1387_, v___y_1388_);
if (lean_obj_tag(v___x_1400_) == 0)
{
lean_object* v_a_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; 
v_a_1401_ = lean_ctor_get(v___x_1400_, 0);
lean_inc(v_a_1401_);
lean_dec_ref_known(v___x_1400_, 1);
v___x_1402_ = l_Lean_mkAppN(v_a_1397_, v_a_1401_);
lean_dec(v_a_1401_);
v___x_1403_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1381_, v_post_1382_, v___x_1402_, v___y_1386_, v___y_1387_, v___y_1388_);
return v___x_1403_;
}
else
{
lean_object* v_a_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1411_; 
lean_dec(v_a_1397_);
lean_dec_ref(v_post_1382_);
lean_dec_ref(v_pre_1381_);
v_a_1404_ = lean_ctor_get(v___x_1400_, 0);
v_isSharedCheck_1411_ = !lean_is_exclusive(v___x_1400_);
if (v_isSharedCheck_1411_ == 0)
{
v___x_1406_ = v___x_1400_;
v_isShared_1407_ = v_isSharedCheck_1411_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_a_1404_);
lean_dec(v___x_1400_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1411_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v___x_1409_; 
if (v_isShared_1407_ == 0)
{
v___x_1409_ = v___x_1406_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v_a_1404_);
v___x_1409_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
return v___x_1409_;
}
}
}
}
else
{
lean_dec_ref(v_x_1384_);
lean_dec_ref(v_post_1382_);
lean_dec_ref(v_pre_1381_);
return v___x_1396_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__1(lean_object* v___x_1412_, lean_object* v_pre_1413_, lean_object* v_e_1414_, lean_object* v_post_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_){
_start:
{
uint8_t v___y_1421_; lean_object* v___y_1422_; lean_object* v___y_1423_; lean_object* v___y_1424_; lean_object* v___y_1425_; lean_object* v___y_1426_; lean_object* v___y_1427_; uint8_t v___y_1428_; uint8_t v___y_1438_; lean_object* v___y_1439_; lean_object* v___y_1440_; lean_object* v___y_1441_; lean_object* v___y_1442_; uint8_t v___y_1443_; lean_object* v___y_1451_; lean_object* v___y_1452_; lean_object* v___y_1453_; lean_object* v___y_1454_; uint8_t v___y_1455_; uint8_t v___y_1456_; lean_object* v___x_1463_; 
v___x_1463_ = l_Lean_Core_checkSystem(v___x_1412_, v___y_1417_, v___y_1418_);
if (lean_obj_tag(v___x_1463_) == 0)
{
lean_object* v___x_1464_; 
lean_dec_ref_known(v___x_1463_, 1);
lean_inc_ref(v_pre_1413_);
lean_inc(v___y_1418_);
lean_inc_ref(v___y_1417_);
lean_inc_ref(v_e_1414_);
v___x_1464_ = lean_apply_4(v_pre_1413_, v_e_1414_, v___y_1417_, v___y_1418_, lean_box(0));
if (lean_obj_tag(v___x_1464_) == 0)
{
lean_object* v_a_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1554_; 
v_a_1465_ = lean_ctor_get(v___x_1464_, 0);
v_isSharedCheck_1554_ = !lean_is_exclusive(v___x_1464_);
if (v_isSharedCheck_1554_ == 0)
{
v___x_1467_ = v___x_1464_;
v_isShared_1468_ = v_isSharedCheck_1554_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_a_1465_);
lean_dec(v___x_1464_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1554_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v___y_1470_; 
switch(lean_obj_tag(v_a_1465_))
{
case 0:
{
lean_object* v_e_1544_; lean_object* v___x_1546_; 
lean_dec_ref(v_post_1415_);
lean_dec_ref(v_e_1414_);
lean_dec_ref(v_pre_1413_);
v_e_1544_ = lean_ctor_get(v_a_1465_, 0);
lean_inc_ref(v_e_1544_);
lean_dec_ref_known(v_a_1465_, 1);
if (v_isShared_1468_ == 0)
{
lean_ctor_set(v___x_1467_, 0, v_e_1544_);
v___x_1546_ = v___x_1467_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v_e_1544_);
v___x_1546_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
return v___x_1546_;
}
}
case 1:
{
lean_object* v_e_1548_; lean_object* v___x_1549_; 
lean_del_object(v___x_1467_);
lean_dec_ref(v_e_1414_);
v_e_1548_ = lean_ctor_get(v_a_1465_, 0);
lean_inc_ref(v_e_1548_);
lean_dec_ref_known(v_a_1465_, 1);
lean_inc_ref(v_post_1415_);
lean_inc_ref(v_pre_1413_);
v___x_1549_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1413_, v_post_1415_, v_e_1548_, v___y_1416_, v___y_1417_, v___y_1418_);
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_object* v_a_1550_; lean_object* v___x_1551_; 
v_a_1550_ = lean_ctor_get(v___x_1549_, 0);
lean_inc(v_a_1550_);
lean_dec_ref_known(v___x_1549_, 1);
v___x_1551_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1413_, v_post_1415_, v_a_1550_, v___y_1416_, v___y_1417_, v___y_1418_);
return v___x_1551_;
}
else
{
lean_dec_ref(v_post_1415_);
lean_dec_ref(v_pre_1413_);
return v___x_1549_;
}
}
default: 
{
lean_object* v_e_x3f_1552_; 
lean_del_object(v___x_1467_);
v_e_x3f_1552_ = lean_ctor_get(v_a_1465_, 0);
lean_inc(v_e_x3f_1552_);
lean_dec_ref_known(v_a_1465_, 1);
if (lean_obj_tag(v_e_x3f_1552_) == 0)
{
v___y_1470_ = v_e_1414_;
goto v___jp_1469_;
}
else
{
lean_object* v_val_1553_; 
lean_dec_ref(v_e_1414_);
v_val_1553_ = lean_ctor_get(v_e_x3f_1552_, 0);
lean_inc(v_val_1553_);
lean_dec_ref_known(v_e_x3f_1552_, 1);
v___y_1470_ = v_val_1553_;
goto v___jp_1469_;
}
}
}
v___jp_1469_:
{
switch(lean_obj_tag(v___y_1470_))
{
case 7:
{
lean_object* v_binderName_1471_; lean_object* v_binderType_1472_; lean_object* v_body_1473_; uint8_t v_binderInfo_1474_; lean_object* v___x_1475_; 
v_binderName_1471_ = lean_ctor_get(v___y_1470_, 0);
lean_inc(v_binderName_1471_);
v_binderType_1472_ = lean_ctor_get(v___y_1470_, 1);
v_body_1473_ = lean_ctor_get(v___y_1470_, 2);
v_binderInfo_1474_ = lean_ctor_get_uint8(v___y_1470_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1472_);
lean_inc_ref(v_post_1415_);
lean_inc_ref(v_pre_1413_);
v___x_1475_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1413_, v_post_1415_, v_binderType_1472_, v___y_1416_, v___y_1417_, v___y_1418_);
if (lean_obj_tag(v___x_1475_) == 0)
{
lean_object* v_a_1476_; lean_object* v___x_1477_; 
v_a_1476_ = lean_ctor_get(v___x_1475_, 0);
lean_inc(v_a_1476_);
lean_dec_ref_known(v___x_1475_, 1);
lean_inc_ref(v_body_1473_);
lean_inc_ref(v_post_1415_);
lean_inc_ref(v_pre_1413_);
v___x_1477_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1413_, v_post_1415_, v_body_1473_, v___y_1416_, v___y_1417_, v___y_1418_);
if (lean_obj_tag(v___x_1477_) == 0)
{
lean_object* v_a_1478_; size_t v___x_1479_; size_t v___x_1480_; uint8_t v___x_1481_; 
v_a_1478_ = lean_ctor_get(v___x_1477_, 0);
lean_inc(v_a_1478_);
lean_dec_ref_known(v___x_1477_, 1);
v___x_1479_ = lean_ptr_addr(v_binderType_1472_);
v___x_1480_ = lean_ptr_addr(v_a_1476_);
v___x_1481_ = lean_usize_dec_eq(v___x_1479_, v___x_1480_);
if (v___x_1481_ == 0)
{
v___y_1451_ = v_binderName_1471_;
v___y_1452_ = v_a_1478_;
v___y_1453_ = v___y_1470_;
v___y_1454_ = v_a_1476_;
v___y_1455_ = v_binderInfo_1474_;
v___y_1456_ = v___x_1481_;
goto v___jp_1450_;
}
else
{
size_t v___x_1482_; size_t v___x_1483_; uint8_t v___x_1484_; 
v___x_1482_ = lean_ptr_addr(v_body_1473_);
v___x_1483_ = lean_ptr_addr(v_a_1478_);
v___x_1484_ = lean_usize_dec_eq(v___x_1482_, v___x_1483_);
v___y_1451_ = v_binderName_1471_;
v___y_1452_ = v_a_1478_;
v___y_1453_ = v___y_1470_;
v___y_1454_ = v_a_1476_;
v___y_1455_ = v_binderInfo_1474_;
v___y_1456_ = v___x_1484_;
goto v___jp_1450_;
}
}
else
{
lean_dec(v_a_1476_);
lean_dec(v_binderName_1471_);
lean_dec_ref_known(v___y_1470_, 3);
lean_dec_ref(v_post_1415_);
lean_dec_ref(v_pre_1413_);
return v___x_1477_;
}
}
else
{
lean_dec(v_binderName_1471_);
lean_dec_ref_known(v___y_1470_, 3);
lean_dec_ref(v_post_1415_);
lean_dec_ref(v_pre_1413_);
return v___x_1475_;
}
}
case 6:
{
lean_object* v_binderName_1485_; lean_object* v_binderType_1486_; lean_object* v_body_1487_; uint8_t v_binderInfo_1488_; lean_object* v___x_1489_; 
v_binderName_1485_ = lean_ctor_get(v___y_1470_, 0);
lean_inc(v_binderName_1485_);
v_binderType_1486_ = lean_ctor_get(v___y_1470_, 1);
v_body_1487_ = lean_ctor_get(v___y_1470_, 2);
v_binderInfo_1488_ = lean_ctor_get_uint8(v___y_1470_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1486_);
lean_inc_ref(v_post_1415_);
lean_inc_ref(v_pre_1413_);
v___x_1489_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1413_, v_post_1415_, v_binderType_1486_, v___y_1416_, v___y_1417_, v___y_1418_);
if (lean_obj_tag(v___x_1489_) == 0)
{
lean_object* v_a_1490_; lean_object* v___x_1491_; 
v_a_1490_ = lean_ctor_get(v___x_1489_, 0);
lean_inc(v_a_1490_);
lean_dec_ref_known(v___x_1489_, 1);
lean_inc_ref(v_body_1487_);
lean_inc_ref(v_post_1415_);
lean_inc_ref(v_pre_1413_);
v___x_1491_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1413_, v_post_1415_, v_body_1487_, v___y_1416_, v___y_1417_, v___y_1418_);
if (lean_obj_tag(v___x_1491_) == 0)
{
lean_object* v_a_1492_; size_t v___x_1493_; size_t v___x_1494_; uint8_t v___x_1495_; 
v_a_1492_ = lean_ctor_get(v___x_1491_, 0);
lean_inc(v_a_1492_);
lean_dec_ref_known(v___x_1491_, 1);
v___x_1493_ = lean_ptr_addr(v_binderType_1486_);
v___x_1494_ = lean_ptr_addr(v_a_1490_);
v___x_1495_ = lean_usize_dec_eq(v___x_1493_, v___x_1494_);
if (v___x_1495_ == 0)
{
v___y_1438_ = v_binderInfo_1488_;
v___y_1439_ = v_a_1492_;
v___y_1440_ = v___y_1470_;
v___y_1441_ = v_binderName_1485_;
v___y_1442_ = v_a_1490_;
v___y_1443_ = v___x_1495_;
goto v___jp_1437_;
}
else
{
size_t v___x_1496_; size_t v___x_1497_; uint8_t v___x_1498_; 
v___x_1496_ = lean_ptr_addr(v_body_1487_);
v___x_1497_ = lean_ptr_addr(v_a_1492_);
v___x_1498_ = lean_usize_dec_eq(v___x_1496_, v___x_1497_);
v___y_1438_ = v_binderInfo_1488_;
v___y_1439_ = v_a_1492_;
v___y_1440_ = v___y_1470_;
v___y_1441_ = v_binderName_1485_;
v___y_1442_ = v_a_1490_;
v___y_1443_ = v___x_1498_;
goto v___jp_1437_;
}
}
else
{
lean_dec(v_a_1490_);
lean_dec_ref_known(v___y_1470_, 3);
lean_dec(v_binderName_1485_);
lean_dec_ref(v_post_1415_);
lean_dec_ref(v_pre_1413_);
return v___x_1491_;
}
}
else
{
lean_dec(v_binderName_1485_);
lean_dec_ref_known(v___y_1470_, 3);
lean_dec_ref(v_post_1415_);
lean_dec_ref(v_pre_1413_);
return v___x_1489_;
}
}
case 8:
{
lean_object* v_declName_1499_; lean_object* v_type_1500_; lean_object* v_value_1501_; lean_object* v_body_1502_; uint8_t v_nondep_1503_; lean_object* v___x_1504_; 
v_declName_1499_ = lean_ctor_get(v___y_1470_, 0);
lean_inc(v_declName_1499_);
v_type_1500_ = lean_ctor_get(v___y_1470_, 1);
v_value_1501_ = lean_ctor_get(v___y_1470_, 2);
v_body_1502_ = lean_ctor_get(v___y_1470_, 3);
lean_inc_ref(v_body_1502_);
v_nondep_1503_ = lean_ctor_get_uint8(v___y_1470_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_1500_);
lean_inc_ref(v_post_1415_);
lean_inc_ref(v_pre_1413_);
v___x_1504_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1413_, v_post_1415_, v_type_1500_, v___y_1416_, v___y_1417_, v___y_1418_);
if (lean_obj_tag(v___x_1504_) == 0)
{
lean_object* v_a_1505_; lean_object* v___x_1506_; 
v_a_1505_ = lean_ctor_get(v___x_1504_, 0);
lean_inc(v_a_1505_);
lean_dec_ref_known(v___x_1504_, 1);
lean_inc_ref(v_value_1501_);
lean_inc_ref(v_post_1415_);
lean_inc_ref(v_pre_1413_);
v___x_1506_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1413_, v_post_1415_, v_value_1501_, v___y_1416_, v___y_1417_, v___y_1418_);
if (lean_obj_tag(v___x_1506_) == 0)
{
lean_object* v_a_1507_; lean_object* v___x_1508_; 
v_a_1507_ = lean_ctor_get(v___x_1506_, 0);
lean_inc(v_a_1507_);
lean_dec_ref_known(v___x_1506_, 1);
lean_inc_ref(v_body_1502_);
lean_inc_ref(v_post_1415_);
lean_inc_ref(v_pre_1413_);
v___x_1508_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1413_, v_post_1415_, v_body_1502_, v___y_1416_, v___y_1417_, v___y_1418_);
if (lean_obj_tag(v___x_1508_) == 0)
{
lean_object* v_a_1509_; size_t v___x_1510_; size_t v___x_1511_; uint8_t v___x_1512_; 
v_a_1509_ = lean_ctor_get(v___x_1508_, 0);
lean_inc(v_a_1509_);
lean_dec_ref_known(v___x_1508_, 1);
v___x_1510_ = lean_ptr_addr(v_type_1500_);
v___x_1511_ = lean_ptr_addr(v_a_1505_);
v___x_1512_ = lean_usize_dec_eq(v___x_1510_, v___x_1511_);
if (v___x_1512_ == 0)
{
v___y_1421_ = v_nondep_1503_;
v___y_1422_ = v_a_1507_;
v___y_1423_ = v_a_1509_;
v___y_1424_ = v_a_1505_;
v___y_1425_ = v___y_1470_;
v___y_1426_ = v_declName_1499_;
v___y_1427_ = v_body_1502_;
v___y_1428_ = v___x_1512_;
goto v___jp_1420_;
}
else
{
size_t v___x_1513_; size_t v___x_1514_; uint8_t v___x_1515_; 
v___x_1513_ = lean_ptr_addr(v_value_1501_);
v___x_1514_ = lean_ptr_addr(v_a_1507_);
v___x_1515_ = lean_usize_dec_eq(v___x_1513_, v___x_1514_);
v___y_1421_ = v_nondep_1503_;
v___y_1422_ = v_a_1507_;
v___y_1423_ = v_a_1509_;
v___y_1424_ = v_a_1505_;
v___y_1425_ = v___y_1470_;
v___y_1426_ = v_declName_1499_;
v___y_1427_ = v_body_1502_;
v___y_1428_ = v___x_1515_;
goto v___jp_1420_;
}
}
else
{
lean_dec(v_a_1507_);
lean_dec(v_a_1505_);
lean_dec_ref(v_body_1502_);
lean_dec_ref_known(v___y_1470_, 4);
lean_dec(v_declName_1499_);
lean_dec_ref(v_post_1415_);
lean_dec_ref(v_pre_1413_);
return v___x_1508_;
}
}
else
{
lean_dec(v_a_1505_);
lean_dec_ref(v_body_1502_);
lean_dec(v_declName_1499_);
lean_dec_ref_known(v___y_1470_, 4);
lean_dec_ref(v_post_1415_);
lean_dec_ref(v_pre_1413_);
return v___x_1506_;
}
}
else
{
lean_dec_ref(v_body_1502_);
lean_dec(v_declName_1499_);
lean_dec_ref_known(v___y_1470_, 4);
lean_dec_ref(v_post_1415_);
lean_dec_ref(v_pre_1413_);
return v___x_1504_;
}
}
case 5:
{
lean_object* v_dummy_1516_; lean_object* v_nargs_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; 
v_dummy_1516_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_1517_ = l_Lean_Expr_getAppNumArgs(v___y_1470_);
lean_inc(v_nargs_1517_);
v___x_1518_ = lean_mk_array(v_nargs_1517_, v_dummy_1516_);
v___x_1519_ = lean_unsigned_to_nat(1u);
v___x_1520_ = lean_nat_sub(v_nargs_1517_, v___x_1519_);
lean_dec(v_nargs_1517_);
v___x_1521_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__4(v_pre_1413_, v_post_1415_, v___y_1470_, v___x_1518_, v___x_1520_, v___y_1416_, v___y_1417_, v___y_1418_);
return v___x_1521_;
}
case 10:
{
lean_object* v_data_1522_; lean_object* v_expr_1523_; lean_object* v___x_1524_; 
v_data_1522_ = lean_ctor_get(v___y_1470_, 0);
v_expr_1523_ = lean_ctor_get(v___y_1470_, 1);
lean_inc_ref(v_expr_1523_);
lean_inc_ref(v_post_1415_);
lean_inc_ref(v_pre_1413_);
v___x_1524_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1413_, v_post_1415_, v_expr_1523_, v___y_1416_, v___y_1417_, v___y_1418_);
if (lean_obj_tag(v___x_1524_) == 0)
{
lean_object* v_a_1525_; size_t v___x_1526_; size_t v___x_1527_; uint8_t v___x_1528_; 
v_a_1525_ = lean_ctor_get(v___x_1524_, 0);
lean_inc(v_a_1525_);
lean_dec_ref_known(v___x_1524_, 1);
v___x_1526_ = lean_ptr_addr(v_expr_1523_);
v___x_1527_ = lean_ptr_addr(v_a_1525_);
v___x_1528_ = lean_usize_dec_eq(v___x_1526_, v___x_1527_);
if (v___x_1528_ == 0)
{
lean_object* v___x_1529_; lean_object* v___x_1530_; 
lean_inc(v_data_1522_);
lean_dec_ref_known(v___y_1470_, 2);
v___x_1529_ = l_Lean_Expr_mdata___override(v_data_1522_, v_a_1525_);
v___x_1530_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1413_, v_post_1415_, v___x_1529_, v___y_1416_, v___y_1417_, v___y_1418_);
return v___x_1530_;
}
else
{
lean_object* v___x_1531_; 
lean_dec(v_a_1525_);
v___x_1531_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1413_, v_post_1415_, v___y_1470_, v___y_1416_, v___y_1417_, v___y_1418_);
return v___x_1531_;
}
}
else
{
lean_dec_ref_known(v___y_1470_, 2);
lean_dec_ref(v_post_1415_);
lean_dec_ref(v_pre_1413_);
return v___x_1524_;
}
}
case 11:
{
lean_object* v_typeName_1532_; lean_object* v_idx_1533_; lean_object* v_struct_1534_; lean_object* v___x_1535_; 
v_typeName_1532_ = lean_ctor_get(v___y_1470_, 0);
v_idx_1533_ = lean_ctor_get(v___y_1470_, 1);
v_struct_1534_ = lean_ctor_get(v___y_1470_, 2);
lean_inc_ref(v_struct_1534_);
lean_inc_ref(v_post_1415_);
lean_inc_ref(v_pre_1413_);
v___x_1535_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1413_, v_post_1415_, v_struct_1534_, v___y_1416_, v___y_1417_, v___y_1418_);
if (lean_obj_tag(v___x_1535_) == 0)
{
lean_object* v_a_1536_; size_t v___x_1537_; size_t v___x_1538_; uint8_t v___x_1539_; 
v_a_1536_ = lean_ctor_get(v___x_1535_, 0);
lean_inc(v_a_1536_);
lean_dec_ref_known(v___x_1535_, 1);
v___x_1537_ = lean_ptr_addr(v_struct_1534_);
v___x_1538_ = lean_ptr_addr(v_a_1536_);
v___x_1539_ = lean_usize_dec_eq(v___x_1537_, v___x_1538_);
if (v___x_1539_ == 0)
{
lean_object* v___x_1540_; lean_object* v___x_1541_; 
lean_inc(v_idx_1533_);
lean_inc(v_typeName_1532_);
lean_dec_ref_known(v___y_1470_, 3);
v___x_1540_ = l_Lean_Expr_proj___override(v_typeName_1532_, v_idx_1533_, v_a_1536_);
v___x_1541_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1413_, v_post_1415_, v___x_1540_, v___y_1416_, v___y_1417_, v___y_1418_);
return v___x_1541_;
}
else
{
lean_object* v___x_1542_; 
lean_dec(v_a_1536_);
v___x_1542_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1413_, v_post_1415_, v___y_1470_, v___y_1416_, v___y_1417_, v___y_1418_);
return v___x_1542_;
}
}
else
{
lean_dec_ref_known(v___y_1470_, 3);
lean_dec_ref(v_post_1415_);
lean_dec_ref(v_pre_1413_);
return v___x_1535_;
}
}
default: 
{
lean_object* v___x_1543_; 
v___x_1543_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1413_, v_post_1415_, v___y_1470_, v___y_1416_, v___y_1417_, v___y_1418_);
return v___x_1543_;
}
}
}
}
}
else
{
lean_object* v_a_1555_; lean_object* v___x_1557_; uint8_t v_isShared_1558_; uint8_t v_isSharedCheck_1562_; 
lean_dec_ref(v_post_1415_);
lean_dec_ref(v_e_1414_);
lean_dec_ref(v_pre_1413_);
v_a_1555_ = lean_ctor_get(v___x_1464_, 0);
v_isSharedCheck_1562_ = !lean_is_exclusive(v___x_1464_);
if (v_isSharedCheck_1562_ == 0)
{
v___x_1557_ = v___x_1464_;
v_isShared_1558_ = v_isSharedCheck_1562_;
goto v_resetjp_1556_;
}
else
{
lean_inc(v_a_1555_);
lean_dec(v___x_1464_);
v___x_1557_ = lean_box(0);
v_isShared_1558_ = v_isSharedCheck_1562_;
goto v_resetjp_1556_;
}
v_resetjp_1556_:
{
lean_object* v___x_1560_; 
if (v_isShared_1558_ == 0)
{
v___x_1560_ = v___x_1557_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v_a_1555_);
v___x_1560_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
return v___x_1560_;
}
}
}
}
else
{
lean_object* v_a_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1570_; 
lean_dec_ref(v_post_1415_);
lean_dec_ref(v_e_1414_);
lean_dec_ref(v_pre_1413_);
v_a_1563_ = lean_ctor_get(v___x_1463_, 0);
v_isSharedCheck_1570_ = !lean_is_exclusive(v___x_1463_);
if (v_isSharedCheck_1570_ == 0)
{
v___x_1565_ = v___x_1463_;
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_a_1563_);
lean_dec(v___x_1463_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
lean_object* v___x_1568_; 
if (v_isShared_1566_ == 0)
{
v___x_1568_ = v___x_1565_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v_a_1563_);
v___x_1568_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
return v___x_1568_;
}
}
}
v___jp_1420_:
{
if (v___y_1428_ == 0)
{
lean_object* v___x_1429_; lean_object* v___x_1430_; 
lean_dec_ref(v___y_1427_);
lean_dec_ref(v___y_1425_);
v___x_1429_ = l_Lean_Expr_letE___override(v___y_1426_, v___y_1424_, v___y_1422_, v___y_1423_, v___y_1421_);
v___x_1430_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1413_, v_post_1415_, v___x_1429_, v___y_1416_, v___y_1417_, v___y_1418_);
return v___x_1430_;
}
else
{
size_t v___x_1431_; size_t v___x_1432_; uint8_t v___x_1433_; 
v___x_1431_ = lean_ptr_addr(v___y_1427_);
lean_dec_ref(v___y_1427_);
v___x_1432_ = lean_ptr_addr(v___y_1423_);
v___x_1433_ = lean_usize_dec_eq(v___x_1431_, v___x_1432_);
if (v___x_1433_ == 0)
{
lean_object* v___x_1434_; lean_object* v___x_1435_; 
lean_dec_ref(v___y_1425_);
v___x_1434_ = l_Lean_Expr_letE___override(v___y_1426_, v___y_1424_, v___y_1422_, v___y_1423_, v___y_1421_);
v___x_1435_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1413_, v_post_1415_, v___x_1434_, v___y_1416_, v___y_1417_, v___y_1418_);
return v___x_1435_;
}
else
{
lean_object* v___x_1436_; 
lean_dec(v___y_1426_);
lean_dec_ref(v___y_1424_);
lean_dec_ref(v___y_1423_);
lean_dec_ref(v___y_1422_);
v___x_1436_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1413_, v_post_1415_, v___y_1425_, v___y_1416_, v___y_1417_, v___y_1418_);
return v___x_1436_;
}
}
}
v___jp_1437_:
{
if (v___y_1443_ == 0)
{
lean_object* v___x_1444_; lean_object* v___x_1445_; 
lean_dec_ref(v___y_1440_);
v___x_1444_ = l_Lean_Expr_lam___override(v___y_1441_, v___y_1442_, v___y_1439_, v___y_1438_);
v___x_1445_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1413_, v_post_1415_, v___x_1444_, v___y_1416_, v___y_1417_, v___y_1418_);
return v___x_1445_;
}
else
{
uint8_t v___x_1446_; 
v___x_1446_ = l_Lean_instBEqBinderInfo_beq(v___y_1438_, v___y_1438_);
if (v___x_1446_ == 0)
{
lean_object* v___x_1447_; lean_object* v___x_1448_; 
lean_dec_ref(v___y_1440_);
v___x_1447_ = l_Lean_Expr_lam___override(v___y_1441_, v___y_1442_, v___y_1439_, v___y_1438_);
v___x_1448_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1413_, v_post_1415_, v___x_1447_, v___y_1416_, v___y_1417_, v___y_1418_);
return v___x_1448_;
}
else
{
lean_object* v___x_1449_; 
lean_dec_ref(v___y_1442_);
lean_dec(v___y_1441_);
lean_dec_ref(v___y_1439_);
v___x_1449_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1413_, v_post_1415_, v___y_1440_, v___y_1416_, v___y_1417_, v___y_1418_);
return v___x_1449_;
}
}
}
v___jp_1450_:
{
if (v___y_1456_ == 0)
{
lean_object* v___x_1457_; lean_object* v___x_1458_; 
lean_dec_ref(v___y_1453_);
v___x_1457_ = l_Lean_Expr_forallE___override(v___y_1451_, v___y_1454_, v___y_1452_, v___y_1455_);
v___x_1458_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1413_, v_post_1415_, v___x_1457_, v___y_1416_, v___y_1417_, v___y_1418_);
return v___x_1458_;
}
else
{
uint8_t v___x_1459_; 
v___x_1459_ = l_Lean_instBEqBinderInfo_beq(v___y_1455_, v___y_1455_);
if (v___x_1459_ == 0)
{
lean_object* v___x_1460_; lean_object* v___x_1461_; 
lean_dec_ref(v___y_1453_);
v___x_1460_ = l_Lean_Expr_forallE___override(v___y_1451_, v___y_1454_, v___y_1452_, v___y_1455_);
v___x_1461_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1413_, v_post_1415_, v___x_1460_, v___y_1416_, v___y_1417_, v___y_1418_);
return v___x_1461_;
}
else
{
lean_object* v___x_1462_; 
lean_dec_ref(v___y_1454_);
lean_dec_ref(v___y_1452_);
lean_dec(v___y_1451_);
v___x_1462_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1413_, v_post_1415_, v___y_1453_, v___y_1416_, v___y_1417_, v___y_1418_);
return v___x_1462_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__1___boxed(lean_object* v___x_1571_, lean_object* v_pre_1572_, lean_object* v_e_1573_, lean_object* v_post_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_){
_start:
{
lean_object* v_res_1579_; 
v_res_1579_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__1(v___x_1571_, v_pre_1572_, v_e_1573_, v_post_1574_, v___y_1575_, v___y_1576_, v___y_1577_);
lean_dec(v___y_1577_);
lean_dec_ref(v___y_1576_);
lean_dec(v___y_1575_);
return v_res_1579_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(lean_object* v_pre_1580_, lean_object* v_post_1581_, lean_object* v_e_1582_, lean_object* v_a_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_){
_start:
{
lean_object* v___x_1587_; lean_object* v___x_1588_; 
lean_inc(v_a_1583_);
v___x_1587_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1587_, 0, lean_box(0));
lean_closure_set(v___x_1587_, 1, lean_box(0));
lean_closure_set(v___x_1587_, 2, v_a_1583_);
v___x_1588_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__0(lean_box(0), v___x_1587_, v___y_1584_, v___y_1585_);
if (lean_obj_tag(v___x_1588_) == 0)
{
lean_object* v_a_1589_; lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1620_; 
v_a_1589_ = lean_ctor_get(v___x_1588_, 0);
v_isSharedCheck_1620_ = !lean_is_exclusive(v___x_1588_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1591_ = v___x_1588_;
v_isShared_1592_ = v_isSharedCheck_1620_;
goto v_resetjp_1590_;
}
else
{
lean_inc(v_a_1589_);
lean_dec(v___x_1588_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1620_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
lean_object* v___x_1593_; 
v___x_1593_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg(v_a_1589_, v_e_1582_);
lean_dec(v_a_1589_);
if (lean_obj_tag(v___x_1593_) == 0)
{
lean_object* v___x_1594_; lean_object* v___f_1595_; lean_object* v___x_1596_; 
lean_del_object(v___x_1591_);
v___x_1594_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__19___closed__0));
lean_inc_ref(v_e_1582_);
v___f_1595_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__1___boxed), 8, 4);
lean_closure_set(v___f_1595_, 0, v___x_1594_);
lean_closure_set(v___f_1595_, 1, v_pre_1580_);
lean_closure_set(v___f_1595_, 2, v_e_1582_);
lean_closure_set(v___f_1595_, 3, v_post_1581_);
v___x_1596_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___redArg(v___f_1595_, v_a_1583_, v___y_1584_, v___y_1585_);
if (lean_obj_tag(v___x_1596_) == 0)
{
lean_object* v_a_1597_; lean_object* v___f_1598_; lean_object* v___x_1599_; 
v_a_1597_ = lean_ctor_get(v___x_1596_, 0);
lean_inc_n(v_a_1597_, 2);
lean_dec_ref_known(v___x_1596_, 1);
lean_inc(v_a_1583_);
v___f_1598_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1598_, 0, v_a_1583_);
lean_closure_set(v___f_1598_, 1, v_e_1582_);
lean_closure_set(v___f_1598_, 2, v_a_1597_);
v___x_1599_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__0(lean_box(0), v___f_1598_, v___y_1584_, v___y_1585_);
if (lean_obj_tag(v___x_1599_) == 0)
{
lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1606_; 
v_isSharedCheck_1606_ = !lean_is_exclusive(v___x_1599_);
if (v_isSharedCheck_1606_ == 0)
{
lean_object* v_unused_1607_; 
v_unused_1607_ = lean_ctor_get(v___x_1599_, 0);
lean_dec(v_unused_1607_);
v___x_1601_ = v___x_1599_;
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
else
{
lean_dec(v___x_1599_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1604_; 
if (v_isShared_1602_ == 0)
{
lean_ctor_set(v___x_1601_, 0, v_a_1597_);
v___x_1604_ = v___x_1601_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_a_1597_);
v___x_1604_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
return v___x_1604_;
}
}
}
else
{
lean_object* v_a_1608_; lean_object* v___x_1610_; uint8_t v_isShared_1611_; uint8_t v_isSharedCheck_1615_; 
lean_dec(v_a_1597_);
v_a_1608_ = lean_ctor_get(v___x_1599_, 0);
v_isSharedCheck_1615_ = !lean_is_exclusive(v___x_1599_);
if (v_isSharedCheck_1615_ == 0)
{
v___x_1610_ = v___x_1599_;
v_isShared_1611_ = v_isSharedCheck_1615_;
goto v_resetjp_1609_;
}
else
{
lean_inc(v_a_1608_);
lean_dec(v___x_1599_);
v___x_1610_ = lean_box(0);
v_isShared_1611_ = v_isSharedCheck_1615_;
goto v_resetjp_1609_;
}
v_resetjp_1609_:
{
lean_object* v___x_1613_; 
if (v_isShared_1611_ == 0)
{
v___x_1613_ = v___x_1610_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v_a_1608_);
v___x_1613_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
return v___x_1613_;
}
}
}
}
else
{
lean_dec_ref(v_e_1582_);
return v___x_1596_;
}
}
else
{
lean_object* v_val_1616_; lean_object* v___x_1618_; 
lean_dec_ref(v_e_1582_);
lean_dec_ref(v_post_1581_);
lean_dec_ref(v_pre_1580_);
v_val_1616_ = lean_ctor_get(v___x_1593_, 0);
lean_inc(v_val_1616_);
lean_dec_ref_known(v___x_1593_, 1);
if (v_isShared_1592_ == 0)
{
lean_ctor_set(v___x_1591_, 0, v_val_1616_);
v___x_1618_ = v___x_1591_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v_val_1616_);
v___x_1618_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
return v___x_1618_;
}
}
}
}
else
{
lean_object* v_a_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1628_; 
lean_dec_ref(v_e_1582_);
lean_dec_ref(v_post_1581_);
lean_dec_ref(v_pre_1580_);
v_a_1621_ = lean_ctor_get(v___x_1588_, 0);
v_isSharedCheck_1628_ = !lean_is_exclusive(v___x_1588_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1623_ = v___x_1588_;
v_isShared_1624_ = v_isSharedCheck_1628_;
goto v_resetjp_1622_;
}
else
{
lean_inc(v_a_1621_);
lean_dec(v___x_1588_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1628_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
lean_object* v___x_1626_; 
if (v_isShared_1624_ == 0)
{
v___x_1626_ = v___x_1623_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v_a_1621_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(lean_object* v_pre_1629_, lean_object* v_post_1630_, lean_object* v_e_1631_, lean_object* v_a_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_){
_start:
{
lean_object* v___x_1636_; 
lean_inc_ref(v_post_1630_);
lean_inc(v___y_1634_);
lean_inc_ref(v___y_1633_);
lean_inc_ref(v_e_1631_);
v___x_1636_ = lean_apply_4(v_post_1630_, v_e_1631_, v___y_1633_, v___y_1634_, lean_box(0));
if (lean_obj_tag(v___x_1636_) == 0)
{
lean_object* v_a_1637_; lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1655_; 
v_a_1637_ = lean_ctor_get(v___x_1636_, 0);
v_isSharedCheck_1655_ = !lean_is_exclusive(v___x_1636_);
if (v_isSharedCheck_1655_ == 0)
{
v___x_1639_ = v___x_1636_;
v_isShared_1640_ = v_isSharedCheck_1655_;
goto v_resetjp_1638_;
}
else
{
lean_inc(v_a_1637_);
lean_dec(v___x_1636_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1655_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
switch(lean_obj_tag(v_a_1637_))
{
case 0:
{
lean_object* v_e_1641_; lean_object* v___x_1643_; 
lean_dec_ref(v_e_1631_);
lean_dec_ref(v_post_1630_);
lean_dec_ref(v_pre_1629_);
v_e_1641_ = lean_ctor_get(v_a_1637_, 0);
lean_inc_ref(v_e_1641_);
lean_dec_ref_known(v_a_1637_, 1);
if (v_isShared_1640_ == 0)
{
lean_ctor_set(v___x_1639_, 0, v_e_1641_);
v___x_1643_ = v___x_1639_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v_e_1641_);
v___x_1643_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
return v___x_1643_;
}
}
case 1:
{
lean_object* v_e_1645_; lean_object* v___x_1646_; 
lean_del_object(v___x_1639_);
lean_dec_ref(v_e_1631_);
v_e_1645_ = lean_ctor_get(v_a_1637_, 0);
lean_inc_ref(v_e_1645_);
lean_dec_ref_known(v_a_1637_, 1);
v___x_1646_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1629_, v_post_1630_, v_e_1645_, v_a_1632_, v___y_1633_, v___y_1634_);
return v___x_1646_;
}
default: 
{
lean_object* v_e_x3f_1647_; 
lean_dec_ref(v_post_1630_);
lean_dec_ref(v_pre_1629_);
v_e_x3f_1647_ = lean_ctor_get(v_a_1637_, 0);
lean_inc(v_e_x3f_1647_);
lean_dec_ref_known(v_a_1637_, 1);
if (lean_obj_tag(v_e_x3f_1647_) == 0)
{
lean_object* v___x_1649_; 
if (v_isShared_1640_ == 0)
{
lean_ctor_set(v___x_1639_, 0, v_e_1631_);
v___x_1649_ = v___x_1639_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v_e_1631_);
v___x_1649_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
return v___x_1649_;
}
}
else
{
lean_object* v_val_1651_; lean_object* v___x_1653_; 
lean_dec_ref(v_e_1631_);
v_val_1651_ = lean_ctor_get(v_e_x3f_1647_, 0);
lean_inc(v_val_1651_);
lean_dec_ref_known(v_e_x3f_1647_, 1);
if (v_isShared_1640_ == 0)
{
lean_ctor_set(v___x_1639_, 0, v_val_1651_);
v___x_1653_ = v___x_1639_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v_val_1651_);
v___x_1653_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
return v___x_1653_;
}
}
}
}
}
}
else
{
lean_object* v_a_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1663_; 
lean_dec_ref(v_e_1631_);
lean_dec_ref(v_post_1630_);
lean_dec_ref(v_pre_1629_);
v_a_1656_ = lean_ctor_get(v___x_1636_, 0);
v_isSharedCheck_1663_ = !lean_is_exclusive(v___x_1636_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1658_ = v___x_1636_;
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_a_1656_);
lean_dec(v___x_1636_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v___x_1661_; 
if (v_isShared_1659_ == 0)
{
v___x_1661_ = v___x_1658_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v_a_1656_);
v___x_1661_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
return v___x_1661_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_1664_, lean_object* v_post_1665_, lean_object* v_e_1666_, lean_object* v_a_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_){
_start:
{
lean_object* v_res_1671_; 
v_res_1671_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1664_, v_post_1665_, v_e_1666_, v_a_1667_, v___y_1668_, v___y_1669_);
lean_dec(v___y_1669_);
lean_dec_ref(v___y_1668_);
lean_dec(v_a_1667_);
return v_res_1671_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_1672_, lean_object* v_post_1673_, lean_object* v_sz_1674_, lean_object* v_i_1675_, lean_object* v_bs_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_){
_start:
{
size_t v_sz_boxed_1681_; size_t v_i_boxed_1682_; lean_object* v_res_1683_; 
v_sz_boxed_1681_ = lean_unbox_usize(v_sz_1674_);
lean_dec(v_sz_1674_);
v_i_boxed_1682_ = lean_unbox_usize(v_i_1675_);
lean_dec(v_i_1675_);
v_res_1683_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1(v_pre_1672_, v_post_1673_, v_sz_boxed_1681_, v_i_boxed_1682_, v_bs_1676_, v___y_1677_, v___y_1678_, v___y_1679_);
lean_dec(v___y_1679_);
lean_dec_ref(v___y_1678_);
lean_dec(v___y_1677_);
return v_res_1683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__4___boxed(lean_object* v_pre_1684_, lean_object* v_post_1685_, lean_object* v_x_1686_, lean_object* v_x_1687_, lean_object* v_x_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_){
_start:
{
lean_object* v_res_1693_; 
v_res_1693_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__4(v_pre_1684_, v_post_1685_, v_x_1686_, v_x_1687_, v_x_1688_, v___y_1689_, v___y_1690_, v___y_1691_);
lean_dec(v___y_1691_);
lean_dec_ref(v___y_1690_);
lean_dec(v___y_1689_);
return v_res_1693_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___boxed(lean_object* v_pre_1694_, lean_object* v_post_1695_, lean_object* v_e_1696_, lean_object* v_a_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_){
_start:
{
lean_object* v_res_1701_; 
v_res_1701_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1694_, v_post_1695_, v_e_1696_, v_a_1697_, v___y_1698_, v___y_1699_);
lean_dec(v___y_1699_);
lean_dec_ref(v___y_1698_);
lean_dec(v_a_1697_);
return v_res_1701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___lam__0(lean_object* v_00_u03b1_1702_, lean_object* v_x_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_){
_start:
{
lean_object* v___x_1707_; lean_object* v___x_1708_; 
v___x_1707_ = lean_apply_1(v_x_1703_, lean_box(0));
v___x_1708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1708_, 0, v___x_1707_);
return v___x_1708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___lam__0___boxed(lean_object* v_00_u03b1_1709_, lean_object* v_x_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_){
_start:
{
lean_object* v_res_1714_; 
v_res_1714_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___lam__0(v_00_u03b1_1709_, v_x_1710_, v___y_1711_, v___y_1712_);
lean_dec(v___y_1712_);
lean_dec_ref(v___y_1711_);
return v_res_1714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(lean_object* v_input_1715_, lean_object* v_pre_1716_, lean_object* v_post_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_){
_start:
{
lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v_a_1723_; lean_object* v___x_1724_; 
v___x_1721_ = lean_obj_once(&l_Lean_Core_transform___redArg___closed__2, &l_Lean_Core_transform___redArg___closed__2_once, _init_l_Lean_Core_transform___redArg___closed__2);
v___x_1722_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___lam__0(lean_box(0), v___x_1721_, v___y_1718_, v___y_1719_);
v_a_1723_ = lean_ctor_get(v___x_1722_, 0);
lean_inc(v_a_1723_);
lean_dec_ref(v___x_1722_);
v___x_1724_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1716_, v_post_1717_, v_input_1715_, v_a_1723_, v___y_1718_, v___y_1719_);
if (lean_obj_tag(v___x_1724_) == 0)
{
lean_object* v_a_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1734_; 
v_a_1725_ = lean_ctor_get(v___x_1724_, 0);
lean_inc(v_a_1725_);
lean_dec_ref_known(v___x_1724_, 1);
v___x_1726_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1726_, 0, lean_box(0));
lean_closure_set(v___x_1726_, 1, lean_box(0));
lean_closure_set(v___x_1726_, 2, v_a_1723_);
v___x_1727_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___lam__0(lean_box(0), v___x_1726_, v___y_1718_, v___y_1719_);
v_isSharedCheck_1734_ = !lean_is_exclusive(v___x_1727_);
if (v_isSharedCheck_1734_ == 0)
{
lean_object* v_unused_1735_; 
v_unused_1735_ = lean_ctor_get(v___x_1727_, 0);
lean_dec(v_unused_1735_);
v___x_1729_ = v___x_1727_;
v_isShared_1730_ = v_isSharedCheck_1734_;
goto v_resetjp_1728_;
}
else
{
lean_dec(v___x_1727_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1734_;
goto v_resetjp_1728_;
}
v_resetjp_1728_:
{
lean_object* v___x_1732_; 
if (v_isShared_1730_ == 0)
{
lean_ctor_set(v___x_1729_, 0, v_a_1725_);
v___x_1732_ = v___x_1729_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v_a_1725_);
v___x_1732_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
return v___x_1732_;
}
}
}
else
{
lean_dec(v_a_1723_);
return v___x_1724_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___boxed(lean_object* v_input_1736_, lean_object* v_pre_1737_, lean_object* v_post_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_){
_start:
{
lean_object* v_res_1742_; 
v_res_1742_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_input_1736_, v_pre_1737_, v_post_1738_, v___y_1739_, v___y_1740_);
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
return v_res_1742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_betaReduce(lean_object* v_e_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_){
_start:
{
lean_object* v___f_1749_; lean_object* v___f_1750_; lean_object* v___x_1751_; 
v___f_1749_ = ((lean_object*)(l_Lean_Core_betaReduce___closed__0));
v___f_1750_ = ((lean_object*)(l_Lean_Core_betaReduce___closed__1));
v___x_1751_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_1745_, v___f_1749_, v___f_1750_, v_a_1746_, v_a_1747_);
return v___x_1751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_betaReduce___boxed(lean_object* v_e_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_){
_start:
{
lean_object* v_res_1756_; 
v_res_1756_ = l_Lean_Core_betaReduce(v_e_1752_, v_a_1753_, v_a_1754_);
lean_dec(v_a_1754_);
lean_dec_ref(v_a_1753_);
return v_res_1756_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_1757_, lean_object* v_m_1758_, lean_object* v_a_1759_){
_start:
{
lean_object* v___x_1760_; 
v___x_1760_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg(v_m_1758_, v_a_1759_);
return v___x_1760_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_1761_, lean_object* v_m_1762_, lean_object* v_a_1763_){
_start:
{
lean_object* v_res_1764_; 
v_res_1764_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3(v_00_u03b2_1761_, v_m_1762_, v_a_1763_);
lean_dec_ref(v_a_1763_);
lean_dec_ref(v_m_1762_);
return v_res_1764_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_1765_, lean_object* v_ref_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_){
_start:
{
lean_object* v___x_1770_; 
v___x_1770_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_1766_);
return v___x_1770_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1771_, lean_object* v_ref_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_){
_start:
{
lean_object* v_res_1776_; 
v_res_1776_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_1771_, v_ref_1772_, v___y_1773_, v___y_1774_);
lean_dec(v___y_1774_);
lean_dec_ref(v___y_1773_);
return v_res_1776_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8(lean_object* v_00_u03b1_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_){
_start:
{
lean_object* v___x_1781_; 
v___x_1781_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___redArg();
return v___x_1781_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___boxed(lean_object* v_00_u03b1_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_){
_start:
{
lean_object* v_res_1786_; 
v_res_1786_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8(v_00_u03b1_1782_, v___y_1783_, v___y_1784_);
lean_dec(v___y_1784_);
lean_dec_ref(v___y_1783_);
return v_res_1786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5(lean_object* v_00_u03b1_1787_, lean_object* v_x_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_){
_start:
{
lean_object* v___x_1793_; 
v___x_1793_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___redArg(v_x_1788_, v___y_1789_, v___y_1790_, v___y_1791_);
return v___x_1793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b1_1794_, lean_object* v_x_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_){
_start:
{
lean_object* v_res_1800_; 
v_res_1800_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5(v_00_u03b1_1794_, v_x_1795_, v___y_1796_, v___y_1797_, v___y_1798_);
lean_dec(v___y_1798_);
lean_dec_ref(v___y_1797_);
lean_dec(v___y_1796_);
return v_res_1800_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6(lean_object* v_00_u03b2_1801_, lean_object* v_m_1802_, lean_object* v_a_1803_, lean_object* v_b_1804_){
_start:
{
lean_object* v___x_1805_; 
v___x_1805_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6___redArg(v_m_1802_, v_a_1803_, v_b_1804_);
return v___x_1805_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4(lean_object* v_00_u03b2_1806_, lean_object* v_a_1807_, lean_object* v_x_1808_){
_start:
{
lean_object* v___x_1809_; 
v___x_1809_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___redArg(v_a_1807_, v_x_1808_);
return v___x_1809_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___boxed(lean_object* v_00_u03b2_1810_, lean_object* v_a_1811_, lean_object* v_x_1812_){
_start:
{
lean_object* v_res_1813_; 
v_res_1813_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4(v_00_u03b2_1810_, v_a_1811_, v_x_1812_);
lean_dec(v_x_1812_);
lean_dec_ref(v_a_1811_);
return v_res_1813_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10(lean_object* v_00_u03b2_1814_, lean_object* v_a_1815_, lean_object* v_x_1816_){
_start:
{
uint8_t v___x_1817_; 
v___x_1817_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___redArg(v_a_1815_, v_x_1816_);
return v___x_1817_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___boxed(lean_object* v_00_u03b2_1818_, lean_object* v_a_1819_, lean_object* v_x_1820_){
_start:
{
uint8_t v_res_1821_; lean_object* v_r_1822_; 
v_res_1821_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10(v_00_u03b2_1818_, v_a_1819_, v_x_1820_);
lean_dec(v_x_1820_);
lean_dec_ref(v_a_1819_);
v_r_1822_ = lean_box(v_res_1821_);
return v_r_1822_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11(lean_object* v_00_u03b2_1823_, lean_object* v_data_1824_){
_start:
{
lean_object* v___x_1825_; 
v___x_1825_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11___redArg(v_data_1824_);
return v___x_1825_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__12(lean_object* v_00_u03b2_1826_, lean_object* v_a_1827_, lean_object* v_b_1828_, lean_object* v_x_1829_){
_start:
{
lean_object* v___x_1830_; 
v___x_1830_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__12___redArg(v_a_1827_, v_b_1828_, v_x_1829_);
return v___x_1830_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12(lean_object* v_00_u03b2_1831_, lean_object* v_i_1832_, lean_object* v_source_1833_, lean_object* v_target_1834_){
_start:
{
lean_object* v___x_1835_; 
v___x_1835_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v_i_1832_, v_source_1833_, v_target_1834_);
return v___x_1835_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13(lean_object* v_00_u03b2_1836_, lean_object* v_x_1837_, lean_object* v_x_1838_){
_start:
{
lean_object* v___x_1839_; 
v___x_1839_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_x_1837_, v_x_1838_);
return v___x_1839_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__0(lean_object* v_toApplicative_1840_, lean_object* v_a_1841_){
_start:
{
lean_object* v_toPure_1842_; lean_object* v___x_1843_; 
v_toPure_1842_ = lean_ctor_get(v_toApplicative_1840_, 1);
lean_inc(v_toPure_1842_);
lean_dec_ref(v_toApplicative_1840_);
v___x_1843_ = lean_apply_2(v_toPure_1842_, lean_box(0), v_a_1841_);
return v___x_1843_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__13(lean_object* v___x_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_){
_start:
{
lean_object* v___x_1850_; 
v___x_1850_ = l_Lean_Core_checkSystem(v___x_1844_, v___y_1847_, v___y_1848_);
return v___x_1850_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__13___boxed(lean_object* v___x_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_){
_start:
{
lean_object* v_res_1857_; 
v_res_1857_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__13(v___x_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_);
lean_dec(v___y_1855_);
lean_dec_ref(v___y_1854_);
lean_dec(v___y_1853_);
lean_dec_ref(v___y_1852_);
return v_res_1857_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14(lean_object* v_inst_1860_, lean_object* v_x_1861_, lean_object* v___x_1862_, lean_object* v___x_1863_, lean_object* v_inst_1864_, lean_object* v___f_1865_, lean_object* v___x_1866_, lean_object* v___x_1867_, lean_object* v_a_1868_, lean_object* v_toBind_1869_, lean_object* v___f_1870_, lean_object* v_toApplicative_1871_, lean_object* v_a_1872_){
_start:
{
if (lean_obj_tag(v_a_1872_) == 0)
{
lean_object* v___f_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_3801__overap_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; 
lean_dec_ref(v_toApplicative_1871_);
v___f_1873_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14___closed__0));
v___x_1874_ = lean_apply_2(v_inst_1860_, lean_box(0), v___f_1873_);
lean_inc_ref(v___x_1863_);
lean_inc_ref(v___x_1862_);
v___x_1875_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonadLift___aux__1___boxed), 10, 9);
lean_closure_set(v___x_1875_, 0, lean_box(0));
lean_closure_set(v___x_1875_, 1, lean_box(0));
lean_closure_set(v___x_1875_, 2, lean_box(0));
lean_closure_set(v___x_1875_, 3, lean_box(0));
lean_closure_set(v___x_1875_, 4, v_x_1861_);
lean_closure_set(v___x_1875_, 5, v___x_1862_);
lean_closure_set(v___x_1875_, 6, v___x_1863_);
lean_closure_set(v___x_1875_, 7, lean_box(0));
lean_closure_set(v___x_1875_, 8, v___x_1874_);
v___x_1876_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonad___aux__13___boxed), 13, 12);
lean_closure_set(v___x_1876_, 0, lean_box(0));
lean_closure_set(v___x_1876_, 1, lean_box(0));
lean_closure_set(v___x_1876_, 2, lean_box(0));
lean_closure_set(v___x_1876_, 3, lean_box(0));
lean_closure_set(v___x_1876_, 4, v_x_1861_);
lean_closure_set(v___x_1876_, 5, v___x_1862_);
lean_closure_set(v___x_1876_, 6, v___x_1863_);
lean_closure_set(v___x_1876_, 7, v_inst_1864_);
lean_closure_set(v___x_1876_, 8, lean_box(0));
lean_closure_set(v___x_1876_, 9, lean_box(0));
lean_closure_set(v___x_1876_, 10, v___x_1875_);
lean_closure_set(v___x_1876_, 11, v___f_1865_);
v___x_3801__overap_1877_ = l_Lean_Meta_withIncRecDepth___redArg(v___x_1866_, v___x_1867_, v___x_1876_);
lean_inc(v_a_1868_);
v___x_1878_ = lean_apply_1(v___x_3801__overap_1877_, v_a_1868_);
v___x_1879_ = lean_apply_4(v_toBind_1869_, lean_box(0), lean_box(0), v___x_1878_, v___f_1870_);
return v___x_1879_;
}
else
{
lean_object* v_val_1880_; lean_object* v_toPure_1881_; lean_object* v___x_1882_; 
lean_dec(v___f_1870_);
lean_dec(v_toBind_1869_);
lean_dec_ref(v___x_1867_);
lean_dec_ref(v___x_1866_);
lean_dec(v___f_1865_);
lean_dec_ref(v_inst_1864_);
lean_dec_ref(v___x_1863_);
lean_dec_ref(v___x_1862_);
lean_dec(v_inst_1860_);
v_val_1880_ = lean_ctor_get(v_a_1872_, 0);
lean_inc(v_val_1880_);
lean_dec_ref_known(v_a_1872_, 1);
v_toPure_1881_ = lean_ctor_get(v_toApplicative_1871_, 1);
lean_inc(v_toPure_1881_);
lean_dec_ref(v_toApplicative_1871_);
v___x_1882_ = lean_apply_2(v_toPure_1881_, lean_box(0), v_val_1880_);
return v___x_1882_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14___boxed(lean_object* v_inst_1883_, lean_object* v_x_1884_, lean_object* v___x_1885_, lean_object* v___x_1886_, lean_object* v_inst_1887_, lean_object* v___f_1888_, lean_object* v___x_1889_, lean_object* v___x_1890_, lean_object* v_a_1891_, lean_object* v_toBind_1892_, lean_object* v___f_1893_, lean_object* v_toApplicative_1894_, lean_object* v_a_1895_){
_start:
{
lean_object* v_res_1896_; 
v_res_1896_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14(v_inst_1883_, v_x_1884_, v___x_1885_, v___x_1886_, v_inst_1887_, v___f_1888_, v___x_1889_, v___x_1890_, v_a_1891_, v_toBind_1892_, v___f_1893_, v_toApplicative_1894_, v_a_1895_);
lean_dec(v_a_1891_);
return v_res_1896_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__1(lean_object* v___x_1897_, lean_object* v___x_1898_, lean_object* v_declName_1899_, lean_object* v_a_1900_, lean_object* v___f_1901_, uint8_t v_nondep_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_){
_start:
{
uint8_t v___x_1905_; lean_object* v___x_3820__overap_1906_; lean_object* v___x_1907_; 
v___x_1905_ = 0;
v___x_3820__overap_1906_ = l_Lean_Meta_withLetDecl___redArg(v___x_1897_, v___x_1898_, v_declName_1899_, v_a_1900_, v_a_1904_, v___f_1901_, v_nondep_1902_, v___x_1905_);
lean_inc(v_a_1903_);
v___x_1907_ = lean_apply_1(v___x_3820__overap_1906_, v_a_1903_);
return v___x_1907_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__1___boxed(lean_object* v___x_1908_, lean_object* v___x_1909_, lean_object* v_declName_1910_, lean_object* v_a_1911_, lean_object* v___f_1912_, lean_object* v_nondep_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_){
_start:
{
uint8_t v_nondep_3999__boxed_1916_; lean_object* v_res_1917_; 
v_nondep_3999__boxed_1916_ = lean_unbox(v_nondep_1913_);
v_res_1917_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__1(v___x_1908_, v___x_1909_, v_declName_1910_, v_a_1911_, v___f_1912_, v_nondep_3999__boxed_1916_, v_a_1914_, v_a_1915_);
lean_dec(v_a_1914_);
return v_res_1917_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__4(lean_object* v_fvars_1918_, uint8_t v_usedLetOnly_1919_, lean_object* v_inst_1920_, lean_object* v_toBind_1921_, lean_object* v___f_1922_, lean_object* v_a_1923_){
_start:
{
uint8_t v___x_1924_; uint8_t v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; 
v___x_1924_ = 0;
v___x_1925_ = 1;
v___x_1926_ = lean_box(v_usedLetOnly_1919_);
v___x_1927_ = lean_box(v___x_1924_);
v___x_1928_ = lean_box(v___x_1925_);
v___x_1929_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLetFVars___boxed), 10, 5);
lean_closure_set(v___x_1929_, 0, v_fvars_1918_);
lean_closure_set(v___x_1929_, 1, v_a_1923_);
lean_closure_set(v___x_1929_, 2, v___x_1926_);
lean_closure_set(v___x_1929_, 3, v___x_1927_);
lean_closure_set(v___x_1929_, 4, v___x_1928_);
v___x_1930_ = lean_apply_2(v_inst_1920_, lean_box(0), v___x_1929_);
v___x_1931_ = lean_apply_4(v_toBind_1921_, lean_box(0), lean_box(0), v___x_1930_, v___f_1922_);
return v___x_1931_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__4___boxed(lean_object* v_fvars_1932_, lean_object* v_usedLetOnly_1933_, lean_object* v_inst_1934_, lean_object* v_toBind_1935_, lean_object* v___f_1936_, lean_object* v_a_1937_){
_start:
{
uint8_t v_usedLetOnly_boxed_1938_; lean_object* v_res_1939_; 
v_usedLetOnly_boxed_1938_ = lean_unbox(v_usedLetOnly_1933_);
v_res_1939_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__4(v_fvars_1932_, v_usedLetOnly_boxed_1938_, v_inst_1934_, v_toBind_1935_, v___f_1936_, v_a_1937_);
return v_res_1939_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__3(lean_object* v_fvars_1940_, uint8_t v_usedLetOnly_1941_, lean_object* v_inst_1942_, lean_object* v_toBind_1943_, lean_object* v___f_1944_, lean_object* v_a_1945_){
_start:
{
uint8_t v___x_1946_; uint8_t v___x_1947_; uint8_t v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; 
v___x_1946_ = 0;
v___x_1947_ = 1;
v___x_1948_ = 1;
v___x_1949_ = lean_box(v___x_1946_);
v___x_1950_ = lean_box(v_usedLetOnly_1941_);
v___x_1951_ = lean_box(v___x_1946_);
v___x_1952_ = lean_box(v___x_1947_);
v___x_1953_ = lean_box(v___x_1948_);
v___x_1954_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(v___x_1954_, 0, v_fvars_1940_);
lean_closure_set(v___x_1954_, 1, v_a_1945_);
lean_closure_set(v___x_1954_, 2, v___x_1949_);
lean_closure_set(v___x_1954_, 3, v___x_1950_);
lean_closure_set(v___x_1954_, 4, v___x_1951_);
lean_closure_set(v___x_1954_, 5, v___x_1952_);
lean_closure_set(v___x_1954_, 6, v___x_1953_);
v___x_1955_ = lean_apply_2(v_inst_1942_, lean_box(0), v___x_1954_);
v___x_1956_ = lean_apply_4(v_toBind_1943_, lean_box(0), lean_box(0), v___x_1955_, v___f_1944_);
return v___x_1956_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__3___boxed(lean_object* v_fvars_1957_, lean_object* v_usedLetOnly_1958_, lean_object* v_inst_1959_, lean_object* v_toBind_1960_, lean_object* v___f_1961_, lean_object* v_a_1962_){
_start:
{
uint8_t v_usedLetOnly_boxed_1963_; lean_object* v_res_1964_; 
v_usedLetOnly_boxed_1963_ = lean_unbox(v_usedLetOnly_1958_);
v_res_1964_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__3(v_fvars_1957_, v_usedLetOnly_boxed_1963_, v_inst_1959_, v_toBind_1960_, v___f_1961_, v_a_1962_);
return v_res_1964_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1(lean_object* v___x_1965_, lean_object* v___x_1966_, lean_object* v_binderName_1967_, uint8_t v_binderInfo_1968_, lean_object* v___f_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_){
_start:
{
uint8_t v___x_1972_; lean_object* v___x_3878__overap_1973_; lean_object* v___x_1974_; 
v___x_1972_ = 0;
v___x_3878__overap_1973_ = l_Lean_Meta_withLocalDecl___redArg(v___x_1965_, v___x_1966_, v_binderName_1967_, v_binderInfo_1968_, v_a_1971_, v___f_1969_, v___x_1972_);
lean_inc(v_a_1970_);
v___x_1974_ = lean_apply_1(v___x_3878__overap_1973_, v_a_1970_);
return v___x_1974_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1___boxed(lean_object* v___x_1975_, lean_object* v___x_1976_, lean_object* v_binderName_1977_, lean_object* v_binderInfo_1978_, lean_object* v___f_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_){
_start:
{
uint8_t v_binderInfo_4067__boxed_1982_; lean_object* v_res_1983_; 
v_binderInfo_4067__boxed_1982_ = lean_unbox(v_binderInfo_1978_);
v_res_1983_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1(v___x_1975_, v___x_1976_, v_binderName_1977_, v_binderInfo_4067__boxed_1982_, v___f_1979_, v_a_1980_, v_a_1981_);
lean_dec(v_a_1980_);
return v_res_1983_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__3(lean_object* v_fvars_1984_, uint8_t v_usedLetOnly_1985_, lean_object* v_inst_1986_, lean_object* v_toBind_1987_, lean_object* v___f_1988_, lean_object* v_a_1989_){
_start:
{
uint8_t v___x_1990_; uint8_t v___x_1991_; uint8_t v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; 
v___x_1990_ = 0;
v___x_1991_ = 1;
v___x_1992_ = 1;
v___x_1993_ = lean_box(v___x_1990_);
v___x_1994_ = lean_box(v_usedLetOnly_1985_);
v___x_1995_ = lean_box(v___x_1991_);
v___x_1996_ = lean_box(v___x_1992_);
v___x_1997_ = lean_alloc_closure((void*)(l_Lean_Meta_mkForallFVars___boxed), 11, 6);
lean_closure_set(v___x_1997_, 0, v_fvars_1984_);
lean_closure_set(v___x_1997_, 1, v_a_1989_);
lean_closure_set(v___x_1997_, 2, v___x_1993_);
lean_closure_set(v___x_1997_, 3, v___x_1994_);
lean_closure_set(v___x_1997_, 4, v___x_1995_);
lean_closure_set(v___x_1997_, 5, v___x_1996_);
v___x_1998_ = lean_apply_2(v_inst_1986_, lean_box(0), v___x_1997_);
v___x_1999_ = lean_apply_4(v_toBind_1987_, lean_box(0), lean_box(0), v___x_1998_, v___f_1988_);
return v___x_1999_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__3___boxed(lean_object* v_fvars_2000_, lean_object* v_usedLetOnly_2001_, lean_object* v_inst_2002_, lean_object* v_toBind_2003_, lean_object* v___f_2004_, lean_object* v_a_2005_){
_start:
{
uint8_t v_usedLetOnly_boxed_2006_; lean_object* v_res_2007_; 
v_usedLetOnly_boxed_2006_ = lean_unbox(v_usedLetOnly_2001_);
v_res_2007_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__3(v_fvars_2000_, v_usedLetOnly_boxed_2006_, v_inst_2002_, v_toBind_2003_, v___f_2004_, v_a_2005_);
return v_res_2007_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__7(lean_object* v___f_2008_, lean_object* v___y_2009_, lean_object* v_a_2010_){
_start:
{
lean_object* v___x_2011_; 
lean_inc(v___y_2009_);
v___x_2011_ = lean_apply_2(v___f_2008_, v_a_2010_, v___y_2009_);
return v___x_2011_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__7___boxed(lean_object* v___f_2012_, lean_object* v___y_2013_, lean_object* v_a_2014_){
_start:
{
lean_object* v_res_2015_; 
v_res_2015_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__7(v___f_2012_, v___y_2013_, v_a_2014_);
lean_dec(v___y_2013_);
return v_res_2015_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1(lean_object* v_toApplicative_2016_, lean_object* v_acc_2017_, lean_object* v_next_2018_, lean_object* v_a_2019_){
_start:
{
lean_object* v_toPure_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; 
v_toPure_2020_ = lean_ctor_get(v_toApplicative_2016_, 1);
lean_inc(v_toPure_2020_);
lean_dec_ref(v_toApplicative_2016_);
v___x_2021_ = lean_array_fset(v_acc_2017_, v_next_2018_, v_a_2019_);
v___x_2022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2022_, 0, v___x_2021_);
v___x_2023_ = lean_apply_2(v_toPure_2020_, lean_box(0), v___x_2022_);
return v___x_2023_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1___boxed(lean_object* v_toApplicative_2024_, lean_object* v_acc_2025_, lean_object* v_next_2026_, lean_object* v_a_2027_){
_start:
{
lean_object* v_res_2028_; 
v_res_2028_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1(v_toApplicative_2024_, v_acc_2025_, v_next_2026_, v_a_2027_);
lean_dec(v_next_2026_);
return v_res_2028_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__2(lean_object* v_toApplicative_2029_, lean_object* v_next_2030_, lean_object* v_G_2031_, lean_object* v___y_2032_, lean_object* v_a_2033_){
_start:
{
if (lean_obj_tag(v_a_2033_) == 0)
{
lean_object* v_a_2034_; lean_object* v_toPure_2035_; lean_object* v___x_2036_; 
lean_dec(v_G_2031_);
v_a_2034_ = lean_ctor_get(v_a_2033_, 0);
lean_inc(v_a_2034_);
lean_dec_ref_known(v_a_2033_, 1);
v_toPure_2035_ = lean_ctor_get(v_toApplicative_2029_, 1);
lean_inc(v_toPure_2035_);
lean_dec_ref(v_toApplicative_2029_);
v___x_2036_ = lean_apply_2(v_toPure_2035_, lean_box(0), v_a_2034_);
return v___x_2036_;
}
else
{
lean_object* v_a_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; 
lean_dec_ref(v_toApplicative_2029_);
v_a_2037_ = lean_ctor_get(v_a_2033_, 0);
lean_inc(v_a_2037_);
lean_dec_ref_known(v_a_2033_, 1);
v___x_2038_ = lean_unsigned_to_nat(1u);
v___x_2039_ = lean_nat_add(v_next_2030_, v___x_2038_);
lean_inc(v___y_2032_);
v___x_2040_ = lean_apply_5(v_G_2031_, v___x_2039_, v_a_2037_, lean_box(0), lean_box(0), v___y_2032_);
return v___x_2040_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__2___boxed(lean_object* v_toApplicative_2041_, lean_object* v_next_2042_, lean_object* v_G_2043_, lean_object* v___y_2044_, lean_object* v_a_2045_){
_start:
{
lean_object* v_res_2046_; 
v_res_2046_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__2(v_toApplicative_2041_, v_next_2042_, v_G_2043_, v___y_2044_, v_a_2045_);
lean_dec(v___y_2044_);
lean_dec(v_next_2042_);
return v_res_2046_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5(lean_object* v_f_2047_, lean_object* v_inst_2048_, lean_object* v_inst_2049_, lean_object* v_inst_2050_, lean_object* v_pre_2051_, lean_object* v_post_2052_, uint8_t v_usedLetOnly_2053_, uint8_t v_skipConstInApp_2054_, uint8_t v_skipInstances_2055_, lean_object* v_x_2056_, lean_object* v_x_2057_, lean_object* v___y_2058_, lean_object* v_a_2059_){
_start:
{
lean_object* v___x_2060_; lean_object* v___x_2061_; 
v___x_2060_ = l_Lean_mkAppN(v_f_2047_, v_a_2059_);
v___x_2061_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2048_, v_inst_2049_, v_inst_2050_, v_pre_2051_, v_post_2052_, v_usedLetOnly_2053_, v_skipConstInApp_2054_, v_skipInstances_2055_, v_x_2056_, v_x_2057_, v___x_2060_, v___y_2058_);
return v___x_2061_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5___boxed(lean_object* v_f_2062_, lean_object* v_inst_2063_, lean_object* v_inst_2064_, lean_object* v_inst_2065_, lean_object* v_pre_2066_, lean_object* v_post_2067_, lean_object* v_usedLetOnly_2068_, lean_object* v_skipConstInApp_2069_, lean_object* v_skipInstances_2070_, lean_object* v_x_2071_, lean_object* v_x_2072_, lean_object* v___y_2073_, lean_object* v_a_2074_){
_start:
{
uint8_t v_usedLetOnly_boxed_2075_; uint8_t v_skipConstInApp_boxed_2076_; uint8_t v_skipInstances_boxed_2077_; lean_object* v_res_2078_; 
v_usedLetOnly_boxed_2075_ = lean_unbox(v_usedLetOnly_2068_);
v_skipConstInApp_boxed_2076_ = lean_unbox(v_skipConstInApp_2069_);
v_skipInstances_boxed_2077_ = lean_unbox(v_skipInstances_2070_);
v_res_2078_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5(v_f_2062_, v_inst_2063_, v_inst_2064_, v_inst_2065_, v_pre_2066_, v_post_2067_, v_usedLetOnly_boxed_2075_, v_skipConstInApp_boxed_2076_, v_skipInstances_boxed_2077_, v_x_2071_, v_x_2072_, v___y_2073_, v_a_2074_);
lean_dec_ref(v_a_2074_);
lean_dec(v___y_2073_);
return v_res_2078_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___boxed(lean_object* v_inst_2079_, lean_object* v_inst_2080_, lean_object* v_inst_2081_, lean_object* v_pre_2082_, lean_object* v_post_2083_, lean_object* v_usedLetOnly_2084_, lean_object* v_skipConstInApp_2085_, lean_object* v_skipInstances_2086_, lean_object* v_x_2087_, lean_object* v_x_2088_, lean_object* v_e_2089_, lean_object* v_a_2090_){
_start:
{
uint8_t v_usedLetOnly_boxed_2091_; uint8_t v_skipConstInApp_boxed_2092_; uint8_t v_skipInstances_boxed_2093_; lean_object* v_res_2094_; 
v_usedLetOnly_boxed_2091_ = lean_unbox(v_usedLetOnly_2084_);
v_skipConstInApp_boxed_2092_ = lean_unbox(v_skipConstInApp_2085_);
v_skipInstances_boxed_2093_ = lean_unbox(v_skipInstances_2086_);
v_res_2094_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2079_, v_inst_2080_, v_inst_2081_, v_pre_2082_, v_post_2083_, v_usedLetOnly_boxed_2091_, v_skipConstInApp_boxed_2092_, v_skipInstances_boxed_2093_, v_x_2087_, v_x_2088_, v_e_2089_, v_a_2090_);
lean_dec(v_a_2090_);
return v_res_2094_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__4(lean_object* v___x_2095_, lean_object* v_toApplicative_2096_, lean_object* v_toBind_2097_, lean_object* v___f_2098_, lean_object* v_paramInfo_2099_, lean_object* v_inst_2100_, lean_object* v_inst_2101_, lean_object* v_inst_2102_, lean_object* v_pre_2103_, lean_object* v_post_2104_, uint8_t v_usedLetOnly_2105_, uint8_t v_skipConstInApp_2106_, uint8_t v_skipInstances_2107_, lean_object* v_x_2108_, lean_object* v_x_2109_, lean_object* v_next_2110_, lean_object* v_acc_2111_, lean_object* v_h_2112_, lean_object* v_G_2113_, lean_object* v___y_2114_){
_start:
{
uint8_t v___x_2115_; 
v___x_2115_ = lean_nat_dec_lt(v_next_2110_, v___x_2095_);
if (v___x_2115_ == 0)
{
lean_object* v_toPure_2116_; lean_object* v___x_2117_; 
lean_dec(v_G_2113_);
lean_dec(v_next_2110_);
lean_dec(v_x_2109_);
lean_dec(v_post_2104_);
lean_dec(v_pre_2103_);
lean_dec_ref(v_inst_2102_);
lean_dec(v_inst_2101_);
lean_dec_ref(v_inst_2100_);
lean_dec(v___f_2098_);
lean_dec(v_toBind_2097_);
v_toPure_2116_ = lean_ctor_get(v_toApplicative_2096_, 1);
lean_inc(v_toPure_2116_);
lean_dec_ref(v_toApplicative_2096_);
v___x_2117_ = lean_apply_2(v_toPure_2116_, lean_box(0), v_acc_2111_);
return v___x_2117_;
}
else
{
lean_object* v___f_2118_; lean_object* v___y_2120_; lean_object* v___x_2123_; lean_object* v___x_2124_; uint8_t v___x_2125_; 
lean_inc(v___y_2114_);
lean_inc(v_next_2110_);
lean_inc_ref(v_toApplicative_2096_);
v___f_2118_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__2___boxed), 5, 4);
lean_closure_set(v___f_2118_, 0, v_toApplicative_2096_);
lean_closure_set(v___f_2118_, 1, v_next_2110_);
lean_closure_set(v___f_2118_, 2, v_G_2113_);
lean_closure_set(v___f_2118_, 3, v___y_2114_);
v___x_2123_ = lean_array_fget_borrowed(v_acc_2111_, v_next_2110_);
v___x_2124_ = lean_array_get_size(v_paramInfo_2099_);
v___x_2125_ = lean_nat_dec_lt(v_next_2110_, v___x_2124_);
if (v___x_2125_ == 0)
{
lean_object* v___f_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; 
lean_inc(v___x_2123_);
v___f_2126_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2126_, 0, v_toApplicative_2096_);
lean_closure_set(v___f_2126_, 1, v_acc_2111_);
lean_closure_set(v___f_2126_, 2, v_next_2110_);
v___x_2127_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2100_, v_inst_2101_, v_inst_2102_, v_pre_2103_, v_post_2104_, v_usedLetOnly_2105_, v_skipConstInApp_2106_, v_skipInstances_2107_, v_x_2108_, v_x_2109_, v___x_2123_, v___y_2114_);
lean_inc(v_toBind_2097_);
v___x_2128_ = lean_apply_4(v_toBind_2097_, lean_box(0), lean_box(0), v___x_2127_, v___f_2126_);
v___y_2120_ = v___x_2128_;
goto v___jp_2119_;
}
else
{
lean_object* v___x_2129_; uint8_t v_isInstance_2130_; 
v___x_2129_ = lean_array_fget_borrowed(v_paramInfo_2099_, v_next_2110_);
v_isInstance_2130_ = lean_ctor_get_uint8(v___x_2129_, sizeof(void*)*1 + 4);
if (v_isInstance_2130_ == 0)
{
lean_object* v___f_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; 
lean_inc(v___x_2123_);
v___f_2131_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2131_, 0, v_toApplicative_2096_);
lean_closure_set(v___f_2131_, 1, v_acc_2111_);
lean_closure_set(v___f_2131_, 2, v_next_2110_);
v___x_2132_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2100_, v_inst_2101_, v_inst_2102_, v_pre_2103_, v_post_2104_, v_usedLetOnly_2105_, v_skipConstInApp_2106_, v_skipInstances_2107_, v_x_2108_, v_x_2109_, v___x_2123_, v___y_2114_);
lean_inc(v_toBind_2097_);
v___x_2133_ = lean_apply_4(v_toBind_2097_, lean_box(0), lean_box(0), v___x_2132_, v___f_2131_);
v___y_2120_ = v___x_2133_;
goto v___jp_2119_;
}
else
{
lean_object* v_toPure_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; 
lean_dec(v_next_2110_);
lean_dec(v_x_2109_);
lean_dec(v_post_2104_);
lean_dec(v_pre_2103_);
lean_dec_ref(v_inst_2102_);
lean_dec(v_inst_2101_);
lean_dec_ref(v_inst_2100_);
v_toPure_2134_ = lean_ctor_get(v_toApplicative_2096_, 1);
lean_inc(v_toPure_2134_);
lean_dec_ref(v_toApplicative_2096_);
v___x_2135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2135_, 0, v_acc_2111_);
v___x_2136_ = lean_apply_2(v_toPure_2134_, lean_box(0), v___x_2135_);
v___y_2120_ = v___x_2136_;
goto v___jp_2119_;
}
}
v___jp_2119_:
{
lean_object* v___x_2121_; lean_object* v___x_2122_; 
lean_inc(v_toBind_2097_);
v___x_2121_ = lean_apply_4(v_toBind_2097_, lean_box(0), lean_box(0), v___y_2120_, v___f_2098_);
v___x_2122_ = lean_apply_4(v_toBind_2097_, lean_box(0), lean_box(0), v___x_2121_, v___f_2118_);
return v___x_2122_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__4___boxed(lean_object** _args){
lean_object* v___x_2137_ = _args[0];
lean_object* v_toApplicative_2138_ = _args[1];
lean_object* v_toBind_2139_ = _args[2];
lean_object* v___f_2140_ = _args[3];
lean_object* v_paramInfo_2141_ = _args[4];
lean_object* v_inst_2142_ = _args[5];
lean_object* v_inst_2143_ = _args[6];
lean_object* v_inst_2144_ = _args[7];
lean_object* v_pre_2145_ = _args[8];
lean_object* v_post_2146_ = _args[9];
lean_object* v_usedLetOnly_2147_ = _args[10];
lean_object* v_skipConstInApp_2148_ = _args[11];
lean_object* v_skipInstances_2149_ = _args[12];
lean_object* v_x_2150_ = _args[13];
lean_object* v_x_2151_ = _args[14];
lean_object* v_next_2152_ = _args[15];
lean_object* v_acc_2153_ = _args[16];
lean_object* v_h_2154_ = _args[17];
lean_object* v_G_2155_ = _args[18];
lean_object* v___y_2156_ = _args[19];
_start:
{
uint8_t v_usedLetOnly_boxed_2157_; uint8_t v_skipConstInApp_boxed_2158_; uint8_t v_skipInstances_boxed_2159_; lean_object* v_res_2160_; 
v_usedLetOnly_boxed_2157_ = lean_unbox(v_usedLetOnly_2147_);
v_skipConstInApp_boxed_2158_ = lean_unbox(v_skipConstInApp_2148_);
v_skipInstances_boxed_2159_ = lean_unbox(v_skipInstances_2149_);
v_res_2160_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__4(v___x_2137_, v_toApplicative_2138_, v_toBind_2139_, v___f_2140_, v_paramInfo_2141_, v_inst_2142_, v_inst_2143_, v_inst_2144_, v_pre_2145_, v_post_2146_, v_usedLetOnly_boxed_2157_, v_skipConstInApp_boxed_2158_, v_skipInstances_boxed_2159_, v_x_2150_, v_x_2151_, v_next_2152_, v_acc_2153_, v_h_2154_, v_G_2155_, v___y_2156_);
lean_dec(v___y_2156_);
lean_dec_ref(v_paramInfo_2141_);
lean_dec(v___x_2137_);
return v_res_2160_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__3(lean_object* v___x_2161_, lean_object* v_toApplicative_2162_, lean_object* v_toBind_2163_, lean_object* v___f_2164_, lean_object* v_inst_2165_, lean_object* v_inst_2166_, lean_object* v_inst_2167_, lean_object* v_pre_2168_, lean_object* v_post_2169_, uint8_t v_usedLetOnly_2170_, uint8_t v_skipConstInApp_2171_, uint8_t v_skipInstances_2172_, lean_object* v_x_2173_, lean_object* v_x_2174_, lean_object* v_args_2175_, lean_object* v___y_2176_, lean_object* v___f_2177_, lean_object* v_a_2178_){
_start:
{
lean_object* v_paramInfo_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___f_2184_; lean_object* v___x_3638__overap_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; 
v_paramInfo_2179_ = lean_ctor_get(v_a_2178_, 0);
lean_inc_ref(v_paramInfo_2179_);
lean_dec_ref(v_a_2178_);
v___x_2180_ = lean_unsigned_to_nat(0u);
v___x_2181_ = lean_box(v_usedLetOnly_2170_);
v___x_2182_ = lean_box(v_skipConstInApp_2171_);
v___x_2183_ = lean_box(v_skipInstances_2172_);
lean_inc(v_toBind_2163_);
v___f_2184_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__4___boxed), 20, 15);
lean_closure_set(v___f_2184_, 0, v___x_2161_);
lean_closure_set(v___f_2184_, 1, v_toApplicative_2162_);
lean_closure_set(v___f_2184_, 2, v_toBind_2163_);
lean_closure_set(v___f_2184_, 3, v___f_2164_);
lean_closure_set(v___f_2184_, 4, v_paramInfo_2179_);
lean_closure_set(v___f_2184_, 5, v_inst_2165_);
lean_closure_set(v___f_2184_, 6, v_inst_2166_);
lean_closure_set(v___f_2184_, 7, v_inst_2167_);
lean_closure_set(v___f_2184_, 8, v_pre_2168_);
lean_closure_set(v___f_2184_, 9, v_post_2169_);
lean_closure_set(v___f_2184_, 10, v___x_2181_);
lean_closure_set(v___f_2184_, 11, v___x_2182_);
lean_closure_set(v___f_2184_, 12, v___x_2183_);
lean_closure_set(v___f_2184_, 13, v_x_2173_);
lean_closure_set(v___f_2184_, 14, v_x_2174_);
v___x_3638__overap_2185_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_2184_, v___x_2180_, v_args_2175_, lean_box(0));
lean_inc(v___y_2176_);
v___x_2186_ = lean_apply_1(v___x_3638__overap_2185_, v___y_2176_);
v___x_2187_ = lean_apply_4(v_toBind_2163_, lean_box(0), lean_box(0), v___x_2186_, v___f_2177_);
return v___x_2187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__3___boxed(lean_object** _args){
lean_object* v___x_2188_ = _args[0];
lean_object* v_toApplicative_2189_ = _args[1];
lean_object* v_toBind_2190_ = _args[2];
lean_object* v___f_2191_ = _args[3];
lean_object* v_inst_2192_ = _args[4];
lean_object* v_inst_2193_ = _args[5];
lean_object* v_inst_2194_ = _args[6];
lean_object* v_pre_2195_ = _args[7];
lean_object* v_post_2196_ = _args[8];
lean_object* v_usedLetOnly_2197_ = _args[9];
lean_object* v_skipConstInApp_2198_ = _args[10];
lean_object* v_skipInstances_2199_ = _args[11];
lean_object* v_x_2200_ = _args[12];
lean_object* v_x_2201_ = _args[13];
lean_object* v_args_2202_ = _args[14];
lean_object* v___y_2203_ = _args[15];
lean_object* v___f_2204_ = _args[16];
lean_object* v_a_2205_ = _args[17];
_start:
{
uint8_t v_usedLetOnly_boxed_2206_; uint8_t v_skipConstInApp_boxed_2207_; uint8_t v_skipInstances_boxed_2208_; lean_object* v_res_2209_; 
v_usedLetOnly_boxed_2206_ = lean_unbox(v_usedLetOnly_2197_);
v_skipConstInApp_boxed_2207_ = lean_unbox(v_skipConstInApp_2198_);
v_skipInstances_boxed_2208_ = lean_unbox(v_skipInstances_2199_);
v_res_2209_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__3(v___x_2188_, v_toApplicative_2189_, v_toBind_2190_, v___f_2191_, v_inst_2192_, v_inst_2193_, v_inst_2194_, v_pre_2195_, v_post_2196_, v_usedLetOnly_boxed_2206_, v_skipConstInApp_boxed_2207_, v_skipInstances_boxed_2208_, v_x_2200_, v_x_2201_, v_args_2202_, v___y_2203_, v___f_2204_, v_a_2205_);
lean_dec(v___y_2203_);
return v_res_2209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__6(uint8_t v_skipInstances_2210_, lean_object* v_inst_2211_, lean_object* v_inst_2212_, lean_object* v_inst_2213_, lean_object* v_pre_2214_, lean_object* v_post_2215_, uint8_t v_usedLetOnly_2216_, uint8_t v_skipConstInApp_2217_, lean_object* v_x_2218_, lean_object* v_x_2219_, lean_object* v_args_2220_, lean_object* v___x_2221_, lean_object* v_toBind_2222_, lean_object* v_toApplicative_2223_, lean_object* v___f_2224_, lean_object* v_f_2225_, lean_object* v___y_2226_){
_start:
{
if (v_skipInstances_2210_ == 0)
{
lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___f_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; size_t v_sz_2235_; size_t v___x_2236_; lean_object* v___x_3651__overap_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; 
lean_dec(v___f_2224_);
lean_dec_ref(v_toApplicative_2223_);
v___x_2227_ = lean_box(v_usedLetOnly_2216_);
v___x_2228_ = lean_box(v_skipConstInApp_2217_);
v___x_2229_ = lean_box(v_skipInstances_2210_);
lean_inc_n(v___y_2226_, 2);
lean_inc(v_x_2219_);
lean_inc(v_post_2215_);
lean_inc(v_pre_2214_);
lean_inc_ref(v_inst_2213_);
lean_inc(v_inst_2212_);
lean_inc_ref(v_inst_2211_);
v___f_2230_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5___boxed), 13, 12);
lean_closure_set(v___f_2230_, 0, v_f_2225_);
lean_closure_set(v___f_2230_, 1, v_inst_2211_);
lean_closure_set(v___f_2230_, 2, v_inst_2212_);
lean_closure_set(v___f_2230_, 3, v_inst_2213_);
lean_closure_set(v___f_2230_, 4, v_pre_2214_);
lean_closure_set(v___f_2230_, 5, v_post_2215_);
lean_closure_set(v___f_2230_, 6, v___x_2227_);
lean_closure_set(v___f_2230_, 7, v___x_2228_);
lean_closure_set(v___f_2230_, 8, v___x_2229_);
lean_closure_set(v___f_2230_, 9, v_x_2218_);
lean_closure_set(v___f_2230_, 10, v_x_2219_);
lean_closure_set(v___f_2230_, 11, v___y_2226_);
v___x_2231_ = lean_box(v_usedLetOnly_2216_);
v___x_2232_ = lean_box(v_skipConstInApp_2217_);
v___x_2233_ = lean_box(v_skipInstances_2210_);
v___x_2234_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___boxed), 12, 10);
lean_closure_set(v___x_2234_, 0, v_inst_2211_);
lean_closure_set(v___x_2234_, 1, v_inst_2212_);
lean_closure_set(v___x_2234_, 2, v_inst_2213_);
lean_closure_set(v___x_2234_, 3, v_pre_2214_);
lean_closure_set(v___x_2234_, 4, v_post_2215_);
lean_closure_set(v___x_2234_, 5, v___x_2231_);
lean_closure_set(v___x_2234_, 6, v___x_2232_);
lean_closure_set(v___x_2234_, 7, v___x_2233_);
lean_closure_set(v___x_2234_, 8, v_x_2218_);
lean_closure_set(v___x_2234_, 9, v_x_2219_);
v_sz_2235_ = lean_array_size(v_args_2220_);
v___x_2236_ = ((size_t)0ULL);
v___x_3651__overap_2237_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2221_, v___x_2234_, v_sz_2235_, v___x_2236_, v_args_2220_);
v___x_2238_ = lean_apply_1(v___x_3651__overap_2237_, v___y_2226_);
v___x_2239_ = lean_apply_4(v_toBind_2222_, lean_box(0), lean_box(0), v___x_2238_, v___f_2230_);
return v___x_2239_;
}
else
{
lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___f_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___f_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; 
lean_dec_ref(v___x_2221_);
v___x_2240_ = lean_box(v_usedLetOnly_2216_);
v___x_2241_ = lean_box(v_skipConstInApp_2217_);
v___x_2242_ = lean_box(v_skipInstances_2210_);
lean_inc_n(v___y_2226_, 2);
lean_inc(v_x_2219_);
lean_inc(v_post_2215_);
lean_inc(v_pre_2214_);
lean_inc_ref(v_inst_2213_);
lean_inc_n(v_inst_2212_, 2);
lean_inc_ref(v_inst_2211_);
lean_inc_ref(v_f_2225_);
v___f_2243_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5___boxed), 13, 12);
lean_closure_set(v___f_2243_, 0, v_f_2225_);
lean_closure_set(v___f_2243_, 1, v_inst_2211_);
lean_closure_set(v___f_2243_, 2, v_inst_2212_);
lean_closure_set(v___f_2243_, 3, v_inst_2213_);
lean_closure_set(v___f_2243_, 4, v_pre_2214_);
lean_closure_set(v___f_2243_, 5, v_post_2215_);
lean_closure_set(v___f_2243_, 6, v___x_2240_);
lean_closure_set(v___f_2243_, 7, v___x_2241_);
lean_closure_set(v___f_2243_, 8, v___x_2242_);
lean_closure_set(v___f_2243_, 9, v_x_2218_);
lean_closure_set(v___f_2243_, 10, v_x_2219_);
lean_closure_set(v___f_2243_, 11, v___y_2226_);
v___x_2244_ = lean_array_get_size(v_args_2220_);
v___x_2245_ = lean_box(v_usedLetOnly_2216_);
v___x_2246_ = lean_box(v_skipConstInApp_2217_);
v___x_2247_ = lean_box(v_skipInstances_2210_);
lean_inc(v_toBind_2222_);
v___f_2248_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__3___boxed), 18, 17);
lean_closure_set(v___f_2248_, 0, v___x_2244_);
lean_closure_set(v___f_2248_, 1, v_toApplicative_2223_);
lean_closure_set(v___f_2248_, 2, v_toBind_2222_);
lean_closure_set(v___f_2248_, 3, v___f_2224_);
lean_closure_set(v___f_2248_, 4, v_inst_2211_);
lean_closure_set(v___f_2248_, 5, v_inst_2212_);
lean_closure_set(v___f_2248_, 6, v_inst_2213_);
lean_closure_set(v___f_2248_, 7, v_pre_2214_);
lean_closure_set(v___f_2248_, 8, v_post_2215_);
lean_closure_set(v___f_2248_, 9, v___x_2245_);
lean_closure_set(v___f_2248_, 10, v___x_2246_);
lean_closure_set(v___f_2248_, 11, v___x_2247_);
lean_closure_set(v___f_2248_, 12, v_x_2218_);
lean_closure_set(v___f_2248_, 13, v_x_2219_);
lean_closure_set(v___f_2248_, 14, v_args_2220_);
lean_closure_set(v___f_2248_, 15, v___y_2226_);
lean_closure_set(v___f_2248_, 16, v___f_2243_);
v___x_2249_ = lean_alloc_closure((void*)(l_Lean_Meta_getFunInfoNArgs___boxed), 7, 2);
lean_closure_set(v___x_2249_, 0, v_f_2225_);
lean_closure_set(v___x_2249_, 1, v___x_2244_);
v___x_2250_ = lean_apply_2(v_inst_2212_, lean_box(0), v___x_2249_);
v___x_2251_ = lean_apply_4(v_toBind_2222_, lean_box(0), lean_box(0), v___x_2250_, v___f_2248_);
return v___x_2251_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__6___boxed(lean_object** _args){
lean_object* v_skipInstances_2252_ = _args[0];
lean_object* v_inst_2253_ = _args[1];
lean_object* v_inst_2254_ = _args[2];
lean_object* v_inst_2255_ = _args[3];
lean_object* v_pre_2256_ = _args[4];
lean_object* v_post_2257_ = _args[5];
lean_object* v_usedLetOnly_2258_ = _args[6];
lean_object* v_skipConstInApp_2259_ = _args[7];
lean_object* v_x_2260_ = _args[8];
lean_object* v_x_2261_ = _args[9];
lean_object* v_args_2262_ = _args[10];
lean_object* v___x_2263_ = _args[11];
lean_object* v_toBind_2264_ = _args[12];
lean_object* v_toApplicative_2265_ = _args[13];
lean_object* v___f_2266_ = _args[14];
lean_object* v_f_2267_ = _args[15];
lean_object* v___y_2268_ = _args[16];
_start:
{
uint8_t v_skipInstances_boxed_2269_; uint8_t v_usedLetOnly_boxed_2270_; uint8_t v_skipConstInApp_boxed_2271_; lean_object* v_res_2272_; 
v_skipInstances_boxed_2269_ = lean_unbox(v_skipInstances_2252_);
v_usedLetOnly_boxed_2270_ = lean_unbox(v_usedLetOnly_2258_);
v_skipConstInApp_boxed_2271_ = lean_unbox(v_skipConstInApp_2259_);
v_res_2272_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__6(v_skipInstances_boxed_2269_, v_inst_2253_, v_inst_2254_, v_inst_2255_, v_pre_2256_, v_post_2257_, v_usedLetOnly_boxed_2270_, v_skipConstInApp_boxed_2271_, v_x_2260_, v_x_2261_, v_args_2262_, v___x_2263_, v_toBind_2264_, v_toApplicative_2265_, v___f_2266_, v_f_2267_, v___y_2268_);
lean_dec(v___y_2268_);
return v_res_2272_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__9(uint8_t v_skipInstances_2273_, lean_object* v_inst_2274_, lean_object* v_inst_2275_, lean_object* v_inst_2276_, lean_object* v_pre_2277_, lean_object* v_post_2278_, uint8_t v_usedLetOnly_2279_, uint8_t v_skipConstInApp_2280_, lean_object* v_x_2281_, lean_object* v_x_2282_, lean_object* v___x_2283_, lean_object* v_toBind_2284_, lean_object* v_toApplicative_2285_, lean_object* v___f_2286_, lean_object* v_f_2287_, lean_object* v_args_2288_, lean_object* v___y_2289_){
_start:
{
lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___f_2293_; lean_object* v___f_2294_; 
v___x_2290_ = lean_box(v_skipInstances_2273_);
v___x_2291_ = lean_box(v_usedLetOnly_2279_);
v___x_2292_ = lean_box(v_skipConstInApp_2280_);
lean_inc_ref(v_toApplicative_2285_);
lean_inc(v_toBind_2284_);
lean_inc(v_x_2282_);
lean_inc(v_post_2278_);
lean_inc(v_pre_2277_);
lean_inc_ref(v_inst_2276_);
lean_inc(v_inst_2275_);
lean_inc_ref(v_inst_2274_);
v___f_2293_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__6___boxed), 17, 15);
lean_closure_set(v___f_2293_, 0, v___x_2290_);
lean_closure_set(v___f_2293_, 1, v_inst_2274_);
lean_closure_set(v___f_2293_, 2, v_inst_2275_);
lean_closure_set(v___f_2293_, 3, v_inst_2276_);
lean_closure_set(v___f_2293_, 4, v_pre_2277_);
lean_closure_set(v___f_2293_, 5, v_post_2278_);
lean_closure_set(v___f_2293_, 6, v___x_2291_);
lean_closure_set(v___f_2293_, 7, v___x_2292_);
lean_closure_set(v___f_2293_, 8, v_x_2281_);
lean_closure_set(v___f_2293_, 9, v_x_2282_);
lean_closure_set(v___f_2293_, 10, v_args_2288_);
lean_closure_set(v___f_2293_, 11, v___x_2283_);
lean_closure_set(v___f_2293_, 12, v_toBind_2284_);
lean_closure_set(v___f_2293_, 13, v_toApplicative_2285_);
lean_closure_set(v___f_2293_, 14, v___f_2286_);
lean_inc(v___y_2289_);
v___f_2294_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__7___boxed), 3, 2);
lean_closure_set(v___f_2294_, 0, v___f_2293_);
lean_closure_set(v___f_2294_, 1, v___y_2289_);
if (v_skipConstInApp_2280_ == 0)
{
lean_dec_ref(v_toApplicative_2285_);
goto v___jp_2295_;
}
else
{
uint8_t v___x_2298_; 
v___x_2298_ = l_Lean_Expr_isConst(v_f_2287_);
if (v___x_2298_ == 0)
{
lean_dec_ref(v_toApplicative_2285_);
goto v___jp_2295_;
}
else
{
lean_object* v_toPure_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; 
lean_dec(v_x_2282_);
lean_dec(v_post_2278_);
lean_dec(v_pre_2277_);
lean_dec_ref(v_inst_2276_);
lean_dec(v_inst_2275_);
lean_dec_ref(v_inst_2274_);
v_toPure_2299_ = lean_ctor_get(v_toApplicative_2285_, 1);
lean_inc(v_toPure_2299_);
lean_dec_ref(v_toApplicative_2285_);
v___x_2300_ = lean_apply_2(v_toPure_2299_, lean_box(0), v_f_2287_);
v___x_2301_ = lean_apply_4(v_toBind_2284_, lean_box(0), lean_box(0), v___x_2300_, v___f_2294_);
return v___x_2301_;
}
}
v___jp_2295_:
{
lean_object* v___x_2296_; lean_object* v___x_2297_; 
v___x_2296_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2274_, v_inst_2275_, v_inst_2276_, v_pre_2277_, v_post_2278_, v_usedLetOnly_2279_, v_skipConstInApp_2280_, v_skipInstances_2273_, v_x_2281_, v_x_2282_, v_f_2287_, v___y_2289_);
v___x_2297_ = lean_apply_4(v_toBind_2284_, lean_box(0), lean_box(0), v___x_2296_, v___f_2294_);
return v___x_2297_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__9___boxed(lean_object** _args){
lean_object* v_skipInstances_2302_ = _args[0];
lean_object* v_inst_2303_ = _args[1];
lean_object* v_inst_2304_ = _args[2];
lean_object* v_inst_2305_ = _args[3];
lean_object* v_pre_2306_ = _args[4];
lean_object* v_post_2307_ = _args[5];
lean_object* v_usedLetOnly_2308_ = _args[6];
lean_object* v_skipConstInApp_2309_ = _args[7];
lean_object* v_x_2310_ = _args[8];
lean_object* v_x_2311_ = _args[9];
lean_object* v___x_2312_ = _args[10];
lean_object* v_toBind_2313_ = _args[11];
lean_object* v_toApplicative_2314_ = _args[12];
lean_object* v___f_2315_ = _args[13];
lean_object* v_f_2316_ = _args[14];
lean_object* v_args_2317_ = _args[15];
lean_object* v___y_2318_ = _args[16];
_start:
{
uint8_t v_skipInstances_boxed_2319_; uint8_t v_usedLetOnly_boxed_2320_; uint8_t v_skipConstInApp_boxed_2321_; lean_object* v_res_2322_; 
v_skipInstances_boxed_2319_ = lean_unbox(v_skipInstances_2302_);
v_usedLetOnly_boxed_2320_ = lean_unbox(v_usedLetOnly_2308_);
v_skipConstInApp_boxed_2321_ = lean_unbox(v_skipConstInApp_2309_);
v_res_2322_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__9(v_skipInstances_boxed_2319_, v_inst_2303_, v_inst_2304_, v_inst_2305_, v_pre_2306_, v_post_2307_, v_usedLetOnly_boxed_2320_, v_skipConstInApp_boxed_2321_, v_x_2310_, v_x_2311_, v___x_2312_, v_toBind_2313_, v_toApplicative_2314_, v___f_2315_, v_f_2316_, v_args_2317_, v___y_2318_);
lean_dec(v___y_2318_);
return v_res_2322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__0(lean_object* v_fvars_2325_, lean_object* v_inst_2326_, lean_object* v_inst_2327_, lean_object* v_inst_2328_, lean_object* v_pre_2329_, lean_object* v_post_2330_, uint8_t v_usedLetOnly_2331_, uint8_t v_skipConstInApp_2332_, uint8_t v_skipInstances_2333_, lean_object* v_x_2334_, lean_object* v_x_2335_, lean_object* v_body_2336_, lean_object* v_x_2337_, lean_object* v___y_2338_){
_start:
{
lean_object* v___x_2339_; lean_object* v___x_2340_; 
v___x_2339_ = lean_array_push(v_fvars_2325_, v_x_2337_);
v___x_2340_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(v_inst_2326_, v_inst_2327_, v_inst_2328_, v_pre_2329_, v_post_2330_, v_usedLetOnly_2331_, v_skipConstInApp_2332_, v_skipInstances_2333_, v_x_2334_, v_x_2335_, v___x_2339_, v_body_2336_, v___y_2338_);
return v___x_2340_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__0___boxed(lean_object* v_fvars_2341_, lean_object* v_inst_2342_, lean_object* v_inst_2343_, lean_object* v_inst_2344_, lean_object* v_pre_2345_, lean_object* v_post_2346_, lean_object* v_usedLetOnly_2347_, lean_object* v_skipConstInApp_2348_, lean_object* v_skipInstances_2349_, lean_object* v_x_2350_, lean_object* v_x_2351_, lean_object* v_body_2352_, lean_object* v_x_2353_, lean_object* v___y_2354_){
_start:
{
uint8_t v_usedLetOnly_boxed_2355_; uint8_t v_skipConstInApp_boxed_2356_; uint8_t v_skipInstances_boxed_2357_; lean_object* v_res_2358_; 
v_usedLetOnly_boxed_2355_ = lean_unbox(v_usedLetOnly_2347_);
v_skipConstInApp_boxed_2356_ = lean_unbox(v_skipConstInApp_2348_);
v_skipInstances_boxed_2357_ = lean_unbox(v_skipInstances_2349_);
v_res_2358_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__0(v_fvars_2341_, v_inst_2342_, v_inst_2343_, v_inst_2344_, v_pre_2345_, v_post_2346_, v_usedLetOnly_boxed_2355_, v_skipConstInApp_boxed_2356_, v_skipInstances_boxed_2357_, v_x_2350_, v_x_2351_, v_body_2352_, v_x_2353_, v___y_2354_);
lean_dec(v___y_2354_);
return v_res_2358_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3___boxed(lean_object* v_inst_2359_, lean_object* v_inst_2360_, lean_object* v_inst_2361_, lean_object* v_pre_2362_, lean_object* v_post_2363_, lean_object* v_usedLetOnly_2364_, lean_object* v_skipConstInApp_2365_, lean_object* v_skipInstances_2366_, lean_object* v_x_2367_, lean_object* v_x_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_){
_start:
{
uint8_t v_usedLetOnly_boxed_2371_; uint8_t v_skipConstInApp_boxed_2372_; uint8_t v_skipInstances_boxed_2373_; lean_object* v_res_2374_; 
v_usedLetOnly_boxed_2371_ = lean_unbox(v_usedLetOnly_2364_);
v_skipConstInApp_boxed_2372_ = lean_unbox(v_skipConstInApp_2365_);
v_skipInstances_boxed_2373_ = lean_unbox(v_skipInstances_2366_);
v_res_2374_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3(v_inst_2359_, v_inst_2360_, v_inst_2361_, v_pre_2362_, v_post_2363_, v_usedLetOnly_boxed_2371_, v_skipConstInApp_boxed_2372_, v_skipInstances_boxed_2373_, v_x_2367_, v_x_2368_, v_a_2369_, v_a_2370_);
lean_dec(v_a_2369_);
return v_res_2374_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(lean_object* v_inst_2375_, lean_object* v_inst_2376_, lean_object* v_inst_2377_, lean_object* v_pre_2378_, lean_object* v_post_2379_, uint8_t v_usedLetOnly_2380_, uint8_t v_skipConstInApp_2381_, uint8_t v_skipInstances_2382_, lean_object* v_x_2383_, lean_object* v_x_2384_, lean_object* v_fvars_2385_, lean_object* v_e_2386_, lean_object* v_a_2387_){
_start:
{
lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___f_2392_; lean_object* v___f_2393_; lean_object* v___x_2394_; 
v___x_2388_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0));
v___x_2389_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1));
lean_inc_ref(v_inst_2375_);
v___x_2390_ = l_Lean_MonadCacheT_instMonad___redArg(v_x_2383_, v___x_2388_, v___x_2389_, v_inst_2375_);
v___x_2391_ = l_Lean_MonadCacheT_instMonadControl___redArg(v_x_2383_, v___x_2388_, v___x_2389_);
lean_inc_ref_n(v_inst_2377_, 2);
lean_inc_ref(v___x_2391_);
v___f_2392_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_2392_, 0, v___x_2391_);
lean_closure_set(v___f_2392_, 1, v_inst_2377_);
v___f_2393_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_2393_, 0, v___x_2391_);
lean_closure_set(v___f_2393_, 1, v_inst_2377_);
v___x_2394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2394_, 0, v___f_2392_);
lean_ctor_set(v___x_2394_, 1, v___f_2393_);
if (lean_obj_tag(v_e_2386_) == 7)
{
lean_object* v_binderName_2395_; lean_object* v_binderType_2396_; lean_object* v_body_2397_; uint8_t v_binderInfo_2398_; lean_object* v_toBind_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___f_2403_; lean_object* v___x_2404_; lean_object* v___f_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; 
v_binderName_2395_ = lean_ctor_get(v_e_2386_, 0);
lean_inc(v_binderName_2395_);
v_binderType_2396_ = lean_ctor_get(v_e_2386_, 1);
lean_inc_ref(v_binderType_2396_);
v_body_2397_ = lean_ctor_get(v_e_2386_, 2);
lean_inc_ref(v_body_2397_);
v_binderInfo_2398_ = lean_ctor_get_uint8(v_e_2386_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2386_, 3);
v_toBind_2399_ = lean_ctor_get(v_inst_2375_, 1);
lean_inc(v_toBind_2399_);
v___x_2400_ = lean_box(v_usedLetOnly_2380_);
v___x_2401_ = lean_box(v_skipConstInApp_2381_);
v___x_2402_ = lean_box(v_skipInstances_2382_);
lean_inc(v_x_2384_);
lean_inc(v_post_2379_);
lean_inc(v_pre_2378_);
lean_inc_ref(v_inst_2377_);
lean_inc(v_inst_2376_);
lean_inc_ref(v_inst_2375_);
lean_inc_ref(v_fvars_2385_);
v___f_2403_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__0___boxed), 14, 12);
lean_closure_set(v___f_2403_, 0, v_fvars_2385_);
lean_closure_set(v___f_2403_, 1, v_inst_2375_);
lean_closure_set(v___f_2403_, 2, v_inst_2376_);
lean_closure_set(v___f_2403_, 3, v_inst_2377_);
lean_closure_set(v___f_2403_, 4, v_pre_2378_);
lean_closure_set(v___f_2403_, 5, v_post_2379_);
lean_closure_set(v___f_2403_, 6, v___x_2400_);
lean_closure_set(v___f_2403_, 7, v___x_2401_);
lean_closure_set(v___f_2403_, 8, v___x_2402_);
lean_closure_set(v___f_2403_, 9, v_x_2383_);
lean_closure_set(v___f_2403_, 10, v_x_2384_);
lean_closure_set(v___f_2403_, 11, v_body_2397_);
v___x_2404_ = lean_box(v_binderInfo_2398_);
lean_inc(v_a_2387_);
v___f_2405_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_2405_, 0, v___x_2394_);
lean_closure_set(v___f_2405_, 1, v___x_2390_);
lean_closure_set(v___f_2405_, 2, v_binderName_2395_);
lean_closure_set(v___f_2405_, 3, v___x_2404_);
lean_closure_set(v___f_2405_, 4, v___f_2403_);
lean_closure_set(v___f_2405_, 5, v_a_2387_);
v___x_2406_ = lean_expr_instantiate_rev(v_binderType_2396_, v_fvars_2385_);
lean_dec_ref(v_fvars_2385_);
lean_dec_ref(v_binderType_2396_);
v___x_2407_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2375_, v_inst_2376_, v_inst_2377_, v_pre_2378_, v_post_2379_, v_usedLetOnly_2380_, v_skipConstInApp_2381_, v_skipInstances_2382_, v_x_2383_, v_x_2384_, v___x_2406_, v_a_2387_);
v___x_2408_ = lean_apply_4(v_toBind_2399_, lean_box(0), lean_box(0), v___x_2407_, v___f_2405_);
return v___x_2408_;
}
else
{
lean_object* v_toBind_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___f_2413_; lean_object* v___x_2414_; lean_object* v___f_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; 
lean_dec_ref_known(v___x_2394_, 2);
lean_dec_ref(v___x_2390_);
v_toBind_2409_ = lean_ctor_get(v_inst_2375_, 1);
lean_inc_n(v_toBind_2409_, 2);
v___x_2410_ = lean_box(v_usedLetOnly_2380_);
v___x_2411_ = lean_box(v_skipConstInApp_2381_);
v___x_2412_ = lean_box(v_skipInstances_2382_);
lean_inc(v_a_2387_);
lean_inc(v_x_2384_);
lean_inc(v_post_2379_);
lean_inc(v_pre_2378_);
lean_inc_ref(v_inst_2377_);
lean_inc_n(v_inst_2376_, 2);
lean_inc_ref(v_inst_2375_);
v___f_2413_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3___boxed), 12, 11);
lean_closure_set(v___f_2413_, 0, v_inst_2375_);
lean_closure_set(v___f_2413_, 1, v_inst_2376_);
lean_closure_set(v___f_2413_, 2, v_inst_2377_);
lean_closure_set(v___f_2413_, 3, v_pre_2378_);
lean_closure_set(v___f_2413_, 4, v_post_2379_);
lean_closure_set(v___f_2413_, 5, v___x_2410_);
lean_closure_set(v___f_2413_, 6, v___x_2411_);
lean_closure_set(v___f_2413_, 7, v___x_2412_);
lean_closure_set(v___f_2413_, 8, v_x_2383_);
lean_closure_set(v___f_2413_, 9, v_x_2384_);
lean_closure_set(v___f_2413_, 10, v_a_2387_);
v___x_2414_ = lean_box(v_usedLetOnly_2380_);
lean_inc_ref(v_fvars_2385_);
v___f_2415_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__3___boxed), 6, 5);
lean_closure_set(v___f_2415_, 0, v_fvars_2385_);
lean_closure_set(v___f_2415_, 1, v___x_2414_);
lean_closure_set(v___f_2415_, 2, v_inst_2376_);
lean_closure_set(v___f_2415_, 3, v_toBind_2409_);
lean_closure_set(v___f_2415_, 4, v___f_2413_);
v___x_2416_ = lean_expr_instantiate_rev(v_e_2386_, v_fvars_2385_);
lean_dec_ref(v_fvars_2385_);
lean_dec_ref(v_e_2386_);
v___x_2417_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2375_, v_inst_2376_, v_inst_2377_, v_pre_2378_, v_post_2379_, v_usedLetOnly_2380_, v_skipConstInApp_2381_, v_skipInstances_2382_, v_x_2383_, v_x_2384_, v___x_2416_, v_a_2387_);
v___x_2418_ = lean_apply_4(v_toBind_2409_, lean_box(0), lean_box(0), v___x_2417_, v___f_2415_);
return v___x_2418_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__0(lean_object* v_fvars_2419_, lean_object* v_inst_2420_, lean_object* v_inst_2421_, lean_object* v_inst_2422_, lean_object* v_pre_2423_, lean_object* v_post_2424_, uint8_t v_usedLetOnly_2425_, uint8_t v_skipConstInApp_2426_, uint8_t v_skipInstances_2427_, lean_object* v_x_2428_, lean_object* v_x_2429_, lean_object* v_body_2430_, lean_object* v_x_2431_, lean_object* v___y_2432_){
_start:
{
lean_object* v___x_2433_; lean_object* v___x_2434_; 
v___x_2433_ = lean_array_push(v_fvars_2419_, v_x_2431_);
v___x_2434_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(v_inst_2420_, v_inst_2421_, v_inst_2422_, v_pre_2423_, v_post_2424_, v_usedLetOnly_2425_, v_skipConstInApp_2426_, v_skipInstances_2427_, v_x_2428_, v_x_2429_, v___x_2433_, v_body_2430_, v___y_2432_);
return v___x_2434_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__0___boxed(lean_object* v_fvars_2435_, lean_object* v_inst_2436_, lean_object* v_inst_2437_, lean_object* v_inst_2438_, lean_object* v_pre_2439_, lean_object* v_post_2440_, lean_object* v_usedLetOnly_2441_, lean_object* v_skipConstInApp_2442_, lean_object* v_skipInstances_2443_, lean_object* v_x_2444_, lean_object* v_x_2445_, lean_object* v_body_2446_, lean_object* v_x_2447_, lean_object* v___y_2448_){
_start:
{
uint8_t v_usedLetOnly_boxed_2449_; uint8_t v_skipConstInApp_boxed_2450_; uint8_t v_skipInstances_boxed_2451_; lean_object* v_res_2452_; 
v_usedLetOnly_boxed_2449_ = lean_unbox(v_usedLetOnly_2441_);
v_skipConstInApp_boxed_2450_ = lean_unbox(v_skipConstInApp_2442_);
v_skipInstances_boxed_2451_ = lean_unbox(v_skipInstances_2443_);
v_res_2452_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__0(v_fvars_2435_, v_inst_2436_, v_inst_2437_, v_inst_2438_, v_pre_2439_, v_post_2440_, v_usedLetOnly_boxed_2449_, v_skipConstInApp_boxed_2450_, v_skipInstances_boxed_2451_, v_x_2444_, v_x_2445_, v_body_2446_, v_x_2447_, v___y_2448_);
lean_dec(v___y_2448_);
return v_res_2452_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(lean_object* v_inst_2453_, lean_object* v_inst_2454_, lean_object* v_inst_2455_, lean_object* v_pre_2456_, lean_object* v_post_2457_, uint8_t v_usedLetOnly_2458_, uint8_t v_skipConstInApp_2459_, uint8_t v_skipInstances_2460_, lean_object* v_x_2461_, lean_object* v_x_2462_, lean_object* v_fvars_2463_, lean_object* v_e_2464_, lean_object* v_a_2465_){
_start:
{
lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___f_2470_; lean_object* v___f_2471_; lean_object* v___x_2472_; 
v___x_2466_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0));
v___x_2467_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1));
lean_inc_ref(v_inst_2453_);
v___x_2468_ = l_Lean_MonadCacheT_instMonad___redArg(v_x_2461_, v___x_2466_, v___x_2467_, v_inst_2453_);
v___x_2469_ = l_Lean_MonadCacheT_instMonadControl___redArg(v_x_2461_, v___x_2466_, v___x_2467_);
lean_inc_ref_n(v_inst_2455_, 2);
lean_inc_ref(v___x_2469_);
v___f_2470_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_2470_, 0, v___x_2469_);
lean_closure_set(v___f_2470_, 1, v_inst_2455_);
v___f_2471_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_2471_, 0, v___x_2469_);
lean_closure_set(v___f_2471_, 1, v_inst_2455_);
v___x_2472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2472_, 0, v___f_2470_);
lean_ctor_set(v___x_2472_, 1, v___f_2471_);
if (lean_obj_tag(v_e_2464_) == 6)
{
lean_object* v_binderName_2473_; lean_object* v_binderType_2474_; lean_object* v_body_2475_; uint8_t v_binderInfo_2476_; lean_object* v_toBind_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___f_2481_; lean_object* v___x_2482_; lean_object* v___f_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; 
v_binderName_2473_ = lean_ctor_get(v_e_2464_, 0);
lean_inc(v_binderName_2473_);
v_binderType_2474_ = lean_ctor_get(v_e_2464_, 1);
lean_inc_ref(v_binderType_2474_);
v_body_2475_ = lean_ctor_get(v_e_2464_, 2);
lean_inc_ref(v_body_2475_);
v_binderInfo_2476_ = lean_ctor_get_uint8(v_e_2464_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2464_, 3);
v_toBind_2477_ = lean_ctor_get(v_inst_2453_, 1);
lean_inc(v_toBind_2477_);
v___x_2478_ = lean_box(v_usedLetOnly_2458_);
v___x_2479_ = lean_box(v_skipConstInApp_2459_);
v___x_2480_ = lean_box(v_skipInstances_2460_);
lean_inc(v_x_2462_);
lean_inc(v_post_2457_);
lean_inc(v_pre_2456_);
lean_inc_ref(v_inst_2455_);
lean_inc(v_inst_2454_);
lean_inc_ref(v_inst_2453_);
lean_inc_ref(v_fvars_2463_);
v___f_2481_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__0___boxed), 14, 12);
lean_closure_set(v___f_2481_, 0, v_fvars_2463_);
lean_closure_set(v___f_2481_, 1, v_inst_2453_);
lean_closure_set(v___f_2481_, 2, v_inst_2454_);
lean_closure_set(v___f_2481_, 3, v_inst_2455_);
lean_closure_set(v___f_2481_, 4, v_pre_2456_);
lean_closure_set(v___f_2481_, 5, v_post_2457_);
lean_closure_set(v___f_2481_, 6, v___x_2478_);
lean_closure_set(v___f_2481_, 7, v___x_2479_);
lean_closure_set(v___f_2481_, 8, v___x_2480_);
lean_closure_set(v___f_2481_, 9, v_x_2461_);
lean_closure_set(v___f_2481_, 10, v_x_2462_);
lean_closure_set(v___f_2481_, 11, v_body_2475_);
v___x_2482_ = lean_box(v_binderInfo_2476_);
lean_inc(v_a_2465_);
v___f_2483_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_2483_, 0, v___x_2472_);
lean_closure_set(v___f_2483_, 1, v___x_2468_);
lean_closure_set(v___f_2483_, 2, v_binderName_2473_);
lean_closure_set(v___f_2483_, 3, v___x_2482_);
lean_closure_set(v___f_2483_, 4, v___f_2481_);
lean_closure_set(v___f_2483_, 5, v_a_2465_);
v___x_2484_ = lean_expr_instantiate_rev(v_binderType_2474_, v_fvars_2463_);
lean_dec_ref(v_fvars_2463_);
lean_dec_ref(v_binderType_2474_);
v___x_2485_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2453_, v_inst_2454_, v_inst_2455_, v_pre_2456_, v_post_2457_, v_usedLetOnly_2458_, v_skipConstInApp_2459_, v_skipInstances_2460_, v_x_2461_, v_x_2462_, v___x_2484_, v_a_2465_);
v___x_2486_ = lean_apply_4(v_toBind_2477_, lean_box(0), lean_box(0), v___x_2485_, v___f_2483_);
return v___x_2486_;
}
else
{
lean_object* v_toBind_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___f_2491_; lean_object* v___x_2492_; lean_object* v___f_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; 
lean_dec_ref_known(v___x_2472_, 2);
lean_dec_ref(v___x_2468_);
v_toBind_2487_ = lean_ctor_get(v_inst_2453_, 1);
lean_inc_n(v_toBind_2487_, 2);
v___x_2488_ = lean_box(v_usedLetOnly_2458_);
v___x_2489_ = lean_box(v_skipConstInApp_2459_);
v___x_2490_ = lean_box(v_skipInstances_2460_);
lean_inc(v_a_2465_);
lean_inc(v_x_2462_);
lean_inc(v_post_2457_);
lean_inc(v_pre_2456_);
lean_inc_ref(v_inst_2455_);
lean_inc_n(v_inst_2454_, 2);
lean_inc_ref(v_inst_2453_);
v___f_2491_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3___boxed), 12, 11);
lean_closure_set(v___f_2491_, 0, v_inst_2453_);
lean_closure_set(v___f_2491_, 1, v_inst_2454_);
lean_closure_set(v___f_2491_, 2, v_inst_2455_);
lean_closure_set(v___f_2491_, 3, v_pre_2456_);
lean_closure_set(v___f_2491_, 4, v_post_2457_);
lean_closure_set(v___f_2491_, 5, v___x_2488_);
lean_closure_set(v___f_2491_, 6, v___x_2489_);
lean_closure_set(v___f_2491_, 7, v___x_2490_);
lean_closure_set(v___f_2491_, 8, v_x_2461_);
lean_closure_set(v___f_2491_, 9, v_x_2462_);
lean_closure_set(v___f_2491_, 10, v_a_2465_);
v___x_2492_ = lean_box(v_usedLetOnly_2458_);
lean_inc_ref(v_fvars_2463_);
v___f_2493_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__3___boxed), 6, 5);
lean_closure_set(v___f_2493_, 0, v_fvars_2463_);
lean_closure_set(v___f_2493_, 1, v___x_2492_);
lean_closure_set(v___f_2493_, 2, v_inst_2454_);
lean_closure_set(v___f_2493_, 3, v_toBind_2487_);
lean_closure_set(v___f_2493_, 4, v___f_2491_);
v___x_2494_ = lean_expr_instantiate_rev(v_e_2464_, v_fvars_2463_);
lean_dec_ref(v_fvars_2463_);
lean_dec_ref(v_e_2464_);
v___x_2495_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2453_, v_inst_2454_, v_inst_2455_, v_pre_2456_, v_post_2457_, v_usedLetOnly_2458_, v_skipConstInApp_2459_, v_skipInstances_2460_, v_x_2461_, v_x_2462_, v___x_2494_, v_a_2465_);
v___x_2496_ = lean_apply_4(v_toBind_2487_, lean_box(0), lean_box(0), v___x_2495_, v___f_2493_);
return v___x_2496_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__0(lean_object* v_fvars_2497_, lean_object* v_inst_2498_, lean_object* v_inst_2499_, lean_object* v_inst_2500_, lean_object* v_pre_2501_, lean_object* v_post_2502_, uint8_t v_usedLetOnly_2503_, uint8_t v_skipConstInApp_2504_, uint8_t v_skipInstances_2505_, lean_object* v_x_2506_, lean_object* v_x_2507_, lean_object* v_body_2508_, lean_object* v_x_2509_, lean_object* v___y_2510_){
_start:
{
lean_object* v___x_2511_; lean_object* v___x_2512_; 
v___x_2511_ = lean_array_push(v_fvars_2497_, v_x_2509_);
v___x_2512_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(v_inst_2498_, v_inst_2499_, v_inst_2500_, v_pre_2501_, v_post_2502_, v_usedLetOnly_2503_, v_skipConstInApp_2504_, v_skipInstances_2505_, v_x_2506_, v_x_2507_, v___x_2511_, v_body_2508_, v___y_2510_);
return v___x_2512_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__0___boxed(lean_object* v_fvars_2513_, lean_object* v_inst_2514_, lean_object* v_inst_2515_, lean_object* v_inst_2516_, lean_object* v_pre_2517_, lean_object* v_post_2518_, lean_object* v_usedLetOnly_2519_, lean_object* v_skipConstInApp_2520_, lean_object* v_skipInstances_2521_, lean_object* v_x_2522_, lean_object* v_x_2523_, lean_object* v_body_2524_, lean_object* v_x_2525_, lean_object* v___y_2526_){
_start:
{
uint8_t v_usedLetOnly_boxed_2527_; uint8_t v_skipConstInApp_boxed_2528_; uint8_t v_skipInstances_boxed_2529_; lean_object* v_res_2530_; 
v_usedLetOnly_boxed_2527_ = lean_unbox(v_usedLetOnly_2519_);
v_skipConstInApp_boxed_2528_ = lean_unbox(v_skipConstInApp_2520_);
v_skipInstances_boxed_2529_ = lean_unbox(v_skipInstances_2521_);
v_res_2530_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__0(v_fvars_2513_, v_inst_2514_, v_inst_2515_, v_inst_2516_, v_pre_2517_, v_post_2518_, v_usedLetOnly_boxed_2527_, v_skipConstInApp_boxed_2528_, v_skipInstances_boxed_2529_, v_x_2522_, v_x_2523_, v_body_2524_, v_x_2525_, v___y_2526_);
lean_dec(v___y_2526_);
return v_res_2530_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__2(lean_object* v___x_2531_, lean_object* v___x_2532_, lean_object* v_declName_2533_, lean_object* v___f_2534_, uint8_t v_nondep_2535_, lean_object* v_a_2536_, lean_object* v_value_2537_, lean_object* v_fvars_2538_, lean_object* v_inst_2539_, lean_object* v_inst_2540_, lean_object* v_inst_2541_, lean_object* v_pre_2542_, lean_object* v_post_2543_, uint8_t v_usedLetOnly_2544_, uint8_t v_skipConstInApp_2545_, uint8_t v_skipInstances_2546_, lean_object* v_x_2547_, lean_object* v_x_2548_, lean_object* v_toBind_2549_, lean_object* v_a_2550_){
_start:
{
lean_object* v___x_2551_; lean_object* v___f_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; 
v___x_2551_ = lean_box(v_nondep_2535_);
lean_inc(v_a_2536_);
v___f_2552_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_2552_, 0, v___x_2531_);
lean_closure_set(v___f_2552_, 1, v___x_2532_);
lean_closure_set(v___f_2552_, 2, v_declName_2533_);
lean_closure_set(v___f_2552_, 3, v_a_2550_);
lean_closure_set(v___f_2552_, 4, v___f_2534_);
lean_closure_set(v___f_2552_, 5, v___x_2551_);
lean_closure_set(v___f_2552_, 6, v_a_2536_);
v___x_2553_ = lean_expr_instantiate_rev(v_value_2537_, v_fvars_2538_);
v___x_2554_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2539_, v_inst_2540_, v_inst_2541_, v_pre_2542_, v_post_2543_, v_usedLetOnly_2544_, v_skipConstInApp_2545_, v_skipInstances_2546_, v_x_2547_, v_x_2548_, v___x_2553_, v_a_2536_);
v___x_2555_ = lean_apply_4(v_toBind_2549_, lean_box(0), lean_box(0), v___x_2554_, v___f_2552_);
return v___x_2555_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__2___boxed(lean_object** _args){
lean_object* v___x_2556_ = _args[0];
lean_object* v___x_2557_ = _args[1];
lean_object* v_declName_2558_ = _args[2];
lean_object* v___f_2559_ = _args[3];
lean_object* v_nondep_2560_ = _args[4];
lean_object* v_a_2561_ = _args[5];
lean_object* v_value_2562_ = _args[6];
lean_object* v_fvars_2563_ = _args[7];
lean_object* v_inst_2564_ = _args[8];
lean_object* v_inst_2565_ = _args[9];
lean_object* v_inst_2566_ = _args[10];
lean_object* v_pre_2567_ = _args[11];
lean_object* v_post_2568_ = _args[12];
lean_object* v_usedLetOnly_2569_ = _args[13];
lean_object* v_skipConstInApp_2570_ = _args[14];
lean_object* v_skipInstances_2571_ = _args[15];
lean_object* v_x_2572_ = _args[16];
lean_object* v_x_2573_ = _args[17];
lean_object* v_toBind_2574_ = _args[18];
lean_object* v_a_2575_ = _args[19];
_start:
{
uint8_t v_nondep_4209__boxed_2576_; uint8_t v_usedLetOnly_boxed_2577_; uint8_t v_skipConstInApp_boxed_2578_; uint8_t v_skipInstances_boxed_2579_; lean_object* v_res_2580_; 
v_nondep_4209__boxed_2576_ = lean_unbox(v_nondep_2560_);
v_usedLetOnly_boxed_2577_ = lean_unbox(v_usedLetOnly_2569_);
v_skipConstInApp_boxed_2578_ = lean_unbox(v_skipConstInApp_2570_);
v_skipInstances_boxed_2579_ = lean_unbox(v_skipInstances_2571_);
v_res_2580_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__2(v___x_2556_, v___x_2557_, v_declName_2558_, v___f_2559_, v_nondep_4209__boxed_2576_, v_a_2561_, v_value_2562_, v_fvars_2563_, v_inst_2564_, v_inst_2565_, v_inst_2566_, v_pre_2567_, v_post_2568_, v_usedLetOnly_boxed_2577_, v_skipConstInApp_boxed_2578_, v_skipInstances_boxed_2579_, v_x_2572_, v_x_2573_, v_toBind_2574_, v_a_2575_);
lean_dec_ref(v_fvars_2563_);
lean_dec_ref(v_value_2562_);
lean_dec(v_a_2561_);
return v_res_2580_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(lean_object* v_inst_2581_, lean_object* v_inst_2582_, lean_object* v_inst_2583_, lean_object* v_pre_2584_, lean_object* v_post_2585_, uint8_t v_usedLetOnly_2586_, uint8_t v_skipConstInApp_2587_, uint8_t v_skipInstances_2588_, lean_object* v_x_2589_, lean_object* v_x_2590_, lean_object* v_fvars_2591_, lean_object* v_e_2592_, lean_object* v_a_2593_){
_start:
{
lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___f_2598_; lean_object* v___f_2599_; lean_object* v___x_2600_; 
v___x_2594_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0));
v___x_2595_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1));
lean_inc_ref(v_inst_2581_);
v___x_2596_ = l_Lean_MonadCacheT_instMonad___redArg(v_x_2589_, v___x_2594_, v___x_2595_, v_inst_2581_);
v___x_2597_ = l_Lean_MonadCacheT_instMonadControl___redArg(v_x_2589_, v___x_2594_, v___x_2595_);
lean_inc_ref_n(v_inst_2583_, 2);
lean_inc_ref(v___x_2597_);
v___f_2598_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_2598_, 0, v___x_2597_);
lean_closure_set(v___f_2598_, 1, v_inst_2583_);
v___f_2599_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_2599_, 0, v___x_2597_);
lean_closure_set(v___f_2599_, 1, v_inst_2583_);
v___x_2600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2600_, 0, v___f_2598_);
lean_ctor_set(v___x_2600_, 1, v___f_2599_);
if (lean_obj_tag(v_e_2592_) == 8)
{
lean_object* v_declName_2601_; lean_object* v_type_2602_; lean_object* v_value_2603_; lean_object* v_body_2604_; uint8_t v_nondep_2605_; lean_object* v_toBind_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___f_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___f_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; 
v_declName_2601_ = lean_ctor_get(v_e_2592_, 0);
lean_inc(v_declName_2601_);
v_type_2602_ = lean_ctor_get(v_e_2592_, 1);
lean_inc_ref(v_type_2602_);
v_value_2603_ = lean_ctor_get(v_e_2592_, 2);
lean_inc_ref(v_value_2603_);
v_body_2604_ = lean_ctor_get(v_e_2592_, 3);
lean_inc_ref(v_body_2604_);
v_nondep_2605_ = lean_ctor_get_uint8(v_e_2592_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_2592_, 4);
v_toBind_2606_ = lean_ctor_get(v_inst_2581_, 1);
lean_inc_n(v_toBind_2606_, 2);
v___x_2607_ = lean_box(v_usedLetOnly_2586_);
v___x_2608_ = lean_box(v_skipConstInApp_2587_);
v___x_2609_ = lean_box(v_skipInstances_2588_);
lean_inc_n(v_x_2590_, 2);
lean_inc_n(v_post_2585_, 2);
lean_inc_n(v_pre_2584_, 2);
lean_inc_ref_n(v_inst_2583_, 2);
lean_inc_n(v_inst_2582_, 2);
lean_inc_ref_n(v_inst_2581_, 2);
lean_inc_ref_n(v_fvars_2591_, 2);
v___f_2610_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__0___boxed), 14, 12);
lean_closure_set(v___f_2610_, 0, v_fvars_2591_);
lean_closure_set(v___f_2610_, 1, v_inst_2581_);
lean_closure_set(v___f_2610_, 2, v_inst_2582_);
lean_closure_set(v___f_2610_, 3, v_inst_2583_);
lean_closure_set(v___f_2610_, 4, v_pre_2584_);
lean_closure_set(v___f_2610_, 5, v_post_2585_);
lean_closure_set(v___f_2610_, 6, v___x_2607_);
lean_closure_set(v___f_2610_, 7, v___x_2608_);
lean_closure_set(v___f_2610_, 8, v___x_2609_);
lean_closure_set(v___f_2610_, 9, v_x_2589_);
lean_closure_set(v___f_2610_, 10, v_x_2590_);
lean_closure_set(v___f_2610_, 11, v_body_2604_);
v___x_2611_ = lean_box(v_nondep_2605_);
v___x_2612_ = lean_box(v_usedLetOnly_2586_);
v___x_2613_ = lean_box(v_skipConstInApp_2587_);
v___x_2614_ = lean_box(v_skipInstances_2588_);
lean_inc(v_a_2593_);
v___f_2615_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__2___boxed), 20, 19);
lean_closure_set(v___f_2615_, 0, v___x_2600_);
lean_closure_set(v___f_2615_, 1, v___x_2596_);
lean_closure_set(v___f_2615_, 2, v_declName_2601_);
lean_closure_set(v___f_2615_, 3, v___f_2610_);
lean_closure_set(v___f_2615_, 4, v___x_2611_);
lean_closure_set(v___f_2615_, 5, v_a_2593_);
lean_closure_set(v___f_2615_, 6, v_value_2603_);
lean_closure_set(v___f_2615_, 7, v_fvars_2591_);
lean_closure_set(v___f_2615_, 8, v_inst_2581_);
lean_closure_set(v___f_2615_, 9, v_inst_2582_);
lean_closure_set(v___f_2615_, 10, v_inst_2583_);
lean_closure_set(v___f_2615_, 11, v_pre_2584_);
lean_closure_set(v___f_2615_, 12, v_post_2585_);
lean_closure_set(v___f_2615_, 13, v___x_2612_);
lean_closure_set(v___f_2615_, 14, v___x_2613_);
lean_closure_set(v___f_2615_, 15, v___x_2614_);
lean_closure_set(v___f_2615_, 16, v_x_2589_);
lean_closure_set(v___f_2615_, 17, v_x_2590_);
lean_closure_set(v___f_2615_, 18, v_toBind_2606_);
v___x_2616_ = lean_expr_instantiate_rev(v_type_2602_, v_fvars_2591_);
lean_dec_ref(v_fvars_2591_);
lean_dec_ref(v_type_2602_);
v___x_2617_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2581_, v_inst_2582_, v_inst_2583_, v_pre_2584_, v_post_2585_, v_usedLetOnly_2586_, v_skipConstInApp_2587_, v_skipInstances_2588_, v_x_2589_, v_x_2590_, v___x_2616_, v_a_2593_);
v___x_2618_ = lean_apply_4(v_toBind_2606_, lean_box(0), lean_box(0), v___x_2617_, v___f_2615_);
return v___x_2618_;
}
else
{
lean_object* v_toBind_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___f_2623_; lean_object* v___x_2624_; lean_object* v___f_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; 
lean_dec_ref_known(v___x_2600_, 2);
lean_dec_ref(v___x_2596_);
v_toBind_2619_ = lean_ctor_get(v_inst_2581_, 1);
lean_inc_n(v_toBind_2619_, 2);
v___x_2620_ = lean_box(v_usedLetOnly_2586_);
v___x_2621_ = lean_box(v_skipConstInApp_2587_);
v___x_2622_ = lean_box(v_skipInstances_2588_);
lean_inc(v_a_2593_);
lean_inc(v_x_2590_);
lean_inc(v_post_2585_);
lean_inc(v_pre_2584_);
lean_inc_ref(v_inst_2583_);
lean_inc_n(v_inst_2582_, 2);
lean_inc_ref(v_inst_2581_);
v___f_2623_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3___boxed), 12, 11);
lean_closure_set(v___f_2623_, 0, v_inst_2581_);
lean_closure_set(v___f_2623_, 1, v_inst_2582_);
lean_closure_set(v___f_2623_, 2, v_inst_2583_);
lean_closure_set(v___f_2623_, 3, v_pre_2584_);
lean_closure_set(v___f_2623_, 4, v_post_2585_);
lean_closure_set(v___f_2623_, 5, v___x_2620_);
lean_closure_set(v___f_2623_, 6, v___x_2621_);
lean_closure_set(v___f_2623_, 7, v___x_2622_);
lean_closure_set(v___f_2623_, 8, v_x_2589_);
lean_closure_set(v___f_2623_, 9, v_x_2590_);
lean_closure_set(v___f_2623_, 10, v_a_2593_);
v___x_2624_ = lean_box(v_usedLetOnly_2586_);
lean_inc_ref(v_fvars_2591_);
v___f_2625_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__4___boxed), 6, 5);
lean_closure_set(v___f_2625_, 0, v_fvars_2591_);
lean_closure_set(v___f_2625_, 1, v___x_2624_);
lean_closure_set(v___f_2625_, 2, v_inst_2582_);
lean_closure_set(v___f_2625_, 3, v_toBind_2619_);
lean_closure_set(v___f_2625_, 4, v___f_2623_);
v___x_2626_ = lean_expr_instantiate_rev(v_e_2592_, v_fvars_2591_);
lean_dec_ref(v_fvars_2591_);
lean_dec_ref(v_e_2592_);
v___x_2627_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2581_, v_inst_2582_, v_inst_2583_, v_pre_2584_, v_post_2585_, v_usedLetOnly_2586_, v_skipConstInApp_2587_, v_skipInstances_2588_, v_x_2589_, v_x_2590_, v___x_2626_, v_a_2593_);
v___x_2628_ = lean_apply_4(v_toBind_2619_, lean_box(0), lean_box(0), v___x_2627_, v___f_2625_);
return v___x_2628_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__8(lean_object* v_expr_2629_, lean_object* v_data_2630_, lean_object* v_inst_2631_, lean_object* v_inst_2632_, lean_object* v_inst_2633_, lean_object* v_pre_2634_, lean_object* v_post_2635_, uint8_t v_usedLetOnly_2636_, uint8_t v_skipConstInApp_2637_, uint8_t v_skipInstances_2638_, lean_object* v_x_2639_, lean_object* v_x_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v_a_2643_){
_start:
{
size_t v___x_2644_; size_t v___x_2645_; uint8_t v___x_2646_; 
v___x_2644_ = lean_ptr_addr(v_expr_2629_);
v___x_2645_ = lean_ptr_addr(v_a_2643_);
v___x_2646_ = lean_usize_dec_eq(v___x_2644_, v___x_2645_);
if (v___x_2646_ == 0)
{
lean_object* v___x_2647_; lean_object* v___x_2648_; 
lean_dec_ref(v___y_2642_);
v___x_2647_ = l_Lean_Expr_mdata___override(v_data_2630_, v_a_2643_);
v___x_2648_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2631_, v_inst_2632_, v_inst_2633_, v_pre_2634_, v_post_2635_, v_usedLetOnly_2636_, v_skipConstInApp_2637_, v_skipInstances_2638_, v_x_2639_, v_x_2640_, v___x_2647_, v___y_2641_);
return v___x_2648_;
}
else
{
lean_object* v___x_2649_; 
lean_dec_ref(v_a_2643_);
lean_dec(v_data_2630_);
v___x_2649_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2631_, v_inst_2632_, v_inst_2633_, v_pre_2634_, v_post_2635_, v_usedLetOnly_2636_, v_skipConstInApp_2637_, v_skipInstances_2638_, v_x_2639_, v_x_2640_, v___y_2642_, v___y_2641_);
return v___x_2649_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__8___boxed(lean_object* v_expr_2650_, lean_object* v_data_2651_, lean_object* v_inst_2652_, lean_object* v_inst_2653_, lean_object* v_inst_2654_, lean_object* v_pre_2655_, lean_object* v_post_2656_, lean_object* v_usedLetOnly_2657_, lean_object* v_skipConstInApp_2658_, lean_object* v_skipInstances_2659_, lean_object* v_x_2660_, lean_object* v_x_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v_a_2664_){
_start:
{
uint8_t v_usedLetOnly_boxed_2665_; uint8_t v_skipConstInApp_boxed_2666_; uint8_t v_skipInstances_boxed_2667_; lean_object* v_res_2668_; 
v_usedLetOnly_boxed_2665_ = lean_unbox(v_usedLetOnly_2657_);
v_skipConstInApp_boxed_2666_ = lean_unbox(v_skipConstInApp_2658_);
v_skipInstances_boxed_2667_ = lean_unbox(v_skipInstances_2659_);
v_res_2668_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__8(v_expr_2650_, v_data_2651_, v_inst_2652_, v_inst_2653_, v_inst_2654_, v_pre_2655_, v_post_2656_, v_usedLetOnly_boxed_2665_, v_skipConstInApp_boxed_2666_, v_skipInstances_boxed_2667_, v_x_2660_, v_x_2661_, v___y_2662_, v___y_2663_, v_a_2664_);
lean_dec(v___y_2662_);
lean_dec_ref(v_expr_2650_);
return v_res_2668_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__10(lean_object* v_struct_2669_, lean_object* v_typeName_2670_, lean_object* v_idx_2671_, lean_object* v_inst_2672_, lean_object* v_inst_2673_, lean_object* v_inst_2674_, lean_object* v_pre_2675_, lean_object* v_post_2676_, uint8_t v_usedLetOnly_2677_, uint8_t v_skipConstInApp_2678_, uint8_t v_skipInstances_2679_, lean_object* v_x_2680_, lean_object* v_x_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v_a_2684_){
_start:
{
size_t v___x_2685_; size_t v___x_2686_; uint8_t v___x_2687_; 
v___x_2685_ = lean_ptr_addr(v_struct_2669_);
v___x_2686_ = lean_ptr_addr(v_a_2684_);
v___x_2687_ = lean_usize_dec_eq(v___x_2685_, v___x_2686_);
if (v___x_2687_ == 0)
{
lean_object* v___x_2688_; lean_object* v___x_2689_; 
lean_dec_ref(v___y_2683_);
v___x_2688_ = l_Lean_Expr_proj___override(v_typeName_2670_, v_idx_2671_, v_a_2684_);
v___x_2689_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2672_, v_inst_2673_, v_inst_2674_, v_pre_2675_, v_post_2676_, v_usedLetOnly_2677_, v_skipConstInApp_2678_, v_skipInstances_2679_, v_x_2680_, v_x_2681_, v___x_2688_, v___y_2682_);
return v___x_2689_;
}
else
{
lean_object* v___x_2690_; 
lean_dec_ref(v_a_2684_);
lean_dec(v_idx_2671_);
lean_dec(v_typeName_2670_);
v___x_2690_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2672_, v_inst_2673_, v_inst_2674_, v_pre_2675_, v_post_2676_, v_usedLetOnly_2677_, v_skipConstInApp_2678_, v_skipInstances_2679_, v_x_2680_, v_x_2681_, v___y_2683_, v___y_2682_);
return v___x_2690_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__10___boxed(lean_object* v_struct_2691_, lean_object* v_typeName_2692_, lean_object* v_idx_2693_, lean_object* v_inst_2694_, lean_object* v_inst_2695_, lean_object* v_inst_2696_, lean_object* v_pre_2697_, lean_object* v_post_2698_, lean_object* v_usedLetOnly_2699_, lean_object* v_skipConstInApp_2700_, lean_object* v_skipInstances_2701_, lean_object* v_x_2702_, lean_object* v_x_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v_a_2706_){
_start:
{
uint8_t v_usedLetOnly_boxed_2707_; uint8_t v_skipConstInApp_boxed_2708_; uint8_t v_skipInstances_boxed_2709_; lean_object* v_res_2710_; 
v_usedLetOnly_boxed_2707_ = lean_unbox(v_usedLetOnly_2699_);
v_skipConstInApp_boxed_2708_ = lean_unbox(v_skipConstInApp_2700_);
v_skipInstances_boxed_2709_ = lean_unbox(v_skipInstances_2701_);
v_res_2710_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__10(v_struct_2691_, v_typeName_2692_, v_idx_2693_, v_inst_2694_, v_inst_2695_, v_inst_2696_, v_pre_2697_, v_post_2698_, v_usedLetOnly_boxed_2707_, v_skipConstInApp_boxed_2708_, v_skipInstances_boxed_2709_, v_x_2702_, v_x_2703_, v___y_2704_, v___y_2705_, v_a_2706_);
lean_dec(v___y_2704_);
lean_dec_ref(v_struct_2691_);
return v_res_2710_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11(lean_object* v_toApplicative_2711_, lean_object* v_inst_2712_, lean_object* v_inst_2713_, lean_object* v_inst_2714_, lean_object* v_pre_2715_, lean_object* v_post_2716_, uint8_t v_usedLetOnly_2717_, uint8_t v_skipConstInApp_2718_, uint8_t v_skipInstances_2719_, lean_object* v_x_2720_, lean_object* v_x_2721_, lean_object* v___y_2722_, lean_object* v___f_2723_, lean_object* v_toBind_2724_, lean_object* v_e_2725_, lean_object* v_a_2726_){
_start:
{
lean_object* v___y_2728_; 
switch(lean_obj_tag(v_a_2726_))
{
case 0:
{
lean_object* v_e_2760_; lean_object* v_toPure_2761_; lean_object* v___x_2762_; 
lean_dec_ref(v_e_2725_);
lean_dec(v_toBind_2724_);
lean_dec(v___f_2723_);
lean_dec(v_x_2721_);
lean_dec(v_post_2716_);
lean_dec(v_pre_2715_);
lean_dec_ref(v_inst_2714_);
lean_dec(v_inst_2713_);
lean_dec_ref(v_inst_2712_);
v_e_2760_ = lean_ctor_get(v_a_2726_, 0);
lean_inc_ref(v_e_2760_);
lean_dec_ref_known(v_a_2726_, 1);
v_toPure_2761_ = lean_ctor_get(v_toApplicative_2711_, 1);
lean_inc(v_toPure_2761_);
lean_dec_ref(v_toApplicative_2711_);
v___x_2762_ = lean_apply_2(v_toPure_2761_, lean_box(0), v_e_2760_);
return v___x_2762_;
}
case 1:
{
lean_object* v_e_2763_; lean_object* v___x_2764_; 
lean_dec_ref(v_e_2725_);
lean_dec(v_toBind_2724_);
lean_dec(v___f_2723_);
lean_dec_ref(v_toApplicative_2711_);
v_e_2763_ = lean_ctor_get(v_a_2726_, 0);
lean_inc_ref(v_e_2763_);
lean_dec_ref_known(v_a_2726_, 1);
v___x_2764_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2712_, v_inst_2713_, v_inst_2714_, v_pre_2715_, v_post_2716_, v_usedLetOnly_2717_, v_skipConstInApp_2718_, v_skipInstances_2719_, v_x_2720_, v_x_2721_, v_e_2763_, v___y_2722_);
return v___x_2764_;
}
default: 
{
lean_object* v_e_x3f_2765_; 
lean_dec_ref(v_toApplicative_2711_);
v_e_x3f_2765_ = lean_ctor_get(v_a_2726_, 0);
lean_inc(v_e_x3f_2765_);
lean_dec_ref_known(v_a_2726_, 1);
if (lean_obj_tag(v_e_x3f_2765_) == 0)
{
v___y_2728_ = v_e_2725_;
goto v___jp_2727_;
}
else
{
lean_object* v_val_2766_; 
lean_dec_ref(v_e_2725_);
v_val_2766_ = lean_ctor_get(v_e_x3f_2765_, 0);
lean_inc(v_val_2766_);
lean_dec_ref_known(v_e_x3f_2765_, 1);
v___y_2728_ = v_val_2766_;
goto v___jp_2727_;
}
}
}
v___jp_2727_:
{
switch(lean_obj_tag(v___y_2728_))
{
case 7:
{
lean_object* v___x_2729_; lean_object* v___x_2730_; 
lean_dec(v_toBind_2724_);
lean_dec(v___f_2723_);
v___x_2729_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_2730_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(v_inst_2712_, v_inst_2713_, v_inst_2714_, v_pre_2715_, v_post_2716_, v_usedLetOnly_2717_, v_skipConstInApp_2718_, v_skipInstances_2719_, v_x_2720_, v_x_2721_, v___x_2729_, v___y_2728_, v___y_2722_);
return v___x_2730_;
}
case 6:
{
lean_object* v___x_2731_; lean_object* v___x_2732_; 
lean_dec(v_toBind_2724_);
lean_dec(v___f_2723_);
v___x_2731_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_2732_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(v_inst_2712_, v_inst_2713_, v_inst_2714_, v_pre_2715_, v_post_2716_, v_usedLetOnly_2717_, v_skipConstInApp_2718_, v_skipInstances_2719_, v_x_2720_, v_x_2721_, v___x_2731_, v___y_2728_, v___y_2722_);
return v___x_2732_;
}
case 8:
{
lean_object* v___x_2733_; lean_object* v___x_2734_; 
lean_dec(v_toBind_2724_);
lean_dec(v___f_2723_);
v___x_2733_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_2734_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(v_inst_2712_, v_inst_2713_, v_inst_2714_, v_pre_2715_, v_post_2716_, v_usedLetOnly_2717_, v_skipConstInApp_2718_, v_skipInstances_2719_, v_x_2720_, v_x_2721_, v___x_2733_, v___y_2728_, v___y_2722_);
return v___x_2734_;
}
case 5:
{
lean_object* v_dummy_2735_; lean_object* v_nargs_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_3755__overap_2740_; lean_object* v___x_2741_; 
lean_dec(v_toBind_2724_);
lean_dec(v_x_2721_);
lean_dec(v_post_2716_);
lean_dec(v_pre_2715_);
lean_dec_ref(v_inst_2714_);
lean_dec(v_inst_2713_);
lean_dec_ref(v_inst_2712_);
v_dummy_2735_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_2736_ = l_Lean_Expr_getAppNumArgs(v___y_2728_);
lean_inc(v_nargs_2736_);
v___x_2737_ = lean_mk_array(v_nargs_2736_, v_dummy_2735_);
v___x_2738_ = lean_unsigned_to_nat(1u);
v___x_2739_ = lean_nat_sub(v_nargs_2736_, v___x_2738_);
lean_dec(v_nargs_2736_);
v___x_3755__overap_2740_ = l_Lean_Expr_withAppAux___redArg(v___f_2723_, v___y_2728_, v___x_2737_, v___x_2739_);
lean_inc(v___y_2722_);
v___x_2741_ = lean_apply_1(v___x_3755__overap_2740_, v___y_2722_);
return v___x_2741_;
}
case 10:
{
lean_object* v_data_2742_; lean_object* v_expr_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___f_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; 
lean_dec(v___f_2723_);
v_data_2742_ = lean_ctor_get(v___y_2728_, 0);
lean_inc(v_data_2742_);
v_expr_2743_ = lean_ctor_get(v___y_2728_, 1);
lean_inc_ref_n(v_expr_2743_, 2);
v___x_2744_ = lean_box(v_usedLetOnly_2717_);
v___x_2745_ = lean_box(v_skipConstInApp_2718_);
v___x_2746_ = lean_box(v_skipInstances_2719_);
lean_inc(v___y_2722_);
lean_inc(v_x_2721_);
lean_inc(v_post_2716_);
lean_inc(v_pre_2715_);
lean_inc_ref(v_inst_2714_);
lean_inc(v_inst_2713_);
lean_inc_ref(v_inst_2712_);
v___f_2747_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__8___boxed), 15, 14);
lean_closure_set(v___f_2747_, 0, v_expr_2743_);
lean_closure_set(v___f_2747_, 1, v_data_2742_);
lean_closure_set(v___f_2747_, 2, v_inst_2712_);
lean_closure_set(v___f_2747_, 3, v_inst_2713_);
lean_closure_set(v___f_2747_, 4, v_inst_2714_);
lean_closure_set(v___f_2747_, 5, v_pre_2715_);
lean_closure_set(v___f_2747_, 6, v_post_2716_);
lean_closure_set(v___f_2747_, 7, v___x_2744_);
lean_closure_set(v___f_2747_, 8, v___x_2745_);
lean_closure_set(v___f_2747_, 9, v___x_2746_);
lean_closure_set(v___f_2747_, 10, v_x_2720_);
lean_closure_set(v___f_2747_, 11, v_x_2721_);
lean_closure_set(v___f_2747_, 12, v___y_2722_);
lean_closure_set(v___f_2747_, 13, v___y_2728_);
v___x_2748_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2712_, v_inst_2713_, v_inst_2714_, v_pre_2715_, v_post_2716_, v_usedLetOnly_2717_, v_skipConstInApp_2718_, v_skipInstances_2719_, v_x_2720_, v_x_2721_, v_expr_2743_, v___y_2722_);
v___x_2749_ = lean_apply_4(v_toBind_2724_, lean_box(0), lean_box(0), v___x_2748_, v___f_2747_);
return v___x_2749_;
}
case 11:
{
lean_object* v_typeName_2750_; lean_object* v_idx_2751_; lean_object* v_struct_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___f_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; 
lean_dec(v___f_2723_);
v_typeName_2750_ = lean_ctor_get(v___y_2728_, 0);
lean_inc(v_typeName_2750_);
v_idx_2751_ = lean_ctor_get(v___y_2728_, 1);
lean_inc(v_idx_2751_);
v_struct_2752_ = lean_ctor_get(v___y_2728_, 2);
lean_inc_ref_n(v_struct_2752_, 2);
v___x_2753_ = lean_box(v_usedLetOnly_2717_);
v___x_2754_ = lean_box(v_skipConstInApp_2718_);
v___x_2755_ = lean_box(v_skipInstances_2719_);
lean_inc(v___y_2722_);
lean_inc(v_x_2721_);
lean_inc(v_post_2716_);
lean_inc(v_pre_2715_);
lean_inc_ref(v_inst_2714_);
lean_inc(v_inst_2713_);
lean_inc_ref(v_inst_2712_);
v___f_2756_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__10___boxed), 16, 15);
lean_closure_set(v___f_2756_, 0, v_struct_2752_);
lean_closure_set(v___f_2756_, 1, v_typeName_2750_);
lean_closure_set(v___f_2756_, 2, v_idx_2751_);
lean_closure_set(v___f_2756_, 3, v_inst_2712_);
lean_closure_set(v___f_2756_, 4, v_inst_2713_);
lean_closure_set(v___f_2756_, 5, v_inst_2714_);
lean_closure_set(v___f_2756_, 6, v_pre_2715_);
lean_closure_set(v___f_2756_, 7, v_post_2716_);
lean_closure_set(v___f_2756_, 8, v___x_2753_);
lean_closure_set(v___f_2756_, 9, v___x_2754_);
lean_closure_set(v___f_2756_, 10, v___x_2755_);
lean_closure_set(v___f_2756_, 11, v_x_2720_);
lean_closure_set(v___f_2756_, 12, v_x_2721_);
lean_closure_set(v___f_2756_, 13, v___y_2722_);
lean_closure_set(v___f_2756_, 14, v___y_2728_);
v___x_2757_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2712_, v_inst_2713_, v_inst_2714_, v_pre_2715_, v_post_2716_, v_usedLetOnly_2717_, v_skipConstInApp_2718_, v_skipInstances_2719_, v_x_2720_, v_x_2721_, v_struct_2752_, v___y_2722_);
v___x_2758_ = lean_apply_4(v_toBind_2724_, lean_box(0), lean_box(0), v___x_2757_, v___f_2756_);
return v___x_2758_;
}
default: 
{
lean_object* v___x_2759_; 
lean_dec(v_toBind_2724_);
lean_dec(v___f_2723_);
v___x_2759_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2712_, v_inst_2713_, v_inst_2714_, v_pre_2715_, v_post_2716_, v_usedLetOnly_2717_, v_skipConstInApp_2718_, v_skipInstances_2719_, v_x_2720_, v_x_2721_, v___y_2728_, v___y_2722_);
return v___x_2759_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___boxed(lean_object* v_toApplicative_2767_, lean_object* v_inst_2768_, lean_object* v_inst_2769_, lean_object* v_inst_2770_, lean_object* v_pre_2771_, lean_object* v_post_2772_, lean_object* v_usedLetOnly_2773_, lean_object* v_skipConstInApp_2774_, lean_object* v_skipInstances_2775_, lean_object* v_x_2776_, lean_object* v_x_2777_, lean_object* v___y_2778_, lean_object* v___f_2779_, lean_object* v_toBind_2780_, lean_object* v_e_2781_, lean_object* v_a_2782_){
_start:
{
uint8_t v_usedLetOnly_boxed_2783_; uint8_t v_skipConstInApp_boxed_2784_; uint8_t v_skipInstances_boxed_2785_; lean_object* v_res_2786_; 
v_usedLetOnly_boxed_2783_ = lean_unbox(v_usedLetOnly_2773_);
v_skipConstInApp_boxed_2784_ = lean_unbox(v_skipConstInApp_2774_);
v_skipInstances_boxed_2785_ = lean_unbox(v_skipInstances_2775_);
v_res_2786_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11(v_toApplicative_2767_, v_inst_2768_, v_inst_2769_, v_inst_2770_, v_pre_2771_, v_post_2772_, v_usedLetOnly_boxed_2783_, v_skipConstInApp_boxed_2784_, v_skipInstances_boxed_2785_, v_x_2776_, v_x_2777_, v___y_2778_, v___f_2779_, v_toBind_2780_, v_e_2781_, v_a_2782_);
lean_dec(v___y_2778_);
return v_res_2786_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12(lean_object* v_toApplicative_2787_, lean_object* v_inst_2788_, lean_object* v_inst_2789_, lean_object* v_inst_2790_, lean_object* v_pre_2791_, lean_object* v_post_2792_, uint8_t v_usedLetOnly_2793_, uint8_t v_skipConstInApp_2794_, uint8_t v_skipInstances_2795_, lean_object* v_x_2796_, lean_object* v_x_2797_, lean_object* v___f_2798_, lean_object* v_toBind_2799_, lean_object* v_e_2800_, lean_object* v_____r_2801_, lean_object* v___y_2802_){
_start:
{
lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___f_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; 
v___x_2803_ = lean_box(v_usedLetOnly_2793_);
v___x_2804_ = lean_box(v_skipConstInApp_2794_);
v___x_2805_ = lean_box(v_skipInstances_2795_);
lean_inc_ref(v_e_2800_);
lean_inc(v_toBind_2799_);
lean_inc(v___y_2802_);
lean_inc(v_pre_2791_);
v___f_2806_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___boxed), 16, 15);
lean_closure_set(v___f_2806_, 0, v_toApplicative_2787_);
lean_closure_set(v___f_2806_, 1, v_inst_2788_);
lean_closure_set(v___f_2806_, 2, v_inst_2789_);
lean_closure_set(v___f_2806_, 3, v_inst_2790_);
lean_closure_set(v___f_2806_, 4, v_pre_2791_);
lean_closure_set(v___f_2806_, 5, v_post_2792_);
lean_closure_set(v___f_2806_, 6, v___x_2803_);
lean_closure_set(v___f_2806_, 7, v___x_2804_);
lean_closure_set(v___f_2806_, 8, v___x_2805_);
lean_closure_set(v___f_2806_, 9, v_x_2796_);
lean_closure_set(v___f_2806_, 10, v_x_2797_);
lean_closure_set(v___f_2806_, 11, v___y_2802_);
lean_closure_set(v___f_2806_, 12, v___f_2798_);
lean_closure_set(v___f_2806_, 13, v_toBind_2799_);
lean_closure_set(v___f_2806_, 14, v_e_2800_);
v___x_2807_ = lean_apply_1(v_pre_2791_, v_e_2800_);
v___x_2808_ = lean_apply_4(v_toBind_2799_, lean_box(0), lean_box(0), v___x_2807_, v___f_2806_);
return v___x_2808_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12___boxed(lean_object* v_toApplicative_2809_, lean_object* v_inst_2810_, lean_object* v_inst_2811_, lean_object* v_inst_2812_, lean_object* v_pre_2813_, lean_object* v_post_2814_, lean_object* v_usedLetOnly_2815_, lean_object* v_skipConstInApp_2816_, lean_object* v_skipInstances_2817_, lean_object* v_x_2818_, lean_object* v_x_2819_, lean_object* v___f_2820_, lean_object* v_toBind_2821_, lean_object* v_e_2822_, lean_object* v_____r_2823_, lean_object* v___y_2824_){
_start:
{
uint8_t v_usedLetOnly_boxed_2825_; uint8_t v_skipConstInApp_boxed_2826_; uint8_t v_skipInstances_boxed_2827_; lean_object* v_res_2828_; 
v_usedLetOnly_boxed_2825_ = lean_unbox(v_usedLetOnly_2815_);
v_skipConstInApp_boxed_2826_ = lean_unbox(v_skipConstInApp_2816_);
v_skipInstances_boxed_2827_ = lean_unbox(v_skipInstances_2817_);
v_res_2828_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12(v_toApplicative_2809_, v_inst_2810_, v_inst_2811_, v_inst_2812_, v_pre_2813_, v_post_2814_, v_usedLetOnly_boxed_2825_, v_skipConstInApp_boxed_2826_, v_skipInstances_boxed_2827_, v_x_2818_, v_x_2819_, v___f_2820_, v_toBind_2821_, v_e_2822_, v_____r_2823_, v___y_2824_);
lean_dec(v___y_2824_);
return v_res_2828_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(lean_object* v_inst_2829_, lean_object* v_inst_2830_, lean_object* v_inst_2831_, lean_object* v_pre_2832_, lean_object* v_post_2833_, uint8_t v_usedLetOnly_2834_, uint8_t v_skipConstInApp_2835_, uint8_t v_skipInstances_2836_, lean_object* v_x_2837_, lean_object* v_x_2838_, lean_object* v_e_2839_, lean_object* v_a_2840_){
_start:
{
lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___f_2845_; lean_object* v___f_2846_; lean_object* v___x_2847_; lean_object* v_toApplicative_2848_; lean_object* v_toBind_2849_; lean_object* v___f_2850_; lean_object* v___f_2851_; lean_object* v___f_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___f_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___f_2860_; lean_object* v___f_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; 
v___x_2841_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0));
v___x_2842_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1));
lean_inc_ref_n(v_inst_2829_, 3);
v___x_2843_ = l_Lean_MonadCacheT_instMonad___redArg(v_x_2837_, v___x_2841_, v___x_2842_, v_inst_2829_);
v___x_2844_ = l_Lean_MonadCacheT_instMonadControl___redArg(v_x_2837_, v___x_2841_, v___x_2842_);
lean_inc_ref_n(v_inst_2831_, 3);
lean_inc_ref(v___x_2844_);
v___f_2845_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_2845_, 0, v___x_2844_);
lean_closure_set(v___f_2845_, 1, v_inst_2831_);
v___f_2846_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_2846_, 0, v___x_2844_);
lean_closure_set(v___f_2846_, 1, v_inst_2831_);
v___x_2847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2847_, 0, v___f_2845_);
lean_ctor_set(v___x_2847_, 1, v___f_2846_);
v_toApplicative_2848_ = lean_ctor_get(v_inst_2829_, 0);
lean_inc_ref_n(v_toApplicative_2848_, 6);
v_toBind_2849_ = lean_ctor_get(v_inst_2829_, 1);
lean_inc_n(v_toBind_2849_, 6);
v___f_2850_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2850_, 0, v_toApplicative_2848_);
lean_inc_n(v_x_2838_, 3);
lean_inc_n(v_a_2840_, 3);
lean_inc_ref_n(v_e_2839_, 2);
v___f_2851_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_2851_, 0, v_toApplicative_2848_);
lean_closure_set(v___f_2851_, 1, v___x_2841_);
lean_closure_set(v___f_2851_, 2, v___x_2842_);
lean_closure_set(v___f_2851_, 3, v_e_2839_);
lean_closure_set(v___f_2851_, 4, v_a_2840_);
lean_closure_set(v___f_2851_, 5, v_x_2838_);
lean_closure_set(v___f_2851_, 6, v_toBind_2849_);
v___f_2852_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__3___boxed), 5, 4);
lean_closure_set(v___f_2852_, 0, v_toApplicative_2848_);
lean_closure_set(v___f_2852_, 1, v___x_2841_);
lean_closure_set(v___f_2852_, 2, v___x_2842_);
lean_closure_set(v___f_2852_, 3, v_e_2839_);
v___x_2853_ = lean_box(v_skipInstances_2836_);
v___x_2854_ = lean_box(v_usedLetOnly_2834_);
v___x_2855_ = lean_box(v_skipConstInApp_2835_);
lean_inc_ref(v___x_2843_);
lean_inc(v_post_2833_);
lean_inc(v_pre_2832_);
lean_inc_n(v_inst_2830_, 2);
v___f_2856_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__9___boxed), 17, 14);
lean_closure_set(v___f_2856_, 0, v___x_2853_);
lean_closure_set(v___f_2856_, 1, v_inst_2829_);
lean_closure_set(v___f_2856_, 2, v_inst_2830_);
lean_closure_set(v___f_2856_, 3, v_inst_2831_);
lean_closure_set(v___f_2856_, 4, v_pre_2832_);
lean_closure_set(v___f_2856_, 5, v_post_2833_);
lean_closure_set(v___f_2856_, 6, v___x_2854_);
lean_closure_set(v___f_2856_, 7, v___x_2855_);
lean_closure_set(v___f_2856_, 8, v_x_2837_);
lean_closure_set(v___f_2856_, 9, v_x_2838_);
lean_closure_set(v___f_2856_, 10, v___x_2843_);
lean_closure_set(v___f_2856_, 11, v_toBind_2849_);
lean_closure_set(v___f_2856_, 12, v_toApplicative_2848_);
lean_closure_set(v___f_2856_, 13, v___f_2850_);
v___x_2857_ = lean_box(v_usedLetOnly_2834_);
v___x_2858_ = lean_box(v_skipConstInApp_2835_);
v___x_2859_ = lean_box(v_skipInstances_2836_);
v___f_2860_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12___boxed), 16, 14);
lean_closure_set(v___f_2860_, 0, v_toApplicative_2848_);
lean_closure_set(v___f_2860_, 1, v_inst_2829_);
lean_closure_set(v___f_2860_, 2, v_inst_2830_);
lean_closure_set(v___f_2860_, 3, v_inst_2831_);
lean_closure_set(v___f_2860_, 4, v_pre_2832_);
lean_closure_set(v___f_2860_, 5, v_post_2833_);
lean_closure_set(v___f_2860_, 6, v___x_2857_);
lean_closure_set(v___f_2860_, 7, v___x_2858_);
lean_closure_set(v___f_2860_, 8, v___x_2859_);
lean_closure_set(v___f_2860_, 9, v_x_2837_);
lean_closure_set(v___f_2860_, 10, v_x_2838_);
lean_closure_set(v___f_2860_, 11, v___f_2856_);
lean_closure_set(v___f_2860_, 12, v_toBind_2849_);
lean_closure_set(v___f_2860_, 13, v_e_2839_);
v___f_2861_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14___boxed), 13, 12);
lean_closure_set(v___f_2861_, 0, v_inst_2830_);
lean_closure_set(v___f_2861_, 1, v_x_2837_);
lean_closure_set(v___f_2861_, 2, v___x_2841_);
lean_closure_set(v___f_2861_, 3, v___x_2842_);
lean_closure_set(v___f_2861_, 4, v_inst_2829_);
lean_closure_set(v___f_2861_, 5, v___f_2860_);
lean_closure_set(v___f_2861_, 6, v___x_2847_);
lean_closure_set(v___f_2861_, 7, v___x_2843_);
lean_closure_set(v___f_2861_, 8, v_a_2840_);
lean_closure_set(v___f_2861_, 9, v_toBind_2849_);
lean_closure_set(v___f_2861_, 10, v___f_2851_);
lean_closure_set(v___f_2861_, 11, v_toApplicative_2848_);
v___x_2862_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2862_, 0, lean_box(0));
lean_closure_set(v___x_2862_, 1, lean_box(0));
lean_closure_set(v___x_2862_, 2, v_a_2840_);
v___x_2863_ = lean_apply_2(v_x_2838_, lean_box(0), v___x_2862_);
v___x_2864_ = lean_apply_4(v_toBind_2849_, lean_box(0), lean_box(0), v___x_2863_, v___f_2852_);
v___x_2865_ = lean_apply_4(v_toBind_2849_, lean_box(0), lean_box(0), v___x_2864_, v___f_2861_);
return v___x_2865_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___lam__0(lean_object* v_toApplicative_2866_, lean_object* v_inst_2867_, lean_object* v_inst_2868_, lean_object* v_inst_2869_, lean_object* v_pre_2870_, lean_object* v_post_2871_, uint8_t v_usedLetOnly_2872_, uint8_t v_skipConstInApp_2873_, uint8_t v_skipInstances_2874_, lean_object* v_x_2875_, lean_object* v_x_2876_, lean_object* v_a_2877_, lean_object* v_e_2878_, lean_object* v_a_2879_){
_start:
{
lean_object* v___y_2881_; 
switch(lean_obj_tag(v_a_2879_))
{
case 0:
{
lean_object* v_e_2884_; lean_object* v_toPure_2885_; lean_object* v___x_2886_; 
lean_dec_ref(v_e_2878_);
lean_dec(v_x_2876_);
lean_dec(v_post_2871_);
lean_dec(v_pre_2870_);
lean_dec_ref(v_inst_2869_);
lean_dec(v_inst_2868_);
lean_dec_ref(v_inst_2867_);
v_e_2884_ = lean_ctor_get(v_a_2879_, 0);
lean_inc_ref(v_e_2884_);
lean_dec_ref_known(v_a_2879_, 1);
v_toPure_2885_ = lean_ctor_get(v_toApplicative_2866_, 1);
lean_inc(v_toPure_2885_);
lean_dec_ref(v_toApplicative_2866_);
v___x_2886_ = lean_apply_2(v_toPure_2885_, lean_box(0), v_e_2884_);
return v___x_2886_;
}
case 1:
{
lean_object* v_e_2887_; lean_object* v___x_2888_; 
lean_dec_ref(v_e_2878_);
lean_dec_ref(v_toApplicative_2866_);
v_e_2887_ = lean_ctor_get(v_a_2879_, 0);
lean_inc_ref(v_e_2887_);
lean_dec_ref_known(v_a_2879_, 1);
v___x_2888_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2867_, v_inst_2868_, v_inst_2869_, v_pre_2870_, v_post_2871_, v_usedLetOnly_2872_, v_skipConstInApp_2873_, v_skipInstances_2874_, v_x_2875_, v_x_2876_, v_e_2887_, v_a_2877_);
return v___x_2888_;
}
default: 
{
lean_object* v_e_x3f_2889_; 
lean_dec(v_x_2876_);
lean_dec(v_post_2871_);
lean_dec(v_pre_2870_);
lean_dec_ref(v_inst_2869_);
lean_dec(v_inst_2868_);
lean_dec_ref(v_inst_2867_);
v_e_x3f_2889_ = lean_ctor_get(v_a_2879_, 0);
lean_inc(v_e_x3f_2889_);
lean_dec_ref_known(v_a_2879_, 1);
if (lean_obj_tag(v_e_x3f_2889_) == 0)
{
v___y_2881_ = v_e_2878_;
goto v___jp_2880_;
}
else
{
lean_object* v_val_2890_; 
lean_dec_ref(v_e_2878_);
v_val_2890_ = lean_ctor_get(v_e_x3f_2889_, 0);
lean_inc(v_val_2890_);
lean_dec_ref_known(v_e_x3f_2889_, 1);
v___y_2881_ = v_val_2890_;
goto v___jp_2880_;
}
}
}
v___jp_2880_:
{
lean_object* v_toPure_2882_; lean_object* v___x_2883_; 
v_toPure_2882_ = lean_ctor_get(v_toApplicative_2866_, 1);
lean_inc(v_toPure_2882_);
lean_dec_ref(v_toApplicative_2866_);
v___x_2883_ = lean_apply_2(v_toPure_2882_, lean_box(0), v___y_2881_);
return v___x_2883_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___lam__0___boxed(lean_object* v_toApplicative_2891_, lean_object* v_inst_2892_, lean_object* v_inst_2893_, lean_object* v_inst_2894_, lean_object* v_pre_2895_, lean_object* v_post_2896_, lean_object* v_usedLetOnly_2897_, lean_object* v_skipConstInApp_2898_, lean_object* v_skipInstances_2899_, lean_object* v_x_2900_, lean_object* v_x_2901_, lean_object* v_a_2902_, lean_object* v_e_2903_, lean_object* v_a_2904_){
_start:
{
uint8_t v_usedLetOnly_boxed_2905_; uint8_t v_skipConstInApp_boxed_2906_; uint8_t v_skipInstances_boxed_2907_; lean_object* v_res_2908_; 
v_usedLetOnly_boxed_2905_ = lean_unbox(v_usedLetOnly_2897_);
v_skipConstInApp_boxed_2906_ = lean_unbox(v_skipConstInApp_2898_);
v_skipInstances_boxed_2907_ = lean_unbox(v_skipInstances_2899_);
v_res_2908_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___lam__0(v_toApplicative_2891_, v_inst_2892_, v_inst_2893_, v_inst_2894_, v_pre_2895_, v_post_2896_, v_usedLetOnly_boxed_2905_, v_skipConstInApp_boxed_2906_, v_skipInstances_boxed_2907_, v_x_2900_, v_x_2901_, v_a_2902_, v_e_2903_, v_a_2904_);
lean_dec(v_a_2902_);
return v_res_2908_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(lean_object* v_inst_2909_, lean_object* v_inst_2910_, lean_object* v_inst_2911_, lean_object* v_pre_2912_, lean_object* v_post_2913_, uint8_t v_usedLetOnly_2914_, uint8_t v_skipConstInApp_2915_, uint8_t v_skipInstances_2916_, lean_object* v_x_2917_, lean_object* v_x_2918_, lean_object* v_e_2919_, lean_object* v_a_2920_){
_start:
{
lean_object* v_toApplicative_2921_; lean_object* v_toBind_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___f_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; 
v_toApplicative_2921_ = lean_ctor_get(v_inst_2909_, 0);
lean_inc_ref(v_toApplicative_2921_);
v_toBind_2922_ = lean_ctor_get(v_inst_2909_, 1);
lean_inc(v_toBind_2922_);
v___x_2923_ = lean_box(v_usedLetOnly_2914_);
v___x_2924_ = lean_box(v_skipConstInApp_2915_);
v___x_2925_ = lean_box(v_skipInstances_2916_);
lean_inc_ref(v_e_2919_);
lean_inc(v_a_2920_);
lean_inc(v_post_2913_);
v___f_2926_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___lam__0___boxed), 14, 13);
lean_closure_set(v___f_2926_, 0, v_toApplicative_2921_);
lean_closure_set(v___f_2926_, 1, v_inst_2909_);
lean_closure_set(v___f_2926_, 2, v_inst_2910_);
lean_closure_set(v___f_2926_, 3, v_inst_2911_);
lean_closure_set(v___f_2926_, 4, v_pre_2912_);
lean_closure_set(v___f_2926_, 5, v_post_2913_);
lean_closure_set(v___f_2926_, 6, v___x_2923_);
lean_closure_set(v___f_2926_, 7, v___x_2924_);
lean_closure_set(v___f_2926_, 8, v___x_2925_);
lean_closure_set(v___f_2926_, 9, v_x_2917_);
lean_closure_set(v___f_2926_, 10, v_x_2918_);
lean_closure_set(v___f_2926_, 11, v_a_2920_);
lean_closure_set(v___f_2926_, 12, v_e_2919_);
v___x_2927_ = lean_apply_1(v_post_2913_, v_e_2919_);
v___x_2928_ = lean_apply_4(v_toBind_2922_, lean_box(0), lean_box(0), v___x_2927_, v___f_2926_);
return v___x_2928_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3(lean_object* v_inst_2929_, lean_object* v_inst_2930_, lean_object* v_inst_2931_, lean_object* v_pre_2932_, lean_object* v_post_2933_, uint8_t v_usedLetOnly_2934_, uint8_t v_skipConstInApp_2935_, uint8_t v_skipInstances_2936_, lean_object* v_x_2937_, lean_object* v_x_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_){
_start:
{
lean_object* v___x_2941_; 
v___x_2941_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2929_, v_inst_2930_, v_inst_2931_, v_pre_2932_, v_post_2933_, v_usedLetOnly_2934_, v_skipConstInApp_2935_, v_skipInstances_2936_, v_x_2937_, v_x_2938_, v_a_2940_, v_a_2939_);
return v___x_2941_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___boxed(lean_object* v_inst_2942_, lean_object* v_inst_2943_, lean_object* v_inst_2944_, lean_object* v_pre_2945_, lean_object* v_post_2946_, lean_object* v_usedLetOnly_2947_, lean_object* v_skipConstInApp_2948_, lean_object* v_skipInstances_2949_, lean_object* v_x_2950_, lean_object* v_x_2951_, lean_object* v_e_2952_, lean_object* v_a_2953_){
_start:
{
uint8_t v_usedLetOnly_boxed_2954_; uint8_t v_skipConstInApp_boxed_2955_; uint8_t v_skipInstances_boxed_2956_; lean_object* v_res_2957_; 
v_usedLetOnly_boxed_2954_ = lean_unbox(v_usedLetOnly_2947_);
v_skipConstInApp_boxed_2955_ = lean_unbox(v_skipConstInApp_2948_);
v_skipInstances_boxed_2956_ = lean_unbox(v_skipInstances_2949_);
v_res_2957_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2942_, v_inst_2943_, v_inst_2944_, v_pre_2945_, v_post_2946_, v_usedLetOnly_boxed_2954_, v_skipConstInApp_boxed_2955_, v_skipInstances_boxed_2956_, v_x_2950_, v_x_2951_, v_e_2952_, v_a_2953_);
lean_dec(v_a_2953_);
return v_res_2957_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___boxed(lean_object* v_inst_2958_, lean_object* v_inst_2959_, lean_object* v_inst_2960_, lean_object* v_pre_2961_, lean_object* v_post_2962_, lean_object* v_usedLetOnly_2963_, lean_object* v_skipConstInApp_2964_, lean_object* v_skipInstances_2965_, lean_object* v_x_2966_, lean_object* v_x_2967_, lean_object* v_fvars_2968_, lean_object* v_e_2969_, lean_object* v_a_2970_){
_start:
{
uint8_t v_usedLetOnly_boxed_2971_; uint8_t v_skipConstInApp_boxed_2972_; uint8_t v_skipInstances_boxed_2973_; lean_object* v_res_2974_; 
v_usedLetOnly_boxed_2971_ = lean_unbox(v_usedLetOnly_2963_);
v_skipConstInApp_boxed_2972_ = lean_unbox(v_skipConstInApp_2964_);
v_skipInstances_boxed_2973_ = lean_unbox(v_skipInstances_2965_);
v_res_2974_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(v_inst_2958_, v_inst_2959_, v_inst_2960_, v_pre_2961_, v_post_2962_, v_usedLetOnly_boxed_2971_, v_skipConstInApp_boxed_2972_, v_skipInstances_boxed_2973_, v_x_2966_, v_x_2967_, v_fvars_2968_, v_e_2969_, v_a_2970_);
lean_dec(v_a_2970_);
return v_res_2974_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___boxed(lean_object* v_inst_2975_, lean_object* v_inst_2976_, lean_object* v_inst_2977_, lean_object* v_pre_2978_, lean_object* v_post_2979_, lean_object* v_usedLetOnly_2980_, lean_object* v_skipConstInApp_2981_, lean_object* v_skipInstances_2982_, lean_object* v_x_2983_, lean_object* v_x_2984_, lean_object* v_fvars_2985_, lean_object* v_e_2986_, lean_object* v_a_2987_){
_start:
{
uint8_t v_usedLetOnly_boxed_2988_; uint8_t v_skipConstInApp_boxed_2989_; uint8_t v_skipInstances_boxed_2990_; lean_object* v_res_2991_; 
v_usedLetOnly_boxed_2988_ = lean_unbox(v_usedLetOnly_2980_);
v_skipConstInApp_boxed_2989_ = lean_unbox(v_skipConstInApp_2981_);
v_skipInstances_boxed_2990_ = lean_unbox(v_skipInstances_2982_);
v_res_2991_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(v_inst_2975_, v_inst_2976_, v_inst_2977_, v_pre_2978_, v_post_2979_, v_usedLetOnly_boxed_2988_, v_skipConstInApp_boxed_2989_, v_skipInstances_boxed_2990_, v_x_2983_, v_x_2984_, v_fvars_2985_, v_e_2986_, v_a_2987_);
lean_dec(v_a_2987_);
return v_res_2991_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___boxed(lean_object* v_inst_2992_, lean_object* v_inst_2993_, lean_object* v_inst_2994_, lean_object* v_pre_2995_, lean_object* v_post_2996_, lean_object* v_usedLetOnly_2997_, lean_object* v_skipConstInApp_2998_, lean_object* v_skipInstances_2999_, lean_object* v_x_3000_, lean_object* v_x_3001_, lean_object* v_fvars_3002_, lean_object* v_e_3003_, lean_object* v_a_3004_){
_start:
{
uint8_t v_usedLetOnly_boxed_3005_; uint8_t v_skipConstInApp_boxed_3006_; uint8_t v_skipInstances_boxed_3007_; lean_object* v_res_3008_; 
v_usedLetOnly_boxed_3005_ = lean_unbox(v_usedLetOnly_2997_);
v_skipConstInApp_boxed_3006_ = lean_unbox(v_skipConstInApp_2998_);
v_skipInstances_boxed_3007_ = lean_unbox(v_skipInstances_2999_);
v_res_3008_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(v_inst_2992_, v_inst_2993_, v_inst_2994_, v_pre_2995_, v_post_2996_, v_usedLetOnly_boxed_3005_, v_skipConstInApp_boxed_3006_, v_skipInstances_boxed_3007_, v_x_3000_, v_x_3001_, v_fvars_3002_, v_e_3003_, v_a_3004_);
lean_dec(v_a_3004_);
return v_res_3008_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit(lean_object* v_m_3009_, lean_object* v_inst_3010_, lean_object* v_inst_3011_, lean_object* v_inst_3012_, lean_object* v_pre_3013_, lean_object* v_post_3014_, uint8_t v_usedLetOnly_3015_, uint8_t v_skipConstInApp_3016_, uint8_t v_skipInstances_3017_, lean_object* v_x_3018_, lean_object* v_x_3019_, lean_object* v_e_3020_, lean_object* v_a_3021_){
_start:
{
lean_object* v___x_3022_; 
v___x_3022_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_3010_, v_inst_3011_, v_inst_3012_, v_pre_3013_, v_post_3014_, v_usedLetOnly_3015_, v_skipConstInApp_3016_, v_skipInstances_3017_, v_x_3018_, v_x_3019_, v_e_3020_, v_a_3021_);
return v___x_3022_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___boxed(lean_object* v_m_3023_, lean_object* v_inst_3024_, lean_object* v_inst_3025_, lean_object* v_inst_3026_, lean_object* v_pre_3027_, lean_object* v_post_3028_, lean_object* v_usedLetOnly_3029_, lean_object* v_skipConstInApp_3030_, lean_object* v_skipInstances_3031_, lean_object* v_x_3032_, lean_object* v_x_3033_, lean_object* v_e_3034_, lean_object* v_a_3035_){
_start:
{
uint8_t v_usedLetOnly_boxed_3036_; uint8_t v_skipConstInApp_boxed_3037_; uint8_t v_skipInstances_boxed_3038_; lean_object* v_res_3039_; 
v_usedLetOnly_boxed_3036_ = lean_unbox(v_usedLetOnly_3029_);
v_skipConstInApp_boxed_3037_ = lean_unbox(v_skipConstInApp_3030_);
v_skipInstances_boxed_3038_ = lean_unbox(v_skipInstances_3031_);
v_res_3039_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit(v_m_3023_, v_inst_3024_, v_inst_3025_, v_inst_3026_, v_pre_3027_, v_post_3028_, v_usedLetOnly_boxed_3036_, v_skipConstInApp_boxed_3037_, v_skipInstances_boxed_3038_, v_x_3032_, v_x_3033_, v_e_3034_, v_a_3035_);
lean_dec(v_a_3035_);
return v_res_3039_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet(lean_object* v_m_3040_, lean_object* v_inst_3041_, lean_object* v_inst_3042_, lean_object* v_inst_3043_, lean_object* v_pre_3044_, lean_object* v_post_3045_, uint8_t v_usedLetOnly_3046_, uint8_t v_skipConstInApp_3047_, uint8_t v_skipInstances_3048_, lean_object* v_x_3049_, lean_object* v_x_3050_, lean_object* v_fvars_3051_, lean_object* v_e_3052_, lean_object* v_a_3053_){
_start:
{
lean_object* v___x_3054_; 
v___x_3054_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(v_inst_3041_, v_inst_3042_, v_inst_3043_, v_pre_3044_, v_post_3045_, v_usedLetOnly_3046_, v_skipConstInApp_3047_, v_skipInstances_3048_, v_x_3049_, v_x_3050_, v_fvars_3051_, v_e_3052_, v_a_3053_);
return v___x_3054_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___boxed(lean_object* v_m_3055_, lean_object* v_inst_3056_, lean_object* v_inst_3057_, lean_object* v_inst_3058_, lean_object* v_pre_3059_, lean_object* v_post_3060_, lean_object* v_usedLetOnly_3061_, lean_object* v_skipConstInApp_3062_, lean_object* v_skipInstances_3063_, lean_object* v_x_3064_, lean_object* v_x_3065_, lean_object* v_fvars_3066_, lean_object* v_e_3067_, lean_object* v_a_3068_){
_start:
{
uint8_t v_usedLetOnly_boxed_3069_; uint8_t v_skipConstInApp_boxed_3070_; uint8_t v_skipInstances_boxed_3071_; lean_object* v_res_3072_; 
v_usedLetOnly_boxed_3069_ = lean_unbox(v_usedLetOnly_3061_);
v_skipConstInApp_boxed_3070_ = lean_unbox(v_skipConstInApp_3062_);
v_skipInstances_boxed_3071_ = lean_unbox(v_skipInstances_3063_);
v_res_3072_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet(v_m_3055_, v_inst_3056_, v_inst_3057_, v_inst_3058_, v_pre_3059_, v_post_3060_, v_usedLetOnly_boxed_3069_, v_skipConstInApp_boxed_3070_, v_skipInstances_boxed_3071_, v_x_3064_, v_x_3065_, v_fvars_3066_, v_e_3067_, v_a_3068_);
lean_dec(v_a_3068_);
return v_res_3072_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost(lean_object* v_m_3073_, lean_object* v_inst_3074_, lean_object* v_inst_3075_, lean_object* v_inst_3076_, lean_object* v_pre_3077_, lean_object* v_post_3078_, uint8_t v_usedLetOnly_3079_, uint8_t v_skipConstInApp_3080_, uint8_t v_skipInstances_3081_, lean_object* v_x_3082_, lean_object* v_x_3083_, lean_object* v_e_3084_, lean_object* v_a_3085_){
_start:
{
lean_object* v___x_3086_; 
v___x_3086_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_3074_, v_inst_3075_, v_inst_3076_, v_pre_3077_, v_post_3078_, v_usedLetOnly_3079_, v_skipConstInApp_3080_, v_skipInstances_3081_, v_x_3082_, v_x_3083_, v_e_3084_, v_a_3085_);
return v___x_3086_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___boxed(lean_object* v_m_3087_, lean_object* v_inst_3088_, lean_object* v_inst_3089_, lean_object* v_inst_3090_, lean_object* v_pre_3091_, lean_object* v_post_3092_, lean_object* v_usedLetOnly_3093_, lean_object* v_skipConstInApp_3094_, lean_object* v_skipInstances_3095_, lean_object* v_x_3096_, lean_object* v_x_3097_, lean_object* v_e_3098_, lean_object* v_a_3099_){
_start:
{
uint8_t v_usedLetOnly_boxed_3100_; uint8_t v_skipConstInApp_boxed_3101_; uint8_t v_skipInstances_boxed_3102_; lean_object* v_res_3103_; 
v_usedLetOnly_boxed_3100_ = lean_unbox(v_usedLetOnly_3093_);
v_skipConstInApp_boxed_3101_ = lean_unbox(v_skipConstInApp_3094_);
v_skipInstances_boxed_3102_ = lean_unbox(v_skipInstances_3095_);
v_res_3103_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost(v_m_3087_, v_inst_3088_, v_inst_3089_, v_inst_3090_, v_pre_3091_, v_post_3092_, v_usedLetOnly_boxed_3100_, v_skipConstInApp_boxed_3101_, v_skipInstances_boxed_3102_, v_x_3096_, v_x_3097_, v_e_3098_, v_a_3099_);
lean_dec(v_a_3099_);
return v_res_3103_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda(lean_object* v_m_3104_, lean_object* v_inst_3105_, lean_object* v_inst_3106_, lean_object* v_inst_3107_, lean_object* v_pre_3108_, lean_object* v_post_3109_, uint8_t v_usedLetOnly_3110_, uint8_t v_skipConstInApp_3111_, uint8_t v_skipInstances_3112_, lean_object* v_x_3113_, lean_object* v_x_3114_, lean_object* v_fvars_3115_, lean_object* v_e_3116_, lean_object* v_a_3117_){
_start:
{
lean_object* v___x_3118_; 
v___x_3118_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(v_inst_3105_, v_inst_3106_, v_inst_3107_, v_pre_3108_, v_post_3109_, v_usedLetOnly_3110_, v_skipConstInApp_3111_, v_skipInstances_3112_, v_x_3113_, v_x_3114_, v_fvars_3115_, v_e_3116_, v_a_3117_);
return v___x_3118_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___boxed(lean_object* v_m_3119_, lean_object* v_inst_3120_, lean_object* v_inst_3121_, lean_object* v_inst_3122_, lean_object* v_pre_3123_, lean_object* v_post_3124_, lean_object* v_usedLetOnly_3125_, lean_object* v_skipConstInApp_3126_, lean_object* v_skipInstances_3127_, lean_object* v_x_3128_, lean_object* v_x_3129_, lean_object* v_fvars_3130_, lean_object* v_e_3131_, lean_object* v_a_3132_){
_start:
{
uint8_t v_usedLetOnly_boxed_3133_; uint8_t v_skipConstInApp_boxed_3134_; uint8_t v_skipInstances_boxed_3135_; lean_object* v_res_3136_; 
v_usedLetOnly_boxed_3133_ = lean_unbox(v_usedLetOnly_3125_);
v_skipConstInApp_boxed_3134_ = lean_unbox(v_skipConstInApp_3126_);
v_skipInstances_boxed_3135_ = lean_unbox(v_skipInstances_3127_);
v_res_3136_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda(v_m_3119_, v_inst_3120_, v_inst_3121_, v_inst_3122_, v_pre_3123_, v_post_3124_, v_usedLetOnly_boxed_3133_, v_skipConstInApp_boxed_3134_, v_skipInstances_boxed_3135_, v_x_3128_, v_x_3129_, v_fvars_3130_, v_e_3131_, v_a_3132_);
lean_dec(v_a_3132_);
return v_res_3136_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall(lean_object* v_m_3137_, lean_object* v_inst_3138_, lean_object* v_inst_3139_, lean_object* v_inst_3140_, lean_object* v_pre_3141_, lean_object* v_post_3142_, uint8_t v_usedLetOnly_3143_, uint8_t v_skipConstInApp_3144_, uint8_t v_skipInstances_3145_, lean_object* v_x_3146_, lean_object* v_x_3147_, lean_object* v_fvars_3148_, lean_object* v_e_3149_, lean_object* v_a_3150_){
_start:
{
lean_object* v___x_3151_; 
v___x_3151_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(v_inst_3138_, v_inst_3139_, v_inst_3140_, v_pre_3141_, v_post_3142_, v_usedLetOnly_3143_, v_skipConstInApp_3144_, v_skipInstances_3145_, v_x_3146_, v_x_3147_, v_fvars_3148_, v_e_3149_, v_a_3150_);
return v___x_3151_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___boxed(lean_object* v_m_3152_, lean_object* v_inst_3153_, lean_object* v_inst_3154_, lean_object* v_inst_3155_, lean_object* v_pre_3156_, lean_object* v_post_3157_, lean_object* v_usedLetOnly_3158_, lean_object* v_skipConstInApp_3159_, lean_object* v_skipInstances_3160_, lean_object* v_x_3161_, lean_object* v_x_3162_, lean_object* v_fvars_3163_, lean_object* v_e_3164_, lean_object* v_a_3165_){
_start:
{
uint8_t v_usedLetOnly_boxed_3166_; uint8_t v_skipConstInApp_boxed_3167_; uint8_t v_skipInstances_boxed_3168_; lean_object* v_res_3169_; 
v_usedLetOnly_boxed_3166_ = lean_unbox(v_usedLetOnly_3158_);
v_skipConstInApp_boxed_3167_ = lean_unbox(v_skipConstInApp_3159_);
v_skipInstances_boxed_3168_ = lean_unbox(v_skipInstances_3160_);
v_res_3169_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall(v_m_3152_, v_inst_3153_, v_inst_3154_, v_inst_3155_, v_pre_3156_, v_post_3157_, v_usedLetOnly_boxed_3166_, v_skipConstInApp_boxed_3167_, v_skipInstances_boxed_3168_, v_x_3161_, v_x_3162_, v_fvars_3163_, v_e_3164_, v_a_3165_);
lean_dec(v_a_3165_);
return v_res_3169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__0(lean_object* v_x_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_){
_start:
{
lean_object* v___x_3176_; lean_object* v___x_3177_; 
v___x_3176_ = lean_apply_1(v_x_3170_, lean_box(0));
v___x_3177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3177_, 0, v___x_3176_);
return v___x_3177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__0___boxed(lean_object* v_x_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_){
_start:
{
lean_object* v_res_3184_; 
v_res_3184_ = l_Lean_Meta_transformWithCache___redArg___lam__0(v_x_3178_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_);
lean_dec(v___y_3182_);
lean_dec_ref(v___y_3181_);
lean_dec(v___y_3180_);
lean_dec_ref(v___y_3179_);
return v_res_3184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__1(lean_object* v_inst_3185_, lean_object* v_00_u03b1_3186_, lean_object* v_x_3187_){
_start:
{
lean_object* v___f_3188_; lean_object* v___x_3189_; 
v___f_3188_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_3188_, 0, v_x_3187_);
v___x_3189_ = lean_apply_2(v_inst_3185_, lean_box(0), v___f_3188_);
return v___x_3189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__4(lean_object* v_toPure_3190_, lean_object* v_x_3191_, lean_object* v_toBind_3192_, lean_object* v_inst_3193_, lean_object* v_inst_3194_, lean_object* v_inst_3195_, lean_object* v_pre_3196_, lean_object* v_post_3197_, uint8_t v_usedLetOnly_3198_, uint8_t v_skipConstInApp_3199_, uint8_t v_skipInstances_3200_, lean_object* v_x_3201_, lean_object* v_input_3202_, lean_object* v_ref_3203_){
_start:
{
lean_object* v___f_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; 
lean_inc(v_toBind_3192_);
lean_inc(v_x_3191_);
lean_inc(v_ref_3203_);
v___f_3204_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__4), 5, 4);
lean_closure_set(v___f_3204_, 0, v_toPure_3190_);
lean_closure_set(v___f_3204_, 1, v_ref_3203_);
lean_closure_set(v___f_3204_, 2, v_x_3191_);
lean_closure_set(v___f_3204_, 3, v_toBind_3192_);
v___x_3205_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_3193_, v_inst_3194_, v_inst_3195_, v_pre_3196_, v_post_3197_, v_usedLetOnly_3198_, v_skipConstInApp_3199_, v_skipInstances_3200_, v_x_3201_, v_x_3191_, v_input_3202_, v_ref_3203_);
lean_dec(v_ref_3203_);
v___x_3206_ = lean_apply_4(v_toBind_3192_, lean_box(0), lean_box(0), v___x_3205_, v___f_3204_);
return v___x_3206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__4___boxed(lean_object* v_toPure_3207_, lean_object* v_x_3208_, lean_object* v_toBind_3209_, lean_object* v_inst_3210_, lean_object* v_inst_3211_, lean_object* v_inst_3212_, lean_object* v_pre_3213_, lean_object* v_post_3214_, lean_object* v_usedLetOnly_3215_, lean_object* v_skipConstInApp_3216_, lean_object* v_skipInstances_3217_, lean_object* v_x_3218_, lean_object* v_input_3219_, lean_object* v_ref_3220_){
_start:
{
uint8_t v_usedLetOnly_boxed_3221_; uint8_t v_skipConstInApp_boxed_3222_; uint8_t v_skipInstances_boxed_3223_; lean_object* v_res_3224_; 
v_usedLetOnly_boxed_3221_ = lean_unbox(v_usedLetOnly_3215_);
v_skipConstInApp_boxed_3222_ = lean_unbox(v_skipConstInApp_3216_);
v_skipInstances_boxed_3223_ = lean_unbox(v_skipInstances_3217_);
v_res_3224_ = l_Lean_Meta_transformWithCache___redArg___lam__4(v_toPure_3207_, v_x_3208_, v_toBind_3209_, v_inst_3210_, v_inst_3211_, v_inst_3212_, v_pre_3213_, v_post_3214_, v_usedLetOnly_boxed_3221_, v_skipConstInApp_boxed_3222_, v_skipInstances_boxed_3223_, v_x_3218_, v_input_3219_, v_ref_3220_);
return v_res_3224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg(lean_object* v_inst_3225_, lean_object* v_inst_3226_, lean_object* v_inst_3227_, lean_object* v_input_3228_, lean_object* v_cache_3229_, lean_object* v_pre_3230_, lean_object* v_post_3231_, uint8_t v_usedLetOnly_3232_, uint8_t v_skipConstInApp_3233_, uint8_t v_skipInstances_3234_){
_start:
{
lean_object* v_x_3235_; lean_object* v_toApplicative_3236_; lean_object* v_toBind_3237_; lean_object* v_toPure_3238_; lean_object* v_x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___f_3245_; lean_object* v___x_3246_; 
v_x_3235_ = lean_box(0);
v_toApplicative_3236_ = lean_ctor_get(v_inst_3225_, 0);
v_toBind_3237_ = lean_ctor_get(v_inst_3225_, 1);
lean_inc_n(v_toBind_3237_, 2);
v_toPure_3238_ = lean_ctor_get(v_toApplicative_3236_, 1);
lean_inc(v_toPure_3238_);
lean_inc_n(v_inst_3226_, 2);
v_x_3239_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__1), 3, 1);
lean_closure_set(v_x_3239_, 0, v_inst_3226_);
v___x_3240_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_3240_, 0, lean_box(0));
lean_closure_set(v___x_3240_, 1, lean_box(0));
lean_closure_set(v___x_3240_, 2, v_cache_3229_);
v___x_3241_ = l_Lean_Meta_transformWithCache___redArg___lam__1(v_inst_3226_, lean_box(0), v___x_3240_);
v___x_3242_ = lean_box(v_usedLetOnly_3232_);
v___x_3243_ = lean_box(v_skipConstInApp_3233_);
v___x_3244_ = lean_box(v_skipInstances_3234_);
v___f_3245_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__4___boxed), 14, 13);
lean_closure_set(v___f_3245_, 0, v_toPure_3238_);
lean_closure_set(v___f_3245_, 1, v_x_3239_);
lean_closure_set(v___f_3245_, 2, v_toBind_3237_);
lean_closure_set(v___f_3245_, 3, v_inst_3225_);
lean_closure_set(v___f_3245_, 4, v_inst_3226_);
lean_closure_set(v___f_3245_, 5, v_inst_3227_);
lean_closure_set(v___f_3245_, 6, v_pre_3230_);
lean_closure_set(v___f_3245_, 7, v_post_3231_);
lean_closure_set(v___f_3245_, 8, v___x_3242_);
lean_closure_set(v___f_3245_, 9, v___x_3243_);
lean_closure_set(v___f_3245_, 10, v___x_3244_);
lean_closure_set(v___f_3245_, 11, v_x_3235_);
lean_closure_set(v___f_3245_, 12, v_input_3228_);
v___x_3246_ = lean_apply_4(v_toBind_3237_, lean_box(0), lean_box(0), v___x_3241_, v___f_3245_);
return v___x_3246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___boxed(lean_object* v_inst_3247_, lean_object* v_inst_3248_, lean_object* v_inst_3249_, lean_object* v_input_3250_, lean_object* v_cache_3251_, lean_object* v_pre_3252_, lean_object* v_post_3253_, lean_object* v_usedLetOnly_3254_, lean_object* v_skipConstInApp_3255_, lean_object* v_skipInstances_3256_){
_start:
{
uint8_t v_usedLetOnly_boxed_3257_; uint8_t v_skipConstInApp_boxed_3258_; uint8_t v_skipInstances_boxed_3259_; lean_object* v_res_3260_; 
v_usedLetOnly_boxed_3257_ = lean_unbox(v_usedLetOnly_3254_);
v_skipConstInApp_boxed_3258_ = lean_unbox(v_skipConstInApp_3255_);
v_skipInstances_boxed_3259_ = lean_unbox(v_skipInstances_3256_);
v_res_3260_ = l_Lean_Meta_transformWithCache___redArg(v_inst_3247_, v_inst_3248_, v_inst_3249_, v_input_3250_, v_cache_3251_, v_pre_3252_, v_post_3253_, v_usedLetOnly_boxed_3257_, v_skipConstInApp_boxed_3258_, v_skipInstances_boxed_3259_);
return v_res_3260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache(lean_object* v_m_3261_, lean_object* v_inst_3262_, lean_object* v_inst_3263_, lean_object* v_inst_3264_, lean_object* v_input_3265_, lean_object* v_cache_3266_, lean_object* v_pre_3267_, lean_object* v_post_3268_, uint8_t v_usedLetOnly_3269_, uint8_t v_skipConstInApp_3270_, uint8_t v_skipInstances_3271_){
_start:
{
lean_object* v_x_3272_; lean_object* v_toApplicative_3273_; lean_object* v_toBind_3274_; lean_object* v_toPure_3275_; lean_object* v_x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___f_3282_; lean_object* v___x_3283_; 
v_x_3272_ = lean_box(0);
v_toApplicative_3273_ = lean_ctor_get(v_inst_3262_, 0);
v_toBind_3274_ = lean_ctor_get(v_inst_3262_, 1);
lean_inc_n(v_toBind_3274_, 2);
v_toPure_3275_ = lean_ctor_get(v_toApplicative_3273_, 1);
lean_inc(v_toPure_3275_);
lean_inc_n(v_inst_3263_, 2);
v_x_3276_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__1), 3, 1);
lean_closure_set(v_x_3276_, 0, v_inst_3263_);
v___x_3277_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_3277_, 0, lean_box(0));
lean_closure_set(v___x_3277_, 1, lean_box(0));
lean_closure_set(v___x_3277_, 2, v_cache_3266_);
v___x_3278_ = l_Lean_Meta_transformWithCache___redArg___lam__1(v_inst_3263_, lean_box(0), v___x_3277_);
v___x_3279_ = lean_box(v_usedLetOnly_3269_);
v___x_3280_ = lean_box(v_skipConstInApp_3270_);
v___x_3281_ = lean_box(v_skipInstances_3271_);
v___f_3282_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__4___boxed), 14, 13);
lean_closure_set(v___f_3282_, 0, v_toPure_3275_);
lean_closure_set(v___f_3282_, 1, v_x_3276_);
lean_closure_set(v___f_3282_, 2, v_toBind_3274_);
lean_closure_set(v___f_3282_, 3, v_inst_3262_);
lean_closure_set(v___f_3282_, 4, v_inst_3263_);
lean_closure_set(v___f_3282_, 5, v_inst_3264_);
lean_closure_set(v___f_3282_, 6, v_pre_3267_);
lean_closure_set(v___f_3282_, 7, v_post_3268_);
lean_closure_set(v___f_3282_, 8, v___x_3279_);
lean_closure_set(v___f_3282_, 9, v___x_3280_);
lean_closure_set(v___f_3282_, 10, v___x_3281_);
lean_closure_set(v___f_3282_, 11, v_x_3272_);
lean_closure_set(v___f_3282_, 12, v_input_3265_);
v___x_3283_ = lean_apply_4(v_toBind_3274_, lean_box(0), lean_box(0), v___x_3278_, v___f_3282_);
return v___x_3283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___boxed(lean_object* v_m_3284_, lean_object* v_inst_3285_, lean_object* v_inst_3286_, lean_object* v_inst_3287_, lean_object* v_input_3288_, lean_object* v_cache_3289_, lean_object* v_pre_3290_, lean_object* v_post_3291_, lean_object* v_usedLetOnly_3292_, lean_object* v_skipConstInApp_3293_, lean_object* v_skipInstances_3294_){
_start:
{
uint8_t v_usedLetOnly_boxed_3295_; uint8_t v_skipConstInApp_boxed_3296_; uint8_t v_skipInstances_boxed_3297_; lean_object* v_res_3298_; 
v_usedLetOnly_boxed_3295_ = lean_unbox(v_usedLetOnly_3292_);
v_skipConstInApp_boxed_3296_ = lean_unbox(v_skipConstInApp_3293_);
v_skipInstances_boxed_3297_ = lean_unbox(v_skipInstances_3294_);
v_res_3298_ = l_Lean_Meta_transformWithCache(v_m_3284_, v_inst_3285_, v_inst_3286_, v_inst_3287_, v_input_3288_, v_cache_3289_, v_pre_3290_, v_post_3291_, v_usedLetOnly_boxed_3295_, v_skipConstInApp_boxed_3296_, v_skipInstances_boxed_3297_);
return v_res_3298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___redArg___lam__5(lean_object* v_toPure_3299_, lean_object* v_x_3300_, lean_object* v_toBind_3301_, lean_object* v_inst_3302_, lean_object* v_inst_3303_, lean_object* v_inst_3304_, lean_object* v_pre_3305_, lean_object* v_post_3306_, uint8_t v_usedLetOnly_3307_, uint8_t v_skipConstInApp_3308_, uint8_t v___x_3309_, lean_object* v_x_3310_, lean_object* v_input_3311_, lean_object* v_ref_3312_){
_start:
{
lean_object* v___f_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; 
lean_inc(v_toBind_3301_);
lean_inc(v_x_3300_);
lean_inc(v_ref_3312_);
v___f_3313_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__4), 5, 4);
lean_closure_set(v___f_3313_, 0, v_toPure_3299_);
lean_closure_set(v___f_3313_, 1, v_ref_3312_);
lean_closure_set(v___f_3313_, 2, v_x_3300_);
lean_closure_set(v___f_3313_, 3, v_toBind_3301_);
v___x_3314_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_3302_, v_inst_3303_, v_inst_3304_, v_pre_3305_, v_post_3306_, v_usedLetOnly_3307_, v_skipConstInApp_3308_, v___x_3309_, v_x_3310_, v_x_3300_, v_input_3311_, v_ref_3312_);
lean_dec(v_ref_3312_);
v___x_3315_ = lean_apply_4(v_toBind_3301_, lean_box(0), lean_box(0), v___x_3314_, v___f_3313_);
return v___x_3315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___redArg___lam__5___boxed(lean_object* v_toPure_3316_, lean_object* v_x_3317_, lean_object* v_toBind_3318_, lean_object* v_inst_3319_, lean_object* v_inst_3320_, lean_object* v_inst_3321_, lean_object* v_pre_3322_, lean_object* v_post_3323_, lean_object* v_usedLetOnly_3324_, lean_object* v_skipConstInApp_3325_, lean_object* v___x_3326_, lean_object* v_x_3327_, lean_object* v_input_3328_, lean_object* v_ref_3329_){
_start:
{
uint8_t v_usedLetOnly_boxed_3330_; uint8_t v_skipConstInApp_boxed_3331_; uint8_t v___x_114__boxed_3332_; lean_object* v_res_3333_; 
v_usedLetOnly_boxed_3330_ = lean_unbox(v_usedLetOnly_3324_);
v_skipConstInApp_boxed_3331_ = lean_unbox(v_skipConstInApp_3325_);
v___x_114__boxed_3332_ = lean_unbox(v___x_3326_);
v_res_3333_ = l_Lean_Meta_transform___redArg___lam__5(v_toPure_3316_, v_x_3317_, v_toBind_3318_, v_inst_3319_, v_inst_3320_, v_inst_3321_, v_pre_3322_, v_post_3323_, v_usedLetOnly_boxed_3330_, v_skipConstInApp_boxed_3331_, v___x_114__boxed_3332_, v_x_3327_, v_input_3328_, v_ref_3329_);
return v_res_3333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___redArg(lean_object* v_inst_3334_, lean_object* v_inst_3335_, lean_object* v_inst_3336_, lean_object* v_input_3337_, lean_object* v_pre_3338_, lean_object* v_post_3339_, uint8_t v_usedLetOnly_3340_, uint8_t v_skipConstInApp_3341_){
_start:
{
lean_object* v_toApplicative_3342_; lean_object* v_toBind_3343_; lean_object* v_x_3344_; lean_object* v_toPure_3345_; lean_object* v_x_3346_; uint8_t v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___f_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___f_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; 
v_toApplicative_3342_ = lean_ctor_get(v_inst_3334_, 0);
v_toBind_3343_ = lean_ctor_get(v_inst_3334_, 1);
lean_inc_n(v_toBind_3343_, 3);
v_x_3344_ = lean_box(0);
v_toPure_3345_ = lean_ctor_get(v_toApplicative_3342_, 1);
lean_inc_n(v_toPure_3345_, 2);
lean_inc_n(v_inst_3335_, 2);
v_x_3346_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__1), 3, 1);
lean_closure_set(v_x_3346_, 0, v_inst_3335_);
v___x_3347_ = 0;
v___x_3348_ = lean_obj_once(&l_Lean_Core_transform___redArg___closed__2, &l_Lean_Core_transform___redArg___closed__2_once, _init_l_Lean_Core_transform___redArg___closed__2);
v___x_3349_ = l_Lean_Meta_transformWithCache___redArg___lam__1(v_inst_3335_, lean_box(0), v___x_3348_);
v___f_3350_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__2), 2, 1);
lean_closure_set(v___f_3350_, 0, v_toPure_3345_);
v___x_3351_ = lean_box(v_usedLetOnly_3340_);
v___x_3352_ = lean_box(v_skipConstInApp_3341_);
v___x_3353_ = lean_box(v___x_3347_);
v___f_3354_ = lean_alloc_closure((void*)(l_Lean_Meta_transform___redArg___lam__5___boxed), 14, 13);
lean_closure_set(v___f_3354_, 0, v_toPure_3345_);
lean_closure_set(v___f_3354_, 1, v_x_3346_);
lean_closure_set(v___f_3354_, 2, v_toBind_3343_);
lean_closure_set(v___f_3354_, 3, v_inst_3334_);
lean_closure_set(v___f_3354_, 4, v_inst_3335_);
lean_closure_set(v___f_3354_, 5, v_inst_3336_);
lean_closure_set(v___f_3354_, 6, v_pre_3338_);
lean_closure_set(v___f_3354_, 7, v_post_3339_);
lean_closure_set(v___f_3354_, 8, v___x_3351_);
lean_closure_set(v___f_3354_, 9, v___x_3352_);
lean_closure_set(v___f_3354_, 10, v___x_3353_);
lean_closure_set(v___f_3354_, 11, v_x_3344_);
lean_closure_set(v___f_3354_, 12, v_input_3337_);
v___x_3355_ = lean_apply_4(v_toBind_3343_, lean_box(0), lean_box(0), v___x_3349_, v___f_3354_);
v___x_3356_ = lean_apply_4(v_toBind_3343_, lean_box(0), lean_box(0), v___x_3355_, v___f_3350_);
return v___x_3356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___redArg___boxed(lean_object* v_inst_3357_, lean_object* v_inst_3358_, lean_object* v_inst_3359_, lean_object* v_input_3360_, lean_object* v_pre_3361_, lean_object* v_post_3362_, lean_object* v_usedLetOnly_3363_, lean_object* v_skipConstInApp_3364_){
_start:
{
uint8_t v_usedLetOnly_boxed_3365_; uint8_t v_skipConstInApp_boxed_3366_; lean_object* v_res_3367_; 
v_usedLetOnly_boxed_3365_ = lean_unbox(v_usedLetOnly_3363_);
v_skipConstInApp_boxed_3366_ = lean_unbox(v_skipConstInApp_3364_);
v_res_3367_ = l_Lean_Meta_transform___redArg(v_inst_3357_, v_inst_3358_, v_inst_3359_, v_input_3360_, v_pre_3361_, v_post_3362_, v_usedLetOnly_boxed_3365_, v_skipConstInApp_boxed_3366_);
return v_res_3367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform(lean_object* v_m_3368_, lean_object* v_inst_3369_, lean_object* v_inst_3370_, lean_object* v_inst_3371_, lean_object* v_input_3372_, lean_object* v_pre_3373_, lean_object* v_post_3374_, uint8_t v_usedLetOnly_3375_, uint8_t v_skipConstInApp_3376_){
_start:
{
lean_object* v___x_3377_; 
v___x_3377_ = l_Lean_Meta_transform___redArg(v_inst_3369_, v_inst_3370_, v_inst_3371_, v_input_3372_, v_pre_3373_, v_post_3374_, v_usedLetOnly_3375_, v_skipConstInApp_3376_);
return v___x_3377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___boxed(lean_object* v_m_3378_, lean_object* v_inst_3379_, lean_object* v_inst_3380_, lean_object* v_inst_3381_, lean_object* v_input_3382_, lean_object* v_pre_3383_, lean_object* v_post_3384_, lean_object* v_usedLetOnly_3385_, lean_object* v_skipConstInApp_3386_){
_start:
{
uint8_t v_usedLetOnly_boxed_3387_; uint8_t v_skipConstInApp_boxed_3388_; lean_object* v_res_3389_; 
v_usedLetOnly_boxed_3387_ = lean_unbox(v_usedLetOnly_3385_);
v_skipConstInApp_boxed_3388_ = lean_unbox(v_skipConstInApp_3386_);
v_res_3389_ = l_Lean_Meta_transform(v_m_3378_, v_inst_3379_, v_inst_3380_, v_inst_3381_, v_input_3382_, v_pre_3383_, v_post_3384_, v_usedLetOnly_boxed_3387_, v_skipConstInApp_boxed_3388_);
return v_res_3389_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(lean_object* v_e_3390_, lean_object* v___y_3391_){
_start:
{
uint8_t v___x_3393_; uint8_t v___x_3394_; 
v___x_3393_ = l_Lean_Expr_hasMVar(v_e_3390_);
v___x_3394_ = lean_bool_not(v___x_3393_);
if (v___x_3394_ == 0)
{
lean_object* v___x_3395_; lean_object* v_mctx_3396_; lean_object* v___x_3397_; lean_object* v_fst_3398_; lean_object* v_snd_3399_; lean_object* v___x_3400_; lean_object* v_cache_3401_; lean_object* v_zetaDeltaFVarIds_3402_; lean_object* v_postponed_3403_; lean_object* v_diag_3404_; lean_object* v___x_3406_; uint8_t v_isShared_3407_; uint8_t v_isSharedCheck_3413_; 
v___x_3395_ = lean_st_ref_get(v___y_3391_);
v_mctx_3396_ = lean_ctor_get(v___x_3395_, 0);
lean_inc_ref(v_mctx_3396_);
lean_dec(v___x_3395_);
v___x_3397_ = l_Lean_instantiateMVarsCore(v_mctx_3396_, v_e_3390_);
v_fst_3398_ = lean_ctor_get(v___x_3397_, 0);
lean_inc(v_fst_3398_);
v_snd_3399_ = lean_ctor_get(v___x_3397_, 1);
lean_inc(v_snd_3399_);
lean_dec_ref(v___x_3397_);
v___x_3400_ = lean_st_ref_take(v___y_3391_);
v_cache_3401_ = lean_ctor_get(v___x_3400_, 1);
v_zetaDeltaFVarIds_3402_ = lean_ctor_get(v___x_3400_, 2);
v_postponed_3403_ = lean_ctor_get(v___x_3400_, 3);
v_diag_3404_ = lean_ctor_get(v___x_3400_, 4);
v_isSharedCheck_3413_ = !lean_is_exclusive(v___x_3400_);
if (v_isSharedCheck_3413_ == 0)
{
lean_object* v_unused_3414_; 
v_unused_3414_ = lean_ctor_get(v___x_3400_, 0);
lean_dec(v_unused_3414_);
v___x_3406_ = v___x_3400_;
v_isShared_3407_ = v_isSharedCheck_3413_;
goto v_resetjp_3405_;
}
else
{
lean_inc(v_diag_3404_);
lean_inc(v_postponed_3403_);
lean_inc(v_zetaDeltaFVarIds_3402_);
lean_inc(v_cache_3401_);
lean_dec(v___x_3400_);
v___x_3406_ = lean_box(0);
v_isShared_3407_ = v_isSharedCheck_3413_;
goto v_resetjp_3405_;
}
v_resetjp_3405_:
{
lean_object* v___x_3409_; 
if (v_isShared_3407_ == 0)
{
lean_ctor_set(v___x_3406_, 0, v_snd_3399_);
v___x_3409_ = v___x_3406_;
goto v_reusejp_3408_;
}
else
{
lean_object* v_reuseFailAlloc_3412_; 
v_reuseFailAlloc_3412_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3412_, 0, v_snd_3399_);
lean_ctor_set(v_reuseFailAlloc_3412_, 1, v_cache_3401_);
lean_ctor_set(v_reuseFailAlloc_3412_, 2, v_zetaDeltaFVarIds_3402_);
lean_ctor_set(v_reuseFailAlloc_3412_, 3, v_postponed_3403_);
lean_ctor_set(v_reuseFailAlloc_3412_, 4, v_diag_3404_);
v___x_3409_ = v_reuseFailAlloc_3412_;
goto v_reusejp_3408_;
}
v_reusejp_3408_:
{
lean_object* v___x_3410_; lean_object* v___x_3411_; 
v___x_3410_ = lean_st_ref_set(v___y_3391_, v___x_3409_);
v___x_3411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3411_, 0, v_fst_3398_);
return v___x_3411_;
}
}
}
else
{
lean_object* v___x_3415_; 
v___x_3415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3415_, 0, v_e_3390_);
return v___x_3415_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg___boxed(lean_object* v_e_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_){
_start:
{
lean_object* v_res_3419_; 
v_res_3419_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(v_e_3416_, v___y_3417_);
lean_dec(v___y_3417_);
return v_res_3419_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0(lean_object* v_e_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_){
_start:
{
lean_object* v___x_3426_; 
v___x_3426_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(v_e_3420_, v___y_3422_);
return v___x_3426_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___boxed(lean_object* v_e_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_){
_start:
{
lean_object* v_res_3433_; 
v_res_3433_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0(v_e_3427_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_);
lean_dec(v___y_3431_);
lean_dec_ref(v___y_3430_);
lean_dec(v___y_3429_);
lean_dec_ref(v___y_3428_);
return v_res_3433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__0(uint8_t v_zetaHave_3434_, lean_object* v___x_3435_, uint8_t v_zetaDelta_3436_, lean_object* v_fvarId_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_){
_start:
{
lean_object* v___x_3443_; 
v___x_3443_ = l_Lean_FVarId_findDecl_x3f___redArg(v_fvarId_3437_, v___y_3438_);
if (lean_obj_tag(v___x_3443_) == 0)
{
lean_object* v_a_3444_; lean_object* v___x_3446_; uint8_t v_isShared_3447_; uint8_t v_isSharedCheck_3474_; 
v_a_3444_ = lean_ctor_get(v___x_3443_, 0);
v_isSharedCheck_3474_ = !lean_is_exclusive(v___x_3443_);
if (v_isSharedCheck_3474_ == 0)
{
v___x_3446_ = v___x_3443_;
v_isShared_3447_ = v_isSharedCheck_3474_;
goto v_resetjp_3445_;
}
else
{
lean_inc(v_a_3444_);
lean_dec(v___x_3443_);
v___x_3446_ = lean_box(0);
v_isShared_3447_ = v_isSharedCheck_3474_;
goto v_resetjp_3445_;
}
v_resetjp_3445_:
{
if (lean_obj_tag(v_a_3444_) == 1)
{
lean_object* v_val_3448_; lean_object* v___x_3450_; uint8_t v_isShared_3451_; uint8_t v_isSharedCheck_3469_; 
v_val_3448_ = lean_ctor_get(v_a_3444_, 0);
v_isSharedCheck_3469_ = !lean_is_exclusive(v_a_3444_);
if (v_isSharedCheck_3469_ == 0)
{
v___x_3450_ = v_a_3444_;
v_isShared_3451_ = v_isSharedCheck_3469_;
goto v_resetjp_3449_;
}
else
{
lean_inc(v_val_3448_);
lean_dec(v_a_3444_);
v___x_3450_ = lean_box(0);
v_isShared_3451_ = v_isSharedCheck_3469_;
goto v_resetjp_3449_;
}
v_resetjp_3449_:
{
uint8_t v___y_3453_; uint8_t v___y_3459_; uint8_t v___x_3466_; 
v___x_3466_ = lean_bool_not(v_zetaDelta_3436_);
if (v___x_3466_ == 0)
{
v___y_3459_ = v___x_3466_;
goto v___jp_3458_;
}
else
{
lean_object* v___x_3467_; uint8_t v___x_3468_; 
v___x_3467_ = l_Lean_LocalDecl_index(v_val_3448_);
v___x_3468_ = lean_nat_dec_lt(v___x_3467_, v___x_3435_);
lean_dec(v___x_3467_);
v___y_3459_ = v___x_3468_;
goto v___jp_3458_;
}
v___jp_3452_:
{
lean_object* v___x_3454_; lean_object* v___x_3456_; 
v___x_3454_ = l_Lean_LocalDecl_value_x3f(v_val_3448_, v___y_3453_);
lean_dec(v_val_3448_);
if (v_isShared_3447_ == 0)
{
lean_ctor_set(v___x_3446_, 0, v___x_3454_);
v___x_3456_ = v___x_3446_;
goto v_reusejp_3455_;
}
else
{
lean_object* v_reuseFailAlloc_3457_; 
v_reuseFailAlloc_3457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3457_, 0, v___x_3454_);
v___x_3456_ = v_reuseFailAlloc_3457_;
goto v_reusejp_3455_;
}
v_reusejp_3455_:
{
return v___x_3456_;
}
}
v___jp_3458_:
{
if (v___y_3459_ == 0)
{
lean_del_object(v___x_3450_);
if (v_zetaHave_3434_ == 0)
{
v___y_3453_ = v_zetaHave_3434_;
goto v___jp_3452_;
}
else
{
lean_object* v___x_3460_; uint8_t v___x_3461_; 
v___x_3460_ = l_Lean_LocalDecl_index(v_val_3448_);
v___x_3461_ = lean_nat_dec_le(v___x_3435_, v___x_3460_);
lean_dec(v___x_3460_);
v___y_3453_ = v___x_3461_;
goto v___jp_3452_;
}
}
else
{
lean_object* v___x_3462_; lean_object* v___x_3464_; 
lean_dec(v_val_3448_);
lean_del_object(v___x_3446_);
v___x_3462_ = lean_box(0);
if (v_isShared_3451_ == 0)
{
lean_ctor_set_tag(v___x_3450_, 0);
lean_ctor_set(v___x_3450_, 0, v___x_3462_);
v___x_3464_ = v___x_3450_;
goto v_reusejp_3463_;
}
else
{
lean_object* v_reuseFailAlloc_3465_; 
v_reuseFailAlloc_3465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3465_, 0, v___x_3462_);
v___x_3464_ = v_reuseFailAlloc_3465_;
goto v_reusejp_3463_;
}
v_reusejp_3463_:
{
return v___x_3464_;
}
}
}
}
}
else
{
lean_object* v___x_3470_; lean_object* v___x_3472_; 
lean_dec(v_a_3444_);
v___x_3470_ = lean_box(0);
if (v_isShared_3447_ == 0)
{
lean_ctor_set(v___x_3446_, 0, v___x_3470_);
v___x_3472_ = v___x_3446_;
goto v_reusejp_3471_;
}
else
{
lean_object* v_reuseFailAlloc_3473_; 
v_reuseFailAlloc_3473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3473_, 0, v___x_3470_);
v___x_3472_ = v_reuseFailAlloc_3473_;
goto v_reusejp_3471_;
}
v_reusejp_3471_:
{
return v___x_3472_;
}
}
}
}
else
{
lean_object* v_a_3475_; lean_object* v___x_3477_; uint8_t v_isShared_3478_; uint8_t v_isSharedCheck_3482_; 
v_a_3475_ = lean_ctor_get(v___x_3443_, 0);
v_isSharedCheck_3482_ = !lean_is_exclusive(v___x_3443_);
if (v_isSharedCheck_3482_ == 0)
{
v___x_3477_ = v___x_3443_;
v_isShared_3478_ = v_isSharedCheck_3482_;
goto v_resetjp_3476_;
}
else
{
lean_inc(v_a_3475_);
lean_dec(v___x_3443_);
v___x_3477_ = lean_box(0);
v_isShared_3478_ = v_isSharedCheck_3482_;
goto v_resetjp_3476_;
}
v_resetjp_3476_:
{
lean_object* v___x_3480_; 
if (v_isShared_3478_ == 0)
{
v___x_3480_ = v___x_3477_;
goto v_reusejp_3479_;
}
else
{
lean_object* v_reuseFailAlloc_3481_; 
v_reuseFailAlloc_3481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3481_, 0, v_a_3475_);
v___x_3480_ = v_reuseFailAlloc_3481_;
goto v_reusejp_3479_;
}
v_reusejp_3479_:
{
return v___x_3480_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__0___boxed(lean_object* v_zetaHave_3483_, lean_object* v___x_3484_, lean_object* v_zetaDelta_3485_, lean_object* v_fvarId_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_){
_start:
{
uint8_t v_zetaHave_boxed_3492_; uint8_t v_zetaDelta_boxed_3493_; lean_object* v_res_3494_; 
v_zetaHave_boxed_3492_ = lean_unbox(v_zetaHave_3483_);
v_zetaDelta_boxed_3493_ = lean_unbox(v_zetaDelta_3485_);
v_res_3494_ = l_Lean_Meta_zetaReduce___lam__0(v_zetaHave_boxed_3492_, v___x_3484_, v_zetaDelta_boxed_3493_, v_fvarId_3486_, v___y_3487_, v___y_3488_, v___y_3489_, v___y_3490_);
lean_dec(v___y_3490_);
lean_dec_ref(v___y_3489_);
lean_dec(v___y_3488_);
lean_dec_ref(v___y_3487_);
lean_dec(v___x_3484_);
return v_res_3494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__1(lean_object* v_e_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_){
_start:
{
lean_object* v___x_3501_; lean_object* v___x_3502_; 
v___x_3501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3501_, 0, v_e_3495_);
v___x_3502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3502_, 0, v___x_3501_);
return v___x_3502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__1___boxed(lean_object* v_e_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_){
_start:
{
lean_object* v_res_3509_; 
v_res_3509_ = l_Lean_Meta_zetaReduce___lam__1(v_e_3503_, v___y_3504_, v___y_3505_, v___y_3506_, v___y_3507_);
lean_dec(v___y_3507_);
lean_dec_ref(v___y_3506_);
lean_dec(v___y_3505_);
lean_dec_ref(v___y_3504_);
return v_res_3509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__2(lean_object* v___f_3510_, lean_object* v_e_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_){
_start:
{
if (lean_obj_tag(v_e_3511_) == 1)
{
lean_object* v_fvarId_3517_; lean_object* v___x_3518_; 
v_fvarId_3517_ = lean_ctor_get(v_e_3511_, 0);
lean_inc(v___y_3515_);
lean_inc_ref(v___y_3514_);
lean_inc(v___y_3513_);
lean_inc_ref(v___y_3512_);
lean_inc(v_fvarId_3517_);
v___x_3518_ = lean_apply_6(v___f_3510_, v_fvarId_3517_, v___y_3512_, v___y_3513_, v___y_3514_, v___y_3515_, lean_box(0));
if (lean_obj_tag(v___x_3518_) == 0)
{
lean_object* v_a_3519_; lean_object* v___x_3521_; uint8_t v_isShared_3522_; uint8_t v_isSharedCheck_3544_; 
v_a_3519_ = lean_ctor_get(v___x_3518_, 0);
v_isSharedCheck_3544_ = !lean_is_exclusive(v___x_3518_);
if (v_isSharedCheck_3544_ == 0)
{
v___x_3521_ = v___x_3518_;
v_isShared_3522_ = v_isSharedCheck_3544_;
goto v_resetjp_3520_;
}
else
{
lean_inc(v_a_3519_);
lean_dec(v___x_3518_);
v___x_3521_ = lean_box(0);
v_isShared_3522_ = v_isSharedCheck_3544_;
goto v_resetjp_3520_;
}
v_resetjp_3520_:
{
if (lean_obj_tag(v_a_3519_) == 1)
{
lean_object* v_val_3523_; lean_object* v___x_3525_; uint8_t v_isShared_3526_; uint8_t v_isSharedCheck_3539_; 
lean_del_object(v___x_3521_);
lean_dec_ref_known(v_e_3511_, 1);
v_val_3523_ = lean_ctor_get(v_a_3519_, 0);
v_isSharedCheck_3539_ = !lean_is_exclusive(v_a_3519_);
if (v_isSharedCheck_3539_ == 0)
{
v___x_3525_ = v_a_3519_;
v_isShared_3526_ = v_isSharedCheck_3539_;
goto v_resetjp_3524_;
}
else
{
lean_inc(v_val_3523_);
lean_dec(v_a_3519_);
v___x_3525_ = lean_box(0);
v_isShared_3526_ = v_isSharedCheck_3539_;
goto v_resetjp_3524_;
}
v_resetjp_3524_:
{
lean_object* v___x_3527_; lean_object* v_a_3528_; lean_object* v___x_3530_; uint8_t v_isShared_3531_; uint8_t v_isSharedCheck_3538_; 
v___x_3527_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(v_val_3523_, v___y_3513_);
v_a_3528_ = lean_ctor_get(v___x_3527_, 0);
v_isSharedCheck_3538_ = !lean_is_exclusive(v___x_3527_);
if (v_isSharedCheck_3538_ == 0)
{
v___x_3530_ = v___x_3527_;
v_isShared_3531_ = v_isSharedCheck_3538_;
goto v_resetjp_3529_;
}
else
{
lean_inc(v_a_3528_);
lean_dec(v___x_3527_);
v___x_3530_ = lean_box(0);
v_isShared_3531_ = v_isSharedCheck_3538_;
goto v_resetjp_3529_;
}
v_resetjp_3529_:
{
lean_object* v___x_3533_; 
if (v_isShared_3526_ == 0)
{
lean_ctor_set(v___x_3525_, 0, v_a_3528_);
v___x_3533_ = v___x_3525_;
goto v_reusejp_3532_;
}
else
{
lean_object* v_reuseFailAlloc_3537_; 
v_reuseFailAlloc_3537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3537_, 0, v_a_3528_);
v___x_3533_ = v_reuseFailAlloc_3537_;
goto v_reusejp_3532_;
}
v_reusejp_3532_:
{
lean_object* v___x_3535_; 
if (v_isShared_3531_ == 0)
{
lean_ctor_set(v___x_3530_, 0, v___x_3533_);
v___x_3535_ = v___x_3530_;
goto v_reusejp_3534_;
}
else
{
lean_object* v_reuseFailAlloc_3536_; 
v_reuseFailAlloc_3536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3536_, 0, v___x_3533_);
v___x_3535_ = v_reuseFailAlloc_3536_;
goto v_reusejp_3534_;
}
v_reusejp_3534_:
{
return v___x_3535_;
}
}
}
}
}
else
{
lean_object* v___x_3540_; lean_object* v___x_3542_; 
lean_dec(v_a_3519_);
v___x_3540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3540_, 0, v_e_3511_);
if (v_isShared_3522_ == 0)
{
lean_ctor_set(v___x_3521_, 0, v___x_3540_);
v___x_3542_ = v___x_3521_;
goto v_reusejp_3541_;
}
else
{
lean_object* v_reuseFailAlloc_3543_; 
v_reuseFailAlloc_3543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3543_, 0, v___x_3540_);
v___x_3542_ = v_reuseFailAlloc_3543_;
goto v_reusejp_3541_;
}
v_reusejp_3541_:
{
return v___x_3542_;
}
}
}
}
else
{
lean_object* v_a_3545_; lean_object* v___x_3547_; uint8_t v_isShared_3548_; uint8_t v_isSharedCheck_3552_; 
lean_dec_ref_known(v_e_3511_, 1);
v_a_3545_ = lean_ctor_get(v___x_3518_, 0);
v_isSharedCheck_3552_ = !lean_is_exclusive(v___x_3518_);
if (v_isSharedCheck_3552_ == 0)
{
v___x_3547_ = v___x_3518_;
v_isShared_3548_ = v_isSharedCheck_3552_;
goto v_resetjp_3546_;
}
else
{
lean_inc(v_a_3545_);
lean_dec(v___x_3518_);
v___x_3547_ = lean_box(0);
v_isShared_3548_ = v_isSharedCheck_3552_;
goto v_resetjp_3546_;
}
v_resetjp_3546_:
{
lean_object* v___x_3550_; 
if (v_isShared_3548_ == 0)
{
v___x_3550_ = v___x_3547_;
goto v_reusejp_3549_;
}
else
{
lean_object* v_reuseFailAlloc_3551_; 
v_reuseFailAlloc_3551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3551_, 0, v_a_3545_);
v___x_3550_ = v_reuseFailAlloc_3551_;
goto v_reusejp_3549_;
}
v_reusejp_3549_:
{
return v___x_3550_;
}
}
}
}
else
{
lean_object* v___x_3553_; lean_object* v___x_3554_; 
lean_dec_ref(v_e_3511_);
lean_dec_ref(v___f_3510_);
v___x_3553_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_3554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3554_, 0, v___x_3553_);
return v___x_3554_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__2___boxed(lean_object* v___f_3555_, lean_object* v_e_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_){
_start:
{
lean_object* v_res_3562_; 
v_res_3562_ = l_Lean_Meta_zetaReduce___lam__2(v___f_3555_, v_e_3556_, v___y_3557_, v___y_3558_, v___y_3559_, v___y_3560_);
lean_dec(v___y_3560_);
lean_dec_ref(v___y_3559_);
lean_dec(v___y_3558_);
lean_dec_ref(v___y_3557_);
return v_res_3562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__4(lean_object* v___f_3563_, lean_object* v_e_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_){
_start:
{
lean_object* v___x_3570_; 
v___x_3570_ = l_Lean_Expr_getAppFn(v_e_3564_);
if (lean_obj_tag(v___x_3570_) == 1)
{
lean_object* v_fvarId_3571_; lean_object* v___x_3572_; 
v_fvarId_3571_ = lean_ctor_get(v___x_3570_, 0);
lean_inc(v_fvarId_3571_);
lean_dec_ref_known(v___x_3570_, 1);
lean_inc(v___y_3568_);
lean_inc_ref(v___y_3567_);
lean_inc(v___y_3566_);
lean_inc_ref(v___y_3565_);
v___x_3572_ = lean_apply_6(v___f_3563_, v_fvarId_3571_, v___y_3565_, v___y_3566_, v___y_3567_, v___y_3568_, lean_box(0));
if (lean_obj_tag(v___x_3572_) == 0)
{
lean_object* v_a_3573_; lean_object* v___x_3575_; uint8_t v_isShared_3576_; uint8_t v_isSharedCheck_3605_; 
v_a_3573_ = lean_ctor_get(v___x_3572_, 0);
v_isSharedCheck_3605_ = !lean_is_exclusive(v___x_3572_);
if (v_isSharedCheck_3605_ == 0)
{
v___x_3575_ = v___x_3572_;
v_isShared_3576_ = v_isSharedCheck_3605_;
goto v_resetjp_3574_;
}
else
{
lean_inc(v_a_3573_);
lean_dec(v___x_3572_);
v___x_3575_ = lean_box(0);
v_isShared_3576_ = v_isSharedCheck_3605_;
goto v_resetjp_3574_;
}
v_resetjp_3574_:
{
if (lean_obj_tag(v_a_3573_) == 1)
{
lean_object* v_val_3577_; lean_object* v___x_3579_; uint8_t v_isShared_3580_; uint8_t v_isSharedCheck_3600_; 
lean_del_object(v___x_3575_);
v_val_3577_ = lean_ctor_get(v_a_3573_, 0);
v_isSharedCheck_3600_ = !lean_is_exclusive(v_a_3573_);
if (v_isSharedCheck_3600_ == 0)
{
v___x_3579_ = v_a_3573_;
v_isShared_3580_ = v_isSharedCheck_3600_;
goto v_resetjp_3578_;
}
else
{
lean_inc(v_val_3577_);
lean_dec(v_a_3573_);
v___x_3579_ = lean_box(0);
v_isShared_3580_ = v_isSharedCheck_3600_;
goto v_resetjp_3578_;
}
v_resetjp_3578_:
{
lean_object* v___x_3581_; lean_object* v_a_3582_; lean_object* v___x_3584_; uint8_t v_isShared_3585_; uint8_t v_isSharedCheck_3599_; 
v___x_3581_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(v_val_3577_, v___y_3566_);
v_a_3582_ = lean_ctor_get(v___x_3581_, 0);
v_isSharedCheck_3599_ = !lean_is_exclusive(v___x_3581_);
if (v_isSharedCheck_3599_ == 0)
{
v___x_3584_ = v___x_3581_;
v_isShared_3585_ = v_isSharedCheck_3599_;
goto v_resetjp_3583_;
}
else
{
lean_inc(v_a_3582_);
lean_dec(v___x_3581_);
v___x_3584_ = lean_box(0);
v_isShared_3585_ = v_isSharedCheck_3599_;
goto v_resetjp_3583_;
}
v_resetjp_3583_:
{
lean_object* v_dummy_3586_; lean_object* v_nargs_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3594_; 
v_dummy_3586_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_3587_ = l_Lean_Expr_getAppNumArgs(v_e_3564_);
lean_inc(v_nargs_3587_);
v___x_3588_ = lean_mk_array(v_nargs_3587_, v_dummy_3586_);
v___x_3589_ = lean_unsigned_to_nat(1u);
v___x_3590_ = lean_nat_sub(v_nargs_3587_, v___x_3589_);
lean_dec(v_nargs_3587_);
v___x_3591_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3564_, v___x_3588_, v___x_3590_);
v___x_3592_ = l_Lean_Expr_beta(v_a_3582_, v___x_3591_);
if (v_isShared_3580_ == 0)
{
lean_ctor_set(v___x_3579_, 0, v___x_3592_);
v___x_3594_ = v___x_3579_;
goto v_reusejp_3593_;
}
else
{
lean_object* v_reuseFailAlloc_3598_; 
v_reuseFailAlloc_3598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3598_, 0, v___x_3592_);
v___x_3594_ = v_reuseFailAlloc_3598_;
goto v_reusejp_3593_;
}
v_reusejp_3593_:
{
lean_object* v___x_3596_; 
if (v_isShared_3585_ == 0)
{
lean_ctor_set(v___x_3584_, 0, v___x_3594_);
v___x_3596_ = v___x_3584_;
goto v_reusejp_3595_;
}
else
{
lean_object* v_reuseFailAlloc_3597_; 
v_reuseFailAlloc_3597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3597_, 0, v___x_3594_);
v___x_3596_ = v_reuseFailAlloc_3597_;
goto v_reusejp_3595_;
}
v_reusejp_3595_:
{
return v___x_3596_;
}
}
}
}
}
else
{
lean_object* v___x_3601_; lean_object* v___x_3603_; 
lean_dec(v_a_3573_);
lean_dec_ref(v_e_3564_);
v___x_3601_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
if (v_isShared_3576_ == 0)
{
lean_ctor_set(v___x_3575_, 0, v___x_3601_);
v___x_3603_ = v___x_3575_;
goto v_reusejp_3602_;
}
else
{
lean_object* v_reuseFailAlloc_3604_; 
v_reuseFailAlloc_3604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3604_, 0, v___x_3601_);
v___x_3603_ = v_reuseFailAlloc_3604_;
goto v_reusejp_3602_;
}
v_reusejp_3602_:
{
return v___x_3603_;
}
}
}
}
else
{
lean_object* v_a_3606_; lean_object* v___x_3608_; uint8_t v_isShared_3609_; uint8_t v_isSharedCheck_3613_; 
lean_dec_ref(v_e_3564_);
v_a_3606_ = lean_ctor_get(v___x_3572_, 0);
v_isSharedCheck_3613_ = !lean_is_exclusive(v___x_3572_);
if (v_isSharedCheck_3613_ == 0)
{
v___x_3608_ = v___x_3572_;
v_isShared_3609_ = v_isSharedCheck_3613_;
goto v_resetjp_3607_;
}
else
{
lean_inc(v_a_3606_);
lean_dec(v___x_3572_);
v___x_3608_ = lean_box(0);
v_isShared_3609_ = v_isSharedCheck_3613_;
goto v_resetjp_3607_;
}
v_resetjp_3607_:
{
lean_object* v___x_3611_; 
if (v_isShared_3609_ == 0)
{
v___x_3611_ = v___x_3608_;
goto v_reusejp_3610_;
}
else
{
lean_object* v_reuseFailAlloc_3612_; 
v_reuseFailAlloc_3612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3612_, 0, v_a_3606_);
v___x_3611_ = v_reuseFailAlloc_3612_;
goto v_reusejp_3610_;
}
v_reusejp_3610_:
{
return v___x_3611_;
}
}
}
}
else
{
lean_object* v___x_3614_; lean_object* v___x_3615_; 
lean_dec_ref(v___x_3570_);
lean_dec_ref(v_e_3564_);
lean_dec_ref(v___f_3563_);
v___x_3614_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_3615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3615_, 0, v___x_3614_);
return v___x_3615_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__4___boxed(lean_object* v___f_3616_, lean_object* v_e_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_){
_start:
{
lean_object* v_res_3623_; 
v_res_3623_ = l_Lean_Meta_zetaReduce___lam__4(v___f_3616_, v_e_3617_, v___y_3618_, v___y_3619_, v___y_3620_, v___y_3621_);
lean_dec(v___y_3621_);
lean_dec_ref(v___y_3620_);
lean_dec(v___y_3619_);
lean_dec_ref(v___y_3618_);
return v_res_3623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0(lean_object* v_00_u03b1_3624_, lean_object* v_x_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_){
_start:
{
lean_object* v___x_3631_; lean_object* v___x_3632_; 
v___x_3631_ = lean_apply_1(v_x_3625_, lean_box(0));
v___x_3632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3632_, 0, v___x_3631_);
return v___x_3632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0___boxed(lean_object* v_00_u03b1_3633_, lean_object* v_x_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_){
_start:
{
lean_object* v_res_3640_; 
v_res_3640_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0(v_00_u03b1_3633_, v_x_3634_, v___y_3635_, v___y_3636_, v___y_3637_, v___y_3638_);
lean_dec(v___y_3638_);
lean_dec_ref(v___y_3637_);
lean_dec(v___y_3636_);
lean_dec_ref(v___y_3635_);
return v_res_3640_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__2(lean_object* v___x_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_){
_start:
{
lean_object* v___x_3647_; 
v___x_3647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3647_, 0, v___x_3641_);
return v___x_3647_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__2___boxed(lean_object* v___x_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_){
_start:
{
lean_object* v_res_3654_; 
v_res_3654_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__2(v___x_3648_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_);
lean_dec(v___y_3652_);
lean_dec_ref(v___y_3651_);
lean_dec(v___y_3650_);
lean_dec_ref(v___y_3649_);
return v_res_3654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0(lean_object* v_k_3655_, lean_object* v___y_3656_, lean_object* v_b_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_){
_start:
{
lean_object* v___x_3663_; 
lean_inc(v___y_3661_);
lean_inc_ref(v___y_3660_);
lean_inc(v___y_3659_);
lean_inc_ref(v___y_3658_);
lean_inc(v___y_3656_);
v___x_3663_ = lean_apply_7(v_k_3655_, v_b_3657_, v___y_3656_, v___y_3658_, v___y_3659_, v___y_3660_, v___y_3661_, lean_box(0));
return v___x_3663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0___boxed(lean_object* v_k_3664_, lean_object* v___y_3665_, lean_object* v_b_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_){
_start:
{
lean_object* v_res_3672_; 
v_res_3672_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0(v_k_3664_, v___y_3665_, v_b_3666_, v___y_3667_, v___y_3668_, v___y_3669_, v___y_3670_);
lean_dec(v___y_3670_);
lean_dec_ref(v___y_3669_);
lean_dec(v___y_3668_);
lean_dec_ref(v___y_3667_);
lean_dec(v___y_3665_);
return v_res_3672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(lean_object* v_name_3673_, uint8_t v_bi_3674_, lean_object* v_type_3675_, lean_object* v_k_3676_, uint8_t v_kind_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_, lean_object* v___y_3682_){
_start:
{
lean_object* v___f_3684_; lean_object* v___x_3685_; 
lean_inc(v___y_3678_);
v___f_3684_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3684_, 0, v_k_3676_);
lean_closure_set(v___f_3684_, 1, v___y_3678_);
v___x_3685_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3673_, v_bi_3674_, v_type_3675_, v___f_3684_, v_kind_3677_, v___y_3679_, v___y_3680_, v___y_3681_, v___y_3682_);
if (lean_obj_tag(v___x_3685_) == 0)
{
return v___x_3685_;
}
else
{
lean_object* v_a_3686_; lean_object* v___x_3688_; uint8_t v_isShared_3689_; uint8_t v_isSharedCheck_3693_; 
v_a_3686_ = lean_ctor_get(v___x_3685_, 0);
v_isSharedCheck_3693_ = !lean_is_exclusive(v___x_3685_);
if (v_isSharedCheck_3693_ == 0)
{
v___x_3688_ = v___x_3685_;
v_isShared_3689_ = v_isSharedCheck_3693_;
goto v_resetjp_3687_;
}
else
{
lean_inc(v_a_3686_);
lean_dec(v___x_3685_);
v___x_3688_ = lean_box(0);
v_isShared_3689_ = v_isSharedCheck_3693_;
goto v_resetjp_3687_;
}
v_resetjp_3687_:
{
lean_object* v___x_3691_; 
if (v_isShared_3689_ == 0)
{
v___x_3691_ = v___x_3688_;
goto v_reusejp_3690_;
}
else
{
lean_object* v_reuseFailAlloc_3692_; 
v_reuseFailAlloc_3692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3692_, 0, v_a_3686_);
v___x_3691_ = v_reuseFailAlloc_3692_;
goto v_reusejp_3690_;
}
v_reusejp_3690_:
{
return v___x_3691_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___boxed(lean_object* v_name_3694_, lean_object* v_bi_3695_, lean_object* v_type_3696_, lean_object* v_k_3697_, lean_object* v_kind_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_){
_start:
{
uint8_t v_bi_boxed_3705_; uint8_t v_kind_boxed_3706_; lean_object* v_res_3707_; 
v_bi_boxed_3705_ = lean_unbox(v_bi_3695_);
v_kind_boxed_3706_ = lean_unbox(v_kind_3698_);
v_res_3707_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_name_3694_, v_bi_boxed_3705_, v_type_3696_, v_k_3697_, v_kind_boxed_3706_, v___y_3699_, v___y_3700_, v___y_3701_, v___y_3702_, v___y_3703_);
lean_dec(v___y_3703_);
lean_dec_ref(v___y_3702_);
lean_dec(v___y_3701_);
lean_dec_ref(v___y_3700_);
lean_dec(v___y_3699_);
return v_res_3707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg(lean_object* v_name_3708_, lean_object* v_type_3709_, lean_object* v_val_3710_, lean_object* v_k_3711_, uint8_t v_nondep_3712_, uint8_t v_kind_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_){
_start:
{
lean_object* v___f_3720_; lean_object* v___x_3721_; 
lean_inc(v___y_3714_);
v___f_3720_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3720_, 0, v_k_3711_);
lean_closure_set(v___f_3720_, 1, v___y_3714_);
v___x_3721_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_3708_, v_type_3709_, v_val_3710_, v___f_3720_, v_nondep_3712_, v_kind_3713_, v___y_3715_, v___y_3716_, v___y_3717_, v___y_3718_);
if (lean_obj_tag(v___x_3721_) == 0)
{
return v___x_3721_;
}
else
{
lean_object* v_a_3722_; lean_object* v___x_3724_; uint8_t v_isShared_3725_; uint8_t v_isSharedCheck_3729_; 
v_a_3722_ = lean_ctor_get(v___x_3721_, 0);
v_isSharedCheck_3729_ = !lean_is_exclusive(v___x_3721_);
if (v_isSharedCheck_3729_ == 0)
{
v___x_3724_ = v___x_3721_;
v_isShared_3725_ = v_isSharedCheck_3729_;
goto v_resetjp_3723_;
}
else
{
lean_inc(v_a_3722_);
lean_dec(v___x_3721_);
v___x_3724_ = lean_box(0);
v_isShared_3725_ = v_isSharedCheck_3729_;
goto v_resetjp_3723_;
}
v_resetjp_3723_:
{
lean_object* v___x_3727_; 
if (v_isShared_3725_ == 0)
{
v___x_3727_ = v___x_3724_;
goto v_reusejp_3726_;
}
else
{
lean_object* v_reuseFailAlloc_3728_; 
v_reuseFailAlloc_3728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3728_, 0, v_a_3722_);
v___x_3727_ = v_reuseFailAlloc_3728_;
goto v_reusejp_3726_;
}
v_reusejp_3726_:
{
return v___x_3727_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg___boxed(lean_object* v_name_3730_, lean_object* v_type_3731_, lean_object* v_val_3732_, lean_object* v_k_3733_, lean_object* v_nondep_3734_, lean_object* v_kind_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_){
_start:
{
uint8_t v_nondep_boxed_3742_; uint8_t v_kind_boxed_3743_; lean_object* v_res_3744_; 
v_nondep_boxed_3742_ = lean_unbox(v_nondep_3734_);
v_kind_boxed_3743_ = lean_unbox(v_kind_3735_);
v_res_3744_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg(v_name_3730_, v_type_3731_, v_val_3732_, v_k_3733_, v_nondep_boxed_3742_, v_kind_boxed_3743_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_, v___y_3740_);
lean_dec(v___y_3740_);
lean_dec_ref(v___y_3739_);
lean_dec(v___y_3738_);
lean_dec_ref(v___y_3737_);
lean_dec(v___y_3736_);
return v_res_3744_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0(lean_object* v_00_u03b1_3745_, lean_object* v_x_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_){
_start:
{
lean_object* v___x_3752_; lean_object* v___x_3753_; 
v___x_3752_ = lean_apply_1(v_x_3746_, lean_box(0));
v___x_3753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3753_, 0, v___x_3752_);
return v___x_3753_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0___boxed(lean_object* v_00_u03b1_3754_, lean_object* v_x_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_){
_start:
{
lean_object* v_res_3761_; 
v_res_3761_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0(v_00_u03b1_3754_, v_x_3755_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_);
lean_dec(v___y_3759_);
lean_dec_ref(v___y_3758_);
lean_dec(v___y_3757_);
lean_dec_ref(v___y_3756_);
return v_res_3761_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg(lean_object* v_ref_3762_){
_start:
{
lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; 
v___x_3764_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5);
v___x_3765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3765_, 0, v_ref_3762_);
lean_ctor_set(v___x_3765_, 1, v___x_3764_);
v___x_3766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3766_, 0, v___x_3765_);
return v___x_3766_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg___boxed(lean_object* v_ref_3767_, lean_object* v___y_3768_){
_start:
{
lean_object* v_res_3769_; 
v_res_3769_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg(v_ref_3767_);
return v_res_3769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg(lean_object* v_x_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_){
_start:
{
lean_object* v___y_3778_; lean_object* v_fileName_3787_; lean_object* v_fileMap_3788_; lean_object* v_options_3789_; lean_object* v_currRecDepth_3790_; lean_object* v_maxRecDepth_3791_; lean_object* v_ref_3792_; lean_object* v_currNamespace_3793_; lean_object* v_openDecls_3794_; lean_object* v_initHeartbeats_3795_; lean_object* v_maxHeartbeats_3796_; lean_object* v_quotContext_3797_; lean_object* v_currMacroScope_3798_; uint8_t v_diag_3799_; lean_object* v_cancelTk_x3f_3800_; uint8_t v_suppressElabErrors_3801_; lean_object* v_inheritedTraceOptions_3802_; uint8_t v___y_3804_; lean_object* v___x_3810_; uint8_t v___x_3811_; uint8_t v___x_3812_; 
v_fileName_3787_ = lean_ctor_get(v___y_3774_, 0);
v_fileMap_3788_ = lean_ctor_get(v___y_3774_, 1);
v_options_3789_ = lean_ctor_get(v___y_3774_, 2);
v_currRecDepth_3790_ = lean_ctor_get(v___y_3774_, 3);
v_maxRecDepth_3791_ = lean_ctor_get(v___y_3774_, 4);
v_ref_3792_ = lean_ctor_get(v___y_3774_, 5);
v_currNamespace_3793_ = lean_ctor_get(v___y_3774_, 6);
v_openDecls_3794_ = lean_ctor_get(v___y_3774_, 7);
v_initHeartbeats_3795_ = lean_ctor_get(v___y_3774_, 8);
v_maxHeartbeats_3796_ = lean_ctor_get(v___y_3774_, 9);
v_quotContext_3797_ = lean_ctor_get(v___y_3774_, 10);
v_currMacroScope_3798_ = lean_ctor_get(v___y_3774_, 11);
v_diag_3799_ = lean_ctor_get_uint8(v___y_3774_, sizeof(void*)*14);
v_cancelTk_x3f_3800_ = lean_ctor_get(v___y_3774_, 12);
v_suppressElabErrors_3801_ = lean_ctor_get_uint8(v___y_3774_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3802_ = lean_ctor_get(v___y_3774_, 13);
v___x_3810_ = lean_unsigned_to_nat(0u);
v___x_3811_ = lean_nat_dec_eq(v_maxRecDepth_3791_, v___x_3810_);
v___x_3812_ = lean_bool_not(v___x_3811_);
if (v___x_3812_ == 0)
{
v___y_3804_ = v___x_3812_;
goto v___jp_3803_;
}
else
{
uint8_t v___x_3813_; 
v___x_3813_ = lean_nat_dec_eq(v_currRecDepth_3790_, v_maxRecDepth_3791_);
v___y_3804_ = v___x_3813_;
goto v___jp_3803_;
}
v___jp_3777_:
{
if (lean_obj_tag(v___y_3778_) == 0)
{
return v___y_3778_;
}
else
{
lean_object* v_a_3779_; lean_object* v___x_3781_; uint8_t v_isShared_3782_; uint8_t v_isSharedCheck_3786_; 
v_a_3779_ = lean_ctor_get(v___y_3778_, 0);
v_isSharedCheck_3786_ = !lean_is_exclusive(v___y_3778_);
if (v_isSharedCheck_3786_ == 0)
{
v___x_3781_ = v___y_3778_;
v_isShared_3782_ = v_isSharedCheck_3786_;
goto v_resetjp_3780_;
}
else
{
lean_inc(v_a_3779_);
lean_dec(v___y_3778_);
v___x_3781_ = lean_box(0);
v_isShared_3782_ = v_isSharedCheck_3786_;
goto v_resetjp_3780_;
}
v_resetjp_3780_:
{
lean_object* v___x_3784_; 
if (v_isShared_3782_ == 0)
{
v___x_3784_ = v___x_3781_;
goto v_reusejp_3783_;
}
else
{
lean_object* v_reuseFailAlloc_3785_; 
v_reuseFailAlloc_3785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3785_, 0, v_a_3779_);
v___x_3784_ = v_reuseFailAlloc_3785_;
goto v_reusejp_3783_;
}
v_reusejp_3783_:
{
return v___x_3784_;
}
}
}
}
v___jp_3803_:
{
if (v___y_3804_ == 0)
{
lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; 
v___x_3805_ = lean_unsigned_to_nat(1u);
v___x_3806_ = lean_nat_add(v_currRecDepth_3790_, v___x_3805_);
lean_inc_ref(v_inheritedTraceOptions_3802_);
lean_inc(v_cancelTk_x3f_3800_);
lean_inc(v_currMacroScope_3798_);
lean_inc(v_quotContext_3797_);
lean_inc(v_maxHeartbeats_3796_);
lean_inc(v_initHeartbeats_3795_);
lean_inc(v_openDecls_3794_);
lean_inc(v_currNamespace_3793_);
lean_inc(v_ref_3792_);
lean_inc(v_maxRecDepth_3791_);
lean_inc_ref(v_options_3789_);
lean_inc_ref(v_fileMap_3788_);
lean_inc_ref(v_fileName_3787_);
v___x_3807_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3807_, 0, v_fileName_3787_);
lean_ctor_set(v___x_3807_, 1, v_fileMap_3788_);
lean_ctor_set(v___x_3807_, 2, v_options_3789_);
lean_ctor_set(v___x_3807_, 3, v___x_3806_);
lean_ctor_set(v___x_3807_, 4, v_maxRecDepth_3791_);
lean_ctor_set(v___x_3807_, 5, v_ref_3792_);
lean_ctor_set(v___x_3807_, 6, v_currNamespace_3793_);
lean_ctor_set(v___x_3807_, 7, v_openDecls_3794_);
lean_ctor_set(v___x_3807_, 8, v_initHeartbeats_3795_);
lean_ctor_set(v___x_3807_, 9, v_maxHeartbeats_3796_);
lean_ctor_set(v___x_3807_, 10, v_quotContext_3797_);
lean_ctor_set(v___x_3807_, 11, v_currMacroScope_3798_);
lean_ctor_set(v___x_3807_, 12, v_cancelTk_x3f_3800_);
lean_ctor_set(v___x_3807_, 13, v_inheritedTraceOptions_3802_);
lean_ctor_set_uint8(v___x_3807_, sizeof(void*)*14, v_diag_3799_);
lean_ctor_set_uint8(v___x_3807_, sizeof(void*)*14 + 1, v_suppressElabErrors_3801_);
lean_inc(v___y_3775_);
lean_inc(v___y_3773_);
lean_inc_ref(v___y_3772_);
lean_inc(v___y_3771_);
v___x_3808_ = lean_apply_6(v_x_3770_, v___y_3771_, v___y_3772_, v___y_3773_, v___x_3807_, v___y_3775_, lean_box(0));
v___y_3778_ = v___x_3808_;
goto v___jp_3777_;
}
else
{
lean_object* v___x_3809_; 
lean_dec_ref(v_x_3770_);
lean_inc(v_ref_3792_);
v___x_3809_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg(v_ref_3792_);
v___y_3778_ = v___x_3809_;
goto v___jp_3777_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg___boxed(lean_object* v_x_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_){
_start:
{
lean_object* v_res_3821_; 
v_res_3821_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg(v_x_3814_, v___y_3815_, v___y_3816_, v___y_3817_, v___y_3818_, v___y_3819_);
lean_dec(v___y_3819_);
lean_dec_ref(v___y_3818_);
lean_dec(v___y_3817_);
lean_dec_ref(v___y_3816_);
lean_dec(v___y_3815_);
return v_res_3821_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___lam__0(lean_object* v_fvars_3822_, lean_object* v_pre_3823_, lean_object* v_post_3824_, uint8_t v_usedLetOnly_3825_, uint8_t v_skipConstInApp_3826_, uint8_t v_skipInstances_3827_, lean_object* v_body_3828_, lean_object* v_x_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_){
_start:
{
lean_object* v___x_3836_; lean_object* v___x_3837_; 
v___x_3836_ = lean_array_push(v_fvars_3822_, v_x_3829_);
v___x_3837_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6(v_pre_3823_, v_post_3824_, v_usedLetOnly_3825_, v_skipConstInApp_3826_, v_skipInstances_3827_, v___x_3836_, v_body_3828_, v___y_3830_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_);
return v___x_3837_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___lam__0___boxed(lean_object* v_fvars_3838_, lean_object* v_pre_3839_, lean_object* v_post_3840_, lean_object* v_usedLetOnly_3841_, lean_object* v_skipConstInApp_3842_, lean_object* v_skipInstances_3843_, lean_object* v_body_3844_, lean_object* v_x_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_){
_start:
{
uint8_t v_usedLetOnly_boxed_3852_; uint8_t v_skipConstInApp_boxed_3853_; uint8_t v_skipInstances_boxed_3854_; lean_object* v_res_3855_; 
v_usedLetOnly_boxed_3852_ = lean_unbox(v_usedLetOnly_3841_);
v_skipConstInApp_boxed_3853_ = lean_unbox(v_skipConstInApp_3842_);
v_skipInstances_boxed_3854_ = lean_unbox(v_skipInstances_3843_);
v_res_3855_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___lam__0(v_fvars_3838_, v_pre_3839_, v_post_3840_, v_usedLetOnly_boxed_3852_, v_skipConstInApp_boxed_3853_, v_skipInstances_boxed_3854_, v_body_3844_, v_x_3845_, v___y_3846_, v___y_3847_, v___y_3848_, v___y_3849_, v___y_3850_);
lean_dec(v___y_3850_);
lean_dec_ref(v___y_3849_);
lean_dec(v___y_3848_);
lean_dec_ref(v___y_3847_);
lean_dec(v___y_3846_);
return v_res_3855_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(lean_object* v_pre_3856_, lean_object* v_post_3857_, uint8_t v_usedLetOnly_3858_, uint8_t v_skipConstInApp_3859_, uint8_t v_skipInstances_3860_, lean_object* v_e_3861_, lean_object* v_a_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_){
_start:
{
lean_object* v___x_3868_; 
lean_inc_ref(v_post_3857_);
lean_inc(v___y_3866_);
lean_inc_ref(v___y_3865_);
lean_inc(v___y_3864_);
lean_inc_ref(v___y_3863_);
lean_inc_ref(v_e_3861_);
v___x_3868_ = lean_apply_6(v_post_3857_, v_e_3861_, v___y_3863_, v___y_3864_, v___y_3865_, v___y_3866_, lean_box(0));
if (lean_obj_tag(v___x_3868_) == 0)
{
lean_object* v_a_3869_; lean_object* v___x_3871_; uint8_t v_isShared_3872_; uint8_t v_isSharedCheck_3887_; 
v_a_3869_ = lean_ctor_get(v___x_3868_, 0);
v_isSharedCheck_3887_ = !lean_is_exclusive(v___x_3868_);
if (v_isSharedCheck_3887_ == 0)
{
v___x_3871_ = v___x_3868_;
v_isShared_3872_ = v_isSharedCheck_3887_;
goto v_resetjp_3870_;
}
else
{
lean_inc(v_a_3869_);
lean_dec(v___x_3868_);
v___x_3871_ = lean_box(0);
v_isShared_3872_ = v_isSharedCheck_3887_;
goto v_resetjp_3870_;
}
v_resetjp_3870_:
{
switch(lean_obj_tag(v_a_3869_))
{
case 0:
{
lean_object* v_e_3873_; lean_object* v___x_3875_; 
lean_dec_ref(v_e_3861_);
lean_dec_ref(v_post_3857_);
lean_dec_ref(v_pre_3856_);
v_e_3873_ = lean_ctor_get(v_a_3869_, 0);
lean_inc_ref(v_e_3873_);
lean_dec_ref_known(v_a_3869_, 1);
if (v_isShared_3872_ == 0)
{
lean_ctor_set(v___x_3871_, 0, v_e_3873_);
v___x_3875_ = v___x_3871_;
goto v_reusejp_3874_;
}
else
{
lean_object* v_reuseFailAlloc_3876_; 
v_reuseFailAlloc_3876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3876_, 0, v_e_3873_);
v___x_3875_ = v_reuseFailAlloc_3876_;
goto v_reusejp_3874_;
}
v_reusejp_3874_:
{
return v___x_3875_;
}
}
case 1:
{
lean_object* v_e_3877_; lean_object* v___x_3878_; 
lean_del_object(v___x_3871_);
lean_dec_ref(v_e_3861_);
v_e_3877_ = lean_ctor_get(v_a_3869_, 0);
lean_inc_ref(v_e_3877_);
lean_dec_ref_known(v_a_3869_, 1);
v___x_3878_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3856_, v_post_3857_, v_usedLetOnly_3858_, v_skipConstInApp_3859_, v_skipInstances_3860_, v_e_3877_, v_a_3862_, v___y_3863_, v___y_3864_, v___y_3865_, v___y_3866_);
return v___x_3878_;
}
default: 
{
lean_object* v_e_x3f_3879_; 
lean_dec_ref(v_post_3857_);
lean_dec_ref(v_pre_3856_);
v_e_x3f_3879_ = lean_ctor_get(v_a_3869_, 0);
lean_inc(v_e_x3f_3879_);
lean_dec_ref_known(v_a_3869_, 1);
if (lean_obj_tag(v_e_x3f_3879_) == 0)
{
lean_object* v___x_3881_; 
if (v_isShared_3872_ == 0)
{
lean_ctor_set(v___x_3871_, 0, v_e_3861_);
v___x_3881_ = v___x_3871_;
goto v_reusejp_3880_;
}
else
{
lean_object* v_reuseFailAlloc_3882_; 
v_reuseFailAlloc_3882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3882_, 0, v_e_3861_);
v___x_3881_ = v_reuseFailAlloc_3882_;
goto v_reusejp_3880_;
}
v_reusejp_3880_:
{
return v___x_3881_;
}
}
else
{
lean_object* v_val_3883_; lean_object* v___x_3885_; 
lean_dec_ref(v_e_3861_);
v_val_3883_ = lean_ctor_get(v_e_x3f_3879_, 0);
lean_inc(v_val_3883_);
lean_dec_ref_known(v_e_x3f_3879_, 1);
if (v_isShared_3872_ == 0)
{
lean_ctor_set(v___x_3871_, 0, v_val_3883_);
v___x_3885_ = v___x_3871_;
goto v_reusejp_3884_;
}
else
{
lean_object* v_reuseFailAlloc_3886_; 
v_reuseFailAlloc_3886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3886_, 0, v_val_3883_);
v___x_3885_ = v_reuseFailAlloc_3886_;
goto v_reusejp_3884_;
}
v_reusejp_3884_:
{
return v___x_3885_;
}
}
}
}
}
}
else
{
lean_object* v_a_3888_; lean_object* v___x_3890_; uint8_t v_isShared_3891_; uint8_t v_isSharedCheck_3895_; 
lean_dec_ref(v_e_3861_);
lean_dec_ref(v_post_3857_);
lean_dec_ref(v_pre_3856_);
v_a_3888_ = lean_ctor_get(v___x_3868_, 0);
v_isSharedCheck_3895_ = !lean_is_exclusive(v___x_3868_);
if (v_isSharedCheck_3895_ == 0)
{
v___x_3890_ = v___x_3868_;
v_isShared_3891_ = v_isSharedCheck_3895_;
goto v_resetjp_3889_;
}
else
{
lean_inc(v_a_3888_);
lean_dec(v___x_3868_);
v___x_3890_ = lean_box(0);
v_isShared_3891_ = v_isSharedCheck_3895_;
goto v_resetjp_3889_;
}
v_resetjp_3889_:
{
lean_object* v___x_3893_; 
if (v_isShared_3891_ == 0)
{
v___x_3893_ = v___x_3890_;
goto v_reusejp_3892_;
}
else
{
lean_object* v_reuseFailAlloc_3894_; 
v_reuseFailAlloc_3894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3894_, 0, v_a_3888_);
v___x_3893_ = v_reuseFailAlloc_3894_;
goto v_reusejp_3892_;
}
v_reusejp_3892_:
{
return v___x_3893_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6(lean_object* v_pre_3896_, lean_object* v_post_3897_, uint8_t v_usedLetOnly_3898_, uint8_t v_skipConstInApp_3899_, uint8_t v_skipInstances_3900_, lean_object* v_fvars_3901_, lean_object* v_e_3902_, lean_object* v_a_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_){
_start:
{
if (lean_obj_tag(v_e_3902_) == 6)
{
lean_object* v_binderName_3909_; lean_object* v_binderType_3910_; lean_object* v_body_3911_; uint8_t v_binderInfo_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; 
v_binderName_3909_ = lean_ctor_get(v_e_3902_, 0);
lean_inc(v_binderName_3909_);
v_binderType_3910_ = lean_ctor_get(v_e_3902_, 1);
lean_inc_ref(v_binderType_3910_);
v_body_3911_ = lean_ctor_get(v_e_3902_, 2);
lean_inc_ref(v_body_3911_);
v_binderInfo_3912_ = lean_ctor_get_uint8(v_e_3902_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_3902_, 3);
v___x_3913_ = lean_expr_instantiate_rev(v_binderType_3910_, v_fvars_3901_);
lean_dec_ref(v_binderType_3910_);
lean_inc_ref(v_post_3897_);
lean_inc_ref(v_pre_3896_);
v___x_3914_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3896_, v_post_3897_, v_usedLetOnly_3898_, v_skipConstInApp_3899_, v_skipInstances_3900_, v___x_3913_, v_a_3903_, v___y_3904_, v___y_3905_, v___y_3906_, v___y_3907_);
if (lean_obj_tag(v___x_3914_) == 0)
{
lean_object* v_a_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___f_3919_; uint8_t v___x_3920_; lean_object* v___x_3921_; 
v_a_3915_ = lean_ctor_get(v___x_3914_, 0);
lean_inc(v_a_3915_);
lean_dec_ref_known(v___x_3914_, 1);
v___x_3916_ = lean_box(v_usedLetOnly_3898_);
v___x_3917_ = lean_box(v_skipConstInApp_3899_);
v___x_3918_ = lean_box(v_skipInstances_3900_);
v___f_3919_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___lam__0___boxed), 14, 7);
lean_closure_set(v___f_3919_, 0, v_fvars_3901_);
lean_closure_set(v___f_3919_, 1, v_pre_3896_);
lean_closure_set(v___f_3919_, 2, v_post_3897_);
lean_closure_set(v___f_3919_, 3, v___x_3916_);
lean_closure_set(v___f_3919_, 4, v___x_3917_);
lean_closure_set(v___f_3919_, 5, v___x_3918_);
lean_closure_set(v___f_3919_, 6, v_body_3911_);
v___x_3920_ = 0;
v___x_3921_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_binderName_3909_, v_binderInfo_3912_, v_a_3915_, v___f_3919_, v___x_3920_, v_a_3903_, v___y_3904_, v___y_3905_, v___y_3906_, v___y_3907_);
return v___x_3921_;
}
else
{
lean_dec_ref(v_body_3911_);
lean_dec(v_binderName_3909_);
lean_dec_ref(v_fvars_3901_);
lean_dec_ref(v_post_3897_);
lean_dec_ref(v_pre_3896_);
return v___x_3914_;
}
}
else
{
lean_object* v___x_3922_; lean_object* v___x_3923_; 
v___x_3922_ = lean_expr_instantiate_rev(v_e_3902_, v_fvars_3901_);
lean_dec_ref(v_e_3902_);
lean_inc_ref(v_post_3897_);
lean_inc_ref(v_pre_3896_);
v___x_3923_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3896_, v_post_3897_, v_usedLetOnly_3898_, v_skipConstInApp_3899_, v_skipInstances_3900_, v___x_3922_, v_a_3903_, v___y_3904_, v___y_3905_, v___y_3906_, v___y_3907_);
if (lean_obj_tag(v___x_3923_) == 0)
{
lean_object* v_a_3924_; uint8_t v___x_3925_; uint8_t v___x_3926_; uint8_t v___x_3927_; lean_object* v___x_3928_; 
v_a_3924_ = lean_ctor_get(v___x_3923_, 0);
lean_inc(v_a_3924_);
lean_dec_ref_known(v___x_3923_, 1);
v___x_3925_ = 0;
v___x_3926_ = 1;
v___x_3927_ = 1;
v___x_3928_ = l_Lean_Meta_mkLambdaFVars(v_fvars_3901_, v_a_3924_, v___x_3925_, v_usedLetOnly_3898_, v___x_3925_, v___x_3926_, v___x_3927_, v___y_3904_, v___y_3905_, v___y_3906_, v___y_3907_);
lean_dec_ref(v_fvars_3901_);
if (lean_obj_tag(v___x_3928_) == 0)
{
lean_object* v_a_3929_; lean_object* v___x_3930_; 
v_a_3929_ = lean_ctor_get(v___x_3928_, 0);
lean_inc(v_a_3929_);
lean_dec_ref_known(v___x_3928_, 1);
v___x_3930_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_3896_, v_post_3897_, v_usedLetOnly_3898_, v_skipConstInApp_3899_, v_skipInstances_3900_, v_a_3929_, v_a_3903_, v___y_3904_, v___y_3905_, v___y_3906_, v___y_3907_);
return v___x_3930_;
}
else
{
lean_dec_ref(v_post_3897_);
lean_dec_ref(v_pre_3896_);
return v___x_3928_;
}
}
else
{
lean_dec_ref(v_fvars_3901_);
lean_dec_ref(v_post_3897_);
lean_dec_ref(v_pre_3896_);
return v___x_3923_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___lam__0(lean_object* v_fvars_3931_, lean_object* v_pre_3932_, lean_object* v_post_3933_, uint8_t v_usedLetOnly_3934_, uint8_t v_skipConstInApp_3935_, uint8_t v_skipInstances_3936_, lean_object* v_body_3937_, lean_object* v_x_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_){
_start:
{
lean_object* v___x_3945_; lean_object* v___x_3946_; 
v___x_3945_ = lean_array_push(v_fvars_3931_, v_x_3938_);
v___x_3946_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7(v_pre_3932_, v_post_3933_, v_usedLetOnly_3934_, v_skipConstInApp_3935_, v_skipInstances_3936_, v___x_3945_, v_body_3937_, v___y_3939_, v___y_3940_, v___y_3941_, v___y_3942_, v___y_3943_);
return v___x_3946_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___lam__0___boxed(lean_object* v_fvars_3947_, lean_object* v_pre_3948_, lean_object* v_post_3949_, lean_object* v_usedLetOnly_3950_, lean_object* v_skipConstInApp_3951_, lean_object* v_skipInstances_3952_, lean_object* v_body_3953_, lean_object* v_x_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_){
_start:
{
uint8_t v_usedLetOnly_boxed_3961_; uint8_t v_skipConstInApp_boxed_3962_; uint8_t v_skipInstances_boxed_3963_; lean_object* v_res_3964_; 
v_usedLetOnly_boxed_3961_ = lean_unbox(v_usedLetOnly_3950_);
v_skipConstInApp_boxed_3962_ = lean_unbox(v_skipConstInApp_3951_);
v_skipInstances_boxed_3963_ = lean_unbox(v_skipInstances_3952_);
v_res_3964_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___lam__0(v_fvars_3947_, v_pre_3948_, v_post_3949_, v_usedLetOnly_boxed_3961_, v_skipConstInApp_boxed_3962_, v_skipInstances_boxed_3963_, v_body_3953_, v_x_3954_, v___y_3955_, v___y_3956_, v___y_3957_, v___y_3958_, v___y_3959_);
lean_dec(v___y_3959_);
lean_dec_ref(v___y_3958_);
lean_dec(v___y_3957_);
lean_dec_ref(v___y_3956_);
lean_dec(v___y_3955_);
return v_res_3964_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7(lean_object* v_pre_3965_, lean_object* v_post_3966_, uint8_t v_usedLetOnly_3967_, uint8_t v_skipConstInApp_3968_, uint8_t v_skipInstances_3969_, lean_object* v_fvars_3970_, lean_object* v_e_3971_, lean_object* v_a_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_){
_start:
{
if (lean_obj_tag(v_e_3971_) == 8)
{
lean_object* v_declName_3978_; lean_object* v_type_3979_; lean_object* v_value_3980_; lean_object* v_body_3981_; uint8_t v_nondep_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; 
v_declName_3978_ = lean_ctor_get(v_e_3971_, 0);
lean_inc(v_declName_3978_);
v_type_3979_ = lean_ctor_get(v_e_3971_, 1);
lean_inc_ref(v_type_3979_);
v_value_3980_ = lean_ctor_get(v_e_3971_, 2);
lean_inc_ref(v_value_3980_);
v_body_3981_ = lean_ctor_get(v_e_3971_, 3);
lean_inc_ref(v_body_3981_);
v_nondep_3982_ = lean_ctor_get_uint8(v_e_3971_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_3971_, 4);
v___x_3983_ = lean_expr_instantiate_rev(v_type_3979_, v_fvars_3970_);
lean_dec_ref(v_type_3979_);
lean_inc_ref(v_post_3966_);
lean_inc_ref(v_pre_3965_);
v___x_3984_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3965_, v_post_3966_, v_usedLetOnly_3967_, v_skipConstInApp_3968_, v_skipInstances_3969_, v___x_3983_, v_a_3972_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_);
if (lean_obj_tag(v___x_3984_) == 0)
{
lean_object* v_a_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; 
v_a_3985_ = lean_ctor_get(v___x_3984_, 0);
lean_inc(v_a_3985_);
lean_dec_ref_known(v___x_3984_, 1);
v___x_3986_ = lean_expr_instantiate_rev(v_value_3980_, v_fvars_3970_);
lean_dec_ref(v_value_3980_);
lean_inc_ref(v_post_3966_);
lean_inc_ref(v_pre_3965_);
v___x_3987_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3965_, v_post_3966_, v_usedLetOnly_3967_, v_skipConstInApp_3968_, v_skipInstances_3969_, v___x_3986_, v_a_3972_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_);
if (lean_obj_tag(v___x_3987_) == 0)
{
lean_object* v_a_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___f_3992_; uint8_t v___x_3993_; lean_object* v___x_3994_; 
v_a_3988_ = lean_ctor_get(v___x_3987_, 0);
lean_inc(v_a_3988_);
lean_dec_ref_known(v___x_3987_, 1);
v___x_3989_ = lean_box(v_usedLetOnly_3967_);
v___x_3990_ = lean_box(v_skipConstInApp_3968_);
v___x_3991_ = lean_box(v_skipInstances_3969_);
v___f_3992_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___lam__0___boxed), 14, 7);
lean_closure_set(v___f_3992_, 0, v_fvars_3970_);
lean_closure_set(v___f_3992_, 1, v_pre_3965_);
lean_closure_set(v___f_3992_, 2, v_post_3966_);
lean_closure_set(v___f_3992_, 3, v___x_3989_);
lean_closure_set(v___f_3992_, 4, v___x_3990_);
lean_closure_set(v___f_3992_, 5, v___x_3991_);
lean_closure_set(v___f_3992_, 6, v_body_3981_);
v___x_3993_ = 0;
v___x_3994_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg(v_declName_3978_, v_a_3985_, v_a_3988_, v___f_3992_, v_nondep_3982_, v___x_3993_, v_a_3972_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_);
return v___x_3994_;
}
else
{
lean_dec(v_a_3985_);
lean_dec_ref(v_body_3981_);
lean_dec(v_declName_3978_);
lean_dec_ref(v_fvars_3970_);
lean_dec_ref(v_post_3966_);
lean_dec_ref(v_pre_3965_);
return v___x_3987_;
}
}
else
{
lean_dec_ref(v_body_3981_);
lean_dec_ref(v_value_3980_);
lean_dec(v_declName_3978_);
lean_dec_ref(v_fvars_3970_);
lean_dec_ref(v_post_3966_);
lean_dec_ref(v_pre_3965_);
return v___x_3984_;
}
}
else
{
lean_object* v___x_3995_; lean_object* v___x_3996_; 
v___x_3995_ = lean_expr_instantiate_rev(v_e_3971_, v_fvars_3970_);
lean_dec_ref(v_e_3971_);
lean_inc_ref(v_post_3966_);
lean_inc_ref(v_pre_3965_);
v___x_3996_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3965_, v_post_3966_, v_usedLetOnly_3967_, v_skipConstInApp_3968_, v_skipInstances_3969_, v___x_3995_, v_a_3972_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_);
if (lean_obj_tag(v___x_3996_) == 0)
{
lean_object* v_a_3997_; uint8_t v___x_3998_; uint8_t v___x_3999_; lean_object* v___x_4000_; 
v_a_3997_ = lean_ctor_get(v___x_3996_, 0);
lean_inc(v_a_3997_);
lean_dec_ref_known(v___x_3996_, 1);
v___x_3998_ = 0;
v___x_3999_ = 1;
v___x_4000_ = l_Lean_Meta_mkLetFVars(v_fvars_3970_, v_a_3997_, v_usedLetOnly_3967_, v___x_3998_, v___x_3999_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_);
lean_dec_ref(v_fvars_3970_);
if (lean_obj_tag(v___x_4000_) == 0)
{
lean_object* v_a_4001_; lean_object* v___x_4002_; 
v_a_4001_ = lean_ctor_get(v___x_4000_, 0);
lean_inc(v_a_4001_);
lean_dec_ref_known(v___x_4000_, 1);
v___x_4002_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_3965_, v_post_3966_, v_usedLetOnly_3967_, v_skipConstInApp_3968_, v_skipInstances_3969_, v_a_4001_, v_a_3972_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_);
return v___x_4002_;
}
else
{
lean_dec_ref(v_post_3966_);
lean_dec_ref(v_pre_3965_);
return v___x_4000_;
}
}
else
{
lean_dec_ref(v_fvars_3970_);
lean_dec_ref(v_post_3966_);
lean_dec_ref(v_pre_3965_);
return v___x_3996_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__2(lean_object* v_pre_4003_, lean_object* v_post_4004_, uint8_t v_usedLetOnly_4005_, uint8_t v_skipConstInApp_4006_, uint8_t v_skipInstances_4007_, size_t v_sz_4008_, size_t v_i_4009_, lean_object* v_bs_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_){
_start:
{
uint8_t v___x_4017_; 
v___x_4017_ = lean_usize_dec_lt(v_i_4009_, v_sz_4008_);
if (v___x_4017_ == 0)
{
lean_object* v___x_4018_; 
lean_dec_ref(v_post_4004_);
lean_dec_ref(v_pre_4003_);
v___x_4018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4018_, 0, v_bs_4010_);
return v___x_4018_;
}
else
{
lean_object* v_v_4019_; lean_object* v___x_4020_; 
v_v_4019_ = lean_array_uget_borrowed(v_bs_4010_, v_i_4009_);
lean_inc(v_v_4019_);
lean_inc_ref(v_post_4004_);
lean_inc_ref(v_pre_4003_);
v___x_4020_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4003_, v_post_4004_, v_usedLetOnly_4005_, v_skipConstInApp_4006_, v_skipInstances_4007_, v_v_4019_, v___y_4011_, v___y_4012_, v___y_4013_, v___y_4014_, v___y_4015_);
if (lean_obj_tag(v___x_4020_) == 0)
{
lean_object* v_a_4021_; lean_object* v___x_4022_; lean_object* v_bs_x27_4023_; size_t v___x_4024_; size_t v___x_4025_; lean_object* v___x_4026_; 
v_a_4021_ = lean_ctor_get(v___x_4020_, 0);
lean_inc(v_a_4021_);
lean_dec_ref_known(v___x_4020_, 1);
v___x_4022_ = lean_unsigned_to_nat(0u);
v_bs_x27_4023_ = lean_array_uset(v_bs_4010_, v_i_4009_, v___x_4022_);
v___x_4024_ = ((size_t)1ULL);
v___x_4025_ = lean_usize_add(v_i_4009_, v___x_4024_);
v___x_4026_ = lean_array_uset(v_bs_x27_4023_, v_i_4009_, v_a_4021_);
v_i_4009_ = v___x_4025_;
v_bs_4010_ = v___x_4026_;
goto _start;
}
else
{
lean_object* v_a_4028_; lean_object* v___x_4030_; uint8_t v_isShared_4031_; uint8_t v_isSharedCheck_4035_; 
lean_dec_ref(v_bs_4010_);
lean_dec_ref(v_post_4004_);
lean_dec_ref(v_pre_4003_);
v_a_4028_ = lean_ctor_get(v___x_4020_, 0);
v_isSharedCheck_4035_ = !lean_is_exclusive(v___x_4020_);
if (v_isSharedCheck_4035_ == 0)
{
v___x_4030_ = v___x_4020_;
v_isShared_4031_ = v_isSharedCheck_4035_;
goto v_resetjp_4029_;
}
else
{
lean_inc(v_a_4028_);
lean_dec(v___x_4020_);
v___x_4030_ = lean_box(0);
v_isShared_4031_ = v_isSharedCheck_4035_;
goto v_resetjp_4029_;
}
v_resetjp_4029_:
{
lean_object* v___x_4033_; 
if (v_isShared_4031_ == 0)
{
v___x_4033_ = v___x_4030_;
goto v_reusejp_4032_;
}
else
{
lean_object* v_reuseFailAlloc_4034_; 
v_reuseFailAlloc_4034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4034_, 0, v_a_4028_);
v___x_4033_ = v_reuseFailAlloc_4034_;
goto v_reusejp_4032_;
}
v_reusejp_4032_:
{
return v___x_4033_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0(lean_object* v_pre_4036_, lean_object* v_post_4037_, uint8_t v_usedLetOnly_4038_, uint8_t v_skipConstInApp_4039_, uint8_t v_skipInstances_4040_, lean_object* v___x_4041_, lean_object* v___y_4042_, lean_object* v_b_4043_, lean_object* v_a_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_){
_start:
{
lean_object* v___x_4050_; 
v___x_4050_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4036_, v_post_4037_, v_usedLetOnly_4038_, v_skipConstInApp_4039_, v_skipInstances_4040_, v___x_4041_, v___y_4042_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_);
if (lean_obj_tag(v___x_4050_) == 0)
{
lean_object* v_a_4051_; lean_object* v___x_4053_; uint8_t v_isShared_4054_; uint8_t v_isSharedCheck_4060_; 
v_a_4051_ = lean_ctor_get(v___x_4050_, 0);
v_isSharedCheck_4060_ = !lean_is_exclusive(v___x_4050_);
if (v_isSharedCheck_4060_ == 0)
{
v___x_4053_ = v___x_4050_;
v_isShared_4054_ = v_isSharedCheck_4060_;
goto v_resetjp_4052_;
}
else
{
lean_inc(v_a_4051_);
lean_dec(v___x_4050_);
v___x_4053_ = lean_box(0);
v_isShared_4054_ = v_isSharedCheck_4060_;
goto v_resetjp_4052_;
}
v_resetjp_4052_:
{
lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4058_; 
v___x_4055_ = lean_array_fset(v_b_4043_, v_a_4044_, v_a_4051_);
v___x_4056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4056_, 0, v___x_4055_);
if (v_isShared_4054_ == 0)
{
lean_ctor_set(v___x_4053_, 0, v___x_4056_);
v___x_4058_ = v___x_4053_;
goto v_reusejp_4057_;
}
else
{
lean_object* v_reuseFailAlloc_4059_; 
v_reuseFailAlloc_4059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4059_, 0, v___x_4056_);
v___x_4058_ = v_reuseFailAlloc_4059_;
goto v_reusejp_4057_;
}
v_reusejp_4057_:
{
return v___x_4058_;
}
}
}
else
{
lean_object* v_a_4061_; lean_object* v___x_4063_; uint8_t v_isShared_4064_; uint8_t v_isSharedCheck_4068_; 
lean_dec_ref(v_b_4043_);
v_a_4061_ = lean_ctor_get(v___x_4050_, 0);
v_isSharedCheck_4068_ = !lean_is_exclusive(v___x_4050_);
if (v_isSharedCheck_4068_ == 0)
{
v___x_4063_ = v___x_4050_;
v_isShared_4064_ = v_isSharedCheck_4068_;
goto v_resetjp_4062_;
}
else
{
lean_inc(v_a_4061_);
lean_dec(v___x_4050_);
v___x_4063_ = lean_box(0);
v_isShared_4064_ = v_isSharedCheck_4068_;
goto v_resetjp_4062_;
}
v_resetjp_4062_:
{
lean_object* v___x_4066_; 
if (v_isShared_4064_ == 0)
{
v___x_4066_ = v___x_4063_;
goto v_reusejp_4065_;
}
else
{
lean_object* v_reuseFailAlloc_4067_; 
v_reuseFailAlloc_4067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4067_, 0, v_a_4061_);
v___x_4066_ = v_reuseFailAlloc_4067_;
goto v_reusejp_4065_;
}
v_reusejp_4065_:
{
return v___x_4066_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed(lean_object* v_pre_4069_, lean_object* v_post_4070_, lean_object* v_usedLetOnly_4071_, lean_object* v_skipConstInApp_4072_, lean_object* v_skipInstances_4073_, lean_object* v___x_4074_, lean_object* v___y_4075_, lean_object* v_b_4076_, lean_object* v_a_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_){
_start:
{
uint8_t v_usedLetOnly_boxed_4083_; uint8_t v_skipConstInApp_boxed_4084_; uint8_t v_skipInstances_boxed_4085_; lean_object* v_res_4086_; 
v_usedLetOnly_boxed_4083_ = lean_unbox(v_usedLetOnly_4071_);
v_skipConstInApp_boxed_4084_ = lean_unbox(v_skipConstInApp_4072_);
v_skipInstances_boxed_4085_ = lean_unbox(v_skipInstances_4073_);
v_res_4086_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0(v_pre_4069_, v_post_4070_, v_usedLetOnly_boxed_4083_, v_skipConstInApp_boxed_4084_, v_skipInstances_boxed_4085_, v___x_4074_, v___y_4075_, v_b_4076_, v_a_4077_, v___y_4078_, v___y_4079_, v___y_4080_, v___y_4081_);
lean_dec(v___y_4081_);
lean_dec_ref(v___y_4080_);
lean_dec(v___y_4079_);
lean_dec_ref(v___y_4078_);
lean_dec(v_a_4077_);
lean_dec(v___y_4075_);
return v_res_4086_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg(lean_object* v_upperBound_4087_, lean_object* v___x_4088_, lean_object* v_pre_4089_, lean_object* v_post_4090_, uint8_t v_usedLetOnly_4091_, uint8_t v_skipConstInApp_4092_, uint8_t v_skipInstances_4093_, lean_object* v_a_4094_, lean_object* v_b_4095_, lean_object* v___y_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_){
_start:
{
lean_object* v___y_4103_; uint8_t v___x_4126_; 
v___x_4126_ = lean_nat_dec_lt(v_a_4094_, v_upperBound_4087_);
if (v___x_4126_ == 0)
{
lean_object* v___x_4127_; 
lean_dec(v_a_4094_);
lean_dec_ref(v_post_4090_);
lean_dec_ref(v_pre_4089_);
v___x_4127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4127_, 0, v_b_4095_);
return v___x_4127_;
}
else
{
lean_object* v___x_4128_; lean_object* v___x_4129_; uint8_t v___x_4130_; 
v___x_4128_ = lean_array_fget_borrowed(v_b_4095_, v_a_4094_);
v___x_4129_ = lean_array_get_size(v___x_4088_);
v___x_4130_ = lean_nat_dec_lt(v_a_4094_, v___x_4129_);
if (v___x_4130_ == 0)
{
lean_object* v___x_4131_; lean_object* v___x_4132_; lean_object* v___x_4133_; lean_object* v___f_4134_; 
lean_inc(v___x_4128_);
v___x_4131_ = lean_box(v_usedLetOnly_4091_);
v___x_4132_ = lean_box(v_skipConstInApp_4092_);
v___x_4133_ = lean_box(v_skipInstances_4093_);
lean_inc(v_a_4094_);
lean_inc(v___y_4096_);
lean_inc_ref(v_post_4090_);
lean_inc_ref(v_pre_4089_);
v___f_4134_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_4134_, 0, v_pre_4089_);
lean_closure_set(v___f_4134_, 1, v_post_4090_);
lean_closure_set(v___f_4134_, 2, v___x_4131_);
lean_closure_set(v___f_4134_, 3, v___x_4132_);
lean_closure_set(v___f_4134_, 4, v___x_4133_);
lean_closure_set(v___f_4134_, 5, v___x_4128_);
lean_closure_set(v___f_4134_, 6, v___y_4096_);
lean_closure_set(v___f_4134_, 7, v_b_4095_);
lean_closure_set(v___f_4134_, 8, v_a_4094_);
v___y_4103_ = v___f_4134_;
goto v___jp_4102_;
}
else
{
lean_object* v___x_4135_; uint8_t v_isInstance_4136_; 
v___x_4135_ = lean_array_fget_borrowed(v___x_4088_, v_a_4094_);
v_isInstance_4136_ = lean_ctor_get_uint8(v___x_4135_, sizeof(void*)*1 + 4);
if (v_isInstance_4136_ == 0)
{
lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___f_4140_; 
lean_inc(v___x_4128_);
v___x_4137_ = lean_box(v_usedLetOnly_4091_);
v___x_4138_ = lean_box(v_skipConstInApp_4092_);
v___x_4139_ = lean_box(v_skipInstances_4093_);
lean_inc(v_a_4094_);
lean_inc(v___y_4096_);
lean_inc_ref(v_post_4090_);
lean_inc_ref(v_pre_4089_);
v___f_4140_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_4140_, 0, v_pre_4089_);
lean_closure_set(v___f_4140_, 1, v_post_4090_);
lean_closure_set(v___f_4140_, 2, v___x_4137_);
lean_closure_set(v___f_4140_, 3, v___x_4138_);
lean_closure_set(v___f_4140_, 4, v___x_4139_);
lean_closure_set(v___f_4140_, 5, v___x_4128_);
lean_closure_set(v___f_4140_, 6, v___y_4096_);
lean_closure_set(v___f_4140_, 7, v_b_4095_);
lean_closure_set(v___f_4140_, 8, v_a_4094_);
v___y_4103_ = v___f_4140_;
goto v___jp_4102_;
}
else
{
lean_object* v___x_4141_; lean_object* v___f_4142_; 
v___x_4141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4141_, 0, v_b_4095_);
v___f_4142_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_4142_, 0, v___x_4141_);
v___y_4103_ = v___f_4142_;
goto v___jp_4102_;
}
}
}
v___jp_4102_:
{
lean_object* v___x_4104_; 
lean_inc(v___y_4100_);
lean_inc_ref(v___y_4099_);
lean_inc(v___y_4098_);
lean_inc_ref(v___y_4097_);
v___x_4104_ = lean_apply_5(v___y_4103_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_, lean_box(0));
if (lean_obj_tag(v___x_4104_) == 0)
{
lean_object* v_a_4105_; lean_object* v___x_4107_; uint8_t v_isShared_4108_; uint8_t v_isSharedCheck_4117_; 
v_a_4105_ = lean_ctor_get(v___x_4104_, 0);
v_isSharedCheck_4117_ = !lean_is_exclusive(v___x_4104_);
if (v_isSharedCheck_4117_ == 0)
{
v___x_4107_ = v___x_4104_;
v_isShared_4108_ = v_isSharedCheck_4117_;
goto v_resetjp_4106_;
}
else
{
lean_inc(v_a_4105_);
lean_dec(v___x_4104_);
v___x_4107_ = lean_box(0);
v_isShared_4108_ = v_isSharedCheck_4117_;
goto v_resetjp_4106_;
}
v_resetjp_4106_:
{
if (lean_obj_tag(v_a_4105_) == 0)
{
lean_object* v_a_4109_; lean_object* v___x_4111_; 
lean_dec(v_a_4094_);
lean_dec_ref(v_post_4090_);
lean_dec_ref(v_pre_4089_);
v_a_4109_ = lean_ctor_get(v_a_4105_, 0);
lean_inc(v_a_4109_);
lean_dec_ref_known(v_a_4105_, 1);
if (v_isShared_4108_ == 0)
{
lean_ctor_set(v___x_4107_, 0, v_a_4109_);
v___x_4111_ = v___x_4107_;
goto v_reusejp_4110_;
}
else
{
lean_object* v_reuseFailAlloc_4112_; 
v_reuseFailAlloc_4112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4112_, 0, v_a_4109_);
v___x_4111_ = v_reuseFailAlloc_4112_;
goto v_reusejp_4110_;
}
v_reusejp_4110_:
{
return v___x_4111_;
}
}
else
{
lean_object* v_a_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; 
lean_del_object(v___x_4107_);
v_a_4113_ = lean_ctor_get(v_a_4105_, 0);
lean_inc(v_a_4113_);
lean_dec_ref_known(v_a_4105_, 1);
v___x_4114_ = lean_unsigned_to_nat(1u);
v___x_4115_ = lean_nat_add(v_a_4094_, v___x_4114_);
lean_dec(v_a_4094_);
v_a_4094_ = v___x_4115_;
v_b_4095_ = v_a_4113_;
goto _start;
}
}
}
else
{
lean_object* v_a_4118_; lean_object* v___x_4120_; uint8_t v_isShared_4121_; uint8_t v_isSharedCheck_4125_; 
lean_dec(v_a_4094_);
lean_dec_ref(v_post_4090_);
lean_dec_ref(v_pre_4089_);
v_a_4118_ = lean_ctor_get(v___x_4104_, 0);
v_isSharedCheck_4125_ = !lean_is_exclusive(v___x_4104_);
if (v_isSharedCheck_4125_ == 0)
{
v___x_4120_ = v___x_4104_;
v_isShared_4121_ = v_isSharedCheck_4125_;
goto v_resetjp_4119_;
}
else
{
lean_inc(v_a_4118_);
lean_dec(v___x_4104_);
v___x_4120_ = lean_box(0);
v_isShared_4121_ = v_isSharedCheck_4125_;
goto v_resetjp_4119_;
}
v_resetjp_4119_:
{
lean_object* v___x_4123_; 
if (v_isShared_4121_ == 0)
{
v___x_4123_ = v___x_4120_;
goto v_reusejp_4122_;
}
else
{
lean_object* v_reuseFailAlloc_4124_; 
v_reuseFailAlloc_4124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4124_, 0, v_a_4118_);
v___x_4123_ = v_reuseFailAlloc_4124_;
goto v_reusejp_4122_;
}
v_reusejp_4122_:
{
return v___x_4123_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__8(uint8_t v_skipInstances_4143_, lean_object* v_pre_4144_, lean_object* v_post_4145_, uint8_t v_usedLetOnly_4146_, uint8_t v_skipConstInApp_4147_, lean_object* v_x_4148_, lean_object* v_x_4149_, lean_object* v_x_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_){
_start:
{
lean_object* v_f_4158_; lean_object* v___y_4159_; lean_object* v___y_4160_; lean_object* v___y_4161_; lean_object* v___y_4162_; lean_object* v___y_4163_; 
if (lean_obj_tag(v_x_4148_) == 5)
{
lean_object* v_fn_4206_; lean_object* v_arg_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; 
v_fn_4206_ = lean_ctor_get(v_x_4148_, 0);
lean_inc_ref(v_fn_4206_);
v_arg_4207_ = lean_ctor_get(v_x_4148_, 1);
lean_inc_ref(v_arg_4207_);
lean_dec_ref_known(v_x_4148_, 2);
v___x_4208_ = lean_array_set(v_x_4149_, v_x_4150_, v_arg_4207_);
v___x_4209_ = lean_unsigned_to_nat(1u);
v___x_4210_ = lean_nat_sub(v_x_4150_, v___x_4209_);
lean_dec(v_x_4150_);
v_x_4148_ = v_fn_4206_;
v_x_4149_ = v___x_4208_;
v_x_4150_ = v___x_4210_;
goto _start;
}
else
{
lean_dec(v_x_4150_);
if (v_skipConstInApp_4147_ == 0)
{
goto v___jp_4203_;
}
else
{
uint8_t v___x_4212_; 
v___x_4212_ = l_Lean_Expr_isConst(v_x_4148_);
if (v___x_4212_ == 0)
{
goto v___jp_4203_;
}
else
{
v_f_4158_ = v_x_4148_;
v___y_4159_ = v___y_4151_;
v___y_4160_ = v___y_4152_;
v___y_4161_ = v___y_4153_;
v___y_4162_ = v___y_4154_;
v___y_4163_ = v___y_4155_;
goto v___jp_4157_;
}
}
}
v___jp_4157_:
{
if (v_skipInstances_4143_ == 0)
{
size_t v_sz_4164_; size_t v___x_4165_; lean_object* v___x_4166_; 
v_sz_4164_ = lean_array_size(v_x_4149_);
v___x_4165_ = ((size_t)0ULL);
lean_inc_ref(v_post_4145_);
lean_inc_ref(v_pre_4144_);
v___x_4166_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__2(v_pre_4144_, v_post_4145_, v_usedLetOnly_4146_, v_skipConstInApp_4147_, v_skipInstances_4143_, v_sz_4164_, v___x_4165_, v_x_4149_, v___y_4159_, v___y_4160_, v___y_4161_, v___y_4162_, v___y_4163_);
if (lean_obj_tag(v___x_4166_) == 0)
{
lean_object* v_a_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; 
v_a_4167_ = lean_ctor_get(v___x_4166_, 0);
lean_inc(v_a_4167_);
lean_dec_ref_known(v___x_4166_, 1);
v___x_4168_ = l_Lean_mkAppN(v_f_4158_, v_a_4167_);
lean_dec(v_a_4167_);
v___x_4169_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4144_, v_post_4145_, v_usedLetOnly_4146_, v_skipConstInApp_4147_, v_skipInstances_4143_, v___x_4168_, v___y_4159_, v___y_4160_, v___y_4161_, v___y_4162_, v___y_4163_);
return v___x_4169_;
}
else
{
lean_object* v_a_4170_; lean_object* v___x_4172_; uint8_t v_isShared_4173_; uint8_t v_isSharedCheck_4177_; 
lean_dec_ref(v_f_4158_);
lean_dec_ref(v_post_4145_);
lean_dec_ref(v_pre_4144_);
v_a_4170_ = lean_ctor_get(v___x_4166_, 0);
v_isSharedCheck_4177_ = !lean_is_exclusive(v___x_4166_);
if (v_isSharedCheck_4177_ == 0)
{
v___x_4172_ = v___x_4166_;
v_isShared_4173_ = v_isSharedCheck_4177_;
goto v_resetjp_4171_;
}
else
{
lean_inc(v_a_4170_);
lean_dec(v___x_4166_);
v___x_4172_ = lean_box(0);
v_isShared_4173_ = v_isSharedCheck_4177_;
goto v_resetjp_4171_;
}
v_resetjp_4171_:
{
lean_object* v___x_4175_; 
if (v_isShared_4173_ == 0)
{
v___x_4175_ = v___x_4172_;
goto v_reusejp_4174_;
}
else
{
lean_object* v_reuseFailAlloc_4176_; 
v_reuseFailAlloc_4176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4176_, 0, v_a_4170_);
v___x_4175_ = v_reuseFailAlloc_4176_;
goto v_reusejp_4174_;
}
v_reusejp_4174_:
{
return v___x_4175_;
}
}
}
}
else
{
lean_object* v___x_4178_; lean_object* v___x_4179_; 
v___x_4178_ = lean_array_get_size(v_x_4149_);
lean_inc_ref(v_f_4158_);
v___x_4179_ = l_Lean_Meta_getFunInfoNArgs(v_f_4158_, v___x_4178_, v___y_4160_, v___y_4161_, v___y_4162_, v___y_4163_);
if (lean_obj_tag(v___x_4179_) == 0)
{
lean_object* v_a_4180_; lean_object* v_paramInfo_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; 
v_a_4180_ = lean_ctor_get(v___x_4179_, 0);
lean_inc(v_a_4180_);
lean_dec_ref_known(v___x_4179_, 1);
v_paramInfo_4181_ = lean_ctor_get(v_a_4180_, 0);
lean_inc_ref(v_paramInfo_4181_);
lean_dec(v_a_4180_);
v___x_4182_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_4145_);
lean_inc_ref(v_pre_4144_);
v___x_4183_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg(v___x_4178_, v_paramInfo_4181_, v_pre_4144_, v_post_4145_, v_usedLetOnly_4146_, v_skipConstInApp_4147_, v_skipInstances_4143_, v___x_4182_, v_x_4149_, v___y_4159_, v___y_4160_, v___y_4161_, v___y_4162_, v___y_4163_);
lean_dec_ref(v_paramInfo_4181_);
if (lean_obj_tag(v___x_4183_) == 0)
{
lean_object* v_a_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; 
v_a_4184_ = lean_ctor_get(v___x_4183_, 0);
lean_inc(v_a_4184_);
lean_dec_ref_known(v___x_4183_, 1);
v___x_4185_ = l_Lean_mkAppN(v_f_4158_, v_a_4184_);
lean_dec(v_a_4184_);
v___x_4186_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4144_, v_post_4145_, v_usedLetOnly_4146_, v_skipConstInApp_4147_, v_skipInstances_4143_, v___x_4185_, v___y_4159_, v___y_4160_, v___y_4161_, v___y_4162_, v___y_4163_);
return v___x_4186_;
}
else
{
lean_object* v_a_4187_; lean_object* v___x_4189_; uint8_t v_isShared_4190_; uint8_t v_isSharedCheck_4194_; 
lean_dec_ref(v_f_4158_);
lean_dec_ref(v_post_4145_);
lean_dec_ref(v_pre_4144_);
v_a_4187_ = lean_ctor_get(v___x_4183_, 0);
v_isSharedCheck_4194_ = !lean_is_exclusive(v___x_4183_);
if (v_isSharedCheck_4194_ == 0)
{
v___x_4189_ = v___x_4183_;
v_isShared_4190_ = v_isSharedCheck_4194_;
goto v_resetjp_4188_;
}
else
{
lean_inc(v_a_4187_);
lean_dec(v___x_4183_);
v___x_4189_ = lean_box(0);
v_isShared_4190_ = v_isSharedCheck_4194_;
goto v_resetjp_4188_;
}
v_resetjp_4188_:
{
lean_object* v___x_4192_; 
if (v_isShared_4190_ == 0)
{
v___x_4192_ = v___x_4189_;
goto v_reusejp_4191_;
}
else
{
lean_object* v_reuseFailAlloc_4193_; 
v_reuseFailAlloc_4193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4193_, 0, v_a_4187_);
v___x_4192_ = v_reuseFailAlloc_4193_;
goto v_reusejp_4191_;
}
v_reusejp_4191_:
{
return v___x_4192_;
}
}
}
}
else
{
lean_object* v_a_4195_; lean_object* v___x_4197_; uint8_t v_isShared_4198_; uint8_t v_isSharedCheck_4202_; 
lean_dec_ref(v_f_4158_);
lean_dec_ref(v_x_4149_);
lean_dec_ref(v_post_4145_);
lean_dec_ref(v_pre_4144_);
v_a_4195_ = lean_ctor_get(v___x_4179_, 0);
v_isSharedCheck_4202_ = !lean_is_exclusive(v___x_4179_);
if (v_isSharedCheck_4202_ == 0)
{
v___x_4197_ = v___x_4179_;
v_isShared_4198_ = v_isSharedCheck_4202_;
goto v_resetjp_4196_;
}
else
{
lean_inc(v_a_4195_);
lean_dec(v___x_4179_);
v___x_4197_ = lean_box(0);
v_isShared_4198_ = v_isSharedCheck_4202_;
goto v_resetjp_4196_;
}
v_resetjp_4196_:
{
lean_object* v___x_4200_; 
if (v_isShared_4198_ == 0)
{
v___x_4200_ = v___x_4197_;
goto v_reusejp_4199_;
}
else
{
lean_object* v_reuseFailAlloc_4201_; 
v_reuseFailAlloc_4201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4201_, 0, v_a_4195_);
v___x_4200_ = v_reuseFailAlloc_4201_;
goto v_reusejp_4199_;
}
v_reusejp_4199_:
{
return v___x_4200_;
}
}
}
}
}
v___jp_4203_:
{
lean_object* v___x_4204_; 
lean_inc_ref(v_post_4145_);
lean_inc_ref(v_pre_4144_);
v___x_4204_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4144_, v_post_4145_, v_usedLetOnly_4146_, v_skipConstInApp_4147_, v_skipInstances_4143_, v_x_4148_, v___y_4151_, v___y_4152_, v___y_4153_, v___y_4154_, v___y_4155_);
if (lean_obj_tag(v___x_4204_) == 0)
{
lean_object* v_a_4205_; 
v_a_4205_ = lean_ctor_get(v___x_4204_, 0);
lean_inc(v_a_4205_);
lean_dec_ref_known(v___x_4204_, 1);
v_f_4158_ = v_a_4205_;
v___y_4159_ = v___y_4151_;
v___y_4160_ = v___y_4152_;
v___y_4161_ = v___y_4153_;
v___y_4162_ = v___y_4154_;
v___y_4163_ = v___y_4155_;
goto v___jp_4157_;
}
else
{
lean_dec_ref(v_x_4149_);
lean_dec_ref(v_post_4145_);
lean_dec_ref(v_pre_4144_);
return v___x_4204_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1(lean_object* v___x_4213_, lean_object* v_pre_4214_, lean_object* v_e_4215_, lean_object* v_post_4216_, uint8_t v_usedLetOnly_4217_, uint8_t v_skipConstInApp_4218_, uint8_t v_skipInstances_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_){
_start:
{
lean_object* v___x_4226_; 
v___x_4226_ = l_Lean_Core_checkSystem(v___x_4213_, v___y_4223_, v___y_4224_);
if (lean_obj_tag(v___x_4226_) == 0)
{
lean_object* v___x_4227_; 
lean_dec_ref_known(v___x_4226_, 1);
lean_inc_ref(v_pre_4214_);
lean_inc(v___y_4224_);
lean_inc_ref(v___y_4223_);
lean_inc(v___y_4222_);
lean_inc_ref(v___y_4221_);
lean_inc_ref(v_e_4215_);
v___x_4227_ = lean_apply_6(v_pre_4214_, v_e_4215_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_, lean_box(0));
if (lean_obj_tag(v___x_4227_) == 0)
{
lean_object* v_a_4228_; lean_object* v___x_4230_; uint8_t v_isShared_4231_; uint8_t v_isSharedCheck_4276_; 
v_a_4228_ = lean_ctor_get(v___x_4227_, 0);
v_isSharedCheck_4276_ = !lean_is_exclusive(v___x_4227_);
if (v_isSharedCheck_4276_ == 0)
{
v___x_4230_ = v___x_4227_;
v_isShared_4231_ = v_isSharedCheck_4276_;
goto v_resetjp_4229_;
}
else
{
lean_inc(v_a_4228_);
lean_dec(v___x_4227_);
v___x_4230_ = lean_box(0);
v_isShared_4231_ = v_isSharedCheck_4276_;
goto v_resetjp_4229_;
}
v_resetjp_4229_:
{
lean_object* v___y_4233_; 
switch(lean_obj_tag(v_a_4228_))
{
case 0:
{
lean_object* v_e_4268_; lean_object* v___x_4270_; 
lean_dec_ref(v_post_4216_);
lean_dec_ref(v_e_4215_);
lean_dec_ref(v_pre_4214_);
v_e_4268_ = lean_ctor_get(v_a_4228_, 0);
lean_inc_ref(v_e_4268_);
lean_dec_ref_known(v_a_4228_, 1);
if (v_isShared_4231_ == 0)
{
lean_ctor_set(v___x_4230_, 0, v_e_4268_);
v___x_4270_ = v___x_4230_;
goto v_reusejp_4269_;
}
else
{
lean_object* v_reuseFailAlloc_4271_; 
v_reuseFailAlloc_4271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4271_, 0, v_e_4268_);
v___x_4270_ = v_reuseFailAlloc_4271_;
goto v_reusejp_4269_;
}
v_reusejp_4269_:
{
return v___x_4270_;
}
}
case 1:
{
lean_object* v_e_4272_; lean_object* v___x_4273_; 
lean_del_object(v___x_4230_);
lean_dec_ref(v_e_4215_);
v_e_4272_ = lean_ctor_get(v_a_4228_, 0);
lean_inc_ref(v_e_4272_);
lean_dec_ref_known(v_a_4228_, 1);
v___x_4273_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4214_, v_post_4216_, v_usedLetOnly_4217_, v_skipConstInApp_4218_, v_skipInstances_4219_, v_e_4272_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_);
return v___x_4273_;
}
default: 
{
lean_object* v_e_x3f_4274_; 
lean_del_object(v___x_4230_);
v_e_x3f_4274_ = lean_ctor_get(v_a_4228_, 0);
lean_inc(v_e_x3f_4274_);
lean_dec_ref_known(v_a_4228_, 1);
if (lean_obj_tag(v_e_x3f_4274_) == 0)
{
v___y_4233_ = v_e_4215_;
goto v___jp_4232_;
}
else
{
lean_object* v_val_4275_; 
lean_dec_ref(v_e_4215_);
v_val_4275_ = lean_ctor_get(v_e_x3f_4274_, 0);
lean_inc(v_val_4275_);
lean_dec_ref_known(v_e_x3f_4274_, 1);
v___y_4233_ = v_val_4275_;
goto v___jp_4232_;
}
}
}
v___jp_4232_:
{
switch(lean_obj_tag(v___y_4233_))
{
case 7:
{
lean_object* v___x_4234_; lean_object* v___x_4235_; 
v___x_4234_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_4235_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5(v_pre_4214_, v_post_4216_, v_usedLetOnly_4217_, v_skipConstInApp_4218_, v_skipInstances_4219_, v___x_4234_, v___y_4233_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_);
return v___x_4235_;
}
case 6:
{
lean_object* v___x_4236_; lean_object* v___x_4237_; 
v___x_4236_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_4237_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6(v_pre_4214_, v_post_4216_, v_usedLetOnly_4217_, v_skipConstInApp_4218_, v_skipInstances_4219_, v___x_4236_, v___y_4233_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_);
return v___x_4237_;
}
case 8:
{
lean_object* v___x_4238_; lean_object* v___x_4239_; 
v___x_4238_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_4239_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7(v_pre_4214_, v_post_4216_, v_usedLetOnly_4217_, v_skipConstInApp_4218_, v_skipInstances_4219_, v___x_4238_, v___y_4233_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_);
return v___x_4239_;
}
case 5:
{
lean_object* v_dummy_4240_; lean_object* v_nargs_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; 
v_dummy_4240_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_4241_ = l_Lean_Expr_getAppNumArgs(v___y_4233_);
lean_inc(v_nargs_4241_);
v___x_4242_ = lean_mk_array(v_nargs_4241_, v_dummy_4240_);
v___x_4243_ = lean_unsigned_to_nat(1u);
v___x_4244_ = lean_nat_sub(v_nargs_4241_, v___x_4243_);
lean_dec(v_nargs_4241_);
v___x_4245_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__8(v_skipInstances_4219_, v_pre_4214_, v_post_4216_, v_usedLetOnly_4217_, v_skipConstInApp_4218_, v___y_4233_, v___x_4242_, v___x_4244_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_);
return v___x_4245_;
}
case 10:
{
lean_object* v_data_4246_; lean_object* v_expr_4247_; lean_object* v___x_4248_; 
v_data_4246_ = lean_ctor_get(v___y_4233_, 0);
v_expr_4247_ = lean_ctor_get(v___y_4233_, 1);
lean_inc_ref(v_expr_4247_);
lean_inc_ref(v_post_4216_);
lean_inc_ref(v_pre_4214_);
v___x_4248_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4214_, v_post_4216_, v_usedLetOnly_4217_, v_skipConstInApp_4218_, v_skipInstances_4219_, v_expr_4247_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_);
if (lean_obj_tag(v___x_4248_) == 0)
{
lean_object* v_a_4249_; size_t v___x_4250_; size_t v___x_4251_; uint8_t v___x_4252_; 
v_a_4249_ = lean_ctor_get(v___x_4248_, 0);
lean_inc(v_a_4249_);
lean_dec_ref_known(v___x_4248_, 1);
v___x_4250_ = lean_ptr_addr(v_expr_4247_);
v___x_4251_ = lean_ptr_addr(v_a_4249_);
v___x_4252_ = lean_usize_dec_eq(v___x_4250_, v___x_4251_);
if (v___x_4252_ == 0)
{
lean_object* v___x_4253_; lean_object* v___x_4254_; 
lean_inc(v_data_4246_);
lean_dec_ref_known(v___y_4233_, 2);
v___x_4253_ = l_Lean_Expr_mdata___override(v_data_4246_, v_a_4249_);
v___x_4254_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4214_, v_post_4216_, v_usedLetOnly_4217_, v_skipConstInApp_4218_, v_skipInstances_4219_, v___x_4253_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_);
return v___x_4254_;
}
else
{
lean_object* v___x_4255_; 
lean_dec(v_a_4249_);
v___x_4255_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4214_, v_post_4216_, v_usedLetOnly_4217_, v_skipConstInApp_4218_, v_skipInstances_4219_, v___y_4233_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_);
return v___x_4255_;
}
}
else
{
lean_dec_ref_known(v___y_4233_, 2);
lean_dec_ref(v_post_4216_);
lean_dec_ref(v_pre_4214_);
return v___x_4248_;
}
}
case 11:
{
lean_object* v_typeName_4256_; lean_object* v_idx_4257_; lean_object* v_struct_4258_; lean_object* v___x_4259_; 
v_typeName_4256_ = lean_ctor_get(v___y_4233_, 0);
v_idx_4257_ = lean_ctor_get(v___y_4233_, 1);
v_struct_4258_ = lean_ctor_get(v___y_4233_, 2);
lean_inc_ref(v_struct_4258_);
lean_inc_ref(v_post_4216_);
lean_inc_ref(v_pre_4214_);
v___x_4259_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4214_, v_post_4216_, v_usedLetOnly_4217_, v_skipConstInApp_4218_, v_skipInstances_4219_, v_struct_4258_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_);
if (lean_obj_tag(v___x_4259_) == 0)
{
lean_object* v_a_4260_; size_t v___x_4261_; size_t v___x_4262_; uint8_t v___x_4263_; 
v_a_4260_ = lean_ctor_get(v___x_4259_, 0);
lean_inc(v_a_4260_);
lean_dec_ref_known(v___x_4259_, 1);
v___x_4261_ = lean_ptr_addr(v_struct_4258_);
v___x_4262_ = lean_ptr_addr(v_a_4260_);
v___x_4263_ = lean_usize_dec_eq(v___x_4261_, v___x_4262_);
if (v___x_4263_ == 0)
{
lean_object* v___x_4264_; lean_object* v___x_4265_; 
lean_inc(v_idx_4257_);
lean_inc(v_typeName_4256_);
lean_dec_ref_known(v___y_4233_, 3);
v___x_4264_ = l_Lean_Expr_proj___override(v_typeName_4256_, v_idx_4257_, v_a_4260_);
v___x_4265_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4214_, v_post_4216_, v_usedLetOnly_4217_, v_skipConstInApp_4218_, v_skipInstances_4219_, v___x_4264_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_);
return v___x_4265_;
}
else
{
lean_object* v___x_4266_; 
lean_dec(v_a_4260_);
v___x_4266_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4214_, v_post_4216_, v_usedLetOnly_4217_, v_skipConstInApp_4218_, v_skipInstances_4219_, v___y_4233_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_);
return v___x_4266_;
}
}
else
{
lean_dec_ref_known(v___y_4233_, 3);
lean_dec_ref(v_post_4216_);
lean_dec_ref(v_pre_4214_);
return v___x_4259_;
}
}
default: 
{
lean_object* v___x_4267_; 
v___x_4267_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4214_, v_post_4216_, v_usedLetOnly_4217_, v_skipConstInApp_4218_, v_skipInstances_4219_, v___y_4233_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_);
return v___x_4267_;
}
}
}
}
}
else
{
lean_object* v_a_4277_; lean_object* v___x_4279_; uint8_t v_isShared_4280_; uint8_t v_isSharedCheck_4284_; 
lean_dec_ref(v_post_4216_);
lean_dec_ref(v_e_4215_);
lean_dec_ref(v_pre_4214_);
v_a_4277_ = lean_ctor_get(v___x_4227_, 0);
v_isSharedCheck_4284_ = !lean_is_exclusive(v___x_4227_);
if (v_isSharedCheck_4284_ == 0)
{
v___x_4279_ = v___x_4227_;
v_isShared_4280_ = v_isSharedCheck_4284_;
goto v_resetjp_4278_;
}
else
{
lean_inc(v_a_4277_);
lean_dec(v___x_4227_);
v___x_4279_ = lean_box(0);
v_isShared_4280_ = v_isSharedCheck_4284_;
goto v_resetjp_4278_;
}
v_resetjp_4278_:
{
lean_object* v___x_4282_; 
if (v_isShared_4280_ == 0)
{
v___x_4282_ = v___x_4279_;
goto v_reusejp_4281_;
}
else
{
lean_object* v_reuseFailAlloc_4283_; 
v_reuseFailAlloc_4283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4283_, 0, v_a_4277_);
v___x_4282_ = v_reuseFailAlloc_4283_;
goto v_reusejp_4281_;
}
v_reusejp_4281_:
{
return v___x_4282_;
}
}
}
}
else
{
lean_object* v_a_4285_; lean_object* v___x_4287_; uint8_t v_isShared_4288_; uint8_t v_isSharedCheck_4292_; 
lean_dec_ref(v_post_4216_);
lean_dec_ref(v_e_4215_);
lean_dec_ref(v_pre_4214_);
v_a_4285_ = lean_ctor_get(v___x_4226_, 0);
v_isSharedCheck_4292_ = !lean_is_exclusive(v___x_4226_);
if (v_isSharedCheck_4292_ == 0)
{
v___x_4287_ = v___x_4226_;
v_isShared_4288_ = v_isSharedCheck_4292_;
goto v_resetjp_4286_;
}
else
{
lean_inc(v_a_4285_);
lean_dec(v___x_4226_);
v___x_4287_ = lean_box(0);
v_isShared_4288_ = v_isSharedCheck_4292_;
goto v_resetjp_4286_;
}
v_resetjp_4286_:
{
lean_object* v___x_4290_; 
if (v_isShared_4288_ == 0)
{
v___x_4290_ = v___x_4287_;
goto v_reusejp_4289_;
}
else
{
lean_object* v_reuseFailAlloc_4291_; 
v_reuseFailAlloc_4291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4291_, 0, v_a_4285_);
v___x_4290_ = v_reuseFailAlloc_4291_;
goto v_reusejp_4289_;
}
v_reusejp_4289_:
{
return v___x_4290_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1___boxed(lean_object* v___x_4293_, lean_object* v_pre_4294_, lean_object* v_e_4295_, lean_object* v_post_4296_, lean_object* v_usedLetOnly_4297_, lean_object* v_skipConstInApp_4298_, lean_object* v_skipInstances_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_, lean_object* v___y_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_){
_start:
{
uint8_t v_usedLetOnly_boxed_4306_; uint8_t v_skipConstInApp_boxed_4307_; uint8_t v_skipInstances_boxed_4308_; lean_object* v_res_4309_; 
v_usedLetOnly_boxed_4306_ = lean_unbox(v_usedLetOnly_4297_);
v_skipConstInApp_boxed_4307_ = lean_unbox(v_skipConstInApp_4298_);
v_skipInstances_boxed_4308_ = lean_unbox(v_skipInstances_4299_);
v_res_4309_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1(v___x_4293_, v_pre_4294_, v_e_4295_, v_post_4296_, v_usedLetOnly_boxed_4306_, v_skipConstInApp_boxed_4307_, v_skipInstances_boxed_4308_, v___y_4300_, v___y_4301_, v___y_4302_, v___y_4303_, v___y_4304_);
lean_dec(v___y_4304_);
lean_dec_ref(v___y_4303_);
lean_dec(v___y_4302_);
lean_dec_ref(v___y_4301_);
lean_dec(v___y_4300_);
return v_res_4309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(lean_object* v_pre_4310_, lean_object* v_post_4311_, uint8_t v_usedLetOnly_4312_, uint8_t v_skipConstInApp_4313_, uint8_t v_skipInstances_4314_, lean_object* v_e_4315_, lean_object* v_a_4316_, lean_object* v___y_4317_, lean_object* v___y_4318_, lean_object* v___y_4319_, lean_object* v___y_4320_){
_start:
{
lean_object* v___x_4322_; lean_object* v___x_4323_; 
lean_inc(v_a_4316_);
v___x_4322_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_4322_, 0, lean_box(0));
lean_closure_set(v___x_4322_, 1, lean_box(0));
lean_closure_set(v___x_4322_, 2, v_a_4316_);
v___x_4323_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0(lean_box(0), v___x_4322_, v___y_4317_, v___y_4318_, v___y_4319_, v___y_4320_);
if (lean_obj_tag(v___x_4323_) == 0)
{
lean_object* v_a_4324_; lean_object* v___x_4326_; uint8_t v_isShared_4327_; uint8_t v_isSharedCheck_4358_; 
v_a_4324_ = lean_ctor_get(v___x_4323_, 0);
v_isSharedCheck_4358_ = !lean_is_exclusive(v___x_4323_);
if (v_isSharedCheck_4358_ == 0)
{
v___x_4326_ = v___x_4323_;
v_isShared_4327_ = v_isSharedCheck_4358_;
goto v_resetjp_4325_;
}
else
{
lean_inc(v_a_4324_);
lean_dec(v___x_4323_);
v___x_4326_ = lean_box(0);
v_isShared_4327_ = v_isSharedCheck_4358_;
goto v_resetjp_4325_;
}
v_resetjp_4325_:
{
lean_object* v___x_4328_; 
v___x_4328_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg(v_a_4324_, v_e_4315_);
lean_dec(v_a_4324_);
if (lean_obj_tag(v___x_4328_) == 0)
{
lean_object* v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; lean_object* v___f_4333_; lean_object* v___x_4334_; 
lean_del_object(v___x_4326_);
v___x_4329_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__19___closed__0));
v___x_4330_ = lean_box(v_usedLetOnly_4312_);
v___x_4331_ = lean_box(v_skipConstInApp_4313_);
v___x_4332_ = lean_box(v_skipInstances_4314_);
lean_inc_ref(v_e_4315_);
v___f_4333_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1___boxed), 13, 7);
lean_closure_set(v___f_4333_, 0, v___x_4329_);
lean_closure_set(v___f_4333_, 1, v_pre_4310_);
lean_closure_set(v___f_4333_, 2, v_e_4315_);
lean_closure_set(v___f_4333_, 3, v_post_4311_);
lean_closure_set(v___f_4333_, 4, v___x_4330_);
lean_closure_set(v___f_4333_, 5, v___x_4331_);
lean_closure_set(v___f_4333_, 6, v___x_4332_);
v___x_4334_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg(v___f_4333_, v_a_4316_, v___y_4317_, v___y_4318_, v___y_4319_, v___y_4320_);
if (lean_obj_tag(v___x_4334_) == 0)
{
lean_object* v_a_4335_; lean_object* v___f_4336_; lean_object* v___x_4337_; 
v_a_4335_ = lean_ctor_get(v___x_4334_, 0);
lean_inc_n(v_a_4335_, 2);
lean_dec_ref_known(v___x_4334_, 1);
lean_inc(v_a_4316_);
v___f_4336_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_4336_, 0, v_a_4316_);
lean_closure_set(v___f_4336_, 1, v_e_4315_);
lean_closure_set(v___f_4336_, 2, v_a_4335_);
v___x_4337_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0(lean_box(0), v___f_4336_, v___y_4317_, v___y_4318_, v___y_4319_, v___y_4320_);
if (lean_obj_tag(v___x_4337_) == 0)
{
lean_object* v___x_4339_; uint8_t v_isShared_4340_; uint8_t v_isSharedCheck_4344_; 
v_isSharedCheck_4344_ = !lean_is_exclusive(v___x_4337_);
if (v_isSharedCheck_4344_ == 0)
{
lean_object* v_unused_4345_; 
v_unused_4345_ = lean_ctor_get(v___x_4337_, 0);
lean_dec(v_unused_4345_);
v___x_4339_ = v___x_4337_;
v_isShared_4340_ = v_isSharedCheck_4344_;
goto v_resetjp_4338_;
}
else
{
lean_dec(v___x_4337_);
v___x_4339_ = lean_box(0);
v_isShared_4340_ = v_isSharedCheck_4344_;
goto v_resetjp_4338_;
}
v_resetjp_4338_:
{
lean_object* v___x_4342_; 
if (v_isShared_4340_ == 0)
{
lean_ctor_set(v___x_4339_, 0, v_a_4335_);
v___x_4342_ = v___x_4339_;
goto v_reusejp_4341_;
}
else
{
lean_object* v_reuseFailAlloc_4343_; 
v_reuseFailAlloc_4343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4343_, 0, v_a_4335_);
v___x_4342_ = v_reuseFailAlloc_4343_;
goto v_reusejp_4341_;
}
v_reusejp_4341_:
{
return v___x_4342_;
}
}
}
else
{
lean_object* v_a_4346_; lean_object* v___x_4348_; uint8_t v_isShared_4349_; uint8_t v_isSharedCheck_4353_; 
lean_dec(v_a_4335_);
v_a_4346_ = lean_ctor_get(v___x_4337_, 0);
v_isSharedCheck_4353_ = !lean_is_exclusive(v___x_4337_);
if (v_isSharedCheck_4353_ == 0)
{
v___x_4348_ = v___x_4337_;
v_isShared_4349_ = v_isSharedCheck_4353_;
goto v_resetjp_4347_;
}
else
{
lean_inc(v_a_4346_);
lean_dec(v___x_4337_);
v___x_4348_ = lean_box(0);
v_isShared_4349_ = v_isSharedCheck_4353_;
goto v_resetjp_4347_;
}
v_resetjp_4347_:
{
lean_object* v___x_4351_; 
if (v_isShared_4349_ == 0)
{
v___x_4351_ = v___x_4348_;
goto v_reusejp_4350_;
}
else
{
lean_object* v_reuseFailAlloc_4352_; 
v_reuseFailAlloc_4352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4352_, 0, v_a_4346_);
v___x_4351_ = v_reuseFailAlloc_4352_;
goto v_reusejp_4350_;
}
v_reusejp_4350_:
{
return v___x_4351_;
}
}
}
}
else
{
lean_dec_ref(v_e_4315_);
return v___x_4334_;
}
}
else
{
lean_object* v_val_4354_; lean_object* v___x_4356_; 
lean_dec_ref(v_e_4315_);
lean_dec_ref(v_post_4311_);
lean_dec_ref(v_pre_4310_);
v_val_4354_ = lean_ctor_get(v___x_4328_, 0);
lean_inc(v_val_4354_);
lean_dec_ref_known(v___x_4328_, 1);
if (v_isShared_4327_ == 0)
{
lean_ctor_set(v___x_4326_, 0, v_val_4354_);
v___x_4356_ = v___x_4326_;
goto v_reusejp_4355_;
}
else
{
lean_object* v_reuseFailAlloc_4357_; 
v_reuseFailAlloc_4357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4357_, 0, v_val_4354_);
v___x_4356_ = v_reuseFailAlloc_4357_;
goto v_reusejp_4355_;
}
v_reusejp_4355_:
{
return v___x_4356_;
}
}
}
}
else
{
lean_object* v_a_4359_; lean_object* v___x_4361_; uint8_t v_isShared_4362_; uint8_t v_isSharedCheck_4366_; 
lean_dec_ref(v_e_4315_);
lean_dec_ref(v_post_4311_);
lean_dec_ref(v_pre_4310_);
v_a_4359_ = lean_ctor_get(v___x_4323_, 0);
v_isSharedCheck_4366_ = !lean_is_exclusive(v___x_4323_);
if (v_isSharedCheck_4366_ == 0)
{
v___x_4361_ = v___x_4323_;
v_isShared_4362_ = v_isSharedCheck_4366_;
goto v_resetjp_4360_;
}
else
{
lean_inc(v_a_4359_);
lean_dec(v___x_4323_);
v___x_4361_ = lean_box(0);
v_isShared_4362_ = v_isSharedCheck_4366_;
goto v_resetjp_4360_;
}
v_resetjp_4360_:
{
lean_object* v___x_4364_; 
if (v_isShared_4362_ == 0)
{
v___x_4364_ = v___x_4361_;
goto v_reusejp_4363_;
}
else
{
lean_object* v_reuseFailAlloc_4365_; 
v_reuseFailAlloc_4365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4365_, 0, v_a_4359_);
v___x_4364_ = v_reuseFailAlloc_4365_;
goto v_reusejp_4363_;
}
v_reusejp_4363_:
{
return v___x_4364_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___lam__0___boxed(lean_object* v_fvars_4367_, lean_object* v_pre_4368_, lean_object* v_post_4369_, lean_object* v_usedLetOnly_4370_, lean_object* v_skipConstInApp_4371_, lean_object* v_skipInstances_4372_, lean_object* v_body_4373_, lean_object* v_x_4374_, lean_object* v___y_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_){
_start:
{
uint8_t v_usedLetOnly_boxed_4381_; uint8_t v_skipConstInApp_boxed_4382_; uint8_t v_skipInstances_boxed_4383_; lean_object* v_res_4384_; 
v_usedLetOnly_boxed_4381_ = lean_unbox(v_usedLetOnly_4370_);
v_skipConstInApp_boxed_4382_ = lean_unbox(v_skipConstInApp_4371_);
v_skipInstances_boxed_4383_ = lean_unbox(v_skipInstances_4372_);
v_res_4384_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___lam__0(v_fvars_4367_, v_pre_4368_, v_post_4369_, v_usedLetOnly_boxed_4381_, v_skipConstInApp_boxed_4382_, v_skipInstances_boxed_4383_, v_body_4373_, v_x_4374_, v___y_4375_, v___y_4376_, v___y_4377_, v___y_4378_, v___y_4379_);
lean_dec(v___y_4379_);
lean_dec_ref(v___y_4378_);
lean_dec(v___y_4377_);
lean_dec_ref(v___y_4376_);
lean_dec(v___y_4375_);
return v_res_4384_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5(lean_object* v_pre_4385_, lean_object* v_post_4386_, uint8_t v_usedLetOnly_4387_, uint8_t v_skipConstInApp_4388_, uint8_t v_skipInstances_4389_, lean_object* v_fvars_4390_, lean_object* v_e_4391_, lean_object* v_a_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_){
_start:
{
if (lean_obj_tag(v_e_4391_) == 7)
{
lean_object* v_binderName_4398_; lean_object* v_binderType_4399_; lean_object* v_body_4400_; uint8_t v_binderInfo_4401_; lean_object* v___x_4402_; lean_object* v___x_4403_; 
v_binderName_4398_ = lean_ctor_get(v_e_4391_, 0);
lean_inc(v_binderName_4398_);
v_binderType_4399_ = lean_ctor_get(v_e_4391_, 1);
lean_inc_ref(v_binderType_4399_);
v_body_4400_ = lean_ctor_get(v_e_4391_, 2);
lean_inc_ref(v_body_4400_);
v_binderInfo_4401_ = lean_ctor_get_uint8(v_e_4391_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_4391_, 3);
v___x_4402_ = lean_expr_instantiate_rev(v_binderType_4399_, v_fvars_4390_);
lean_dec_ref(v_binderType_4399_);
lean_inc_ref(v_post_4386_);
lean_inc_ref(v_pre_4385_);
v___x_4403_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4385_, v_post_4386_, v_usedLetOnly_4387_, v_skipConstInApp_4388_, v_skipInstances_4389_, v___x_4402_, v_a_4392_, v___y_4393_, v___y_4394_, v___y_4395_, v___y_4396_);
if (lean_obj_tag(v___x_4403_) == 0)
{
lean_object* v_a_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; lean_object* v___x_4407_; lean_object* v___f_4408_; uint8_t v___x_4409_; lean_object* v___x_4410_; 
v_a_4404_ = lean_ctor_get(v___x_4403_, 0);
lean_inc(v_a_4404_);
lean_dec_ref_known(v___x_4403_, 1);
v___x_4405_ = lean_box(v_usedLetOnly_4387_);
v___x_4406_ = lean_box(v_skipConstInApp_4388_);
v___x_4407_ = lean_box(v_skipInstances_4389_);
v___f_4408_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___lam__0___boxed), 14, 7);
lean_closure_set(v___f_4408_, 0, v_fvars_4390_);
lean_closure_set(v___f_4408_, 1, v_pre_4385_);
lean_closure_set(v___f_4408_, 2, v_post_4386_);
lean_closure_set(v___f_4408_, 3, v___x_4405_);
lean_closure_set(v___f_4408_, 4, v___x_4406_);
lean_closure_set(v___f_4408_, 5, v___x_4407_);
lean_closure_set(v___f_4408_, 6, v_body_4400_);
v___x_4409_ = 0;
v___x_4410_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_binderName_4398_, v_binderInfo_4401_, v_a_4404_, v___f_4408_, v___x_4409_, v_a_4392_, v___y_4393_, v___y_4394_, v___y_4395_, v___y_4396_);
return v___x_4410_;
}
else
{
lean_dec_ref(v_body_4400_);
lean_dec(v_binderName_4398_);
lean_dec_ref(v_fvars_4390_);
lean_dec_ref(v_post_4386_);
lean_dec_ref(v_pre_4385_);
return v___x_4403_;
}
}
else
{
lean_object* v___x_4411_; lean_object* v___x_4412_; 
v___x_4411_ = lean_expr_instantiate_rev(v_e_4391_, v_fvars_4390_);
lean_dec_ref(v_e_4391_);
lean_inc_ref(v_post_4386_);
lean_inc_ref(v_pre_4385_);
v___x_4412_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4385_, v_post_4386_, v_usedLetOnly_4387_, v_skipConstInApp_4388_, v_skipInstances_4389_, v___x_4411_, v_a_4392_, v___y_4393_, v___y_4394_, v___y_4395_, v___y_4396_);
if (lean_obj_tag(v___x_4412_) == 0)
{
lean_object* v_a_4413_; uint8_t v___x_4414_; uint8_t v___x_4415_; uint8_t v___x_4416_; lean_object* v___x_4417_; 
v_a_4413_ = lean_ctor_get(v___x_4412_, 0);
lean_inc(v_a_4413_);
lean_dec_ref_known(v___x_4412_, 1);
v___x_4414_ = 0;
v___x_4415_ = 1;
v___x_4416_ = 1;
v___x_4417_ = l_Lean_Meta_mkForallFVars(v_fvars_4390_, v_a_4413_, v___x_4414_, v_usedLetOnly_4387_, v___x_4415_, v___x_4416_, v___y_4393_, v___y_4394_, v___y_4395_, v___y_4396_);
lean_dec_ref(v_fvars_4390_);
if (lean_obj_tag(v___x_4417_) == 0)
{
lean_object* v_a_4418_; lean_object* v___x_4419_; 
v_a_4418_ = lean_ctor_get(v___x_4417_, 0);
lean_inc(v_a_4418_);
lean_dec_ref_known(v___x_4417_, 1);
v___x_4419_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4385_, v_post_4386_, v_usedLetOnly_4387_, v_skipConstInApp_4388_, v_skipInstances_4389_, v_a_4418_, v_a_4392_, v___y_4393_, v___y_4394_, v___y_4395_, v___y_4396_);
return v___x_4419_;
}
else
{
lean_dec_ref(v_post_4386_);
lean_dec_ref(v_pre_4385_);
return v___x_4417_;
}
}
else
{
lean_dec_ref(v_fvars_4390_);
lean_dec_ref(v_post_4386_);
lean_dec_ref(v_pre_4385_);
return v___x_4412_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___lam__0(lean_object* v_fvars_4420_, lean_object* v_pre_4421_, lean_object* v_post_4422_, uint8_t v_usedLetOnly_4423_, uint8_t v_skipConstInApp_4424_, uint8_t v_skipInstances_4425_, lean_object* v_body_4426_, lean_object* v_x_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_){
_start:
{
lean_object* v___x_4434_; lean_object* v___x_4435_; 
v___x_4434_ = lean_array_push(v_fvars_4420_, v_x_4427_);
v___x_4435_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5(v_pre_4421_, v_post_4422_, v_usedLetOnly_4423_, v_skipConstInApp_4424_, v_skipInstances_4425_, v___x_4434_, v_body_4426_, v___y_4428_, v___y_4429_, v___y_4430_, v___y_4431_, v___y_4432_);
return v___x_4435_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3___boxed(lean_object* v_pre_4436_, lean_object* v_post_4437_, lean_object* v_usedLetOnly_4438_, lean_object* v_skipConstInApp_4439_, lean_object* v_skipInstances_4440_, lean_object* v_e_4441_, lean_object* v_a_4442_, lean_object* v___y_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_){
_start:
{
uint8_t v_usedLetOnly_boxed_4448_; uint8_t v_skipConstInApp_boxed_4449_; uint8_t v_skipInstances_boxed_4450_; lean_object* v_res_4451_; 
v_usedLetOnly_boxed_4448_ = lean_unbox(v_usedLetOnly_4438_);
v_skipConstInApp_boxed_4449_ = lean_unbox(v_skipConstInApp_4439_);
v_skipInstances_boxed_4450_ = lean_unbox(v_skipInstances_4440_);
v_res_4451_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4436_, v_post_4437_, v_usedLetOnly_boxed_4448_, v_skipConstInApp_boxed_4449_, v_skipInstances_boxed_4450_, v_e_4441_, v_a_4442_, v___y_4443_, v___y_4444_, v___y_4445_, v___y_4446_);
lean_dec(v___y_4446_);
lean_dec_ref(v___y_4445_);
lean_dec(v___y_4444_);
lean_dec_ref(v___y_4443_);
lean_dec(v_a_4442_);
return v_res_4451_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__2___boxed(lean_object* v_pre_4452_, lean_object* v_post_4453_, lean_object* v_usedLetOnly_4454_, lean_object* v_skipConstInApp_4455_, lean_object* v_skipInstances_4456_, lean_object* v_sz_4457_, lean_object* v_i_4458_, lean_object* v_bs_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_, lean_object* v___y_4463_, lean_object* v___y_4464_, lean_object* v___y_4465_){
_start:
{
uint8_t v_usedLetOnly_boxed_4466_; uint8_t v_skipConstInApp_boxed_4467_; uint8_t v_skipInstances_boxed_4468_; size_t v_sz_boxed_4469_; size_t v_i_boxed_4470_; lean_object* v_res_4471_; 
v_usedLetOnly_boxed_4466_ = lean_unbox(v_usedLetOnly_4454_);
v_skipConstInApp_boxed_4467_ = lean_unbox(v_skipConstInApp_4455_);
v_skipInstances_boxed_4468_ = lean_unbox(v_skipInstances_4456_);
v_sz_boxed_4469_ = lean_unbox_usize(v_sz_4457_);
lean_dec(v_sz_4457_);
v_i_boxed_4470_ = lean_unbox_usize(v_i_4458_);
lean_dec(v_i_4458_);
v_res_4471_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__2(v_pre_4452_, v_post_4453_, v_usedLetOnly_boxed_4466_, v_skipConstInApp_boxed_4467_, v_skipInstances_boxed_4468_, v_sz_boxed_4469_, v_i_boxed_4470_, v_bs_4459_, v___y_4460_, v___y_4461_, v___y_4462_, v___y_4463_, v___y_4464_);
lean_dec(v___y_4464_);
lean_dec_ref(v___y_4463_);
lean_dec(v___y_4462_);
lean_dec_ref(v___y_4461_);
lean_dec(v___y_4460_);
return v_res_4471_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___boxed(lean_object* v_pre_4472_, lean_object* v_post_4473_, lean_object* v_usedLetOnly_4474_, lean_object* v_skipConstInApp_4475_, lean_object* v_skipInstances_4476_, lean_object* v_e_4477_, lean_object* v_a_4478_, lean_object* v___y_4479_, lean_object* v___y_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_, lean_object* v___y_4483_){
_start:
{
uint8_t v_usedLetOnly_boxed_4484_; uint8_t v_skipConstInApp_boxed_4485_; uint8_t v_skipInstances_boxed_4486_; lean_object* v_res_4487_; 
v_usedLetOnly_boxed_4484_ = lean_unbox(v_usedLetOnly_4474_);
v_skipConstInApp_boxed_4485_ = lean_unbox(v_skipConstInApp_4475_);
v_skipInstances_boxed_4486_ = lean_unbox(v_skipInstances_4476_);
v_res_4487_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4472_, v_post_4473_, v_usedLetOnly_boxed_4484_, v_skipConstInApp_boxed_4485_, v_skipInstances_boxed_4486_, v_e_4477_, v_a_4478_, v___y_4479_, v___y_4480_, v___y_4481_, v___y_4482_);
lean_dec(v___y_4482_);
lean_dec_ref(v___y_4481_);
lean_dec(v___y_4480_);
lean_dec_ref(v___y_4479_);
lean_dec(v_a_4478_);
return v_res_4487_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___boxed(lean_object* v_pre_4488_, lean_object* v_post_4489_, lean_object* v_usedLetOnly_4490_, lean_object* v_skipConstInApp_4491_, lean_object* v_skipInstances_4492_, lean_object* v_fvars_4493_, lean_object* v_e_4494_, lean_object* v_a_4495_, lean_object* v___y_4496_, lean_object* v___y_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_, lean_object* v___y_4500_){
_start:
{
uint8_t v_usedLetOnly_boxed_4501_; uint8_t v_skipConstInApp_boxed_4502_; uint8_t v_skipInstances_boxed_4503_; lean_object* v_res_4504_; 
v_usedLetOnly_boxed_4501_ = lean_unbox(v_usedLetOnly_4490_);
v_skipConstInApp_boxed_4502_ = lean_unbox(v_skipConstInApp_4491_);
v_skipInstances_boxed_4503_ = lean_unbox(v_skipInstances_4492_);
v_res_4504_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5(v_pre_4488_, v_post_4489_, v_usedLetOnly_boxed_4501_, v_skipConstInApp_boxed_4502_, v_skipInstances_boxed_4503_, v_fvars_4493_, v_e_4494_, v_a_4495_, v___y_4496_, v___y_4497_, v___y_4498_, v___y_4499_);
lean_dec(v___y_4499_);
lean_dec_ref(v___y_4498_);
lean_dec(v___y_4497_);
lean_dec_ref(v___y_4496_);
lean_dec(v_a_4495_);
return v_res_4504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___boxed(lean_object* v_pre_4505_, lean_object* v_post_4506_, lean_object* v_usedLetOnly_4507_, lean_object* v_skipConstInApp_4508_, lean_object* v_skipInstances_4509_, lean_object* v_fvars_4510_, lean_object* v_e_4511_, lean_object* v_a_4512_, lean_object* v___y_4513_, lean_object* v___y_4514_, lean_object* v___y_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_){
_start:
{
uint8_t v_usedLetOnly_boxed_4518_; uint8_t v_skipConstInApp_boxed_4519_; uint8_t v_skipInstances_boxed_4520_; lean_object* v_res_4521_; 
v_usedLetOnly_boxed_4518_ = lean_unbox(v_usedLetOnly_4507_);
v_skipConstInApp_boxed_4519_ = lean_unbox(v_skipConstInApp_4508_);
v_skipInstances_boxed_4520_ = lean_unbox(v_skipInstances_4509_);
v_res_4521_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6(v_pre_4505_, v_post_4506_, v_usedLetOnly_boxed_4518_, v_skipConstInApp_boxed_4519_, v_skipInstances_boxed_4520_, v_fvars_4510_, v_e_4511_, v_a_4512_, v___y_4513_, v___y_4514_, v___y_4515_, v___y_4516_);
lean_dec(v___y_4516_);
lean_dec_ref(v___y_4515_);
lean_dec(v___y_4514_);
lean_dec_ref(v___y_4513_);
lean_dec(v_a_4512_);
return v_res_4521_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___boxed(lean_object* v_pre_4522_, lean_object* v_post_4523_, lean_object* v_usedLetOnly_4524_, lean_object* v_skipConstInApp_4525_, lean_object* v_skipInstances_4526_, lean_object* v_fvars_4527_, lean_object* v_e_4528_, lean_object* v_a_4529_, lean_object* v___y_4530_, lean_object* v___y_4531_, lean_object* v___y_4532_, lean_object* v___y_4533_, lean_object* v___y_4534_){
_start:
{
uint8_t v_usedLetOnly_boxed_4535_; uint8_t v_skipConstInApp_boxed_4536_; uint8_t v_skipInstances_boxed_4537_; lean_object* v_res_4538_; 
v_usedLetOnly_boxed_4535_ = lean_unbox(v_usedLetOnly_4524_);
v_skipConstInApp_boxed_4536_ = lean_unbox(v_skipConstInApp_4525_);
v_skipInstances_boxed_4537_ = lean_unbox(v_skipInstances_4526_);
v_res_4538_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7(v_pre_4522_, v_post_4523_, v_usedLetOnly_boxed_4535_, v_skipConstInApp_boxed_4536_, v_skipInstances_boxed_4537_, v_fvars_4527_, v_e_4528_, v_a_4529_, v___y_4530_, v___y_4531_, v___y_4532_, v___y_4533_);
lean_dec(v___y_4533_);
lean_dec_ref(v___y_4532_);
lean_dec(v___y_4531_);
lean_dec_ref(v___y_4530_);
lean_dec(v_a_4529_);
return v_res_4538_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_upperBound_4539_, lean_object* v___x_4540_, lean_object* v_pre_4541_, lean_object* v_post_4542_, lean_object* v_usedLetOnly_4543_, lean_object* v_skipConstInApp_4544_, lean_object* v_skipInstances_4545_, lean_object* v_a_4546_, lean_object* v_b_4547_, lean_object* v___y_4548_, lean_object* v___y_4549_, lean_object* v___y_4550_, lean_object* v___y_4551_, lean_object* v___y_4552_, lean_object* v___y_4553_){
_start:
{
uint8_t v_usedLetOnly_boxed_4554_; uint8_t v_skipConstInApp_boxed_4555_; uint8_t v_skipInstances_boxed_4556_; lean_object* v_res_4557_; 
v_usedLetOnly_boxed_4554_ = lean_unbox(v_usedLetOnly_4543_);
v_skipConstInApp_boxed_4555_ = lean_unbox(v_skipConstInApp_4544_);
v_skipInstances_boxed_4556_ = lean_unbox(v_skipInstances_4545_);
v_res_4557_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg(v_upperBound_4539_, v___x_4540_, v_pre_4541_, v_post_4542_, v_usedLetOnly_boxed_4554_, v_skipConstInApp_boxed_4555_, v_skipInstances_boxed_4556_, v_a_4546_, v_b_4547_, v___y_4548_, v___y_4549_, v___y_4550_, v___y_4551_, v___y_4552_);
lean_dec(v___y_4552_);
lean_dec_ref(v___y_4551_);
lean_dec(v___y_4550_);
lean_dec_ref(v___y_4549_);
lean_dec(v___y_4548_);
lean_dec_ref(v___x_4540_);
lean_dec(v_upperBound_4539_);
return v_res_4557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__8___boxed(lean_object* v_skipInstances_4558_, lean_object* v_pre_4559_, lean_object* v_post_4560_, lean_object* v_usedLetOnly_4561_, lean_object* v_skipConstInApp_4562_, lean_object* v_x_4563_, lean_object* v_x_4564_, lean_object* v_x_4565_, lean_object* v___y_4566_, lean_object* v___y_4567_, lean_object* v___y_4568_, lean_object* v___y_4569_, lean_object* v___y_4570_, lean_object* v___y_4571_){
_start:
{
uint8_t v_skipInstances_boxed_4572_; uint8_t v_usedLetOnly_boxed_4573_; uint8_t v_skipConstInApp_boxed_4574_; lean_object* v_res_4575_; 
v_skipInstances_boxed_4572_ = lean_unbox(v_skipInstances_4558_);
v_usedLetOnly_boxed_4573_ = lean_unbox(v_usedLetOnly_4561_);
v_skipConstInApp_boxed_4574_ = lean_unbox(v_skipConstInApp_4562_);
v_res_4575_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__8(v_skipInstances_boxed_4572_, v_pre_4559_, v_post_4560_, v_usedLetOnly_boxed_4573_, v_skipConstInApp_boxed_4574_, v_x_4563_, v_x_4564_, v_x_4565_, v___y_4566_, v___y_4567_, v___y_4568_, v___y_4569_, v___y_4570_);
lean_dec(v___y_4570_);
lean_dec_ref(v___y_4569_);
lean_dec(v___y_4568_);
lean_dec_ref(v___y_4567_);
lean_dec(v___y_4566_);
return v_res_4575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(lean_object* v_input_4576_, lean_object* v_pre_4577_, lean_object* v_post_4578_, uint8_t v_usedLetOnly_4579_, uint8_t v_skipConstInApp_4580_, lean_object* v___y_4581_, lean_object* v___y_4582_, lean_object* v___y_4583_, lean_object* v___y_4584_){
_start:
{
lean_object* v___x_4586_; lean_object* v___x_4587_; lean_object* v_a_4588_; uint8_t v___x_4589_; lean_object* v___x_4590_; 
v___x_4586_ = lean_obj_once(&l_Lean_Core_transform___redArg___closed__2, &l_Lean_Core_transform___redArg___closed__2_once, _init_l_Lean_Core_transform___redArg___closed__2);
v___x_4587_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0(lean_box(0), v___x_4586_, v___y_4581_, v___y_4582_, v___y_4583_, v___y_4584_);
v_a_4588_ = lean_ctor_get(v___x_4587_, 0);
lean_inc(v_a_4588_);
lean_dec_ref(v___x_4587_);
v___x_4589_ = 0;
v___x_4590_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4577_, v_post_4578_, v_usedLetOnly_4579_, v_skipConstInApp_4580_, v___x_4589_, v_input_4576_, v_a_4588_, v___y_4581_, v___y_4582_, v___y_4583_, v___y_4584_);
if (lean_obj_tag(v___x_4590_) == 0)
{
lean_object* v_a_4591_; lean_object* v___x_4592_; lean_object* v___x_4593_; lean_object* v___x_4595_; uint8_t v_isShared_4596_; uint8_t v_isSharedCheck_4600_; 
v_a_4591_ = lean_ctor_get(v___x_4590_, 0);
lean_inc(v_a_4591_);
lean_dec_ref_known(v___x_4590_, 1);
v___x_4592_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_4592_, 0, lean_box(0));
lean_closure_set(v___x_4592_, 1, lean_box(0));
lean_closure_set(v___x_4592_, 2, v_a_4588_);
v___x_4593_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0(lean_box(0), v___x_4592_, v___y_4581_, v___y_4582_, v___y_4583_, v___y_4584_);
v_isSharedCheck_4600_ = !lean_is_exclusive(v___x_4593_);
if (v_isSharedCheck_4600_ == 0)
{
lean_object* v_unused_4601_; 
v_unused_4601_ = lean_ctor_get(v___x_4593_, 0);
lean_dec(v_unused_4601_);
v___x_4595_ = v___x_4593_;
v_isShared_4596_ = v_isSharedCheck_4600_;
goto v_resetjp_4594_;
}
else
{
lean_dec(v___x_4593_);
v___x_4595_ = lean_box(0);
v_isShared_4596_ = v_isSharedCheck_4600_;
goto v_resetjp_4594_;
}
v_resetjp_4594_:
{
lean_object* v___x_4598_; 
if (v_isShared_4596_ == 0)
{
lean_ctor_set(v___x_4595_, 0, v_a_4591_);
v___x_4598_ = v___x_4595_;
goto v_reusejp_4597_;
}
else
{
lean_object* v_reuseFailAlloc_4599_; 
v_reuseFailAlloc_4599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4599_, 0, v_a_4591_);
v___x_4598_ = v_reuseFailAlloc_4599_;
goto v_reusejp_4597_;
}
v_reusejp_4597_:
{
return v___x_4598_;
}
}
}
else
{
lean_dec(v_a_4588_);
return v___x_4590_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___boxed(lean_object* v_input_4602_, lean_object* v_pre_4603_, lean_object* v_post_4604_, lean_object* v_usedLetOnly_4605_, lean_object* v_skipConstInApp_4606_, lean_object* v___y_4607_, lean_object* v___y_4608_, lean_object* v___y_4609_, lean_object* v___y_4610_, lean_object* v___y_4611_){
_start:
{
uint8_t v_usedLetOnly_boxed_4612_; uint8_t v_skipConstInApp_boxed_4613_; lean_object* v_res_4614_; 
v_usedLetOnly_boxed_4612_ = lean_unbox(v_usedLetOnly_4605_);
v_skipConstInApp_boxed_4613_ = lean_unbox(v_skipConstInApp_4606_);
v_res_4614_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(v_input_4602_, v_pre_4603_, v_post_4604_, v_usedLetOnly_boxed_4612_, v_skipConstInApp_boxed_4613_, v___y_4607_, v___y_4608_, v___y_4609_, v___y_4610_);
lean_dec(v___y_4610_);
lean_dec_ref(v___y_4609_);
lean_dec(v___y_4608_);
lean_dec_ref(v___y_4607_);
return v_res_4614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce(lean_object* v_e_4616_, uint8_t v_zetaDelta_4617_, uint8_t v_zetaHave_4618_, uint8_t v_beta_4619_, lean_object* v_a_4620_, lean_object* v_a_4621_, lean_object* v_a_4622_, lean_object* v_a_4623_){
_start:
{
lean_object* v_lctx_4625_; lean_object* v___x_4626_; lean_object* v___x_4627_; lean_object* v___x_4628_; lean_object* v___f_4629_; uint8_t v___x_4630_; 
v_lctx_4625_ = lean_ctor_get(v_a_4620_, 2);
lean_inc_ref(v_lctx_4625_);
v___x_4626_ = lean_local_ctx_num_indices(v_lctx_4625_);
v___x_4627_ = lean_box(v_zetaHave_4618_);
v___x_4628_ = lean_box(v_zetaDelta_4617_);
v___f_4629_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaReduce___lam__0___boxed), 9, 3);
lean_closure_set(v___f_4629_, 0, v___x_4627_);
lean_closure_set(v___f_4629_, 1, v___x_4626_);
lean_closure_set(v___f_4629_, 2, v___x_4628_);
v___x_4630_ = 1;
if (v_beta_4619_ == 0)
{
lean_object* v___f_4631_; lean_object* v___f_4632_; lean_object* v___x_4633_; 
v___f_4631_ = ((lean_object*)(l_Lean_Meta_zetaReduce___closed__0));
v___f_4632_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaReduce___lam__2___boxed), 7, 1);
lean_closure_set(v___f_4632_, 0, v___f_4629_);
v___x_4633_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(v_e_4616_, v___f_4632_, v___f_4631_, v___x_4630_, v_beta_4619_, v_a_4620_, v_a_4621_, v_a_4622_, v_a_4623_);
return v___x_4633_;
}
else
{
lean_object* v___f_4634_; lean_object* v___f_4635_; uint8_t v___x_4636_; lean_object* v___x_4637_; 
v___f_4634_ = ((lean_object*)(l_Lean_Meta_zetaReduce___closed__0));
v___f_4635_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaReduce___lam__4___boxed), 7, 1);
lean_closure_set(v___f_4635_, 0, v___f_4629_);
v___x_4636_ = 0;
v___x_4637_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(v_e_4616_, v___f_4635_, v___f_4634_, v___x_4630_, v___x_4636_, v_a_4620_, v_a_4621_, v_a_4622_, v_a_4623_);
return v___x_4637_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___boxed(lean_object* v_e_4638_, lean_object* v_zetaDelta_4639_, lean_object* v_zetaHave_4640_, lean_object* v_beta_4641_, lean_object* v_a_4642_, lean_object* v_a_4643_, lean_object* v_a_4644_, lean_object* v_a_4645_, lean_object* v_a_4646_){
_start:
{
uint8_t v_zetaDelta_boxed_4647_; uint8_t v_zetaHave_boxed_4648_; uint8_t v_beta_boxed_4649_; lean_object* v_res_4650_; 
v_zetaDelta_boxed_4647_ = lean_unbox(v_zetaDelta_4639_);
v_zetaHave_boxed_4648_ = lean_unbox(v_zetaHave_4640_);
v_beta_boxed_4649_ = lean_unbox(v_beta_4641_);
v_res_4650_ = l_Lean_Meta_zetaReduce(v_e_4638_, v_zetaDelta_boxed_4647_, v_zetaHave_boxed_4648_, v_beta_boxed_4649_, v_a_4642_, v_a_4643_, v_a_4644_, v_a_4645_);
lean_dec(v_a_4645_);
lean_dec_ref(v_a_4644_);
lean_dec(v_a_4643_);
lean_dec_ref(v_a_4642_);
return v_res_4650_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4(lean_object* v_upperBound_4651_, lean_object* v___x_4652_, lean_object* v_pre_4653_, lean_object* v_post_4654_, uint8_t v_usedLetOnly_4655_, uint8_t v_skipConstInApp_4656_, uint8_t v_skipInstances_4657_, lean_object* v___x_4658_, lean_object* v_inst_4659_, lean_object* v_R_4660_, lean_object* v_a_4661_, lean_object* v_b_4662_, lean_object* v_c_4663_, lean_object* v___y_4664_, lean_object* v___y_4665_, lean_object* v___y_4666_, lean_object* v___y_4667_, lean_object* v___y_4668_){
_start:
{
lean_object* v___x_4670_; 
v___x_4670_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg(v_upperBound_4651_, v___x_4652_, v_pre_4653_, v_post_4654_, v_usedLetOnly_4655_, v_skipConstInApp_4656_, v_skipInstances_4657_, v_a_4661_, v_b_4662_, v___y_4664_, v___y_4665_, v___y_4666_, v___y_4667_, v___y_4668_);
return v___x_4670_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___boxed(lean_object** _args){
lean_object* v_upperBound_4671_ = _args[0];
lean_object* v___x_4672_ = _args[1];
lean_object* v_pre_4673_ = _args[2];
lean_object* v_post_4674_ = _args[3];
lean_object* v_usedLetOnly_4675_ = _args[4];
lean_object* v_skipConstInApp_4676_ = _args[5];
lean_object* v_skipInstances_4677_ = _args[6];
lean_object* v___x_4678_ = _args[7];
lean_object* v_inst_4679_ = _args[8];
lean_object* v_R_4680_ = _args[9];
lean_object* v_a_4681_ = _args[10];
lean_object* v_b_4682_ = _args[11];
lean_object* v_c_4683_ = _args[12];
lean_object* v___y_4684_ = _args[13];
lean_object* v___y_4685_ = _args[14];
lean_object* v___y_4686_ = _args[15];
lean_object* v___y_4687_ = _args[16];
lean_object* v___y_4688_ = _args[17];
lean_object* v___y_4689_ = _args[18];
_start:
{
uint8_t v_usedLetOnly_boxed_4690_; uint8_t v_skipConstInApp_boxed_4691_; uint8_t v_skipInstances_boxed_4692_; lean_object* v_res_4693_; 
v_usedLetOnly_boxed_4690_ = lean_unbox(v_usedLetOnly_4675_);
v_skipConstInApp_boxed_4691_ = lean_unbox(v_skipConstInApp_4676_);
v_skipInstances_boxed_4692_ = lean_unbox(v_skipInstances_4677_);
v_res_4693_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4(v_upperBound_4671_, v___x_4672_, v_pre_4673_, v_post_4674_, v_usedLetOnly_boxed_4690_, v_skipConstInApp_boxed_4691_, v_skipInstances_boxed_4692_, v___x_4678_, v_inst_4679_, v_R_4680_, v_a_4681_, v_b_4682_, v_c_4683_, v___y_4684_, v___y_4685_, v___y_4686_, v___y_4687_, v___y_4688_);
lean_dec(v___y_4688_);
lean_dec_ref(v___y_4687_);
lean_dec(v___y_4686_);
lean_dec_ref(v___y_4685_);
lean_dec(v___y_4684_);
lean_dec(v___x_4678_);
lean_dec_ref(v___x_4672_);
lean_dec(v_upperBound_4671_);
return v_res_4693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6(lean_object* v_00_u03b1_4694_, lean_object* v_name_4695_, uint8_t v_bi_4696_, lean_object* v_type_4697_, lean_object* v_k_4698_, uint8_t v_kind_4699_, lean_object* v___y_4700_, lean_object* v___y_4701_, lean_object* v___y_4702_, lean_object* v___y_4703_, lean_object* v___y_4704_){
_start:
{
lean_object* v___x_4706_; 
v___x_4706_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_name_4695_, v_bi_4696_, v_type_4697_, v_k_4698_, v_kind_4699_, v___y_4700_, v___y_4701_, v___y_4702_, v___y_4703_, v___y_4704_);
return v___x_4706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___boxed(lean_object* v_00_u03b1_4707_, lean_object* v_name_4708_, lean_object* v_bi_4709_, lean_object* v_type_4710_, lean_object* v_k_4711_, lean_object* v_kind_4712_, lean_object* v___y_4713_, lean_object* v___y_4714_, lean_object* v___y_4715_, lean_object* v___y_4716_, lean_object* v___y_4717_, lean_object* v___y_4718_){
_start:
{
uint8_t v_bi_boxed_4719_; uint8_t v_kind_boxed_4720_; lean_object* v_res_4721_; 
v_bi_boxed_4719_ = lean_unbox(v_bi_4709_);
v_kind_boxed_4720_ = lean_unbox(v_kind_4712_);
v_res_4721_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6(v_00_u03b1_4707_, v_name_4708_, v_bi_boxed_4719_, v_type_4710_, v_k_4711_, v_kind_boxed_4720_, v___y_4713_, v___y_4714_, v___y_4715_, v___y_4716_, v___y_4717_);
lean_dec(v___y_4717_);
lean_dec_ref(v___y_4716_);
lean_dec(v___y_4715_);
lean_dec_ref(v___y_4714_);
lean_dec(v___y_4713_);
return v_res_4721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9(lean_object* v_00_u03b1_4722_, lean_object* v_name_4723_, lean_object* v_type_4724_, lean_object* v_val_4725_, lean_object* v_k_4726_, uint8_t v_nondep_4727_, uint8_t v_kind_4728_, lean_object* v___y_4729_, lean_object* v___y_4730_, lean_object* v___y_4731_, lean_object* v___y_4732_, lean_object* v___y_4733_){
_start:
{
lean_object* v___x_4735_; 
v___x_4735_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg(v_name_4723_, v_type_4724_, v_val_4725_, v_k_4726_, v_nondep_4727_, v_kind_4728_, v___y_4729_, v___y_4730_, v___y_4731_, v___y_4732_, v___y_4733_);
return v___x_4735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___boxed(lean_object* v_00_u03b1_4736_, lean_object* v_name_4737_, lean_object* v_type_4738_, lean_object* v_val_4739_, lean_object* v_k_4740_, lean_object* v_nondep_4741_, lean_object* v_kind_4742_, lean_object* v___y_4743_, lean_object* v___y_4744_, lean_object* v___y_4745_, lean_object* v___y_4746_, lean_object* v___y_4747_, lean_object* v___y_4748_){
_start:
{
uint8_t v_nondep_boxed_4749_; uint8_t v_kind_boxed_4750_; lean_object* v_res_4751_; 
v_nondep_boxed_4749_ = lean_unbox(v_nondep_4741_);
v_kind_boxed_4750_ = lean_unbox(v_kind_4742_);
v_res_4751_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9(v_00_u03b1_4736_, v_name_4737_, v_type_4738_, v_val_4739_, v_k_4740_, v_nondep_boxed_4749_, v_kind_boxed_4750_, v___y_4743_, v___y_4744_, v___y_4745_, v___y_4746_, v___y_4747_);
lean_dec(v___y_4747_);
lean_dec_ref(v___y_4746_);
lean_dec(v___y_4745_);
lean_dec_ref(v___y_4744_);
lean_dec(v___y_4743_);
return v_res_4751_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12(lean_object* v_00_u03b1_4752_, lean_object* v_ref_4753_, lean_object* v___y_4754_, lean_object* v___y_4755_, lean_object* v___y_4756_, lean_object* v___y_4757_){
_start:
{
lean_object* v___x_4759_; 
v___x_4759_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg(v_ref_4753_);
return v___x_4759_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___boxed(lean_object* v_00_u03b1_4760_, lean_object* v_ref_4761_, lean_object* v___y_4762_, lean_object* v___y_4763_, lean_object* v___y_4764_, lean_object* v___y_4765_, lean_object* v___y_4766_){
_start:
{
lean_object* v_res_4767_; 
v_res_4767_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12(v_00_u03b1_4760_, v_ref_4761_, v___y_4762_, v___y_4763_, v___y_4764_, v___y_4765_);
lean_dec(v___y_4765_);
lean_dec_ref(v___y_4764_);
lean_dec(v___y_4763_);
lean_dec_ref(v___y_4762_);
return v_res_4767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9(lean_object* v_00_u03b1_4768_, lean_object* v_x_4769_, lean_object* v___y_4770_, lean_object* v___y_4771_, lean_object* v___y_4772_, lean_object* v___y_4773_, lean_object* v___y_4774_){
_start:
{
lean_object* v___x_4776_; 
v___x_4776_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg(v_x_4769_, v___y_4770_, v___y_4771_, v___y_4772_, v___y_4773_, v___y_4774_);
return v___x_4776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___boxed(lean_object* v_00_u03b1_4777_, lean_object* v_x_4778_, lean_object* v___y_4779_, lean_object* v___y_4780_, lean_object* v___y_4781_, lean_object* v___y_4782_, lean_object* v___y_4783_, lean_object* v___y_4784_){
_start:
{
lean_object* v_res_4785_; 
v_res_4785_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9(v_00_u03b1_4777_, v_x_4778_, v___y_4779_, v___y_4780_, v___y_4781_, v___y_4782_, v___y_4783_);
lean_dec(v___y_4783_);
lean_dec_ref(v___y_4782_);
lean_dec(v___y_4781_);
lean_dec_ref(v___y_4780_);
lean_dec(v___y_4779_);
return v_res_4785_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0_spec__0(lean_object* v_a_4786_, lean_object* v_as_4787_, size_t v_i_4788_, size_t v_stop_4789_){
_start:
{
uint8_t v___x_4790_; 
v___x_4790_ = lean_usize_dec_eq(v_i_4788_, v_stop_4789_);
if (v___x_4790_ == 0)
{
lean_object* v___x_4791_; uint8_t v___x_4792_; 
v___x_4791_ = lean_array_uget_borrowed(v_as_4787_, v_i_4788_);
v___x_4792_ = l_Lean_instBEqFVarId_beq(v_a_4786_, v___x_4791_);
if (v___x_4792_ == 0)
{
size_t v___x_4793_; size_t v___x_4794_; 
v___x_4793_ = ((size_t)1ULL);
v___x_4794_ = lean_usize_add(v_i_4788_, v___x_4793_);
v_i_4788_ = v___x_4794_;
goto _start;
}
else
{
return v___x_4792_;
}
}
else
{
uint8_t v___x_4796_; 
v___x_4796_ = 0;
return v___x_4796_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0_spec__0___boxed(lean_object* v_a_4797_, lean_object* v_as_4798_, lean_object* v_i_4799_, lean_object* v_stop_4800_){
_start:
{
size_t v_i_boxed_4801_; size_t v_stop_boxed_4802_; uint8_t v_res_4803_; lean_object* v_r_4804_; 
v_i_boxed_4801_ = lean_unbox_usize(v_i_4799_);
lean_dec(v_i_4799_);
v_stop_boxed_4802_ = lean_unbox_usize(v_stop_4800_);
lean_dec(v_stop_4800_);
v_res_4803_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0_spec__0(v_a_4797_, v_as_4798_, v_i_boxed_4801_, v_stop_boxed_4802_);
lean_dec_ref(v_as_4798_);
lean_dec(v_a_4797_);
v_r_4804_ = lean_box(v_res_4803_);
return v_r_4804_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0(lean_object* v_as_4805_, lean_object* v_a_4806_){
_start:
{
lean_object* v___x_4807_; lean_object* v___x_4808_; uint8_t v___x_4809_; 
v___x_4807_ = lean_unsigned_to_nat(0u);
v___x_4808_ = lean_array_get_size(v_as_4805_);
v___x_4809_ = lean_nat_dec_lt(v___x_4807_, v___x_4808_);
if (v___x_4809_ == 0)
{
return v___x_4809_;
}
else
{
if (v___x_4809_ == 0)
{
return v___x_4809_;
}
else
{
size_t v___x_4810_; size_t v___x_4811_; uint8_t v___x_4812_; 
v___x_4810_ = ((size_t)0ULL);
v___x_4811_ = lean_usize_of_nat(v___x_4808_);
v___x_4812_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0_spec__0(v_a_4806_, v_as_4805_, v___x_4810_, v___x_4811_);
return v___x_4812_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0___boxed(lean_object* v_as_4813_, lean_object* v_a_4814_){
_start:
{
uint8_t v_res_4815_; lean_object* v_r_4816_; 
v_res_4815_ = l_Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0(v_as_4813_, v_a_4814_);
lean_dec(v_a_4814_);
lean_dec_ref(v_as_4813_);
v_r_4816_ = lean_box(v_res_4815_);
return v_r_4816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaFVars___lam__1(lean_object* v_fvars_4817_, lean_object* v_e_4818_, lean_object* v___y_4819_, lean_object* v___y_4820_, lean_object* v___y_4821_, lean_object* v___y_4822_){
_start:
{
lean_object* v___x_4827_; 
v___x_4827_ = l_Lean_Expr_getAppFn(v_e_4818_);
if (lean_obj_tag(v___x_4827_) == 1)
{
lean_object* v_fvarId_4828_; uint8_t v___x_4829_; 
v_fvarId_4828_ = lean_ctor_get(v___x_4827_, 0);
lean_inc(v_fvarId_4828_);
lean_dec_ref_known(v___x_4827_, 1);
v___x_4829_ = l_Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0(v_fvars_4817_, v_fvarId_4828_);
if (v___x_4829_ == 0)
{
lean_dec(v_fvarId_4828_);
lean_dec_ref(v_e_4818_);
goto v___jp_4824_;
}
else
{
uint8_t v___x_4830_; lean_object* v___x_4831_; 
v___x_4830_ = 0;
v___x_4831_ = l_Lean_FVarId_getValue_x3f___redArg(v_fvarId_4828_, v___x_4830_, v___y_4819_, v___y_4821_, v___y_4822_);
if (lean_obj_tag(v___x_4831_) == 0)
{
lean_object* v_a_4832_; 
v_a_4832_ = lean_ctor_get(v___x_4831_, 0);
lean_inc(v_a_4832_);
lean_dec_ref_known(v___x_4831_, 1);
if (lean_obj_tag(v_a_4832_) == 1)
{
lean_object* v_val_4833_; lean_object* v___x_4835_; uint8_t v_isShared_4836_; uint8_t v_isSharedCheck_4856_; 
v_val_4833_ = lean_ctor_get(v_a_4832_, 0);
v_isSharedCheck_4856_ = !lean_is_exclusive(v_a_4832_);
if (v_isSharedCheck_4856_ == 0)
{
v___x_4835_ = v_a_4832_;
v_isShared_4836_ = v_isSharedCheck_4856_;
goto v_resetjp_4834_;
}
else
{
lean_inc(v_val_4833_);
lean_dec(v_a_4832_);
v___x_4835_ = lean_box(0);
v_isShared_4836_ = v_isSharedCheck_4856_;
goto v_resetjp_4834_;
}
v_resetjp_4834_:
{
lean_object* v___x_4837_; lean_object* v_a_4838_; lean_object* v___x_4840_; uint8_t v_isShared_4841_; uint8_t v_isSharedCheck_4855_; 
v___x_4837_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(v_val_4833_, v___y_4820_);
v_a_4838_ = lean_ctor_get(v___x_4837_, 0);
v_isSharedCheck_4855_ = !lean_is_exclusive(v___x_4837_);
if (v_isSharedCheck_4855_ == 0)
{
v___x_4840_ = v___x_4837_;
v_isShared_4841_ = v_isSharedCheck_4855_;
goto v_resetjp_4839_;
}
else
{
lean_inc(v_a_4838_);
lean_dec(v___x_4837_);
v___x_4840_ = lean_box(0);
v_isShared_4841_ = v_isSharedCheck_4855_;
goto v_resetjp_4839_;
}
v_resetjp_4839_:
{
lean_object* v_dummy_4842_; lean_object* v_nargs_4843_; lean_object* v___x_4844_; lean_object* v___x_4845_; lean_object* v___x_4846_; lean_object* v___x_4847_; lean_object* v___x_4848_; lean_object* v___x_4850_; 
v_dummy_4842_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_4843_ = l_Lean_Expr_getAppNumArgs(v_e_4818_);
lean_inc(v_nargs_4843_);
v___x_4844_ = lean_mk_array(v_nargs_4843_, v_dummy_4842_);
v___x_4845_ = lean_unsigned_to_nat(1u);
v___x_4846_ = lean_nat_sub(v_nargs_4843_, v___x_4845_);
lean_dec(v_nargs_4843_);
v___x_4847_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_4818_, v___x_4844_, v___x_4846_);
v___x_4848_ = l_Lean_Expr_beta(v_a_4838_, v___x_4847_);
if (v_isShared_4836_ == 0)
{
lean_ctor_set(v___x_4835_, 0, v___x_4848_);
v___x_4850_ = v___x_4835_;
goto v_reusejp_4849_;
}
else
{
lean_object* v_reuseFailAlloc_4854_; 
v_reuseFailAlloc_4854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4854_, 0, v___x_4848_);
v___x_4850_ = v_reuseFailAlloc_4854_;
goto v_reusejp_4849_;
}
v_reusejp_4849_:
{
lean_object* v___x_4852_; 
if (v_isShared_4841_ == 0)
{
lean_ctor_set(v___x_4840_, 0, v___x_4850_);
v___x_4852_ = v___x_4840_;
goto v_reusejp_4851_;
}
else
{
lean_object* v_reuseFailAlloc_4853_; 
v_reuseFailAlloc_4853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4853_, 0, v___x_4850_);
v___x_4852_ = v_reuseFailAlloc_4853_;
goto v_reusejp_4851_;
}
v_reusejp_4851_:
{
return v___x_4852_;
}
}
}
}
}
else
{
lean_dec(v_a_4832_);
lean_dec_ref(v_e_4818_);
goto v___jp_4824_;
}
}
else
{
lean_object* v_a_4857_; lean_object* v___x_4859_; uint8_t v_isShared_4860_; uint8_t v_isSharedCheck_4864_; 
lean_dec_ref(v_e_4818_);
v_a_4857_ = lean_ctor_get(v___x_4831_, 0);
v_isSharedCheck_4864_ = !lean_is_exclusive(v___x_4831_);
if (v_isSharedCheck_4864_ == 0)
{
v___x_4859_ = v___x_4831_;
v_isShared_4860_ = v_isSharedCheck_4864_;
goto v_resetjp_4858_;
}
else
{
lean_inc(v_a_4857_);
lean_dec(v___x_4831_);
v___x_4859_ = lean_box(0);
v_isShared_4860_ = v_isSharedCheck_4864_;
goto v_resetjp_4858_;
}
v_resetjp_4858_:
{
lean_object* v___x_4862_; 
if (v_isShared_4860_ == 0)
{
v___x_4862_ = v___x_4859_;
goto v_reusejp_4861_;
}
else
{
lean_object* v_reuseFailAlloc_4863_; 
v_reuseFailAlloc_4863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4863_, 0, v_a_4857_);
v___x_4862_ = v_reuseFailAlloc_4863_;
goto v_reusejp_4861_;
}
v_reusejp_4861_:
{
return v___x_4862_;
}
}
}
}
}
else
{
lean_object* v___x_4865_; lean_object* v___x_4866_; 
lean_dec_ref(v___x_4827_);
lean_dec_ref(v_e_4818_);
v___x_4865_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_4866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4866_, 0, v___x_4865_);
return v___x_4866_;
}
v___jp_4824_:
{
lean_object* v___x_4825_; lean_object* v___x_4826_; 
v___x_4825_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_4826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4826_, 0, v___x_4825_);
return v___x_4826_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaFVars___lam__1___boxed(lean_object* v_fvars_4867_, lean_object* v_e_4868_, lean_object* v___y_4869_, lean_object* v___y_4870_, lean_object* v___y_4871_, lean_object* v___y_4872_, lean_object* v___y_4873_){
_start:
{
lean_object* v_res_4874_; 
v_res_4874_ = l_Lean_Meta_zetaDeltaFVars___lam__1(v_fvars_4867_, v_e_4868_, v___y_4869_, v___y_4870_, v___y_4871_, v___y_4872_);
lean_dec(v___y_4872_);
lean_dec_ref(v___y_4871_);
lean_dec(v___y_4870_);
lean_dec_ref(v___y_4869_);
lean_dec_ref(v_fvars_4867_);
return v_res_4874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaFVars(lean_object* v_e_4875_, lean_object* v_fvars_4876_, lean_object* v_a_4877_, lean_object* v_a_4878_, lean_object* v_a_4879_, lean_object* v_a_4880_){
_start:
{
lean_object* v___f_4882_; lean_object* v_pre_4883_; uint8_t v___x_4884_; lean_object* v___x_4885_; 
v___f_4882_ = ((lean_object*)(l_Lean_Meta_zetaReduce___closed__0));
v_pre_4883_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaDeltaFVars___lam__1___boxed), 7, 1);
lean_closure_set(v_pre_4883_, 0, v_fvars_4876_);
v___x_4884_ = 0;
v___x_4885_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(v_e_4875_, v_pre_4883_, v___f_4882_, v___x_4884_, v___x_4884_, v_a_4877_, v_a_4878_, v_a_4879_, v_a_4880_);
return v___x_4885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaFVars___boxed(lean_object* v_e_4886_, lean_object* v_fvars_4887_, lean_object* v_a_4888_, lean_object* v_a_4889_, lean_object* v_a_4890_, lean_object* v_a_4891_, lean_object* v_a_4892_){
_start:
{
lean_object* v_res_4893_; 
v_res_4893_ = l_Lean_Meta_zetaDeltaFVars(v_e_4886_, v_fvars_4887_, v_a_4888_, v_a_4889_, v_a_4890_, v_a_4891_);
lean_dec(v_a_4891_);
lean_dec_ref(v_a_4890_);
lean_dec(v_a_4889_);
lean_dec_ref(v_a_4888_);
return v_res_4893_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_4894_; 
v___x_4894_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4894_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_4895_; lean_object* v___x_4896_; 
v___x_4895_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__0, &l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__0);
v___x_4896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4896_, 0, v___x_4895_);
return v___x_4896_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_4897_; lean_object* v___x_4898_; 
v___x_4897_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__1, &l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__1);
v___x_4898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4898_, 0, v___x_4897_);
lean_ctor_set(v___x_4898_, 1, v___x_4897_);
return v___x_4898_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(lean_object* v_env_4899_, lean_object* v___y_4900_){
_start:
{
lean_object* v___x_4902_; lean_object* v_nextMacroScope_4903_; lean_object* v_ngen_4904_; lean_object* v_auxDeclNGen_4905_; lean_object* v_traceState_4906_; lean_object* v_messages_4907_; lean_object* v_infoState_4908_; lean_object* v_snapshotTasks_4909_; lean_object* v___x_4911_; uint8_t v_isShared_4912_; uint8_t v_isSharedCheck_4920_; 
v___x_4902_ = lean_st_ref_take(v___y_4900_);
v_nextMacroScope_4903_ = lean_ctor_get(v___x_4902_, 1);
v_ngen_4904_ = lean_ctor_get(v___x_4902_, 2);
v_auxDeclNGen_4905_ = lean_ctor_get(v___x_4902_, 3);
v_traceState_4906_ = lean_ctor_get(v___x_4902_, 4);
v_messages_4907_ = lean_ctor_get(v___x_4902_, 6);
v_infoState_4908_ = lean_ctor_get(v___x_4902_, 7);
v_snapshotTasks_4909_ = lean_ctor_get(v___x_4902_, 8);
v_isSharedCheck_4920_ = !lean_is_exclusive(v___x_4902_);
if (v_isSharedCheck_4920_ == 0)
{
lean_object* v_unused_4921_; lean_object* v_unused_4922_; 
v_unused_4921_ = lean_ctor_get(v___x_4902_, 5);
lean_dec(v_unused_4921_);
v_unused_4922_ = lean_ctor_get(v___x_4902_, 0);
lean_dec(v_unused_4922_);
v___x_4911_ = v___x_4902_;
v_isShared_4912_ = v_isSharedCheck_4920_;
goto v_resetjp_4910_;
}
else
{
lean_inc(v_snapshotTasks_4909_);
lean_inc(v_infoState_4908_);
lean_inc(v_messages_4907_);
lean_inc(v_traceState_4906_);
lean_inc(v_auxDeclNGen_4905_);
lean_inc(v_ngen_4904_);
lean_inc(v_nextMacroScope_4903_);
lean_dec(v___x_4902_);
v___x_4911_ = lean_box(0);
v_isShared_4912_ = v_isSharedCheck_4920_;
goto v_resetjp_4910_;
}
v_resetjp_4910_:
{
lean_object* v___x_4913_; lean_object* v___x_4915_; 
v___x_4913_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2, &l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2);
if (v_isShared_4912_ == 0)
{
lean_ctor_set(v___x_4911_, 5, v___x_4913_);
lean_ctor_set(v___x_4911_, 0, v_env_4899_);
v___x_4915_ = v___x_4911_;
goto v_reusejp_4914_;
}
else
{
lean_object* v_reuseFailAlloc_4919_; 
v_reuseFailAlloc_4919_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4919_, 0, v_env_4899_);
lean_ctor_set(v_reuseFailAlloc_4919_, 1, v_nextMacroScope_4903_);
lean_ctor_set(v_reuseFailAlloc_4919_, 2, v_ngen_4904_);
lean_ctor_set(v_reuseFailAlloc_4919_, 3, v_auxDeclNGen_4905_);
lean_ctor_set(v_reuseFailAlloc_4919_, 4, v_traceState_4906_);
lean_ctor_set(v_reuseFailAlloc_4919_, 5, v___x_4913_);
lean_ctor_set(v_reuseFailAlloc_4919_, 6, v_messages_4907_);
lean_ctor_set(v_reuseFailAlloc_4919_, 7, v_infoState_4908_);
lean_ctor_set(v_reuseFailAlloc_4919_, 8, v_snapshotTasks_4909_);
v___x_4915_ = v_reuseFailAlloc_4919_;
goto v_reusejp_4914_;
}
v_reusejp_4914_:
{
lean_object* v___x_4916_; lean_object* v___x_4917_; lean_object* v___x_4918_; 
v___x_4916_ = lean_st_ref_set(v___y_4900_, v___x_4915_);
v___x_4917_ = lean_box(0);
v___x_4918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4918_, 0, v___x_4917_);
return v___x_4918_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___boxed(lean_object* v_env_4923_, lean_object* v___y_4924_, lean_object* v___y_4925_){
_start:
{
lean_object* v_res_4926_; 
v_res_4926_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_4923_, v___y_4924_);
lean_dec(v___y_4924_);
return v_res_4926_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0(lean_object* v_env_4927_, lean_object* v___y_4928_, lean_object* v___y_4929_){
_start:
{
lean_object* v___x_4931_; 
v___x_4931_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_4927_, v___y_4929_);
return v___x_4931_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___boxed(lean_object* v_env_4932_, lean_object* v___y_4933_, lean_object* v___y_4934_, lean_object* v___y_4935_){
_start:
{
lean_object* v_res_4936_; 
v_res_4936_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0(v_env_4932_, v___y_4933_, v___y_4934_);
lean_dec(v___y_4934_);
lean_dec_ref(v___y_4933_);
return v_res_4936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___lam__1(lean_object* v_env_4937_, lean_object* v___x_4938_, uint8_t v___x_4939_, lean_object* v_e_4940_, lean_object* v___y_4941_, lean_object* v___y_4942_){
_start:
{
if (lean_obj_tag(v_e_4940_) == 4)
{
lean_object* v_declName_4944_; lean_object* v_us_4945_; uint8_t v___x_4946_; uint8_t v___x_4947_; 
v_declName_4944_ = lean_ctor_get(v_e_4940_, 0);
v_us_4945_ = lean_ctor_get(v_e_4940_, 1);
v___x_4946_ = 1;
lean_inc(v_declName_4944_);
v___x_4947_ = l_Lean_Environment_contains(v_env_4937_, v_declName_4944_, v___x_4946_);
if (v___x_4947_ == 0)
{
lean_object* v___x_4948_; 
lean_inc(v_declName_4944_);
v___x_4948_ = l_Lean_Environment_find_x3f(v___x_4938_, v_declName_4944_, v___x_4939_);
if (lean_obj_tag(v___x_4948_) == 1)
{
lean_object* v_val_4949_; lean_object* v___x_4951_; uint8_t v_isShared_4952_; uint8_t v_isSharedCheck_4978_; 
v_val_4949_ = lean_ctor_get(v___x_4948_, 0);
v_isSharedCheck_4978_ = !lean_is_exclusive(v___x_4948_);
if (v_isSharedCheck_4978_ == 0)
{
v___x_4951_ = v___x_4948_;
v_isShared_4952_ = v_isSharedCheck_4978_;
goto v_resetjp_4950_;
}
else
{
lean_inc(v_val_4949_);
lean_dec(v___x_4948_);
v___x_4951_ = lean_box(0);
v_isShared_4952_ = v_isSharedCheck_4978_;
goto v_resetjp_4950_;
}
v_resetjp_4950_:
{
uint8_t v___x_4953_; 
v___x_4953_ = l_Lean_ConstantInfo_hasValue(v_val_4949_, v___x_4946_);
if (v___x_4953_ == 0)
{
lean_object* v___x_4955_; 
lean_dec(v_val_4949_);
if (v_isShared_4952_ == 0)
{
lean_ctor_set_tag(v___x_4951_, 0);
lean_ctor_set(v___x_4951_, 0, v_e_4940_);
v___x_4955_ = v___x_4951_;
goto v_reusejp_4954_;
}
else
{
lean_object* v_reuseFailAlloc_4957_; 
v_reuseFailAlloc_4957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4957_, 0, v_e_4940_);
v___x_4955_ = v_reuseFailAlloc_4957_;
goto v_reusejp_4954_;
}
v_reusejp_4954_:
{
lean_object* v___x_4956_; 
v___x_4956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4956_, 0, v___x_4955_);
return v___x_4956_;
}
}
else
{
lean_object* v___x_4958_; 
lean_inc(v_us_4945_);
lean_dec_ref_known(v_e_4940_, 2);
v___x_4958_ = l_Lean_Core_instantiateValueLevelParams(v_val_4949_, v_us_4945_, v___x_4946_, v___y_4941_, v___y_4942_);
lean_dec(v_val_4949_);
if (lean_obj_tag(v___x_4958_) == 0)
{
lean_object* v_a_4959_; lean_object* v___x_4961_; uint8_t v_isShared_4962_; uint8_t v_isSharedCheck_4969_; 
v_a_4959_ = lean_ctor_get(v___x_4958_, 0);
v_isSharedCheck_4969_ = !lean_is_exclusive(v___x_4958_);
if (v_isSharedCheck_4969_ == 0)
{
v___x_4961_ = v___x_4958_;
v_isShared_4962_ = v_isSharedCheck_4969_;
goto v_resetjp_4960_;
}
else
{
lean_inc(v_a_4959_);
lean_dec(v___x_4958_);
v___x_4961_ = lean_box(0);
v_isShared_4962_ = v_isSharedCheck_4969_;
goto v_resetjp_4960_;
}
v_resetjp_4960_:
{
lean_object* v___x_4964_; 
if (v_isShared_4952_ == 0)
{
lean_ctor_set(v___x_4951_, 0, v_a_4959_);
v___x_4964_ = v___x_4951_;
goto v_reusejp_4963_;
}
else
{
lean_object* v_reuseFailAlloc_4968_; 
v_reuseFailAlloc_4968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4968_, 0, v_a_4959_);
v___x_4964_ = v_reuseFailAlloc_4968_;
goto v_reusejp_4963_;
}
v_reusejp_4963_:
{
lean_object* v___x_4966_; 
if (v_isShared_4962_ == 0)
{
lean_ctor_set(v___x_4961_, 0, v___x_4964_);
v___x_4966_ = v___x_4961_;
goto v_reusejp_4965_;
}
else
{
lean_object* v_reuseFailAlloc_4967_; 
v_reuseFailAlloc_4967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4967_, 0, v___x_4964_);
v___x_4966_ = v_reuseFailAlloc_4967_;
goto v_reusejp_4965_;
}
v_reusejp_4965_:
{
return v___x_4966_;
}
}
}
}
else
{
lean_object* v_a_4970_; lean_object* v___x_4972_; uint8_t v_isShared_4973_; uint8_t v_isSharedCheck_4977_; 
lean_del_object(v___x_4951_);
v_a_4970_ = lean_ctor_get(v___x_4958_, 0);
v_isSharedCheck_4977_ = !lean_is_exclusive(v___x_4958_);
if (v_isSharedCheck_4977_ == 0)
{
v___x_4972_ = v___x_4958_;
v_isShared_4973_ = v_isSharedCheck_4977_;
goto v_resetjp_4971_;
}
else
{
lean_inc(v_a_4970_);
lean_dec(v___x_4958_);
v___x_4972_ = lean_box(0);
v_isShared_4973_ = v_isSharedCheck_4977_;
goto v_resetjp_4971_;
}
v_resetjp_4971_:
{
lean_object* v___x_4975_; 
if (v_isShared_4973_ == 0)
{
v___x_4975_ = v___x_4972_;
goto v_reusejp_4974_;
}
else
{
lean_object* v_reuseFailAlloc_4976_; 
v_reuseFailAlloc_4976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4976_, 0, v_a_4970_);
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
}
else
{
lean_object* v___x_4979_; lean_object* v___x_4980_; 
lean_dec(v___x_4948_);
v___x_4979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4979_, 0, v_e_4940_);
v___x_4980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4980_, 0, v___x_4979_);
return v___x_4980_;
}
}
else
{
lean_object* v___x_4981_; lean_object* v___x_4982_; 
lean_dec_ref(v___x_4938_);
v___x_4981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4981_, 0, v_e_4940_);
v___x_4982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4982_, 0, v___x_4981_);
return v___x_4982_;
}
}
else
{
lean_object* v___x_4983_; lean_object* v___x_4984_; 
lean_dec_ref(v_e_4940_);
lean_dec_ref(v___x_4938_);
lean_dec_ref(v_env_4937_);
v___x_4983_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_4984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4984_, 0, v___x_4983_);
return v___x_4984_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___lam__1___boxed(lean_object* v_env_4985_, lean_object* v___x_4986_, lean_object* v___x_4987_, lean_object* v_e_4988_, lean_object* v___y_4989_, lean_object* v___y_4990_, lean_object* v___y_4991_){
_start:
{
uint8_t v___x_2152__boxed_4992_; lean_object* v_res_4993_; 
v___x_2152__boxed_4992_ = lean_unbox(v___x_4987_);
v_res_4993_ = l_Lean_Meta_unfoldDeclsFrom___lam__1(v_env_4985_, v___x_4986_, v___x_2152__boxed_4992_, v_e_4988_, v___y_4989_, v___y_4990_);
lean_dec(v___y_4990_);
lean_dec_ref(v___y_4989_);
return v_res_4993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___lam__0(lean_object* v_biggerEnv_4994_, lean_object* v_e_4995_, lean_object* v___f_4996_, lean_object* v___y_4997_, lean_object* v___y_4998_){
_start:
{
lean_object* v___x_5000_; uint8_t v___x_5001_; lean_object* v___x_5002_; lean_object* v___x_5003_; lean_object* v_env_5004_; lean_object* v___x_5005_; lean_object* v___f_5006_; lean_object* v___x_5007_; 
v___x_5000_ = lean_st_ref_get(v___y_4998_);
v___x_5001_ = 0;
v___x_5002_ = l_Lean_Environment_setExporting(v_biggerEnv_4994_, v___x_5001_);
lean_inc_ref(v___x_5002_);
v___x_5003_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v___x_5002_, v___y_4998_);
lean_dec_ref(v___x_5003_);
v_env_5004_ = lean_ctor_get(v___x_5000_, 0);
lean_inc_ref(v_env_5004_);
lean_dec(v___x_5000_);
v___x_5005_ = lean_box(v___x_5001_);
v___f_5006_ = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDeclsFrom___lam__1___boxed), 7, 3);
lean_closure_set(v___f_5006_, 0, v_env_5004_);
lean_closure_set(v___f_5006_, 1, v___x_5002_);
lean_closure_set(v___f_5006_, 2, v___x_5005_);
v___x_5007_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_4995_, v___f_5006_, v___f_4996_, v___y_4997_, v___y_4998_);
return v___x_5007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___lam__0___boxed(lean_object* v_biggerEnv_5008_, lean_object* v_e_5009_, lean_object* v___f_5010_, lean_object* v___y_5011_, lean_object* v___y_5012_, lean_object* v___y_5013_){
_start:
{
lean_object* v_res_5014_; 
v_res_5014_ = l_Lean_Meta_unfoldDeclsFrom___lam__0(v_biggerEnv_5008_, v_e_5009_, v___f_5010_, v___y_5011_, v___y_5012_);
lean_dec(v___y_5012_);
lean_dec_ref(v___y_5011_);
return v_res_5014_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg(lean_object* v_env_5015_, lean_object* v_x_5016_, lean_object* v___y_5017_, lean_object* v___y_5018_){
_start:
{
lean_object* v___x_5020_; lean_object* v_env_5021_; lean_object* v_a_5023_; lean_object* v___x_5033_; lean_object* v___x_5034_; 
v___x_5020_ = lean_st_ref_get(v___y_5018_);
v_env_5021_ = lean_ctor_get(v___x_5020_, 0);
lean_inc_ref(v_env_5021_);
lean_dec(v___x_5020_);
v___x_5033_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_5015_, v___y_5018_);
lean_dec_ref(v___x_5033_);
lean_inc(v___y_5018_);
lean_inc_ref(v___y_5017_);
v___x_5034_ = lean_apply_3(v_x_5016_, v___y_5017_, v___y_5018_, lean_box(0));
if (lean_obj_tag(v___x_5034_) == 0)
{
lean_object* v_a_5035_; lean_object* v___x_5036_; lean_object* v___x_5038_; uint8_t v_isShared_5039_; uint8_t v_isSharedCheck_5043_; 
v_a_5035_ = lean_ctor_get(v___x_5034_, 0);
lean_inc(v_a_5035_);
lean_dec_ref_known(v___x_5034_, 1);
v___x_5036_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_5021_, v___y_5018_);
v_isSharedCheck_5043_ = !lean_is_exclusive(v___x_5036_);
if (v_isSharedCheck_5043_ == 0)
{
lean_object* v_unused_5044_; 
v_unused_5044_ = lean_ctor_get(v___x_5036_, 0);
lean_dec(v_unused_5044_);
v___x_5038_ = v___x_5036_;
v_isShared_5039_ = v_isSharedCheck_5043_;
goto v_resetjp_5037_;
}
else
{
lean_dec(v___x_5036_);
v___x_5038_ = lean_box(0);
v_isShared_5039_ = v_isSharedCheck_5043_;
goto v_resetjp_5037_;
}
v_resetjp_5037_:
{
lean_object* v___x_5041_; 
if (v_isShared_5039_ == 0)
{
lean_ctor_set(v___x_5038_, 0, v_a_5035_);
v___x_5041_ = v___x_5038_;
goto v_reusejp_5040_;
}
else
{
lean_object* v_reuseFailAlloc_5042_; 
v_reuseFailAlloc_5042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5042_, 0, v_a_5035_);
v___x_5041_ = v_reuseFailAlloc_5042_;
goto v_reusejp_5040_;
}
v_reusejp_5040_:
{
return v___x_5041_;
}
}
}
else
{
lean_object* v_a_5045_; 
v_a_5045_ = lean_ctor_get(v___x_5034_, 0);
lean_inc(v_a_5045_);
lean_dec_ref_known(v___x_5034_, 1);
v_a_5023_ = v_a_5045_;
goto v___jp_5022_;
}
v___jp_5022_:
{
lean_object* v___x_5024_; lean_object* v___x_5026_; uint8_t v_isShared_5027_; uint8_t v_isSharedCheck_5031_; 
v___x_5024_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_5021_, v___y_5018_);
v_isSharedCheck_5031_ = !lean_is_exclusive(v___x_5024_);
if (v_isSharedCheck_5031_ == 0)
{
lean_object* v_unused_5032_; 
v_unused_5032_ = lean_ctor_get(v___x_5024_, 0);
lean_dec(v_unused_5032_);
v___x_5026_ = v___x_5024_;
v_isShared_5027_ = v_isSharedCheck_5031_;
goto v_resetjp_5025_;
}
else
{
lean_dec(v___x_5024_);
v___x_5026_ = lean_box(0);
v_isShared_5027_ = v_isSharedCheck_5031_;
goto v_resetjp_5025_;
}
v_resetjp_5025_:
{
lean_object* v___x_5029_; 
if (v_isShared_5027_ == 0)
{
lean_ctor_set_tag(v___x_5026_, 1);
lean_ctor_set(v___x_5026_, 0, v_a_5023_);
v___x_5029_ = v___x_5026_;
goto v_reusejp_5028_;
}
else
{
lean_object* v_reuseFailAlloc_5030_; 
v_reuseFailAlloc_5030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5030_, 0, v_a_5023_);
v___x_5029_ = v_reuseFailAlloc_5030_;
goto v_reusejp_5028_;
}
v_reusejp_5028_:
{
return v___x_5029_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg___boxed(lean_object* v_env_5046_, lean_object* v_x_5047_, lean_object* v___y_5048_, lean_object* v___y_5049_, lean_object* v___y_5050_){
_start:
{
lean_object* v_res_5051_; 
v_res_5051_ = l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg(v_env_5046_, v_x_5047_, v___y_5048_, v___y_5049_);
lean_dec(v___y_5049_);
lean_dec_ref(v___y_5048_);
return v_res_5051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom(lean_object* v_biggerEnv_5052_, lean_object* v_e_5053_, lean_object* v_a_5054_, lean_object* v_a_5055_){
_start:
{
lean_object* v___x_5057_; lean_object* v_env_5058_; lean_object* v___f_5059_; lean_object* v___f_5060_; lean_object* v___x_5061_; lean_object* v___x_5062_; 
v___x_5057_ = lean_st_ref_get(v_a_5055_);
v_env_5058_ = lean_ctor_get(v___x_5057_, 0);
lean_inc_ref(v_env_5058_);
lean_dec(v___x_5057_);
v___f_5059_ = ((lean_object*)(l_Lean_Core_betaReduce___closed__1));
v___f_5060_ = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDeclsFrom___lam__0___boxed), 6, 3);
lean_closure_set(v___f_5060_, 0, v_biggerEnv_5052_);
lean_closure_set(v___f_5060_, 1, v_e_5053_);
lean_closure_set(v___f_5060_, 2, v___f_5059_);
v___x_5061_ = l_Lean_Environment_unlockAsync(v_env_5058_);
v___x_5062_ = l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg(v___x_5061_, v___f_5060_, v_a_5054_, v_a_5055_);
return v___x_5062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___boxed(lean_object* v_biggerEnv_5063_, lean_object* v_e_5064_, lean_object* v_a_5065_, lean_object* v_a_5066_, lean_object* v_a_5067_){
_start:
{
lean_object* v_res_5068_; 
v_res_5068_ = l_Lean_Meta_unfoldDeclsFrom(v_biggerEnv_5063_, v_e_5064_, v_a_5065_, v_a_5066_);
lean_dec(v_a_5066_);
lean_dec_ref(v_a_5065_);
return v_res_5068_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1(lean_object* v_00_u03b1_5069_, lean_object* v_env_5070_, lean_object* v_x_5071_, lean_object* v___y_5072_, lean_object* v___y_5073_){
_start:
{
lean_object* v___x_5075_; 
v___x_5075_ = l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg(v_env_5070_, v_x_5071_, v___y_5072_, v___y_5073_);
return v___x_5075_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___boxed(lean_object* v_00_u03b1_5076_, lean_object* v_env_5077_, lean_object* v_x_5078_, lean_object* v___y_5079_, lean_object* v___y_5080_, lean_object* v___y_5081_){
_start:
{
lean_object* v_res_5082_; 
v_res_5082_ = l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1(v_00_u03b1_5076_, v_env_5077_, v_x_5078_, v___y_5079_, v___y_5080_);
lean_dec(v___y_5080_);
lean_dec_ref(v___y_5079_);
return v_res_5082_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0(lean_object* v_af_5083_, lean_object* v_axs_5084_, lean_object* v_numSectionVars_5085_, lean_object* v_as_5086_, size_t v_i_5087_, size_t v_stop_5088_){
_start:
{
uint8_t v___x_5089_; 
v___x_5089_ = lean_usize_dec_eq(v_i_5087_, v_stop_5088_);
if (v___x_5089_ == 0)
{
uint8_t v___x_5090_; uint8_t v___y_5092_; lean_object* v___x_5096_; lean_object* v___x_5097_; uint8_t v___x_5098_; 
v___x_5090_ = 1;
v___x_5096_ = lean_array_uget_borrowed(v_as_5086_, v_i_5087_);
v___x_5097_ = l_Lean_Expr_constName_x21(v_af_5083_);
v___x_5098_ = lean_name_eq(v___x_5097_, v___x_5096_);
lean_dec(v___x_5097_);
if (v___x_5098_ == 0)
{
v___y_5092_ = v___x_5098_;
goto v___jp_5091_;
}
else
{
lean_object* v___x_5099_; uint8_t v___x_5100_; 
v___x_5099_ = lean_array_get_size(v_axs_5084_);
v___x_5100_ = lean_nat_dec_le(v___x_5099_, v_numSectionVars_5085_);
v___y_5092_ = v___x_5100_;
goto v___jp_5091_;
}
v___jp_5091_:
{
if (v___y_5092_ == 0)
{
size_t v___x_5093_; size_t v___x_5094_; 
v___x_5093_ = ((size_t)1ULL);
v___x_5094_ = lean_usize_add(v_i_5087_, v___x_5093_);
v_i_5087_ = v___x_5094_;
goto _start;
}
else
{
return v___x_5090_;
}
}
}
else
{
uint8_t v___x_5101_; 
v___x_5101_ = 0;
return v___x_5101_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0___boxed(lean_object* v_af_5102_, lean_object* v_axs_5103_, lean_object* v_numSectionVars_5104_, lean_object* v_as_5105_, lean_object* v_i_5106_, lean_object* v_stop_5107_){
_start:
{
size_t v_i_boxed_5108_; size_t v_stop_boxed_5109_; uint8_t v_res_5110_; lean_object* v_r_5111_; 
v_i_boxed_5108_ = lean_unbox_usize(v_i_5106_);
lean_dec(v_i_5106_);
v_stop_boxed_5109_ = lean_unbox_usize(v_stop_5107_);
lean_dec(v_stop_5107_);
v_res_5110_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0(v_af_5102_, v_axs_5103_, v_numSectionVars_5104_, v_as_5105_, v_i_boxed_5108_, v_stop_boxed_5109_);
lean_dec_ref(v_as_5105_);
lean_dec(v_numSectionVars_5104_);
lean_dec_ref(v_axs_5103_);
lean_dec_ref(v_af_5102_);
v_r_5111_ = lean_box(v_res_5110_);
return v_r_5111_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1_spec__1(lean_object* v_fnNames_5112_, lean_object* v_numSectionVars_5113_, lean_object* v_x_5114_, lean_object* v_x_5115_, lean_object* v_x_5116_){
_start:
{
if (lean_obj_tag(v_x_5114_) == 5)
{
lean_object* v_fn_5117_; lean_object* v_arg_5118_; lean_object* v___x_5119_; lean_object* v___x_5120_; lean_object* v___x_5121_; 
v_fn_5117_ = lean_ctor_get(v_x_5114_, 0);
lean_inc_ref(v_fn_5117_);
v_arg_5118_ = lean_ctor_get(v_x_5114_, 1);
lean_inc_ref(v_arg_5118_);
lean_dec_ref_known(v_x_5114_, 2);
v___x_5119_ = lean_array_set(v_x_5115_, v_x_5116_, v_arg_5118_);
v___x_5120_ = lean_unsigned_to_nat(1u);
v___x_5121_ = lean_nat_sub(v_x_5116_, v___x_5120_);
lean_dec(v_x_5116_);
v_x_5114_ = v_fn_5117_;
v_x_5115_ = v___x_5119_;
v_x_5116_ = v___x_5121_;
goto _start;
}
else
{
uint8_t v___x_5123_; 
lean_dec(v_x_5116_);
v___x_5123_ = l_Lean_Expr_isConst(v_x_5114_);
if (v___x_5123_ == 0)
{
lean_dec_ref(v_x_5115_);
lean_dec_ref(v_x_5114_);
return v___x_5123_;
}
else
{
lean_object* v___x_5124_; lean_object* v___x_5125_; uint8_t v___x_5126_; 
v___x_5124_ = lean_unsigned_to_nat(0u);
v___x_5125_ = lean_array_get_size(v_fnNames_5112_);
v___x_5126_ = lean_nat_dec_lt(v___x_5124_, v___x_5125_);
if (v___x_5126_ == 0)
{
lean_dec_ref(v_x_5115_);
lean_dec_ref(v_x_5114_);
return v___x_5126_;
}
else
{
if (v___x_5126_ == 0)
{
lean_dec_ref(v_x_5115_);
lean_dec_ref(v_x_5114_);
return v___x_5126_;
}
else
{
size_t v___x_5127_; size_t v___x_5128_; uint8_t v___x_5129_; 
v___x_5127_ = ((size_t)0ULL);
v___x_5128_ = lean_usize_of_nat(v___x_5125_);
v___x_5129_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0(v_x_5114_, v_x_5115_, v_numSectionVars_5113_, v_fnNames_5112_, v___x_5127_, v___x_5128_);
lean_dec_ref(v_x_5115_);
lean_dec_ref(v_x_5114_);
return v___x_5129_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1_spec__1___boxed(lean_object* v_fnNames_5130_, lean_object* v_numSectionVars_5131_, lean_object* v_x_5132_, lean_object* v_x_5133_, lean_object* v_x_5134_){
_start:
{
uint8_t v_res_5135_; lean_object* v_r_5136_; 
v_res_5135_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1_spec__1(v_fnNames_5130_, v_numSectionVars_5131_, v_x_5132_, v_x_5133_, v_x_5134_);
lean_dec(v_numSectionVars_5131_);
lean_dec_ref(v_fnNames_5130_);
v_r_5136_ = lean_box(v_res_5135_);
return v_r_5136_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1(lean_object* v_numSectionVars_5137_, lean_object* v_fnNames_5138_, lean_object* v_x_5139_, lean_object* v_x_5140_, lean_object* v_x_5141_){
_start:
{
if (lean_obj_tag(v_x_5139_) == 5)
{
lean_object* v_fn_5142_; lean_object* v_arg_5143_; lean_object* v___x_5144_; lean_object* v___x_5145_; lean_object* v___x_5146_; uint8_t v___x_5147_; 
v_fn_5142_ = lean_ctor_get(v_x_5139_, 0);
lean_inc_ref(v_fn_5142_);
v_arg_5143_ = lean_ctor_get(v_x_5139_, 1);
lean_inc_ref(v_arg_5143_);
lean_dec_ref_known(v_x_5139_, 2);
v___x_5144_ = lean_array_set(v_x_5140_, v_x_5141_, v_arg_5143_);
v___x_5145_ = lean_unsigned_to_nat(1u);
v___x_5146_ = lean_nat_sub(v_x_5141_, v___x_5145_);
v___x_5147_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1_spec__1(v_fnNames_5138_, v_numSectionVars_5137_, v_fn_5142_, v___x_5144_, v___x_5146_);
return v___x_5147_;
}
else
{
uint8_t v___x_5148_; 
v___x_5148_ = l_Lean_Expr_isConst(v_x_5139_);
if (v___x_5148_ == 0)
{
lean_dec_ref(v_x_5140_);
lean_dec_ref(v_x_5139_);
return v___x_5148_;
}
else
{
lean_object* v___x_5149_; lean_object* v___x_5150_; uint8_t v___x_5151_; 
v___x_5149_ = lean_unsigned_to_nat(0u);
v___x_5150_ = lean_array_get_size(v_fnNames_5138_);
v___x_5151_ = lean_nat_dec_lt(v___x_5149_, v___x_5150_);
if (v___x_5151_ == 0)
{
lean_dec_ref(v_x_5140_);
lean_dec_ref(v_x_5139_);
return v___x_5151_;
}
else
{
if (v___x_5151_ == 0)
{
lean_dec_ref(v_x_5140_);
lean_dec_ref(v_x_5139_);
return v___x_5151_;
}
else
{
size_t v___x_5152_; size_t v___x_5153_; uint8_t v___x_5154_; 
v___x_5152_ = ((size_t)0ULL);
v___x_5153_ = lean_usize_of_nat(v___x_5150_);
v___x_5154_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0(v_x_5139_, v_x_5140_, v_numSectionVars_5137_, v_fnNames_5138_, v___x_5152_, v___x_5153_);
lean_dec_ref(v_x_5140_);
lean_dec_ref(v_x_5139_);
return v___x_5154_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1___boxed(lean_object* v_numSectionVars_5155_, lean_object* v_fnNames_5156_, lean_object* v_x_5157_, lean_object* v_x_5158_, lean_object* v_x_5159_){
_start:
{
uint8_t v_res_5160_; lean_object* v_r_5161_; 
v_res_5160_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1(v_numSectionVars_5155_, v_fnNames_5156_, v_x_5157_, v_x_5158_, v_x_5159_);
lean_dec(v_x_5159_);
lean_dec_ref(v_fnNames_5156_);
lean_dec(v_numSectionVars_5155_);
v_r_5161_ = lean_box(v_res_5160_);
return v_r_5161_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg(lean_object* v_fnNames_5162_, lean_object* v_numSectionVars_5163_, lean_object* v_a_5164_){
_start:
{
lean_object* v_dummy_5165_; lean_object* v_nargs_5166_; lean_object* v___x_5167_; lean_object* v___x_5168_; lean_object* v___x_5169_; uint8_t v___x_5170_; 
v_dummy_5165_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_5166_ = l_Lean_Expr_getAppNumArgs(v_a_5164_);
lean_inc(v_nargs_5166_);
v___x_5167_ = lean_mk_array(v_nargs_5166_, v_dummy_5165_);
v___x_5168_ = lean_unsigned_to_nat(1u);
v___x_5169_ = lean_nat_sub(v_nargs_5166_, v___x_5168_);
lean_dec(v_nargs_5166_);
v___x_5170_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1(v_numSectionVars_5163_, v_fnNames_5162_, v_a_5164_, v___x_5167_, v___x_5169_);
lean_dec(v___x_5169_);
return v___x_5170_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg___boxed(lean_object* v_fnNames_5171_, lean_object* v_numSectionVars_5172_, lean_object* v_a_5173_){
_start:
{
uint8_t v_res_5174_; lean_object* v_r_5175_; 
v_res_5174_ = l___private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg(v_fnNames_5171_, v_numSectionVars_5172_, v_a_5173_);
lean_dec(v_numSectionVars_5172_);
lean_dec_ref(v_fnNames_5171_);
v_r_5175_ = lean_box(v_res_5174_);
return v_r_5175_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__0(lean_object* v_fnNames_5176_, lean_object* v_numSectionVars_5177_, lean_object* v_as_5178_, size_t v_i_5179_, size_t v_stop_5180_){
_start:
{
uint8_t v___x_5181_; 
v___x_5181_ = lean_usize_dec_eq(v_i_5179_, v_stop_5180_);
if (v___x_5181_ == 0)
{
lean_object* v___x_5182_; uint8_t v___x_5183_; 
v___x_5182_ = lean_array_uget_borrowed(v_as_5178_, v_i_5179_);
lean_inc(v___x_5182_);
v___x_5183_ = l___private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg(v_fnNames_5176_, v_numSectionVars_5177_, v___x_5182_);
if (v___x_5183_ == 0)
{
size_t v___x_5184_; size_t v___x_5185_; 
v___x_5184_ = ((size_t)1ULL);
v___x_5185_ = lean_usize_add(v_i_5179_, v___x_5184_);
v_i_5179_ = v___x_5185_;
goto _start;
}
else
{
return v___x_5183_;
}
}
else
{
uint8_t v___x_5187_; 
v___x_5187_ = 0;
return v___x_5187_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__0___boxed(lean_object* v_fnNames_5188_, lean_object* v_numSectionVars_5189_, lean_object* v_as_5190_, lean_object* v_i_5191_, lean_object* v_stop_5192_){
_start:
{
size_t v_i_boxed_5193_; size_t v_stop_boxed_5194_; uint8_t v_res_5195_; lean_object* v_r_5196_; 
v_i_boxed_5193_ = lean_unbox_usize(v_i_5191_);
lean_dec(v_i_5191_);
v_stop_boxed_5194_ = lean_unbox_usize(v_stop_5192_);
lean_dec(v_stop_5192_);
v_res_5195_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__0(v_fnNames_5188_, v_numSectionVars_5189_, v_as_5190_, v_i_boxed_5193_, v_stop_boxed_5194_);
lean_dec_ref(v_as_5190_);
lean_dec(v_numSectionVars_5189_);
lean_dec_ref(v_fnNames_5188_);
v_r_5196_ = lean_box(v_res_5195_);
return v_r_5196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__1(lean_object* v_fnNames_5197_, lean_object* v_numSectionVars_5198_, lean_object* v___x_5199_, lean_object* v_x_5200_, lean_object* v_x_5201_, lean_object* v___y_5202_, lean_object* v___y_5203_){
_start:
{
if (lean_obj_tag(v_x_5200_) == 5)
{
lean_object* v_fn_5208_; lean_object* v_arg_5209_; lean_object* v___x_5210_; 
v_fn_5208_ = lean_ctor_get(v_x_5200_, 0);
lean_inc_ref(v_fn_5208_);
v_arg_5209_ = lean_ctor_get(v_x_5200_, 1);
lean_inc_ref(v_arg_5209_);
lean_dec_ref_known(v_x_5200_, 2);
v___x_5210_ = lean_array_push(v_x_5201_, v_arg_5209_);
v_x_5200_ = v_fn_5208_;
v_x_5201_ = v___x_5210_;
goto _start;
}
else
{
uint8_t v___x_5212_; 
v___x_5212_ = l_Lean_Expr_isConst(v_x_5200_);
if (v___x_5212_ == 0)
{
lean_dec_ref(v_x_5201_);
lean_dec_ref(v_x_5200_);
lean_dec_ref(v___x_5199_);
goto v___jp_5205_;
}
else
{
lean_object* v___x_5213_; lean_object* v___x_5214_; uint8_t v___x_5215_; 
v___x_5213_ = lean_unsigned_to_nat(0u);
v___x_5214_ = lean_array_get_size(v_x_5201_);
v___x_5215_ = lean_nat_dec_lt(v___x_5213_, v___x_5214_);
if (v___x_5215_ == 0)
{
lean_dec_ref(v_x_5201_);
lean_dec_ref(v_x_5200_);
lean_dec_ref(v___x_5199_);
goto v___jp_5205_;
}
else
{
if (v___x_5215_ == 0)
{
lean_dec_ref(v_x_5201_);
lean_dec_ref(v_x_5200_);
lean_dec_ref(v___x_5199_);
goto v___jp_5205_;
}
else
{
size_t v___x_5216_; size_t v___x_5217_; uint8_t v___x_5218_; 
v___x_5216_ = ((size_t)0ULL);
v___x_5217_ = lean_usize_of_nat(v___x_5214_);
v___x_5218_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__0(v_fnNames_5197_, v_numSectionVars_5198_, v_x_5201_, v___x_5216_, v___x_5217_);
if (v___x_5218_ == 0)
{
lean_dec_ref(v_x_5201_);
lean_dec_ref(v_x_5200_);
lean_dec_ref(v___x_5199_);
goto v___jp_5205_;
}
else
{
lean_object* v___x_5219_; uint8_t v___x_5220_; lean_object* v___x_5221_; 
v___x_5219_ = l_Lean_Expr_constName_x21(v_x_5200_);
v___x_5220_ = 0;
v___x_5221_ = l_Lean_Environment_find_x3f(v___x_5199_, v___x_5219_, v___x_5220_);
if (lean_obj_tag(v___x_5221_) == 1)
{
lean_object* v_val_5222_; 
v_val_5222_ = lean_ctor_get(v___x_5221_, 0);
lean_inc(v_val_5222_);
lean_dec_ref_known(v___x_5221_, 1);
if (lean_obj_tag(v_val_5222_) == 2)
{
lean_object* v___x_5223_; lean_object* v___x_5224_; lean_object* v___x_5226_; uint8_t v_isShared_5227_; uint8_t v_isSharedCheck_5248_; 
v___x_5223_ = l_Lean_Expr_constLevels_x21(v_x_5200_);
lean_dec_ref(v_x_5200_);
v___x_5224_ = l_Lean_Core_instantiateValueLevelParams(v_val_5222_, v___x_5223_, v___x_5212_, v___y_5202_, v___y_5203_);
v_isSharedCheck_5248_ = !lean_is_exclusive(v_val_5222_);
if (v_isSharedCheck_5248_ == 0)
{
lean_object* v_unused_5249_; 
v_unused_5249_ = lean_ctor_get(v_val_5222_, 0);
lean_dec(v_unused_5249_);
v___x_5226_ = v_val_5222_;
v_isShared_5227_ = v_isSharedCheck_5248_;
goto v_resetjp_5225_;
}
else
{
lean_dec(v_val_5222_);
v___x_5226_ = lean_box(0);
v_isShared_5227_ = v_isSharedCheck_5248_;
goto v_resetjp_5225_;
}
v_resetjp_5225_:
{
if (lean_obj_tag(v___x_5224_) == 0)
{
lean_object* v_a_5228_; lean_object* v___x_5230_; uint8_t v_isShared_5231_; uint8_t v_isSharedCheck_5239_; 
v_a_5228_ = lean_ctor_get(v___x_5224_, 0);
v_isSharedCheck_5239_ = !lean_is_exclusive(v___x_5224_);
if (v_isSharedCheck_5239_ == 0)
{
v___x_5230_ = v___x_5224_;
v_isShared_5231_ = v_isSharedCheck_5239_;
goto v_resetjp_5229_;
}
else
{
lean_inc(v_a_5228_);
lean_dec(v___x_5224_);
v___x_5230_ = lean_box(0);
v_isShared_5231_ = v_isSharedCheck_5239_;
goto v_resetjp_5229_;
}
v_resetjp_5229_:
{
lean_object* v___x_5232_; lean_object* v___x_5234_; 
v___x_5232_ = l_Lean_Expr_betaRev(v_a_5228_, v_x_5201_, v___x_5220_, v___x_5220_);
lean_dec_ref(v_x_5201_);
if (v_isShared_5227_ == 0)
{
lean_ctor_set_tag(v___x_5226_, 1);
lean_ctor_set(v___x_5226_, 0, v___x_5232_);
v___x_5234_ = v___x_5226_;
goto v_reusejp_5233_;
}
else
{
lean_object* v_reuseFailAlloc_5238_; 
v_reuseFailAlloc_5238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5238_, 0, v___x_5232_);
v___x_5234_ = v_reuseFailAlloc_5238_;
goto v_reusejp_5233_;
}
v_reusejp_5233_:
{
lean_object* v___x_5236_; 
if (v_isShared_5231_ == 0)
{
lean_ctor_set(v___x_5230_, 0, v___x_5234_);
v___x_5236_ = v___x_5230_;
goto v_reusejp_5235_;
}
else
{
lean_object* v_reuseFailAlloc_5237_; 
v_reuseFailAlloc_5237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5237_, 0, v___x_5234_);
v___x_5236_ = v_reuseFailAlloc_5237_;
goto v_reusejp_5235_;
}
v_reusejp_5235_:
{
return v___x_5236_;
}
}
}
}
else
{
lean_object* v_a_5240_; lean_object* v___x_5242_; uint8_t v_isShared_5243_; uint8_t v_isSharedCheck_5247_; 
lean_del_object(v___x_5226_);
lean_dec_ref(v_x_5201_);
v_a_5240_ = lean_ctor_get(v___x_5224_, 0);
v_isSharedCheck_5247_ = !lean_is_exclusive(v___x_5224_);
if (v_isSharedCheck_5247_ == 0)
{
v___x_5242_ = v___x_5224_;
v_isShared_5243_ = v_isSharedCheck_5247_;
goto v_resetjp_5241_;
}
else
{
lean_inc(v_a_5240_);
lean_dec(v___x_5224_);
v___x_5242_ = lean_box(0);
v_isShared_5243_ = v_isSharedCheck_5247_;
goto v_resetjp_5241_;
}
v_resetjp_5241_:
{
lean_object* v___x_5245_; 
if (v_isShared_5243_ == 0)
{
v___x_5245_ = v___x_5242_;
goto v_reusejp_5244_;
}
else
{
lean_object* v_reuseFailAlloc_5246_; 
v_reuseFailAlloc_5246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5246_, 0, v_a_5240_);
v___x_5245_ = v_reuseFailAlloc_5246_;
goto v_reusejp_5244_;
}
v_reusejp_5244_:
{
return v___x_5245_;
}
}
}
}
}
else
{
lean_dec(v_val_5222_);
lean_dec_ref(v_x_5201_);
lean_dec_ref(v_x_5200_);
goto v___jp_5205_;
}
}
else
{
lean_dec(v___x_5221_);
lean_dec_ref(v_x_5201_);
lean_dec_ref(v_x_5200_);
goto v___jp_5205_;
}
}
}
}
}
}
v___jp_5205_:
{
lean_object* v___x_5206_; lean_object* v___x_5207_; 
v___x_5206_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_5207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5207_, 0, v___x_5206_);
return v___x_5207_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__1___boxed(lean_object* v_fnNames_5250_, lean_object* v_numSectionVars_5251_, lean_object* v___x_5252_, lean_object* v_x_5253_, lean_object* v_x_5254_, lean_object* v___y_5255_, lean_object* v___y_5256_, lean_object* v___y_5257_){
_start:
{
lean_object* v_res_5258_; 
v_res_5258_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__1(v_fnNames_5250_, v_numSectionVars_5251_, v___x_5252_, v_x_5253_, v_x_5254_, v___y_5255_, v___y_5256_);
lean_dec(v___y_5256_);
lean_dec_ref(v___y_5255_);
lean_dec(v_numSectionVars_5251_);
lean_dec_ref(v_fnNames_5250_);
return v_res_5258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___lam__1(lean_object* v_fnNames_5259_, lean_object* v_numSectionVars_5260_, lean_object* v_env_5261_, lean_object* v_e_5262_, lean_object* v___y_5263_, lean_object* v___y_5264_){
_start:
{
lean_object* v___x_5266_; lean_object* v___x_5267_; lean_object* v___x_5268_; 
v___x_5266_ = l_Lean_Expr_getAppNumArgs(v_e_5262_);
v___x_5267_ = lean_mk_empty_array_with_capacity(v___x_5266_);
lean_dec(v___x_5266_);
v___x_5268_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__1(v_fnNames_5259_, v_numSectionVars_5260_, v_env_5261_, v_e_5262_, v___x_5267_, v___y_5263_, v___y_5264_);
return v___x_5268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___lam__1___boxed(lean_object* v_fnNames_5269_, lean_object* v_numSectionVars_5270_, lean_object* v_env_5271_, lean_object* v_e_5272_, lean_object* v___y_5273_, lean_object* v___y_5274_, lean_object* v___y_5275_){
_start:
{
lean_object* v_res_5276_; 
v_res_5276_ = l_Lean_Meta_unfoldIfArgIsAppOf___lam__1(v_fnNames_5269_, v_numSectionVars_5270_, v_env_5271_, v_e_5272_, v___y_5273_, v___y_5274_);
lean_dec(v___y_5274_);
lean_dec_ref(v___y_5273_);
lean_dec(v_numSectionVars_5270_);
lean_dec_ref(v_fnNames_5269_);
return v_res_5276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___lam__0(lean_object* v_fnNames_5277_, lean_object* v_numSectionVars_5278_, lean_object* v_e_5279_, lean_object* v___f_5280_, lean_object* v___y_5281_, lean_object* v___y_5282_){
_start:
{
lean_object* v___x_5284_; lean_object* v_env_5285_; lean_object* v___f_5286_; lean_object* v___x_5287_; 
v___x_5284_ = lean_st_ref_get(v___y_5282_);
v_env_5285_ = lean_ctor_get(v___x_5284_, 0);
lean_inc_ref(v_env_5285_);
lean_dec(v___x_5284_);
v___f_5286_ = lean_alloc_closure((void*)(l_Lean_Meta_unfoldIfArgIsAppOf___lam__1___boxed), 7, 3);
lean_closure_set(v___f_5286_, 0, v_fnNames_5277_);
lean_closure_set(v___f_5286_, 1, v_numSectionVars_5278_);
lean_closure_set(v___f_5286_, 2, v_env_5285_);
v___x_5287_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_5279_, v___f_5286_, v___f_5280_, v___y_5281_, v___y_5282_);
return v___x_5287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___lam__0___boxed(lean_object* v_fnNames_5288_, lean_object* v_numSectionVars_5289_, lean_object* v_e_5290_, lean_object* v___f_5291_, lean_object* v___y_5292_, lean_object* v___y_5293_, lean_object* v___y_5294_){
_start:
{
lean_object* v_res_5295_; 
v_res_5295_ = l_Lean_Meta_unfoldIfArgIsAppOf___lam__0(v_fnNames_5288_, v_numSectionVars_5289_, v_e_5290_, v___f_5291_, v___y_5292_, v___y_5293_);
lean_dec(v___y_5293_);
lean_dec_ref(v___y_5292_);
return v_res_5295_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0(lean_object* v___y_5296_, uint8_t v_isExporting_5297_, lean_object* v___x_5298_, lean_object* v_a_x3f_5299_){
_start:
{
lean_object* v___x_5301_; lean_object* v_env_5302_; lean_object* v_nextMacroScope_5303_; lean_object* v_ngen_5304_; lean_object* v_auxDeclNGen_5305_; lean_object* v_traceState_5306_; lean_object* v_messages_5307_; lean_object* v_infoState_5308_; lean_object* v_snapshotTasks_5309_; lean_object* v___x_5311_; uint8_t v_isShared_5312_; uint8_t v_isSharedCheck_5320_; 
v___x_5301_ = lean_st_ref_take(v___y_5296_);
v_env_5302_ = lean_ctor_get(v___x_5301_, 0);
v_nextMacroScope_5303_ = lean_ctor_get(v___x_5301_, 1);
v_ngen_5304_ = lean_ctor_get(v___x_5301_, 2);
v_auxDeclNGen_5305_ = lean_ctor_get(v___x_5301_, 3);
v_traceState_5306_ = lean_ctor_get(v___x_5301_, 4);
v_messages_5307_ = lean_ctor_get(v___x_5301_, 6);
v_infoState_5308_ = lean_ctor_get(v___x_5301_, 7);
v_snapshotTasks_5309_ = lean_ctor_get(v___x_5301_, 8);
v_isSharedCheck_5320_ = !lean_is_exclusive(v___x_5301_);
if (v_isSharedCheck_5320_ == 0)
{
lean_object* v_unused_5321_; 
v_unused_5321_ = lean_ctor_get(v___x_5301_, 5);
lean_dec(v_unused_5321_);
v___x_5311_ = v___x_5301_;
v_isShared_5312_ = v_isSharedCheck_5320_;
goto v_resetjp_5310_;
}
else
{
lean_inc(v_snapshotTasks_5309_);
lean_inc(v_infoState_5308_);
lean_inc(v_messages_5307_);
lean_inc(v_traceState_5306_);
lean_inc(v_auxDeclNGen_5305_);
lean_inc(v_ngen_5304_);
lean_inc(v_nextMacroScope_5303_);
lean_inc(v_env_5302_);
lean_dec(v___x_5301_);
v___x_5311_ = lean_box(0);
v_isShared_5312_ = v_isSharedCheck_5320_;
goto v_resetjp_5310_;
}
v_resetjp_5310_:
{
lean_object* v___x_5313_; lean_object* v___x_5315_; 
v___x_5313_ = l_Lean_Environment_setExporting(v_env_5302_, v_isExporting_5297_);
if (v_isShared_5312_ == 0)
{
lean_ctor_set(v___x_5311_, 5, v___x_5298_);
lean_ctor_set(v___x_5311_, 0, v___x_5313_);
v___x_5315_ = v___x_5311_;
goto v_reusejp_5314_;
}
else
{
lean_object* v_reuseFailAlloc_5319_; 
v_reuseFailAlloc_5319_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5319_, 0, v___x_5313_);
lean_ctor_set(v_reuseFailAlloc_5319_, 1, v_nextMacroScope_5303_);
lean_ctor_set(v_reuseFailAlloc_5319_, 2, v_ngen_5304_);
lean_ctor_set(v_reuseFailAlloc_5319_, 3, v_auxDeclNGen_5305_);
lean_ctor_set(v_reuseFailAlloc_5319_, 4, v_traceState_5306_);
lean_ctor_set(v_reuseFailAlloc_5319_, 5, v___x_5298_);
lean_ctor_set(v_reuseFailAlloc_5319_, 6, v_messages_5307_);
lean_ctor_set(v_reuseFailAlloc_5319_, 7, v_infoState_5308_);
lean_ctor_set(v_reuseFailAlloc_5319_, 8, v_snapshotTasks_5309_);
v___x_5315_ = v_reuseFailAlloc_5319_;
goto v_reusejp_5314_;
}
v_reusejp_5314_:
{
lean_object* v___x_5316_; lean_object* v___x_5317_; lean_object* v___x_5318_; 
v___x_5316_ = lean_st_ref_set(v___y_5296_, v___x_5315_);
v___x_5317_ = lean_box(0);
v___x_5318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5318_, 0, v___x_5317_);
return v___x_5318_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0___boxed(lean_object* v___y_5322_, lean_object* v_isExporting_5323_, lean_object* v___x_5324_, lean_object* v_a_x3f_5325_, lean_object* v___y_5326_){
_start:
{
uint8_t v_isExporting_boxed_5327_; lean_object* v_res_5328_; 
v_isExporting_boxed_5327_ = lean_unbox(v_isExporting_5323_);
v_res_5328_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0(v___y_5322_, v_isExporting_boxed_5327_, v___x_5324_, v_a_x3f_5325_);
lean_dec(v_a_x3f_5325_);
lean_dec(v___y_5322_);
return v_res_5328_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg(lean_object* v_x_5329_, uint8_t v_isExporting_5330_, lean_object* v___y_5331_, lean_object* v___y_5332_){
_start:
{
lean_object* v___x_5334_; lean_object* v_env_5335_; uint8_t v_isExporting_5336_; uint8_t v___y_5388_; lean_object* v___x_5390_; uint8_t v_isModule_5391_; uint8_t v___x_5392_; 
v___x_5334_ = lean_st_ref_get(v___y_5332_);
v_env_5335_ = lean_ctor_get(v___x_5334_, 0);
lean_inc_ref(v_env_5335_);
lean_dec(v___x_5334_);
v_isExporting_5336_ = lean_ctor_get_uint8(v_env_5335_, sizeof(void*)*8);
v___x_5390_ = l_Lean_Environment_header(v_env_5335_);
lean_dec_ref(v_env_5335_);
v_isModule_5391_ = lean_ctor_get_uint8(v___x_5390_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_5390_);
v___x_5392_ = lean_bool_not(v_isModule_5391_);
if (v___x_5392_ == 0)
{
if (v_isExporting_5336_ == 0)
{
if (v_isExporting_5330_ == 0)
{
lean_object* v___x_5393_; 
lean_inc(v___y_5332_);
lean_inc_ref(v___y_5331_);
v___x_5393_ = lean_apply_3(v_x_5329_, v___y_5331_, v___y_5332_, lean_box(0));
return v___x_5393_;
}
else
{
goto v___jp_5337_;
}
}
else
{
v___y_5388_ = v_isExporting_5330_;
goto v___jp_5387_;
}
}
else
{
v___y_5388_ = v___x_5392_;
goto v___jp_5387_;
}
v___jp_5337_:
{
lean_object* v___x_5338_; lean_object* v_env_5339_; lean_object* v_nextMacroScope_5340_; lean_object* v_ngen_5341_; lean_object* v_auxDeclNGen_5342_; lean_object* v_traceState_5343_; lean_object* v_messages_5344_; lean_object* v_infoState_5345_; lean_object* v_snapshotTasks_5346_; lean_object* v___x_5348_; uint8_t v_isShared_5349_; uint8_t v_isSharedCheck_5385_; 
v___x_5338_ = lean_st_ref_take(v___y_5332_);
v_env_5339_ = lean_ctor_get(v___x_5338_, 0);
v_nextMacroScope_5340_ = lean_ctor_get(v___x_5338_, 1);
v_ngen_5341_ = lean_ctor_get(v___x_5338_, 2);
v_auxDeclNGen_5342_ = lean_ctor_get(v___x_5338_, 3);
v_traceState_5343_ = lean_ctor_get(v___x_5338_, 4);
v_messages_5344_ = lean_ctor_get(v___x_5338_, 6);
v_infoState_5345_ = lean_ctor_get(v___x_5338_, 7);
v_snapshotTasks_5346_ = lean_ctor_get(v___x_5338_, 8);
v_isSharedCheck_5385_ = !lean_is_exclusive(v___x_5338_);
if (v_isSharedCheck_5385_ == 0)
{
lean_object* v_unused_5386_; 
v_unused_5386_ = lean_ctor_get(v___x_5338_, 5);
lean_dec(v_unused_5386_);
v___x_5348_ = v___x_5338_;
v_isShared_5349_ = v_isSharedCheck_5385_;
goto v_resetjp_5347_;
}
else
{
lean_inc(v_snapshotTasks_5346_);
lean_inc(v_infoState_5345_);
lean_inc(v_messages_5344_);
lean_inc(v_traceState_5343_);
lean_inc(v_auxDeclNGen_5342_);
lean_inc(v_ngen_5341_);
lean_inc(v_nextMacroScope_5340_);
lean_inc(v_env_5339_);
lean_dec(v___x_5338_);
v___x_5348_ = lean_box(0);
v_isShared_5349_ = v_isSharedCheck_5385_;
goto v_resetjp_5347_;
}
v_resetjp_5347_:
{
lean_object* v___x_5350_; lean_object* v___x_5351_; lean_object* v___x_5353_; 
v___x_5350_ = l_Lean_Environment_setExporting(v_env_5339_, v_isExporting_5330_);
v___x_5351_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2, &l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2);
if (v_isShared_5349_ == 0)
{
lean_ctor_set(v___x_5348_, 5, v___x_5351_);
lean_ctor_set(v___x_5348_, 0, v___x_5350_);
v___x_5353_ = v___x_5348_;
goto v_reusejp_5352_;
}
else
{
lean_object* v_reuseFailAlloc_5384_; 
v_reuseFailAlloc_5384_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5384_, 0, v___x_5350_);
lean_ctor_set(v_reuseFailAlloc_5384_, 1, v_nextMacroScope_5340_);
lean_ctor_set(v_reuseFailAlloc_5384_, 2, v_ngen_5341_);
lean_ctor_set(v_reuseFailAlloc_5384_, 3, v_auxDeclNGen_5342_);
lean_ctor_set(v_reuseFailAlloc_5384_, 4, v_traceState_5343_);
lean_ctor_set(v_reuseFailAlloc_5384_, 5, v___x_5351_);
lean_ctor_set(v_reuseFailAlloc_5384_, 6, v_messages_5344_);
lean_ctor_set(v_reuseFailAlloc_5384_, 7, v_infoState_5345_);
lean_ctor_set(v_reuseFailAlloc_5384_, 8, v_snapshotTasks_5346_);
v___x_5353_ = v_reuseFailAlloc_5384_;
goto v_reusejp_5352_;
}
v_reusejp_5352_:
{
lean_object* v___x_5354_; lean_object* v_r_5355_; 
v___x_5354_ = lean_st_ref_set(v___y_5332_, v___x_5353_);
lean_inc(v___y_5332_);
lean_inc_ref(v___y_5331_);
v_r_5355_ = lean_apply_3(v_x_5329_, v___y_5331_, v___y_5332_, lean_box(0));
if (lean_obj_tag(v_r_5355_) == 0)
{
lean_object* v_a_5356_; lean_object* v___x_5358_; uint8_t v_isShared_5359_; uint8_t v_isSharedCheck_5372_; 
v_a_5356_ = lean_ctor_get(v_r_5355_, 0);
v_isSharedCheck_5372_ = !lean_is_exclusive(v_r_5355_);
if (v_isSharedCheck_5372_ == 0)
{
v___x_5358_ = v_r_5355_;
v_isShared_5359_ = v_isSharedCheck_5372_;
goto v_resetjp_5357_;
}
else
{
lean_inc(v_a_5356_);
lean_dec(v_r_5355_);
v___x_5358_ = lean_box(0);
v_isShared_5359_ = v_isSharedCheck_5372_;
goto v_resetjp_5357_;
}
v_resetjp_5357_:
{
lean_object* v___x_5361_; 
lean_inc(v_a_5356_);
if (v_isShared_5359_ == 0)
{
lean_ctor_set_tag(v___x_5358_, 1);
v___x_5361_ = v___x_5358_;
goto v_reusejp_5360_;
}
else
{
lean_object* v_reuseFailAlloc_5371_; 
v_reuseFailAlloc_5371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5371_, 0, v_a_5356_);
v___x_5361_ = v_reuseFailAlloc_5371_;
goto v_reusejp_5360_;
}
v_reusejp_5360_:
{
lean_object* v___x_5362_; lean_object* v___x_5364_; uint8_t v_isShared_5365_; uint8_t v_isSharedCheck_5369_; 
v___x_5362_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0(v___y_5332_, v_isExporting_5336_, v___x_5351_, v___x_5361_);
lean_dec_ref(v___x_5361_);
v_isSharedCheck_5369_ = !lean_is_exclusive(v___x_5362_);
if (v_isSharedCheck_5369_ == 0)
{
lean_object* v_unused_5370_; 
v_unused_5370_ = lean_ctor_get(v___x_5362_, 0);
lean_dec(v_unused_5370_);
v___x_5364_ = v___x_5362_;
v_isShared_5365_ = v_isSharedCheck_5369_;
goto v_resetjp_5363_;
}
else
{
lean_dec(v___x_5362_);
v___x_5364_ = lean_box(0);
v_isShared_5365_ = v_isSharedCheck_5369_;
goto v_resetjp_5363_;
}
v_resetjp_5363_:
{
lean_object* v___x_5367_; 
if (v_isShared_5365_ == 0)
{
lean_ctor_set(v___x_5364_, 0, v_a_5356_);
v___x_5367_ = v___x_5364_;
goto v_reusejp_5366_;
}
else
{
lean_object* v_reuseFailAlloc_5368_; 
v_reuseFailAlloc_5368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5368_, 0, v_a_5356_);
v___x_5367_ = v_reuseFailAlloc_5368_;
goto v_reusejp_5366_;
}
v_reusejp_5366_:
{
return v___x_5367_;
}
}
}
}
}
else
{
lean_object* v_a_5373_; lean_object* v___x_5374_; lean_object* v___x_5375_; lean_object* v___x_5377_; uint8_t v_isShared_5378_; uint8_t v_isSharedCheck_5382_; 
v_a_5373_ = lean_ctor_get(v_r_5355_, 0);
lean_inc(v_a_5373_);
lean_dec_ref_known(v_r_5355_, 1);
v___x_5374_ = lean_box(0);
v___x_5375_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0(v___y_5332_, v_isExporting_5336_, v___x_5351_, v___x_5374_);
v_isSharedCheck_5382_ = !lean_is_exclusive(v___x_5375_);
if (v_isSharedCheck_5382_ == 0)
{
lean_object* v_unused_5383_; 
v_unused_5383_ = lean_ctor_get(v___x_5375_, 0);
lean_dec(v_unused_5383_);
v___x_5377_ = v___x_5375_;
v_isShared_5378_ = v_isSharedCheck_5382_;
goto v_resetjp_5376_;
}
else
{
lean_dec(v___x_5375_);
v___x_5377_ = lean_box(0);
v_isShared_5378_ = v_isSharedCheck_5382_;
goto v_resetjp_5376_;
}
v_resetjp_5376_:
{
lean_object* v___x_5380_; 
if (v_isShared_5378_ == 0)
{
lean_ctor_set_tag(v___x_5377_, 1);
lean_ctor_set(v___x_5377_, 0, v_a_5373_);
v___x_5380_ = v___x_5377_;
goto v_reusejp_5379_;
}
else
{
lean_object* v_reuseFailAlloc_5381_; 
v_reuseFailAlloc_5381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5381_, 0, v_a_5373_);
v___x_5380_ = v_reuseFailAlloc_5381_;
goto v_reusejp_5379_;
}
v_reusejp_5379_:
{
return v___x_5380_;
}
}
}
}
}
}
v___jp_5387_:
{
if (v___y_5388_ == 0)
{
goto v___jp_5337_;
}
else
{
lean_object* v___x_5389_; 
lean_inc(v___y_5332_);
lean_inc_ref(v___y_5331_);
v___x_5389_ = lean_apply_3(v_x_5329_, v___y_5331_, v___y_5332_, lean_box(0));
return v___x_5389_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___boxed(lean_object* v_x_5394_, lean_object* v_isExporting_5395_, lean_object* v___y_5396_, lean_object* v___y_5397_, lean_object* v___y_5398_){
_start:
{
uint8_t v_isExporting_boxed_5399_; lean_object* v_res_5400_; 
v_isExporting_boxed_5399_ = lean_unbox(v_isExporting_5395_);
v_res_5400_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg(v_x_5394_, v_isExporting_boxed_5399_, v___y_5396_, v___y_5397_);
lean_dec(v___y_5397_);
lean_dec_ref(v___y_5396_);
return v_res_5400_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg(lean_object* v_x_5401_, uint8_t v_when_5402_, lean_object* v___y_5403_, lean_object* v___y_5404_){
_start:
{
if (v_when_5402_ == 0)
{
lean_object* v___x_5406_; 
lean_inc(v___y_5404_);
lean_inc_ref(v___y_5403_);
v___x_5406_ = lean_apply_3(v_x_5401_, v___y_5403_, v___y_5404_, lean_box(0));
return v___x_5406_;
}
else
{
uint8_t v___x_5407_; lean_object* v___x_5408_; 
v___x_5407_ = 0;
v___x_5408_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg(v_x_5401_, v___x_5407_, v___y_5403_, v___y_5404_);
return v___x_5408_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg___boxed(lean_object* v_x_5409_, lean_object* v_when_5410_, lean_object* v___y_5411_, lean_object* v___y_5412_, lean_object* v___y_5413_){
_start:
{
uint8_t v_when_boxed_5414_; lean_object* v_res_5415_; 
v_when_boxed_5414_ = lean_unbox(v_when_5410_);
v_res_5415_ = l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg(v_x_5409_, v_when_boxed_5414_, v___y_5411_, v___y_5412_);
lean_dec(v___y_5412_);
lean_dec_ref(v___y_5411_);
return v_res_5415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf(lean_object* v_fnNames_5416_, lean_object* v_numSectionVars_5417_, lean_object* v_e_5418_, lean_object* v_a_5419_, lean_object* v_a_5420_){
_start:
{
lean_object* v___f_5422_; lean_object* v___f_5423_; uint8_t v___x_5424_; lean_object* v___x_5425_; 
v___f_5422_ = ((lean_object*)(l_Lean_Core_betaReduce___closed__1));
v___f_5423_ = lean_alloc_closure((void*)(l_Lean_Meta_unfoldIfArgIsAppOf___lam__0___boxed), 7, 4);
lean_closure_set(v___f_5423_, 0, v_fnNames_5416_);
lean_closure_set(v___f_5423_, 1, v_numSectionVars_5417_);
lean_closure_set(v___f_5423_, 2, v_e_5418_);
lean_closure_set(v___f_5423_, 3, v___f_5422_);
v___x_5424_ = 1;
v___x_5425_ = l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg(v___f_5423_, v___x_5424_, v_a_5419_, v_a_5420_);
return v___x_5425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___boxed(lean_object* v_fnNames_5426_, lean_object* v_numSectionVars_5427_, lean_object* v_e_5428_, lean_object* v_a_5429_, lean_object* v_a_5430_, lean_object* v_a_5431_){
_start:
{
lean_object* v_res_5432_; 
v_res_5432_ = l_Lean_Meta_unfoldIfArgIsAppOf(v_fnNames_5426_, v_numSectionVars_5427_, v_e_5428_, v_a_5429_, v_a_5430_);
lean_dec(v_a_5430_);
lean_dec_ref(v_a_5429_);
return v_res_5432_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2(lean_object* v_00_u03b1_5433_, lean_object* v_x_5434_, uint8_t v_isExporting_5435_, lean_object* v___y_5436_, lean_object* v___y_5437_){
_start:
{
lean_object* v___x_5439_; 
v___x_5439_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg(v_x_5434_, v_isExporting_5435_, v___y_5436_, v___y_5437_);
return v___x_5439_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___boxed(lean_object* v_00_u03b1_5440_, lean_object* v_x_5441_, lean_object* v_isExporting_5442_, lean_object* v___y_5443_, lean_object* v___y_5444_, lean_object* v___y_5445_){
_start:
{
uint8_t v_isExporting_boxed_5446_; lean_object* v_res_5447_; 
v_isExporting_boxed_5446_ = lean_unbox(v_isExporting_5442_);
v_res_5447_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2(v_00_u03b1_5440_, v_x_5441_, v_isExporting_boxed_5446_, v___y_5443_, v___y_5444_);
lean_dec(v___y_5444_);
lean_dec_ref(v___y_5443_);
return v_res_5447_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2(lean_object* v_00_u03b1_5448_, lean_object* v_x_5449_, uint8_t v_when_5450_, lean_object* v___y_5451_, lean_object* v___y_5452_){
_start:
{
lean_object* v___x_5454_; 
v___x_5454_ = l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg(v_x_5449_, v_when_5450_, v___y_5451_, v___y_5452_);
return v___x_5454_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___boxed(lean_object* v_00_u03b1_5455_, lean_object* v_x_5456_, lean_object* v_when_5457_, lean_object* v___y_5458_, lean_object* v___y_5459_, lean_object* v___y_5460_){
_start:
{
uint8_t v_when_boxed_5461_; lean_object* v_res_5462_; 
v_when_boxed_5461_ = lean_unbox(v_when_5457_);
v_res_5462_ = l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2(v_00_u03b1_5455_, v_x_5456_, v_when_boxed_5461_, v___y_5458_, v___y_5459_);
lean_dec(v___y_5459_);
lean_dec_ref(v___y_5458_);
return v_res_5462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___lam__0(lean_object* v_x_5463_, lean_object* v___y_5464_, lean_object* v___y_5465_){
_start:
{
lean_object* v___x_5467_; lean_object* v___x_5468_; 
v___x_5467_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_5468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5468_, 0, v___x_5467_);
return v___x_5468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___lam__0___boxed(lean_object* v_x_5469_, lean_object* v___y_5470_, lean_object* v___y_5471_, lean_object* v___y_5472_){
_start:
{
lean_object* v_res_5473_; 
v_res_5473_ = l_Lean_Meta_eraseInaccessibleAnnotations___lam__0(v_x_5469_, v___y_5470_, v___y_5471_);
lean_dec(v___y_5471_);
lean_dec_ref(v___y_5470_);
lean_dec_ref(v_x_5469_);
return v_res_5473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___lam__1(lean_object* v_e_5474_, lean_object* v___y_5475_, lean_object* v___y_5476_){
_start:
{
lean_object* v___y_5479_; lean_object* v___x_5482_; 
v___x_5482_ = l_Lean_inaccessible_x3f(v_e_5474_);
if (lean_obj_tag(v___x_5482_) == 1)
{
lean_object* v_val_5483_; 
lean_dec_ref(v_e_5474_);
v_val_5483_ = lean_ctor_get(v___x_5482_, 0);
lean_inc(v_val_5483_);
lean_dec_ref_known(v___x_5482_, 1);
v___y_5479_ = v_val_5483_;
goto v___jp_5478_;
}
else
{
lean_dec(v___x_5482_);
v___y_5479_ = v_e_5474_;
goto v___jp_5478_;
}
v___jp_5478_:
{
lean_object* v___x_5480_; lean_object* v___x_5481_; 
v___x_5480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5480_, 0, v___y_5479_);
v___x_5481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5481_, 0, v___x_5480_);
return v___x_5481_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___lam__1___boxed(lean_object* v_e_5484_, lean_object* v___y_5485_, lean_object* v___y_5486_, lean_object* v___y_5487_){
_start:
{
lean_object* v_res_5488_; 
v_res_5488_ = l_Lean_Meta_eraseInaccessibleAnnotations___lam__1(v_e_5484_, v___y_5485_, v___y_5486_);
lean_dec(v___y_5486_);
lean_dec_ref(v___y_5485_);
return v_res_5488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations(lean_object* v_e_5491_, lean_object* v_a_5492_, lean_object* v_a_5493_){
_start:
{
lean_object* v___f_5495_; lean_object* v___f_5496_; lean_object* v___x_5497_; 
v___f_5495_ = ((lean_object*)(l_Lean_Meta_eraseInaccessibleAnnotations___closed__0));
v___f_5496_ = ((lean_object*)(l_Lean_Meta_eraseInaccessibleAnnotations___closed__1));
v___x_5497_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_5491_, v___f_5495_, v___f_5496_, v_a_5492_, v_a_5493_);
return v___x_5497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___boxed(lean_object* v_e_5498_, lean_object* v_a_5499_, lean_object* v_a_5500_, lean_object* v_a_5501_){
_start:
{
lean_object* v_res_5502_; 
v_res_5502_ = l_Lean_Meta_eraseInaccessibleAnnotations(v_e_5498_, v_a_5499_, v_a_5500_);
lean_dec(v_a_5500_);
lean_dec_ref(v_a_5499_);
return v_res_5502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_erasePatternRefAnnotations___lam__1(lean_object* v_e_5503_, lean_object* v___y_5504_, lean_object* v___y_5505_){
_start:
{
lean_object* v___y_5508_; lean_object* v___x_5511_; 
v___x_5511_ = l_Lean_patternWithRef_x3f(v_e_5503_);
if (lean_obj_tag(v___x_5511_) == 1)
{
lean_object* v_val_5512_; lean_object* v_snd_5513_; 
lean_dec_ref(v_e_5503_);
v_val_5512_ = lean_ctor_get(v___x_5511_, 0);
lean_inc(v_val_5512_);
lean_dec_ref_known(v___x_5511_, 1);
v_snd_5513_ = lean_ctor_get(v_val_5512_, 1);
lean_inc(v_snd_5513_);
lean_dec(v_val_5512_);
v___y_5508_ = v_snd_5513_;
goto v___jp_5507_;
}
else
{
lean_dec(v___x_5511_);
v___y_5508_ = v_e_5503_;
goto v___jp_5507_;
}
v___jp_5507_:
{
lean_object* v___x_5509_; lean_object* v___x_5510_; 
v___x_5509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5509_, 0, v___y_5508_);
v___x_5510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5510_, 0, v___x_5509_);
return v___x_5510_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_erasePatternRefAnnotations___lam__1___boxed(lean_object* v_e_5514_, lean_object* v___y_5515_, lean_object* v___y_5516_, lean_object* v___y_5517_){
_start:
{
lean_object* v_res_5518_; 
v_res_5518_ = l_Lean_Meta_erasePatternRefAnnotations___lam__1(v_e_5514_, v___y_5515_, v___y_5516_);
lean_dec(v___y_5516_);
lean_dec_ref(v___y_5515_);
return v_res_5518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_erasePatternRefAnnotations(lean_object* v_e_5520_, lean_object* v_a_5521_, lean_object* v_a_5522_){
_start:
{
lean_object* v___f_5524_; lean_object* v___f_5525_; lean_object* v___x_5526_; 
v___f_5524_ = ((lean_object*)(l_Lean_Meta_eraseInaccessibleAnnotations___closed__0));
v___f_5525_ = ((lean_object*)(l_Lean_Meta_erasePatternRefAnnotations___closed__0));
v___x_5526_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_5520_, v___f_5524_, v___f_5525_, v_a_5521_, v_a_5522_);
return v___x_5526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_erasePatternRefAnnotations___boxed(lean_object* v_e_5527_, lean_object* v_a_5528_, lean_object* v_a_5529_, lean_object* v_a_5530_){
_start:
{
lean_object* v_res_5531_; 
v_res_5531_ = l_Lean_Meta_erasePatternRefAnnotations(v_e_5527_, v_a_5528_, v_a_5529_);
lean_dec(v_a_5529_);
lean_dec_ref(v_a_5528_);
return v_res_5531_;
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
