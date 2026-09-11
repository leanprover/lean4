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
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
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
lean_object* v___y_1099_; lean_object* v___y_1109_; uint8_t v___y_1110_; uint8_t v___y_1111_; lean_object* v___y_1112_; lean_object* v___y_1113_; lean_object* v_toCold_1118_; lean_object* v_currRecDepth_1119_; lean_object* v_ref_1120_; uint8_t v_diag_1121_; uint8_t v_suppressElabErrors_1122_; lean_object* v_maxRecDepth_1123_; lean_object* v_cancelTk_x3f_1124_; 
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
v___x_1115_ = lean_nat_add(v___y_1112_, v___x_1114_);
lean_inc_ref(v___y_1113_);
v___x_1116_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1116_, 0, v___y_1113_);
lean_ctor_set(v___x_1116_, 1, v___x_1115_);
lean_ctor_set(v___x_1116_, 2, v___y_1109_);
lean_ctor_set_uint8(v___x_1116_, sizeof(void*)*3, v___y_1110_);
lean_ctor_set_uint8(v___x_1116_, sizeof(void*)*3 + 1, v___y_1111_);
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
v___y_1109_ = v_ref_1120_;
v___y_1110_ = v_diag_1121_;
v___y_1111_ = v_suppressElabErrors_1122_;
v___y_1112_ = v_currRecDepth_1119_;
v___y_1113_ = v_toCold_1118_;
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
v___y_1109_ = v_ref_1120_;
v___y_1110_ = v_diag_1121_;
v___y_1111_ = v_suppressElabErrors_1122_;
v___y_1112_ = v_currRecDepth_1119_;
v___y_1113_ = v_toCold_1118_;
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
lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v_nbuckets_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; 
v___x_1212_ = lean_array_get_size(v_data_1211_);
v___x_1213_ = lean_unsigned_to_nat(2u);
v_nbuckets_1214_ = lean_nat_mul(v___x_1212_, v___x_1213_);
v___x_1215_ = lean_unsigned_to_nat(0u);
v___x_1216_ = lean_box(0);
v___x_1217_ = lean_mk_array(v_nbuckets_1214_, v___x_1216_);
v___x_1218_ = lean_array_propagate_mark(v_data_1211_, v___x_1217_);
v___x_1219_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v___x_1215_, v_data_1211_, v___x_1218_);
return v___x_1219_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__12___redArg(lean_object* v_a_1220_, lean_object* v_b_1221_, lean_object* v_x_1222_){
_start:
{
if (lean_obj_tag(v_x_1222_) == 0)
{
lean_dec(v_b_1221_);
lean_dec_ref(v_a_1220_);
return v_x_1222_;
}
else
{
lean_object* v_key_1223_; lean_object* v_value_1224_; lean_object* v_tail_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1237_; 
v_key_1223_ = lean_ctor_get(v_x_1222_, 0);
v_value_1224_ = lean_ctor_get(v_x_1222_, 1);
v_tail_1225_ = lean_ctor_get(v_x_1222_, 2);
v_isSharedCheck_1237_ = !lean_is_exclusive(v_x_1222_);
if (v_isSharedCheck_1237_ == 0)
{
v___x_1227_ = v_x_1222_;
v_isShared_1228_ = v_isSharedCheck_1237_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_tail_1225_);
lean_inc(v_value_1224_);
lean_inc(v_key_1223_);
lean_dec(v_x_1222_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1237_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
uint8_t v___x_1229_; 
v___x_1229_ = l_Lean_ExprStructEq_beq(v_key_1223_, v_a_1220_);
if (v___x_1229_ == 0)
{
lean_object* v___x_1230_; lean_object* v___x_1232_; 
v___x_1230_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__12___redArg(v_a_1220_, v_b_1221_, v_tail_1225_);
if (v_isShared_1228_ == 0)
{
lean_ctor_set(v___x_1227_, 2, v___x_1230_);
v___x_1232_ = v___x_1227_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v_key_1223_);
lean_ctor_set(v_reuseFailAlloc_1233_, 1, v_value_1224_);
lean_ctor_set(v_reuseFailAlloc_1233_, 2, v___x_1230_);
v___x_1232_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
return v___x_1232_;
}
}
else
{
lean_object* v___x_1235_; 
lean_dec(v_value_1224_);
lean_dec(v_key_1223_);
if (v_isShared_1228_ == 0)
{
lean_ctor_set(v___x_1227_, 1, v_b_1221_);
lean_ctor_set(v___x_1227_, 0, v_a_1220_);
v___x_1235_ = v___x_1227_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v_a_1220_);
lean_ctor_set(v_reuseFailAlloc_1236_, 1, v_b_1221_);
lean_ctor_set(v_reuseFailAlloc_1236_, 2, v_tail_1225_);
v___x_1235_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
return v___x_1235_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6___redArg(lean_object* v_m_1238_, lean_object* v_a_1239_, lean_object* v_b_1240_){
_start:
{
lean_object* v_size_1241_; lean_object* v_buckets_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1285_; 
v_size_1241_ = lean_ctor_get(v_m_1238_, 0);
v_buckets_1242_ = lean_ctor_get(v_m_1238_, 1);
v_isSharedCheck_1285_ = !lean_is_exclusive(v_m_1238_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1244_ = v_m_1238_;
v_isShared_1245_ = v_isSharedCheck_1285_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_buckets_1242_);
lean_inc(v_size_1241_);
lean_dec(v_m_1238_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1285_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v___x_1246_; uint64_t v___x_1247_; uint64_t v___x_1248_; uint64_t v___x_1249_; uint64_t v_fold_1250_; uint64_t v___x_1251_; uint64_t v___x_1252_; uint64_t v___x_1253_; size_t v___x_1254_; size_t v___x_1255_; size_t v___x_1256_; size_t v___x_1257_; size_t v___x_1258_; lean_object* v_bkt_1259_; uint8_t v___x_1260_; 
v___x_1246_ = lean_array_get_size(v_buckets_1242_);
v___x_1247_ = l_Lean_ExprStructEq_hash(v_a_1239_);
v___x_1248_ = 32ULL;
v___x_1249_ = lean_uint64_shift_right(v___x_1247_, v___x_1248_);
v_fold_1250_ = lean_uint64_xor(v___x_1247_, v___x_1249_);
v___x_1251_ = 16ULL;
v___x_1252_ = lean_uint64_shift_right(v_fold_1250_, v___x_1251_);
v___x_1253_ = lean_uint64_xor(v_fold_1250_, v___x_1252_);
v___x_1254_ = lean_uint64_to_usize(v___x_1253_);
v___x_1255_ = lean_usize_of_nat(v___x_1246_);
v___x_1256_ = ((size_t)1ULL);
v___x_1257_ = lean_usize_sub(v___x_1255_, v___x_1256_);
v___x_1258_ = lean_usize_land(v___x_1254_, v___x_1257_);
v_bkt_1259_ = lean_array_uget_borrowed(v_buckets_1242_, v___x_1258_);
v___x_1260_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___redArg(v_a_1239_, v_bkt_1259_);
if (v___x_1260_ == 0)
{
lean_object* v___x_1261_; lean_object* v_size_x27_1262_; lean_object* v___x_1263_; lean_object* v_buckets_x27_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; uint8_t v___x_1270_; 
v___x_1261_ = lean_unsigned_to_nat(1u);
v_size_x27_1262_ = lean_nat_add(v_size_1241_, v___x_1261_);
lean_dec(v_size_1241_);
lean_inc(v_bkt_1259_);
v___x_1263_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1263_, 0, v_a_1239_);
lean_ctor_set(v___x_1263_, 1, v_b_1240_);
lean_ctor_set(v___x_1263_, 2, v_bkt_1259_);
v_buckets_x27_1264_ = lean_array_uset(v_buckets_1242_, v___x_1258_, v___x_1263_);
v___x_1265_ = lean_unsigned_to_nat(4u);
v___x_1266_ = lean_nat_mul(v_size_x27_1262_, v___x_1265_);
v___x_1267_ = lean_unsigned_to_nat(3u);
v___x_1268_ = lean_nat_div(v___x_1266_, v___x_1267_);
lean_dec(v___x_1266_);
v___x_1269_ = lean_array_get_size(v_buckets_x27_1264_);
v___x_1270_ = lean_nat_dec_le(v___x_1268_, v___x_1269_);
lean_dec(v___x_1268_);
if (v___x_1270_ == 0)
{
lean_object* v_val_1271_; lean_object* v___x_1273_; 
v_val_1271_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11___redArg(v_buckets_x27_1264_);
if (v_isShared_1245_ == 0)
{
lean_ctor_set(v___x_1244_, 1, v_val_1271_);
lean_ctor_set(v___x_1244_, 0, v_size_x27_1262_);
v___x_1273_ = v___x_1244_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v_size_x27_1262_);
lean_ctor_set(v_reuseFailAlloc_1274_, 1, v_val_1271_);
v___x_1273_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
return v___x_1273_;
}
}
else
{
lean_object* v___x_1276_; 
if (v_isShared_1245_ == 0)
{
lean_ctor_set(v___x_1244_, 1, v_buckets_x27_1264_);
lean_ctor_set(v___x_1244_, 0, v_size_x27_1262_);
v___x_1276_ = v___x_1244_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v_size_x27_1262_);
lean_ctor_set(v_reuseFailAlloc_1277_, 1, v_buckets_x27_1264_);
v___x_1276_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
return v___x_1276_;
}
}
}
else
{
lean_object* v___x_1278_; lean_object* v_buckets_x27_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1283_; 
lean_inc(v_bkt_1259_);
v___x_1278_ = lean_box(0);
v_buckets_x27_1279_ = lean_array_uset(v_buckets_1242_, v___x_1258_, v___x_1278_);
v___x_1280_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__12___redArg(v_a_1239_, v_b_1240_, v_bkt_1259_);
v___x_1281_ = lean_array_uset(v_buckets_x27_1279_, v___x_1258_, v___x_1280_);
if (v_isShared_1245_ == 0)
{
lean_ctor_set(v___x_1244_, 1, v___x_1281_);
v___x_1283_ = v___x_1244_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_size_1241_);
lean_ctor_set(v_reuseFailAlloc_1284_, 1, v___x_1281_);
v___x_1283_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
return v___x_1283_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__2(lean_object* v_a_1286_, lean_object* v_e_1287_, lean_object* v_a_1288_){
_start:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; 
v___x_1290_ = lean_st_ref_take(v_a_1286_);
v___x_1291_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6___redArg(v___x_1290_, v_e_1287_, v_a_1288_);
v___x_1292_ = lean_st_ref_put(v_a_1286_, v___x_1291_);
v___x_1293_ = lean_box(0);
return v___x_1293_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__2___boxed(lean_object* v_a_1294_, lean_object* v_e_1295_, lean_object* v_a_1296_, lean_object* v___y_1297_){
_start:
{
lean_object* v_res_1298_; 
v_res_1298_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__2(v_a_1294_, v_e_1295_, v_a_1296_);
lean_dec(v_a_1294_);
return v_res_1298_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___redArg(lean_object* v_a_1299_, lean_object* v_x_1300_){
_start:
{
if (lean_obj_tag(v_x_1300_) == 0)
{
lean_object* v___x_1301_; 
v___x_1301_ = lean_box(0);
return v___x_1301_;
}
else
{
lean_object* v_key_1302_; lean_object* v_value_1303_; lean_object* v_tail_1304_; uint8_t v___x_1305_; 
v_key_1302_ = lean_ctor_get(v_x_1300_, 0);
v_value_1303_ = lean_ctor_get(v_x_1300_, 1);
v_tail_1304_ = lean_ctor_get(v_x_1300_, 2);
v___x_1305_ = l_Lean_ExprStructEq_beq(v_key_1302_, v_a_1299_);
if (v___x_1305_ == 0)
{
v_x_1300_ = v_tail_1304_;
goto _start;
}
else
{
lean_object* v___x_1307_; 
lean_inc(v_value_1303_);
v___x_1307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1307_, 0, v_value_1303_);
return v___x_1307_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___redArg___boxed(lean_object* v_a_1308_, lean_object* v_x_1309_){
_start:
{
lean_object* v_res_1310_; 
v_res_1310_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___redArg(v_a_1308_, v_x_1309_);
lean_dec(v_x_1309_);
lean_dec_ref(v_a_1308_);
return v_res_1310_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg(lean_object* v_m_1311_, lean_object* v_a_1312_){
_start:
{
lean_object* v_buckets_1313_; lean_object* v___x_1314_; uint64_t v___x_1315_; uint64_t v___x_1316_; uint64_t v___x_1317_; uint64_t v_fold_1318_; uint64_t v___x_1319_; uint64_t v___x_1320_; uint64_t v___x_1321_; size_t v___x_1322_; size_t v___x_1323_; size_t v___x_1324_; size_t v___x_1325_; size_t v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; 
v_buckets_1313_ = lean_ctor_get(v_m_1311_, 1);
v___x_1314_ = lean_array_get_size(v_buckets_1313_);
v___x_1315_ = l_Lean_ExprStructEq_hash(v_a_1312_);
v___x_1316_ = 32ULL;
v___x_1317_ = lean_uint64_shift_right(v___x_1315_, v___x_1316_);
v_fold_1318_ = lean_uint64_xor(v___x_1315_, v___x_1317_);
v___x_1319_ = 16ULL;
v___x_1320_ = lean_uint64_shift_right(v_fold_1318_, v___x_1319_);
v___x_1321_ = lean_uint64_xor(v_fold_1318_, v___x_1320_);
v___x_1322_ = lean_uint64_to_usize(v___x_1321_);
v___x_1323_ = lean_usize_of_nat(v___x_1314_);
v___x_1324_ = ((size_t)1ULL);
v___x_1325_ = lean_usize_sub(v___x_1323_, v___x_1324_);
v___x_1326_ = lean_usize_land(v___x_1322_, v___x_1325_);
v___x_1327_ = lean_array_uget_borrowed(v_buckets_1313_, v___x_1326_);
v___x_1328_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___redArg(v_a_1312_, v___x_1327_);
return v___x_1328_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_m_1329_, lean_object* v_a_1330_){
_start:
{
lean_object* v_res_1331_; 
v_res_1331_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg(v_m_1329_, v_a_1330_);
lean_dec_ref(v_a_1330_);
lean_dec_ref(v_m_1329_);
return v_res_1331_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1(lean_object* v_pre_1332_, lean_object* v_post_1333_, size_t v_sz_1334_, size_t v_i_1335_, lean_object* v_bs_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_){
_start:
{
uint8_t v___x_1341_; 
v___x_1341_ = lean_usize_dec_lt(v_i_1335_, v_sz_1334_);
if (v___x_1341_ == 0)
{
lean_object* v___x_1342_; 
lean_dec_ref(v_post_1333_);
lean_dec_ref(v_pre_1332_);
v___x_1342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1342_, 0, v_bs_1336_);
return v___x_1342_;
}
else
{
lean_object* v_v_1343_; lean_object* v___x_1344_; 
v_v_1343_ = lean_array_uget_borrowed(v_bs_1336_, v_i_1335_);
lean_inc(v_v_1343_);
lean_inc_ref(v_post_1333_);
lean_inc_ref(v_pre_1332_);
v___x_1344_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1332_, v_post_1333_, v_v_1343_, v___y_1337_, v___y_1338_, v___y_1339_);
if (lean_obj_tag(v___x_1344_) == 0)
{
lean_object* v_a_1345_; lean_object* v___x_1346_; lean_object* v_bs_x27_1347_; size_t v___x_1348_; size_t v___x_1349_; lean_object* v___x_1350_; 
v_a_1345_ = lean_ctor_get(v___x_1344_, 0);
lean_inc(v_a_1345_);
lean_dec_ref_known(v___x_1344_, 1);
v___x_1346_ = lean_unsigned_to_nat(0u);
v_bs_x27_1347_ = lean_array_uset(v_bs_1336_, v_i_1335_, v___x_1346_);
v___x_1348_ = ((size_t)1ULL);
v___x_1349_ = lean_usize_add(v_i_1335_, v___x_1348_);
v___x_1350_ = lean_array_uset(v_bs_x27_1347_, v_i_1335_, v_a_1345_);
v_i_1335_ = v___x_1349_;
v_bs_1336_ = v___x_1350_;
goto _start;
}
else
{
lean_object* v_a_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1359_; 
lean_dec_ref(v_bs_1336_);
lean_dec_ref(v_post_1333_);
lean_dec_ref(v_pre_1332_);
v_a_1352_ = lean_ctor_get(v___x_1344_, 0);
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1344_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1354_ = v___x_1344_;
v_isShared_1355_ = v_isSharedCheck_1359_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_a_1352_);
lean_dec(v___x_1344_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1359_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v___x_1357_; 
if (v_isShared_1355_ == 0)
{
v___x_1357_ = v___x_1354_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v_a_1352_);
v___x_1357_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
return v___x_1357_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__4(lean_object* v_pre_1360_, lean_object* v_post_1361_, lean_object* v_x_1362_, lean_object* v_x_1363_, lean_object* v_x_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_){
_start:
{
if (lean_obj_tag(v_x_1362_) == 5)
{
lean_object* v_fn_1369_; lean_object* v_arg_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; 
v_fn_1369_ = lean_ctor_get(v_x_1362_, 0);
lean_inc_ref(v_fn_1369_);
v_arg_1370_ = lean_ctor_get(v_x_1362_, 1);
lean_inc_ref(v_arg_1370_);
lean_dec_ref_known(v_x_1362_, 2);
v___x_1371_ = lean_array_set(v_x_1363_, v_x_1364_, v_arg_1370_);
v___x_1372_ = lean_unsigned_to_nat(1u);
v___x_1373_ = lean_nat_sub(v_x_1364_, v___x_1372_);
lean_dec(v_x_1364_);
v_x_1362_ = v_fn_1369_;
v_x_1363_ = v___x_1371_;
v_x_1364_ = v___x_1373_;
goto _start;
}
else
{
lean_object* v___x_1375_; 
lean_dec(v_x_1364_);
lean_inc_ref(v_post_1361_);
lean_inc_ref(v_pre_1360_);
v___x_1375_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1360_, v_post_1361_, v_x_1362_, v___y_1365_, v___y_1366_, v___y_1367_);
if (lean_obj_tag(v___x_1375_) == 0)
{
lean_object* v_a_1376_; size_t v_sz_1377_; size_t v___x_1378_; lean_object* v___x_1379_; 
v_a_1376_ = lean_ctor_get(v___x_1375_, 0);
lean_inc(v_a_1376_);
lean_dec_ref_known(v___x_1375_, 1);
v_sz_1377_ = lean_array_size(v_x_1363_);
v___x_1378_ = ((size_t)0ULL);
lean_inc_ref(v_post_1361_);
lean_inc_ref(v_pre_1360_);
v___x_1379_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1(v_pre_1360_, v_post_1361_, v_sz_1377_, v___x_1378_, v_x_1363_, v___y_1365_, v___y_1366_, v___y_1367_);
if (lean_obj_tag(v___x_1379_) == 0)
{
lean_object* v_a_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; 
v_a_1380_ = lean_ctor_get(v___x_1379_, 0);
lean_inc(v_a_1380_);
lean_dec_ref_known(v___x_1379_, 1);
v___x_1381_ = l_Lean_mkAppN(v_a_1376_, v_a_1380_);
lean_dec(v_a_1380_);
v___x_1382_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1360_, v_post_1361_, v___x_1381_, v___y_1365_, v___y_1366_, v___y_1367_);
return v___x_1382_;
}
else
{
lean_object* v_a_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1390_; 
lean_dec(v_a_1376_);
lean_dec_ref(v_post_1361_);
lean_dec_ref(v_pre_1360_);
v_a_1383_ = lean_ctor_get(v___x_1379_, 0);
v_isSharedCheck_1390_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1390_ == 0)
{
v___x_1385_ = v___x_1379_;
v_isShared_1386_ = v_isSharedCheck_1390_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_a_1383_);
lean_dec(v___x_1379_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1390_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
lean_object* v___x_1388_; 
if (v_isShared_1386_ == 0)
{
v___x_1388_ = v___x_1385_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v_a_1383_);
v___x_1388_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
return v___x_1388_;
}
}
}
}
else
{
lean_dec_ref(v_x_1363_);
lean_dec_ref(v_post_1361_);
lean_dec_ref(v_pre_1360_);
return v___x_1375_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__1(lean_object* v___x_1391_, lean_object* v_pre_1392_, lean_object* v_e_1393_, lean_object* v_post_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_){
_start:
{
lean_object* v___x_1399_; 
v___x_1399_ = l_Lean_Core_checkSystem(v___x_1391_, v___y_1396_, v___y_1397_);
if (lean_obj_tag(v___x_1399_) == 0)
{
lean_object* v___x_1400_; 
lean_dec_ref_known(v___x_1399_, 1);
lean_inc_ref(v_pre_1392_);
lean_inc(v___y_1397_);
lean_inc_ref(v___y_1396_);
lean_inc_ref(v_e_1393_);
v___x_1400_ = lean_apply_4(v_pre_1392_, v_e_1393_, v___y_1396_, v___y_1397_, lean_box(0));
if (lean_obj_tag(v___x_1400_) == 0)
{
lean_object* v_a_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1516_; 
v_a_1401_ = lean_ctor_get(v___x_1400_, 0);
v_isSharedCheck_1516_ = !lean_is_exclusive(v___x_1400_);
if (v_isSharedCheck_1516_ == 0)
{
v___x_1403_ = v___x_1400_;
v_isShared_1404_ = v_isSharedCheck_1516_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_a_1401_);
lean_dec(v___x_1400_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1516_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___y_1406_; 
switch(lean_obj_tag(v_a_1401_))
{
case 0:
{
lean_object* v_e_1506_; lean_object* v___x_1508_; 
lean_dec_ref(v_post_1394_);
lean_dec_ref(v_e_1393_);
lean_dec_ref(v_pre_1392_);
v_e_1506_ = lean_ctor_get(v_a_1401_, 0);
lean_inc_ref(v_e_1506_);
lean_dec_ref_known(v_a_1401_, 1);
if (v_isShared_1404_ == 0)
{
lean_ctor_set(v___x_1403_, 0, v_e_1506_);
v___x_1508_ = v___x_1403_;
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
lean_del_object(v___x_1403_);
lean_dec_ref(v_e_1393_);
v_e_1510_ = lean_ctor_get(v_a_1401_, 0);
lean_inc_ref(v_e_1510_);
lean_dec_ref_known(v_a_1401_, 1);
lean_inc_ref(v_post_1394_);
lean_inc_ref(v_pre_1392_);
v___x_1511_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1392_, v_post_1394_, v_e_1510_, v___y_1395_, v___y_1396_, v___y_1397_);
if (lean_obj_tag(v___x_1511_) == 0)
{
lean_object* v_a_1512_; lean_object* v___x_1513_; 
v_a_1512_ = lean_ctor_get(v___x_1511_, 0);
lean_inc(v_a_1512_);
lean_dec_ref_known(v___x_1511_, 1);
v___x_1513_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1392_, v_post_1394_, v_a_1512_, v___y_1395_, v___y_1396_, v___y_1397_);
return v___x_1513_;
}
else
{
lean_dec_ref(v_post_1394_);
lean_dec_ref(v_pre_1392_);
return v___x_1511_;
}
}
default: 
{
lean_object* v_e_x3f_1514_; 
lean_del_object(v___x_1403_);
v_e_x3f_1514_ = lean_ctor_get(v_a_1401_, 0);
lean_inc(v_e_x3f_1514_);
lean_dec_ref_known(v_a_1401_, 1);
if (lean_obj_tag(v_e_x3f_1514_) == 0)
{
v___y_1406_ = v_e_1393_;
goto v___jp_1405_;
}
else
{
lean_object* v_val_1515_; 
lean_dec_ref(v_e_1393_);
v_val_1515_ = lean_ctor_get(v_e_x3f_1514_, 0);
lean_inc(v_val_1515_);
lean_dec_ref_known(v_e_x3f_1514_, 1);
v___y_1406_ = v_val_1515_;
goto v___jp_1405_;
}
}
}
v___jp_1405_:
{
switch(lean_obj_tag(v___y_1406_))
{
case 7:
{
lean_object* v_binderName_1407_; lean_object* v_binderType_1408_; lean_object* v_body_1409_; uint8_t v_binderInfo_1410_; lean_object* v___x_1411_; 
v_binderName_1407_ = lean_ctor_get(v___y_1406_, 0);
v_binderType_1408_ = lean_ctor_get(v___y_1406_, 1);
v_body_1409_ = lean_ctor_get(v___y_1406_, 2);
v_binderInfo_1410_ = lean_ctor_get_uint8(v___y_1406_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1408_);
lean_inc_ref(v_post_1394_);
lean_inc_ref(v_pre_1392_);
v___x_1411_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1392_, v_post_1394_, v_binderType_1408_, v___y_1395_, v___y_1396_, v___y_1397_);
if (lean_obj_tag(v___x_1411_) == 0)
{
lean_object* v_a_1412_; lean_object* v___x_1413_; 
v_a_1412_ = lean_ctor_get(v___x_1411_, 0);
lean_inc(v_a_1412_);
lean_dec_ref_known(v___x_1411_, 1);
lean_inc_ref(v_body_1409_);
lean_inc_ref(v_post_1394_);
lean_inc_ref(v_pre_1392_);
v___x_1413_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1392_, v_post_1394_, v_body_1409_, v___y_1395_, v___y_1396_, v___y_1397_);
if (lean_obj_tag(v___x_1413_) == 0)
{
lean_object* v_a_1414_; size_t v___x_1415_; size_t v___x_1416_; uint8_t v___x_1417_; 
v_a_1414_ = lean_ctor_get(v___x_1413_, 0);
lean_inc(v_a_1414_);
lean_dec_ref_known(v___x_1413_, 1);
v___x_1415_ = lean_ptr_addr(v_binderType_1408_);
v___x_1416_ = lean_ptr_addr(v_a_1412_);
v___x_1417_ = lean_usize_dec_eq(v___x_1415_, v___x_1416_);
if (v___x_1417_ == 0)
{
lean_object* v___x_1418_; lean_object* v___x_1419_; 
lean_inc(v_binderName_1407_);
lean_dec_ref_known(v___y_1406_, 3);
v___x_1418_ = l_Lean_Expr_forallE___override(v_binderName_1407_, v_a_1412_, v_a_1414_, v_binderInfo_1410_);
v___x_1419_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1392_, v_post_1394_, v___x_1418_, v___y_1395_, v___y_1396_, v___y_1397_);
return v___x_1419_;
}
else
{
size_t v___x_1420_; size_t v___x_1421_; uint8_t v___x_1422_; 
v___x_1420_ = lean_ptr_addr(v_body_1409_);
v___x_1421_ = lean_ptr_addr(v_a_1414_);
v___x_1422_ = lean_usize_dec_eq(v___x_1420_, v___x_1421_);
if (v___x_1422_ == 0)
{
lean_object* v___x_1423_; lean_object* v___x_1424_; 
lean_inc(v_binderName_1407_);
lean_dec_ref_known(v___y_1406_, 3);
v___x_1423_ = l_Lean_Expr_forallE___override(v_binderName_1407_, v_a_1412_, v_a_1414_, v_binderInfo_1410_);
v___x_1424_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1392_, v_post_1394_, v___x_1423_, v___y_1395_, v___y_1396_, v___y_1397_);
return v___x_1424_;
}
else
{
uint8_t v___x_1425_; 
v___x_1425_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1410_, v_binderInfo_1410_);
if (v___x_1425_ == 0)
{
lean_object* v___x_1426_; lean_object* v___x_1427_; 
lean_inc(v_binderName_1407_);
lean_dec_ref_known(v___y_1406_, 3);
v___x_1426_ = l_Lean_Expr_forallE___override(v_binderName_1407_, v_a_1412_, v_a_1414_, v_binderInfo_1410_);
v___x_1427_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1392_, v_post_1394_, v___x_1426_, v___y_1395_, v___y_1396_, v___y_1397_);
return v___x_1427_;
}
else
{
lean_object* v___x_1428_; 
lean_dec(v_a_1414_);
lean_dec(v_a_1412_);
v___x_1428_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1392_, v_post_1394_, v___y_1406_, v___y_1395_, v___y_1396_, v___y_1397_);
return v___x_1428_;
}
}
}
}
else
{
lean_dec(v_a_1412_);
lean_dec_ref_known(v___y_1406_, 3);
lean_dec_ref(v_post_1394_);
lean_dec_ref(v_pre_1392_);
return v___x_1413_;
}
}
else
{
lean_dec_ref_known(v___y_1406_, 3);
lean_dec_ref(v_post_1394_);
lean_dec_ref(v_pre_1392_);
return v___x_1411_;
}
}
case 6:
{
lean_object* v_binderName_1429_; lean_object* v_binderType_1430_; lean_object* v_body_1431_; uint8_t v_binderInfo_1432_; lean_object* v___x_1433_; 
v_binderName_1429_ = lean_ctor_get(v___y_1406_, 0);
v_binderType_1430_ = lean_ctor_get(v___y_1406_, 1);
v_body_1431_ = lean_ctor_get(v___y_1406_, 2);
v_binderInfo_1432_ = lean_ctor_get_uint8(v___y_1406_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1430_);
lean_inc_ref(v_post_1394_);
lean_inc_ref(v_pre_1392_);
v___x_1433_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1392_, v_post_1394_, v_binderType_1430_, v___y_1395_, v___y_1396_, v___y_1397_);
if (lean_obj_tag(v___x_1433_) == 0)
{
lean_object* v_a_1434_; lean_object* v___x_1435_; 
v_a_1434_ = lean_ctor_get(v___x_1433_, 0);
lean_inc(v_a_1434_);
lean_dec_ref_known(v___x_1433_, 1);
lean_inc_ref(v_body_1431_);
lean_inc_ref(v_post_1394_);
lean_inc_ref(v_pre_1392_);
v___x_1435_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1392_, v_post_1394_, v_body_1431_, v___y_1395_, v___y_1396_, v___y_1397_);
if (lean_obj_tag(v___x_1435_) == 0)
{
lean_object* v_a_1436_; size_t v___x_1437_; size_t v___x_1438_; uint8_t v___x_1439_; 
v_a_1436_ = lean_ctor_get(v___x_1435_, 0);
lean_inc(v_a_1436_);
lean_dec_ref_known(v___x_1435_, 1);
v___x_1437_ = lean_ptr_addr(v_binderType_1430_);
v___x_1438_ = lean_ptr_addr(v_a_1434_);
v___x_1439_ = lean_usize_dec_eq(v___x_1437_, v___x_1438_);
if (v___x_1439_ == 0)
{
lean_object* v___x_1440_; lean_object* v___x_1441_; 
lean_inc(v_binderName_1429_);
lean_dec_ref_known(v___y_1406_, 3);
v___x_1440_ = l_Lean_Expr_lam___override(v_binderName_1429_, v_a_1434_, v_a_1436_, v_binderInfo_1432_);
v___x_1441_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1392_, v_post_1394_, v___x_1440_, v___y_1395_, v___y_1396_, v___y_1397_);
return v___x_1441_;
}
else
{
size_t v___x_1442_; size_t v___x_1443_; uint8_t v___x_1444_; 
v___x_1442_ = lean_ptr_addr(v_body_1431_);
v___x_1443_ = lean_ptr_addr(v_a_1436_);
v___x_1444_ = lean_usize_dec_eq(v___x_1442_, v___x_1443_);
if (v___x_1444_ == 0)
{
lean_object* v___x_1445_; lean_object* v___x_1446_; 
lean_inc(v_binderName_1429_);
lean_dec_ref_known(v___y_1406_, 3);
v___x_1445_ = l_Lean_Expr_lam___override(v_binderName_1429_, v_a_1434_, v_a_1436_, v_binderInfo_1432_);
v___x_1446_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1392_, v_post_1394_, v___x_1445_, v___y_1395_, v___y_1396_, v___y_1397_);
return v___x_1446_;
}
else
{
uint8_t v___x_1447_; 
v___x_1447_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1432_, v_binderInfo_1432_);
if (v___x_1447_ == 0)
{
lean_object* v___x_1448_; lean_object* v___x_1449_; 
lean_inc(v_binderName_1429_);
lean_dec_ref_known(v___y_1406_, 3);
v___x_1448_ = l_Lean_Expr_lam___override(v_binderName_1429_, v_a_1434_, v_a_1436_, v_binderInfo_1432_);
v___x_1449_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1392_, v_post_1394_, v___x_1448_, v___y_1395_, v___y_1396_, v___y_1397_);
return v___x_1449_;
}
else
{
lean_object* v___x_1450_; 
lean_dec(v_a_1436_);
lean_dec(v_a_1434_);
v___x_1450_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1392_, v_post_1394_, v___y_1406_, v___y_1395_, v___y_1396_, v___y_1397_);
return v___x_1450_;
}
}
}
}
else
{
lean_dec(v_a_1434_);
lean_dec_ref_known(v___y_1406_, 3);
lean_dec_ref(v_post_1394_);
lean_dec_ref(v_pre_1392_);
return v___x_1435_;
}
}
else
{
lean_dec_ref_known(v___y_1406_, 3);
lean_dec_ref(v_post_1394_);
lean_dec_ref(v_pre_1392_);
return v___x_1433_;
}
}
case 8:
{
lean_object* v_declName_1451_; lean_object* v_type_1452_; lean_object* v_value_1453_; lean_object* v_body_1454_; uint8_t v_nondep_1455_; lean_object* v___x_1456_; 
v_declName_1451_ = lean_ctor_get(v___y_1406_, 0);
v_type_1452_ = lean_ctor_get(v___y_1406_, 1);
v_value_1453_ = lean_ctor_get(v___y_1406_, 2);
v_body_1454_ = lean_ctor_get(v___y_1406_, 3);
v_nondep_1455_ = lean_ctor_get_uint8(v___y_1406_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_1452_);
lean_inc_ref(v_post_1394_);
lean_inc_ref(v_pre_1392_);
v___x_1456_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1392_, v_post_1394_, v_type_1452_, v___y_1395_, v___y_1396_, v___y_1397_);
if (lean_obj_tag(v___x_1456_) == 0)
{
lean_object* v_a_1457_; lean_object* v___x_1458_; 
v_a_1457_ = lean_ctor_get(v___x_1456_, 0);
lean_inc(v_a_1457_);
lean_dec_ref_known(v___x_1456_, 1);
lean_inc_ref(v_value_1453_);
lean_inc_ref(v_post_1394_);
lean_inc_ref(v_pre_1392_);
v___x_1458_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1392_, v_post_1394_, v_value_1453_, v___y_1395_, v___y_1396_, v___y_1397_);
if (lean_obj_tag(v___x_1458_) == 0)
{
lean_object* v_a_1459_; lean_object* v___x_1460_; 
v_a_1459_ = lean_ctor_get(v___x_1458_, 0);
lean_inc(v_a_1459_);
lean_dec_ref_known(v___x_1458_, 1);
lean_inc_ref(v_body_1454_);
lean_inc_ref(v_post_1394_);
lean_inc_ref(v_pre_1392_);
v___x_1460_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1392_, v_post_1394_, v_body_1454_, v___y_1395_, v___y_1396_, v___y_1397_);
if (lean_obj_tag(v___x_1460_) == 0)
{
lean_object* v_a_1461_; size_t v___x_1462_; size_t v___x_1463_; uint8_t v___x_1464_; 
v_a_1461_ = lean_ctor_get(v___x_1460_, 0);
lean_inc(v_a_1461_);
lean_dec_ref_known(v___x_1460_, 1);
v___x_1462_ = lean_ptr_addr(v_type_1452_);
v___x_1463_ = lean_ptr_addr(v_a_1457_);
v___x_1464_ = lean_usize_dec_eq(v___x_1462_, v___x_1463_);
if (v___x_1464_ == 0)
{
lean_object* v___x_1465_; lean_object* v___x_1466_; 
lean_inc(v_declName_1451_);
lean_dec_ref_known(v___y_1406_, 4);
v___x_1465_ = l_Lean_Expr_letE___override(v_declName_1451_, v_a_1457_, v_a_1459_, v_a_1461_, v_nondep_1455_);
v___x_1466_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1392_, v_post_1394_, v___x_1465_, v___y_1395_, v___y_1396_, v___y_1397_);
return v___x_1466_;
}
else
{
size_t v___x_1467_; size_t v___x_1468_; uint8_t v___x_1469_; 
v___x_1467_ = lean_ptr_addr(v_value_1453_);
v___x_1468_ = lean_ptr_addr(v_a_1459_);
v___x_1469_ = lean_usize_dec_eq(v___x_1467_, v___x_1468_);
if (v___x_1469_ == 0)
{
lean_object* v___x_1470_; lean_object* v___x_1471_; 
lean_inc(v_declName_1451_);
lean_dec_ref_known(v___y_1406_, 4);
v___x_1470_ = l_Lean_Expr_letE___override(v_declName_1451_, v_a_1457_, v_a_1459_, v_a_1461_, v_nondep_1455_);
v___x_1471_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1392_, v_post_1394_, v___x_1470_, v___y_1395_, v___y_1396_, v___y_1397_);
return v___x_1471_;
}
else
{
size_t v___x_1472_; size_t v___x_1473_; uint8_t v___x_1474_; 
v___x_1472_ = lean_ptr_addr(v_body_1454_);
v___x_1473_ = lean_ptr_addr(v_a_1461_);
v___x_1474_ = lean_usize_dec_eq(v___x_1472_, v___x_1473_);
if (v___x_1474_ == 0)
{
lean_object* v___x_1475_; lean_object* v___x_1476_; 
lean_inc(v_declName_1451_);
lean_dec_ref_known(v___y_1406_, 4);
v___x_1475_ = l_Lean_Expr_letE___override(v_declName_1451_, v_a_1457_, v_a_1459_, v_a_1461_, v_nondep_1455_);
v___x_1476_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1392_, v_post_1394_, v___x_1475_, v___y_1395_, v___y_1396_, v___y_1397_);
return v___x_1476_;
}
else
{
lean_object* v___x_1477_; 
lean_dec(v_a_1461_);
lean_dec(v_a_1459_);
lean_dec(v_a_1457_);
v___x_1477_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1392_, v_post_1394_, v___y_1406_, v___y_1395_, v___y_1396_, v___y_1397_);
return v___x_1477_;
}
}
}
}
else
{
lean_dec(v_a_1459_);
lean_dec(v_a_1457_);
lean_dec_ref_known(v___y_1406_, 4);
lean_dec_ref(v_post_1394_);
lean_dec_ref(v_pre_1392_);
return v___x_1460_;
}
}
else
{
lean_dec(v_a_1457_);
lean_dec_ref_known(v___y_1406_, 4);
lean_dec_ref(v_post_1394_);
lean_dec_ref(v_pre_1392_);
return v___x_1458_;
}
}
else
{
lean_dec_ref_known(v___y_1406_, 4);
lean_dec_ref(v_post_1394_);
lean_dec_ref(v_pre_1392_);
return v___x_1456_;
}
}
case 5:
{
lean_object* v_dummy_1478_; lean_object* v_nargs_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; 
v_dummy_1478_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_1479_ = l_Lean_Expr_getAppNumArgs(v___y_1406_);
lean_inc(v_nargs_1479_);
v___x_1480_ = lean_mk_array(v_nargs_1479_, v_dummy_1478_);
v___x_1481_ = lean_unsigned_to_nat(1u);
v___x_1482_ = lean_nat_sub(v_nargs_1479_, v___x_1481_);
lean_dec(v_nargs_1479_);
v___x_1483_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__4(v_pre_1392_, v_post_1394_, v___y_1406_, v___x_1480_, v___x_1482_, v___y_1395_, v___y_1396_, v___y_1397_);
return v___x_1483_;
}
case 10:
{
lean_object* v_data_1484_; lean_object* v_expr_1485_; lean_object* v___x_1486_; 
v_data_1484_ = lean_ctor_get(v___y_1406_, 0);
v_expr_1485_ = lean_ctor_get(v___y_1406_, 1);
lean_inc_ref(v_expr_1485_);
lean_inc_ref(v_post_1394_);
lean_inc_ref(v_pre_1392_);
v___x_1486_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1392_, v_post_1394_, v_expr_1485_, v___y_1395_, v___y_1396_, v___y_1397_);
if (lean_obj_tag(v___x_1486_) == 0)
{
lean_object* v_a_1487_; size_t v___x_1488_; size_t v___x_1489_; uint8_t v___x_1490_; 
v_a_1487_ = lean_ctor_get(v___x_1486_, 0);
lean_inc(v_a_1487_);
lean_dec_ref_known(v___x_1486_, 1);
v___x_1488_ = lean_ptr_addr(v_expr_1485_);
v___x_1489_ = lean_ptr_addr(v_a_1487_);
v___x_1490_ = lean_usize_dec_eq(v___x_1488_, v___x_1489_);
if (v___x_1490_ == 0)
{
lean_object* v___x_1491_; lean_object* v___x_1492_; 
lean_inc(v_data_1484_);
lean_dec_ref_known(v___y_1406_, 2);
v___x_1491_ = l_Lean_Expr_mdata___override(v_data_1484_, v_a_1487_);
v___x_1492_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1392_, v_post_1394_, v___x_1491_, v___y_1395_, v___y_1396_, v___y_1397_);
return v___x_1492_;
}
else
{
lean_object* v___x_1493_; 
lean_dec(v_a_1487_);
v___x_1493_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1392_, v_post_1394_, v___y_1406_, v___y_1395_, v___y_1396_, v___y_1397_);
return v___x_1493_;
}
}
else
{
lean_dec_ref_known(v___y_1406_, 2);
lean_dec_ref(v_post_1394_);
lean_dec_ref(v_pre_1392_);
return v___x_1486_;
}
}
case 11:
{
lean_object* v_typeName_1494_; lean_object* v_idx_1495_; lean_object* v_struct_1496_; lean_object* v___x_1497_; 
v_typeName_1494_ = lean_ctor_get(v___y_1406_, 0);
v_idx_1495_ = lean_ctor_get(v___y_1406_, 1);
v_struct_1496_ = lean_ctor_get(v___y_1406_, 2);
lean_inc_ref(v_struct_1496_);
lean_inc_ref(v_post_1394_);
lean_inc_ref(v_pre_1392_);
v___x_1497_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1392_, v_post_1394_, v_struct_1496_, v___y_1395_, v___y_1396_, v___y_1397_);
if (lean_obj_tag(v___x_1497_) == 0)
{
lean_object* v_a_1498_; size_t v___x_1499_; size_t v___x_1500_; uint8_t v___x_1501_; 
v_a_1498_ = lean_ctor_get(v___x_1497_, 0);
lean_inc(v_a_1498_);
lean_dec_ref_known(v___x_1497_, 1);
v___x_1499_ = lean_ptr_addr(v_struct_1496_);
v___x_1500_ = lean_ptr_addr(v_a_1498_);
v___x_1501_ = lean_usize_dec_eq(v___x_1499_, v___x_1500_);
if (v___x_1501_ == 0)
{
lean_object* v___x_1502_; lean_object* v___x_1503_; 
lean_inc(v_idx_1495_);
lean_inc(v_typeName_1494_);
lean_dec_ref_known(v___y_1406_, 3);
v___x_1502_ = l_Lean_Expr_proj___override(v_typeName_1494_, v_idx_1495_, v_a_1498_);
v___x_1503_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1392_, v_post_1394_, v___x_1502_, v___y_1395_, v___y_1396_, v___y_1397_);
return v___x_1503_;
}
else
{
lean_object* v___x_1504_; 
lean_dec(v_a_1498_);
v___x_1504_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1392_, v_post_1394_, v___y_1406_, v___y_1395_, v___y_1396_, v___y_1397_);
return v___x_1504_;
}
}
else
{
lean_dec_ref_known(v___y_1406_, 3);
lean_dec_ref(v_post_1394_);
lean_dec_ref(v_pre_1392_);
return v___x_1497_;
}
}
default: 
{
lean_object* v___x_1505_; 
v___x_1505_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1392_, v_post_1394_, v___y_1406_, v___y_1395_, v___y_1396_, v___y_1397_);
return v___x_1505_;
}
}
}
}
}
else
{
lean_object* v_a_1517_; lean_object* v___x_1519_; uint8_t v_isShared_1520_; uint8_t v_isSharedCheck_1524_; 
lean_dec_ref(v_post_1394_);
lean_dec_ref(v_e_1393_);
lean_dec_ref(v_pre_1392_);
v_a_1517_ = lean_ctor_get(v___x_1400_, 0);
v_isSharedCheck_1524_ = !lean_is_exclusive(v___x_1400_);
if (v_isSharedCheck_1524_ == 0)
{
v___x_1519_ = v___x_1400_;
v_isShared_1520_ = v_isSharedCheck_1524_;
goto v_resetjp_1518_;
}
else
{
lean_inc(v_a_1517_);
lean_dec(v___x_1400_);
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
lean_dec_ref(v_post_1394_);
lean_dec_ref(v_e_1393_);
lean_dec_ref(v_pre_1392_);
v_a_1525_ = lean_ctor_get(v___x_1399_, 0);
v_isSharedCheck_1532_ = !lean_is_exclusive(v___x_1399_);
if (v_isSharedCheck_1532_ == 0)
{
v___x_1527_ = v___x_1399_;
v_isShared_1528_ = v_isSharedCheck_1532_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_a_1525_);
lean_dec(v___x_1399_);
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
lean_dec_ref_known(v___x_1558_, 1);
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
lean_dec_ref_known(v___x_1555_, 1);
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
lean_dec_ref_known(v_a_1599_, 1);
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
lean_dec_ref_known(v_a_1599_, 1);
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
lean_dec_ref_known(v_a_1599_, 1);
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
lean_dec_ref_known(v_e_x3f_1609_, 1);
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
lean_dec_ref_known(v___x_1686_, 1);
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
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8(lean_object* v_00_u03b1_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_){
_start:
{
lean_object* v___x_1743_; 
v___x_1743_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___redArg();
return v___x_1743_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___boxed(lean_object* v_00_u03b1_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_){
_start:
{
lean_object* v_res_1748_; 
v_res_1748_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8(v_00_u03b1_1744_, v___y_1745_, v___y_1746_);
lean_dec(v___y_1746_);
lean_dec_ref(v___y_1745_);
return v_res_1748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5(lean_object* v_00_u03b1_1749_, lean_object* v_x_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_){
_start:
{
lean_object* v___x_1755_; 
v___x_1755_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___redArg(v_x_1750_, v___y_1751_, v___y_1752_, v___y_1753_);
return v___x_1755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b1_1756_, lean_object* v_x_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_){
_start:
{
lean_object* v_res_1762_; 
v_res_1762_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5(v_00_u03b1_1756_, v_x_1757_, v___y_1758_, v___y_1759_, v___y_1760_);
lean_dec(v___y_1760_);
lean_dec_ref(v___y_1759_);
lean_dec(v___y_1758_);
return v_res_1762_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6(lean_object* v_00_u03b2_1763_, lean_object* v_m_1764_, lean_object* v_a_1765_, lean_object* v_b_1766_){
_start:
{
lean_object* v___x_1767_; 
v___x_1767_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6___redArg(v_m_1764_, v_a_1765_, v_b_1766_);
return v___x_1767_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4(lean_object* v_00_u03b2_1768_, lean_object* v_a_1769_, lean_object* v_x_1770_){
_start:
{
lean_object* v___x_1771_; 
v___x_1771_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___redArg(v_a_1769_, v_x_1770_);
return v___x_1771_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___boxed(lean_object* v_00_u03b2_1772_, lean_object* v_a_1773_, lean_object* v_x_1774_){
_start:
{
lean_object* v_res_1775_; 
v_res_1775_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4(v_00_u03b2_1772_, v_a_1773_, v_x_1774_);
lean_dec(v_x_1774_);
lean_dec_ref(v_a_1773_);
return v_res_1775_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10(lean_object* v_00_u03b2_1776_, lean_object* v_a_1777_, lean_object* v_x_1778_){
_start:
{
uint8_t v___x_1779_; 
v___x_1779_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___redArg(v_a_1777_, v_x_1778_);
return v___x_1779_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___boxed(lean_object* v_00_u03b2_1780_, lean_object* v_a_1781_, lean_object* v_x_1782_){
_start:
{
uint8_t v_res_1783_; lean_object* v_r_1784_; 
v_res_1783_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10(v_00_u03b2_1780_, v_a_1781_, v_x_1782_);
lean_dec(v_x_1782_);
lean_dec_ref(v_a_1781_);
v_r_1784_ = lean_box(v_res_1783_);
return v_r_1784_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11(lean_object* v_00_u03b2_1785_, lean_object* v_data_1786_){
_start:
{
lean_object* v___x_1787_; 
v___x_1787_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11___redArg(v_data_1786_);
return v___x_1787_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__12(lean_object* v_00_u03b2_1788_, lean_object* v_a_1789_, lean_object* v_b_1790_, lean_object* v_x_1791_){
_start:
{
lean_object* v___x_1792_; 
v___x_1792_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__12___redArg(v_a_1789_, v_b_1790_, v_x_1791_);
return v___x_1792_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12(lean_object* v_00_u03b2_1793_, lean_object* v_i_1794_, lean_object* v_source_1795_, lean_object* v_target_1796_){
_start:
{
lean_object* v___x_1797_; 
v___x_1797_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v_i_1794_, v_source_1795_, v_target_1796_);
return v___x_1797_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13(lean_object* v_00_u03b2_1798_, lean_object* v_x_1799_, lean_object* v_x_1800_){
_start:
{
lean_object* v___x_1801_; 
v___x_1801_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_x_1799_, v_x_1800_);
return v___x_1801_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__0(lean_object* v_toApplicative_1802_, lean_object* v_a_1803_){
_start:
{
lean_object* v_toPure_1804_; lean_object* v___x_1805_; 
v_toPure_1804_ = lean_ctor_get(v_toApplicative_1802_, 1);
lean_inc(v_toPure_1804_);
lean_dec_ref(v_toApplicative_1802_);
v___x_1805_ = lean_apply_2(v_toPure_1804_, lean_box(0), v_a_1803_);
return v___x_1805_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__13(lean_object* v___x_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_){
_start:
{
lean_object* v___x_1812_; 
v___x_1812_ = l_Lean_Core_checkSystem(v___x_1806_, v___y_1809_, v___y_1810_);
return v___x_1812_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__13___boxed(lean_object* v___x_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_){
_start:
{
lean_object* v_res_1819_; 
v_res_1819_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__13(v___x_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_);
lean_dec(v___y_1817_);
lean_dec_ref(v___y_1816_);
lean_dec(v___y_1815_);
lean_dec_ref(v___y_1814_);
return v_res_1819_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14(lean_object* v_inst_1822_, lean_object* v_x_1823_, lean_object* v___x_1824_, lean_object* v___x_1825_, lean_object* v_inst_1826_, lean_object* v___f_1827_, lean_object* v___x_1828_, lean_object* v___x_1829_, lean_object* v_a_1830_, lean_object* v_toBind_1831_, lean_object* v___f_1832_, lean_object* v_toApplicative_1833_, lean_object* v_a_1834_){
_start:
{
if (lean_obj_tag(v_a_1834_) == 0)
{
lean_object* v___f_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_3407__overap_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; 
lean_dec_ref(v_toApplicative_1833_);
v___f_1835_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14___closed__0));
v___x_1836_ = lean_apply_2(v_inst_1822_, lean_box(0), v___f_1835_);
lean_inc_ref(v___x_1825_);
lean_inc_ref(v___x_1824_);
v___x_1837_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonadLift___aux__1___boxed), 10, 9);
lean_closure_set(v___x_1837_, 0, lean_box(0));
lean_closure_set(v___x_1837_, 1, lean_box(0));
lean_closure_set(v___x_1837_, 2, lean_box(0));
lean_closure_set(v___x_1837_, 3, lean_box(0));
lean_closure_set(v___x_1837_, 4, v_x_1823_);
lean_closure_set(v___x_1837_, 5, v___x_1824_);
lean_closure_set(v___x_1837_, 6, v___x_1825_);
lean_closure_set(v___x_1837_, 7, lean_box(0));
lean_closure_set(v___x_1837_, 8, v___x_1836_);
v___x_1838_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonad___aux__13___boxed), 13, 12);
lean_closure_set(v___x_1838_, 0, lean_box(0));
lean_closure_set(v___x_1838_, 1, lean_box(0));
lean_closure_set(v___x_1838_, 2, lean_box(0));
lean_closure_set(v___x_1838_, 3, lean_box(0));
lean_closure_set(v___x_1838_, 4, v_x_1823_);
lean_closure_set(v___x_1838_, 5, v___x_1824_);
lean_closure_set(v___x_1838_, 6, v___x_1825_);
lean_closure_set(v___x_1838_, 7, v_inst_1826_);
lean_closure_set(v___x_1838_, 8, lean_box(0));
lean_closure_set(v___x_1838_, 9, lean_box(0));
lean_closure_set(v___x_1838_, 10, v___x_1837_);
lean_closure_set(v___x_1838_, 11, v___f_1827_);
v___x_3407__overap_1839_ = l_Lean_Meta_withIncRecDepth___redArg(v___x_1828_, v___x_1829_, v___x_1838_);
lean_inc(v_a_1830_);
v___x_1840_ = lean_apply_1(v___x_3407__overap_1839_, v_a_1830_);
v___x_1841_ = lean_apply_4(v_toBind_1831_, lean_box(0), lean_box(0), v___x_1840_, v___f_1832_);
return v___x_1841_;
}
else
{
lean_object* v_val_1842_; lean_object* v_toPure_1843_; lean_object* v___x_1844_; 
lean_dec(v___f_1832_);
lean_dec(v_toBind_1831_);
lean_dec_ref(v___x_1829_);
lean_dec_ref(v___x_1828_);
lean_dec(v___f_1827_);
lean_dec_ref(v_inst_1826_);
lean_dec_ref(v___x_1825_);
lean_dec_ref(v___x_1824_);
lean_dec(v_inst_1822_);
v_val_1842_ = lean_ctor_get(v_a_1834_, 0);
lean_inc(v_val_1842_);
lean_dec_ref_known(v_a_1834_, 1);
v_toPure_1843_ = lean_ctor_get(v_toApplicative_1833_, 1);
lean_inc(v_toPure_1843_);
lean_dec_ref(v_toApplicative_1833_);
v___x_1844_ = lean_apply_2(v_toPure_1843_, lean_box(0), v_val_1842_);
return v___x_1844_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14___boxed(lean_object* v_inst_1845_, lean_object* v_x_1846_, lean_object* v___x_1847_, lean_object* v___x_1848_, lean_object* v_inst_1849_, lean_object* v___f_1850_, lean_object* v___x_1851_, lean_object* v___x_1852_, lean_object* v_a_1853_, lean_object* v_toBind_1854_, lean_object* v___f_1855_, lean_object* v_toApplicative_1856_, lean_object* v_a_1857_){
_start:
{
lean_object* v_res_1858_; 
v_res_1858_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14(v_inst_1845_, v_x_1846_, v___x_1847_, v___x_1848_, v_inst_1849_, v___f_1850_, v___x_1851_, v___x_1852_, v_a_1853_, v_toBind_1854_, v___f_1855_, v_toApplicative_1856_, v_a_1857_);
lean_dec(v_a_1853_);
return v_res_1858_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__1(lean_object* v___x_1859_, lean_object* v___x_1860_, lean_object* v_declName_1861_, lean_object* v_a_1862_, lean_object* v___f_1863_, uint8_t v_nondep_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_){
_start:
{
uint8_t v___x_1867_; lean_object* v___x_3426__overap_1868_; lean_object* v___x_1869_; 
v___x_1867_ = 0;
v___x_3426__overap_1868_ = l_Lean_Meta_withLetDecl___redArg(v___x_1859_, v___x_1860_, v_declName_1861_, v_a_1862_, v_a_1866_, v___f_1863_, v_nondep_1864_, v___x_1867_);
lean_inc(v_a_1865_);
v___x_1869_ = lean_apply_1(v___x_3426__overap_1868_, v_a_1865_);
return v___x_1869_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__1___boxed(lean_object* v___x_1870_, lean_object* v___x_1871_, lean_object* v_declName_1872_, lean_object* v_a_1873_, lean_object* v___f_1874_, lean_object* v_nondep_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_){
_start:
{
uint8_t v_nondep_3605__boxed_1878_; lean_object* v_res_1879_; 
v_nondep_3605__boxed_1878_ = lean_unbox(v_nondep_1875_);
v_res_1879_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__1(v___x_1870_, v___x_1871_, v_declName_1872_, v_a_1873_, v___f_1874_, v_nondep_3605__boxed_1878_, v_a_1876_, v_a_1877_);
lean_dec(v_a_1876_);
return v_res_1879_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__4(lean_object* v_fvars_1880_, uint8_t v_usedLetOnly_1881_, lean_object* v_inst_1882_, lean_object* v_toBind_1883_, lean_object* v___f_1884_, lean_object* v_a_1885_){
_start:
{
uint8_t v___x_1886_; uint8_t v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; 
v___x_1886_ = 0;
v___x_1887_ = 1;
v___x_1888_ = lean_box(v_usedLetOnly_1881_);
v___x_1889_ = lean_box(v___x_1886_);
v___x_1890_ = lean_box(v___x_1887_);
v___x_1891_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLetFVars___boxed), 10, 5);
lean_closure_set(v___x_1891_, 0, v_fvars_1880_);
lean_closure_set(v___x_1891_, 1, v_a_1885_);
lean_closure_set(v___x_1891_, 2, v___x_1888_);
lean_closure_set(v___x_1891_, 3, v___x_1889_);
lean_closure_set(v___x_1891_, 4, v___x_1890_);
v___x_1892_ = lean_apply_2(v_inst_1882_, lean_box(0), v___x_1891_);
v___x_1893_ = lean_apply_4(v_toBind_1883_, lean_box(0), lean_box(0), v___x_1892_, v___f_1884_);
return v___x_1893_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__4___boxed(lean_object* v_fvars_1894_, lean_object* v_usedLetOnly_1895_, lean_object* v_inst_1896_, lean_object* v_toBind_1897_, lean_object* v___f_1898_, lean_object* v_a_1899_){
_start:
{
uint8_t v_usedLetOnly_boxed_1900_; lean_object* v_res_1901_; 
v_usedLetOnly_boxed_1900_ = lean_unbox(v_usedLetOnly_1895_);
v_res_1901_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__4(v_fvars_1894_, v_usedLetOnly_boxed_1900_, v_inst_1896_, v_toBind_1897_, v___f_1898_, v_a_1899_);
return v_res_1901_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__3(lean_object* v_fvars_1902_, uint8_t v_usedLetOnly_1903_, lean_object* v_inst_1904_, lean_object* v_toBind_1905_, lean_object* v___f_1906_, lean_object* v_a_1907_){
_start:
{
uint8_t v___x_1908_; uint8_t v___x_1909_; uint8_t v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; 
v___x_1908_ = 0;
v___x_1909_ = 1;
v___x_1910_ = 1;
v___x_1911_ = lean_box(v___x_1908_);
v___x_1912_ = lean_box(v_usedLetOnly_1903_);
v___x_1913_ = lean_box(v___x_1908_);
v___x_1914_ = lean_box(v___x_1909_);
v___x_1915_ = lean_box(v___x_1910_);
v___x_1916_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(v___x_1916_, 0, v_fvars_1902_);
lean_closure_set(v___x_1916_, 1, v_a_1907_);
lean_closure_set(v___x_1916_, 2, v___x_1911_);
lean_closure_set(v___x_1916_, 3, v___x_1912_);
lean_closure_set(v___x_1916_, 4, v___x_1913_);
lean_closure_set(v___x_1916_, 5, v___x_1914_);
lean_closure_set(v___x_1916_, 6, v___x_1915_);
v___x_1917_ = lean_apply_2(v_inst_1904_, lean_box(0), v___x_1916_);
v___x_1918_ = lean_apply_4(v_toBind_1905_, lean_box(0), lean_box(0), v___x_1917_, v___f_1906_);
return v___x_1918_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__3___boxed(lean_object* v_fvars_1919_, lean_object* v_usedLetOnly_1920_, lean_object* v_inst_1921_, lean_object* v_toBind_1922_, lean_object* v___f_1923_, lean_object* v_a_1924_){
_start:
{
uint8_t v_usedLetOnly_boxed_1925_; lean_object* v_res_1926_; 
v_usedLetOnly_boxed_1925_ = lean_unbox(v_usedLetOnly_1920_);
v_res_1926_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__3(v_fvars_1919_, v_usedLetOnly_boxed_1925_, v_inst_1921_, v_toBind_1922_, v___f_1923_, v_a_1924_);
return v_res_1926_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1(lean_object* v___x_1927_, lean_object* v___x_1928_, lean_object* v_binderName_1929_, uint8_t v_binderInfo_1930_, lean_object* v___f_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_){
_start:
{
uint8_t v___x_1934_; lean_object* v___x_3484__overap_1935_; lean_object* v___x_1936_; 
v___x_1934_ = 0;
v___x_3484__overap_1935_ = l_Lean_Meta_withLocalDecl___redArg(v___x_1927_, v___x_1928_, v_binderName_1929_, v_binderInfo_1930_, v_a_1933_, v___f_1931_, v___x_1934_);
lean_inc(v_a_1932_);
v___x_1936_ = lean_apply_1(v___x_3484__overap_1935_, v_a_1932_);
return v___x_1936_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1___boxed(lean_object* v___x_1937_, lean_object* v___x_1938_, lean_object* v_binderName_1939_, lean_object* v_binderInfo_1940_, lean_object* v___f_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_){
_start:
{
uint8_t v_binderInfo_3673__boxed_1944_; lean_object* v_res_1945_; 
v_binderInfo_3673__boxed_1944_ = lean_unbox(v_binderInfo_1940_);
v_res_1945_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1(v___x_1937_, v___x_1938_, v_binderName_1939_, v_binderInfo_3673__boxed_1944_, v___f_1941_, v_a_1942_, v_a_1943_);
lean_dec(v_a_1942_);
return v_res_1945_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__3(lean_object* v_fvars_1946_, uint8_t v_usedLetOnly_1947_, lean_object* v_inst_1948_, lean_object* v_toBind_1949_, lean_object* v___f_1950_, lean_object* v_a_1951_){
_start:
{
uint8_t v___x_1952_; uint8_t v___x_1953_; uint8_t v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; 
v___x_1952_ = 0;
v___x_1953_ = 1;
v___x_1954_ = 1;
v___x_1955_ = lean_box(v___x_1952_);
v___x_1956_ = lean_box(v_usedLetOnly_1947_);
v___x_1957_ = lean_box(v___x_1953_);
v___x_1958_ = lean_box(v___x_1954_);
v___x_1959_ = lean_alloc_closure((void*)(l_Lean_Meta_mkForallFVars___boxed), 11, 6);
lean_closure_set(v___x_1959_, 0, v_fvars_1946_);
lean_closure_set(v___x_1959_, 1, v_a_1951_);
lean_closure_set(v___x_1959_, 2, v___x_1955_);
lean_closure_set(v___x_1959_, 3, v___x_1956_);
lean_closure_set(v___x_1959_, 4, v___x_1957_);
lean_closure_set(v___x_1959_, 5, v___x_1958_);
v___x_1960_ = lean_apply_2(v_inst_1948_, lean_box(0), v___x_1959_);
v___x_1961_ = lean_apply_4(v_toBind_1949_, lean_box(0), lean_box(0), v___x_1960_, v___f_1950_);
return v___x_1961_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__3___boxed(lean_object* v_fvars_1962_, lean_object* v_usedLetOnly_1963_, lean_object* v_inst_1964_, lean_object* v_toBind_1965_, lean_object* v___f_1966_, lean_object* v_a_1967_){
_start:
{
uint8_t v_usedLetOnly_boxed_1968_; lean_object* v_res_1969_; 
v_usedLetOnly_boxed_1968_ = lean_unbox(v_usedLetOnly_1963_);
v_res_1969_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__3(v_fvars_1962_, v_usedLetOnly_boxed_1968_, v_inst_1964_, v_toBind_1965_, v___f_1966_, v_a_1967_);
return v_res_1969_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__7(lean_object* v___f_1970_, lean_object* v___y_1971_, lean_object* v_a_1972_){
_start:
{
lean_object* v___x_1973_; 
lean_inc(v___y_1971_);
v___x_1973_ = lean_apply_2(v___f_1970_, v_a_1972_, v___y_1971_);
return v___x_1973_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__7___boxed(lean_object* v___f_1974_, lean_object* v___y_1975_, lean_object* v_a_1976_){
_start:
{
lean_object* v_res_1977_; 
v_res_1977_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__7(v___f_1974_, v___y_1975_, v_a_1976_);
lean_dec(v___y_1975_);
return v_res_1977_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1(lean_object* v_toApplicative_1978_, lean_object* v_acc_1979_, lean_object* v_next_1980_, lean_object* v_a_1981_){
_start:
{
lean_object* v_toPure_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; 
v_toPure_1982_ = lean_ctor_get(v_toApplicative_1978_, 1);
lean_inc(v_toPure_1982_);
lean_dec_ref(v_toApplicative_1978_);
v___x_1983_ = lean_array_fset(v_acc_1979_, v_next_1980_, v_a_1981_);
v___x_1984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1984_, 0, v___x_1983_);
v___x_1985_ = lean_apply_2(v_toPure_1982_, lean_box(0), v___x_1984_);
return v___x_1985_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1___boxed(lean_object* v_toApplicative_1986_, lean_object* v_acc_1987_, lean_object* v_next_1988_, lean_object* v_a_1989_){
_start:
{
lean_object* v_res_1990_; 
v_res_1990_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1(v_toApplicative_1986_, v_acc_1987_, v_next_1988_, v_a_1989_);
lean_dec(v_next_1988_);
return v_res_1990_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__2(lean_object* v_toApplicative_1991_, lean_object* v_next_1992_, lean_object* v_G_1993_, lean_object* v___y_1994_, lean_object* v_a_1995_){
_start:
{
if (lean_obj_tag(v_a_1995_) == 0)
{
lean_object* v_a_1996_; lean_object* v_toPure_1997_; lean_object* v___x_1998_; 
lean_dec(v_G_1993_);
v_a_1996_ = lean_ctor_get(v_a_1995_, 0);
lean_inc(v_a_1996_);
lean_dec_ref_known(v_a_1995_, 1);
v_toPure_1997_ = lean_ctor_get(v_toApplicative_1991_, 1);
lean_inc(v_toPure_1997_);
lean_dec_ref(v_toApplicative_1991_);
v___x_1998_ = lean_apply_2(v_toPure_1997_, lean_box(0), v_a_1996_);
return v___x_1998_;
}
else
{
lean_object* v_a_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; 
lean_dec_ref(v_toApplicative_1991_);
v_a_1999_ = lean_ctor_get(v_a_1995_, 0);
lean_inc(v_a_1999_);
lean_dec_ref_known(v_a_1995_, 1);
v___x_2000_ = lean_unsigned_to_nat(1u);
v___x_2001_ = lean_nat_add(v_next_1992_, v___x_2000_);
lean_inc(v___y_1994_);
v___x_2002_ = lean_apply_5(v_G_1993_, v___x_2001_, v_a_1999_, lean_box(0), lean_box(0), v___y_1994_);
return v___x_2002_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__2___boxed(lean_object* v_toApplicative_2003_, lean_object* v_next_2004_, lean_object* v_G_2005_, lean_object* v___y_2006_, lean_object* v_a_2007_){
_start:
{
lean_object* v_res_2008_; 
v_res_2008_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__2(v_toApplicative_2003_, v_next_2004_, v_G_2005_, v___y_2006_, v_a_2007_);
lean_dec(v___y_2006_);
lean_dec(v_next_2004_);
return v_res_2008_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5(lean_object* v_f_2009_, lean_object* v_inst_2010_, lean_object* v_inst_2011_, lean_object* v_inst_2012_, lean_object* v_pre_2013_, lean_object* v_post_2014_, uint8_t v_usedLetOnly_2015_, uint8_t v_skipConstInApp_2016_, uint8_t v_skipInstances_2017_, lean_object* v_x_2018_, lean_object* v_x_2019_, lean_object* v___y_2020_, lean_object* v_a_2021_){
_start:
{
lean_object* v___x_2022_; lean_object* v___x_2023_; 
v___x_2022_ = l_Lean_mkAppN(v_f_2009_, v_a_2021_);
v___x_2023_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2010_, v_inst_2011_, v_inst_2012_, v_pre_2013_, v_post_2014_, v_usedLetOnly_2015_, v_skipConstInApp_2016_, v_skipInstances_2017_, v_x_2018_, v_x_2019_, v___x_2022_, v___y_2020_);
return v___x_2023_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5___boxed(lean_object* v_f_2024_, lean_object* v_inst_2025_, lean_object* v_inst_2026_, lean_object* v_inst_2027_, lean_object* v_pre_2028_, lean_object* v_post_2029_, lean_object* v_usedLetOnly_2030_, lean_object* v_skipConstInApp_2031_, lean_object* v_skipInstances_2032_, lean_object* v_x_2033_, lean_object* v_x_2034_, lean_object* v___y_2035_, lean_object* v_a_2036_){
_start:
{
uint8_t v_usedLetOnly_boxed_2037_; uint8_t v_skipConstInApp_boxed_2038_; uint8_t v_skipInstances_boxed_2039_; lean_object* v_res_2040_; 
v_usedLetOnly_boxed_2037_ = lean_unbox(v_usedLetOnly_2030_);
v_skipConstInApp_boxed_2038_ = lean_unbox(v_skipConstInApp_2031_);
v_skipInstances_boxed_2039_ = lean_unbox(v_skipInstances_2032_);
v_res_2040_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5(v_f_2024_, v_inst_2025_, v_inst_2026_, v_inst_2027_, v_pre_2028_, v_post_2029_, v_usedLetOnly_boxed_2037_, v_skipConstInApp_boxed_2038_, v_skipInstances_boxed_2039_, v_x_2033_, v_x_2034_, v___y_2035_, v_a_2036_);
lean_dec_ref(v_a_2036_);
lean_dec(v___y_2035_);
return v_res_2040_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___boxed(lean_object* v_inst_2041_, lean_object* v_inst_2042_, lean_object* v_inst_2043_, lean_object* v_pre_2044_, lean_object* v_post_2045_, lean_object* v_usedLetOnly_2046_, lean_object* v_skipConstInApp_2047_, lean_object* v_skipInstances_2048_, lean_object* v_x_2049_, lean_object* v_x_2050_, lean_object* v_e_2051_, lean_object* v_a_2052_){
_start:
{
uint8_t v_usedLetOnly_boxed_2053_; uint8_t v_skipConstInApp_boxed_2054_; uint8_t v_skipInstances_boxed_2055_; lean_object* v_res_2056_; 
v_usedLetOnly_boxed_2053_ = lean_unbox(v_usedLetOnly_2046_);
v_skipConstInApp_boxed_2054_ = lean_unbox(v_skipConstInApp_2047_);
v_skipInstances_boxed_2055_ = lean_unbox(v_skipInstances_2048_);
v_res_2056_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2041_, v_inst_2042_, v_inst_2043_, v_pre_2044_, v_post_2045_, v_usedLetOnly_boxed_2053_, v_skipConstInApp_boxed_2054_, v_skipInstances_boxed_2055_, v_x_2049_, v_x_2050_, v_e_2051_, v_a_2052_);
lean_dec(v_a_2052_);
return v_res_2056_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__4(lean_object* v___x_2057_, lean_object* v_toApplicative_2058_, lean_object* v_toBind_2059_, lean_object* v___f_2060_, lean_object* v_paramInfo_2061_, lean_object* v_inst_2062_, lean_object* v_inst_2063_, lean_object* v_inst_2064_, lean_object* v_pre_2065_, lean_object* v_post_2066_, uint8_t v_usedLetOnly_2067_, uint8_t v_skipConstInApp_2068_, uint8_t v_skipInstances_2069_, lean_object* v_x_2070_, lean_object* v_x_2071_, lean_object* v_next_2072_, lean_object* v_acc_2073_, lean_object* v_h_2074_, lean_object* v_G_2075_, lean_object* v___y_2076_){
_start:
{
uint8_t v___x_2077_; 
v___x_2077_ = lean_nat_dec_lt(v_next_2072_, v___x_2057_);
if (v___x_2077_ == 0)
{
lean_object* v_toPure_2078_; lean_object* v___x_2079_; 
lean_dec(v_G_2075_);
lean_dec(v_next_2072_);
lean_dec(v_x_2071_);
lean_dec(v_post_2066_);
lean_dec(v_pre_2065_);
lean_dec_ref(v_inst_2064_);
lean_dec(v_inst_2063_);
lean_dec_ref(v_inst_2062_);
lean_dec(v___f_2060_);
lean_dec(v_toBind_2059_);
v_toPure_2078_ = lean_ctor_get(v_toApplicative_2058_, 1);
lean_inc(v_toPure_2078_);
lean_dec_ref(v_toApplicative_2058_);
v___x_2079_ = lean_apply_2(v_toPure_2078_, lean_box(0), v_acc_2073_);
return v___x_2079_;
}
else
{
lean_object* v___f_2080_; lean_object* v___y_2082_; lean_object* v___x_2085_; lean_object* v___x_2086_; uint8_t v___x_2087_; 
lean_inc(v___y_2076_);
lean_inc(v_next_2072_);
lean_inc_ref(v_toApplicative_2058_);
v___f_2080_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__2___boxed), 5, 4);
lean_closure_set(v___f_2080_, 0, v_toApplicative_2058_);
lean_closure_set(v___f_2080_, 1, v_next_2072_);
lean_closure_set(v___f_2080_, 2, v_G_2075_);
lean_closure_set(v___f_2080_, 3, v___y_2076_);
v___x_2085_ = lean_array_fget_borrowed(v_acc_2073_, v_next_2072_);
v___x_2086_ = lean_array_get_size(v_paramInfo_2061_);
v___x_2087_ = lean_nat_dec_lt(v_next_2072_, v___x_2086_);
if (v___x_2087_ == 0)
{
lean_object* v___f_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; 
lean_inc(v___x_2085_);
v___f_2088_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2088_, 0, v_toApplicative_2058_);
lean_closure_set(v___f_2088_, 1, v_acc_2073_);
lean_closure_set(v___f_2088_, 2, v_next_2072_);
v___x_2089_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2062_, v_inst_2063_, v_inst_2064_, v_pre_2065_, v_post_2066_, v_usedLetOnly_2067_, v_skipConstInApp_2068_, v_skipInstances_2069_, v_x_2070_, v_x_2071_, v___x_2085_, v___y_2076_);
lean_inc(v_toBind_2059_);
v___x_2090_ = lean_apply_4(v_toBind_2059_, lean_box(0), lean_box(0), v___x_2089_, v___f_2088_);
v___y_2082_ = v___x_2090_;
goto v___jp_2081_;
}
else
{
lean_object* v___x_2091_; uint8_t v_isInstance_2092_; 
v___x_2091_ = lean_array_fget_borrowed(v_paramInfo_2061_, v_next_2072_);
v_isInstance_2092_ = lean_ctor_get_uint8(v___x_2091_, sizeof(void*)*1 + 4);
if (v_isInstance_2092_ == 0)
{
lean_object* v___f_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; 
lean_inc(v___x_2085_);
v___f_2093_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2093_, 0, v_toApplicative_2058_);
lean_closure_set(v___f_2093_, 1, v_acc_2073_);
lean_closure_set(v___f_2093_, 2, v_next_2072_);
v___x_2094_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2062_, v_inst_2063_, v_inst_2064_, v_pre_2065_, v_post_2066_, v_usedLetOnly_2067_, v_skipConstInApp_2068_, v_skipInstances_2069_, v_x_2070_, v_x_2071_, v___x_2085_, v___y_2076_);
lean_inc(v_toBind_2059_);
v___x_2095_ = lean_apply_4(v_toBind_2059_, lean_box(0), lean_box(0), v___x_2094_, v___f_2093_);
v___y_2082_ = v___x_2095_;
goto v___jp_2081_;
}
else
{
lean_object* v_toPure_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; 
lean_dec(v_next_2072_);
lean_dec(v_x_2071_);
lean_dec(v_post_2066_);
lean_dec(v_pre_2065_);
lean_dec_ref(v_inst_2064_);
lean_dec(v_inst_2063_);
lean_dec_ref(v_inst_2062_);
v_toPure_2096_ = lean_ctor_get(v_toApplicative_2058_, 1);
lean_inc(v_toPure_2096_);
lean_dec_ref(v_toApplicative_2058_);
v___x_2097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2097_, 0, v_acc_2073_);
v___x_2098_ = lean_apply_2(v_toPure_2096_, lean_box(0), v___x_2097_);
v___y_2082_ = v___x_2098_;
goto v___jp_2081_;
}
}
v___jp_2081_:
{
lean_object* v___x_2083_; lean_object* v___x_2084_; 
lean_inc(v_toBind_2059_);
v___x_2083_ = lean_apply_4(v_toBind_2059_, lean_box(0), lean_box(0), v___y_2082_, v___f_2060_);
v___x_2084_ = lean_apply_4(v_toBind_2059_, lean_box(0), lean_box(0), v___x_2083_, v___f_2080_);
return v___x_2084_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__4___boxed(lean_object** _args){
lean_object* v___x_2099_ = _args[0];
lean_object* v_toApplicative_2100_ = _args[1];
lean_object* v_toBind_2101_ = _args[2];
lean_object* v___f_2102_ = _args[3];
lean_object* v_paramInfo_2103_ = _args[4];
lean_object* v_inst_2104_ = _args[5];
lean_object* v_inst_2105_ = _args[6];
lean_object* v_inst_2106_ = _args[7];
lean_object* v_pre_2107_ = _args[8];
lean_object* v_post_2108_ = _args[9];
lean_object* v_usedLetOnly_2109_ = _args[10];
lean_object* v_skipConstInApp_2110_ = _args[11];
lean_object* v_skipInstances_2111_ = _args[12];
lean_object* v_x_2112_ = _args[13];
lean_object* v_x_2113_ = _args[14];
lean_object* v_next_2114_ = _args[15];
lean_object* v_acc_2115_ = _args[16];
lean_object* v_h_2116_ = _args[17];
lean_object* v_G_2117_ = _args[18];
lean_object* v___y_2118_ = _args[19];
_start:
{
uint8_t v_usedLetOnly_boxed_2119_; uint8_t v_skipConstInApp_boxed_2120_; uint8_t v_skipInstances_boxed_2121_; lean_object* v_res_2122_; 
v_usedLetOnly_boxed_2119_ = lean_unbox(v_usedLetOnly_2109_);
v_skipConstInApp_boxed_2120_ = lean_unbox(v_skipConstInApp_2110_);
v_skipInstances_boxed_2121_ = lean_unbox(v_skipInstances_2111_);
v_res_2122_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__4(v___x_2099_, v_toApplicative_2100_, v_toBind_2101_, v___f_2102_, v_paramInfo_2103_, v_inst_2104_, v_inst_2105_, v_inst_2106_, v_pre_2107_, v_post_2108_, v_usedLetOnly_boxed_2119_, v_skipConstInApp_boxed_2120_, v_skipInstances_boxed_2121_, v_x_2112_, v_x_2113_, v_next_2114_, v_acc_2115_, v_h_2116_, v_G_2117_, v___y_2118_);
lean_dec(v___y_2118_);
lean_dec_ref(v_paramInfo_2103_);
lean_dec(v___x_2099_);
return v_res_2122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__3(lean_object* v___x_2123_, lean_object* v_toApplicative_2124_, lean_object* v_toBind_2125_, lean_object* v___f_2126_, lean_object* v_inst_2127_, lean_object* v_inst_2128_, lean_object* v_inst_2129_, lean_object* v_pre_2130_, lean_object* v_post_2131_, uint8_t v_usedLetOnly_2132_, uint8_t v_skipConstInApp_2133_, uint8_t v_skipInstances_2134_, lean_object* v_x_2135_, lean_object* v_x_2136_, lean_object* v_args_2137_, lean_object* v___y_2138_, lean_object* v___f_2139_, lean_object* v_a_2140_){
_start:
{
lean_object* v_paramInfo_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___f_2146_; lean_object* v___x_3244__overap_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; 
v_paramInfo_2141_ = lean_ctor_get(v_a_2140_, 0);
lean_inc_ref(v_paramInfo_2141_);
lean_dec_ref(v_a_2140_);
v___x_2142_ = lean_unsigned_to_nat(0u);
v___x_2143_ = lean_box(v_usedLetOnly_2132_);
v___x_2144_ = lean_box(v_skipConstInApp_2133_);
v___x_2145_ = lean_box(v_skipInstances_2134_);
lean_inc(v_toBind_2125_);
v___f_2146_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__4___boxed), 20, 15);
lean_closure_set(v___f_2146_, 0, v___x_2123_);
lean_closure_set(v___f_2146_, 1, v_toApplicative_2124_);
lean_closure_set(v___f_2146_, 2, v_toBind_2125_);
lean_closure_set(v___f_2146_, 3, v___f_2126_);
lean_closure_set(v___f_2146_, 4, v_paramInfo_2141_);
lean_closure_set(v___f_2146_, 5, v_inst_2127_);
lean_closure_set(v___f_2146_, 6, v_inst_2128_);
lean_closure_set(v___f_2146_, 7, v_inst_2129_);
lean_closure_set(v___f_2146_, 8, v_pre_2130_);
lean_closure_set(v___f_2146_, 9, v_post_2131_);
lean_closure_set(v___f_2146_, 10, v___x_2143_);
lean_closure_set(v___f_2146_, 11, v___x_2144_);
lean_closure_set(v___f_2146_, 12, v___x_2145_);
lean_closure_set(v___f_2146_, 13, v_x_2135_);
lean_closure_set(v___f_2146_, 14, v_x_2136_);
v___x_3244__overap_2147_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_2146_, v___x_2142_, v_args_2137_, lean_box(0));
lean_inc(v___y_2138_);
v___x_2148_ = lean_apply_1(v___x_3244__overap_2147_, v___y_2138_);
v___x_2149_ = lean_apply_4(v_toBind_2125_, lean_box(0), lean_box(0), v___x_2148_, v___f_2139_);
return v___x_2149_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__3___boxed(lean_object** _args){
lean_object* v___x_2150_ = _args[0];
lean_object* v_toApplicative_2151_ = _args[1];
lean_object* v_toBind_2152_ = _args[2];
lean_object* v___f_2153_ = _args[3];
lean_object* v_inst_2154_ = _args[4];
lean_object* v_inst_2155_ = _args[5];
lean_object* v_inst_2156_ = _args[6];
lean_object* v_pre_2157_ = _args[7];
lean_object* v_post_2158_ = _args[8];
lean_object* v_usedLetOnly_2159_ = _args[9];
lean_object* v_skipConstInApp_2160_ = _args[10];
lean_object* v_skipInstances_2161_ = _args[11];
lean_object* v_x_2162_ = _args[12];
lean_object* v_x_2163_ = _args[13];
lean_object* v_args_2164_ = _args[14];
lean_object* v___y_2165_ = _args[15];
lean_object* v___f_2166_ = _args[16];
lean_object* v_a_2167_ = _args[17];
_start:
{
uint8_t v_usedLetOnly_boxed_2168_; uint8_t v_skipConstInApp_boxed_2169_; uint8_t v_skipInstances_boxed_2170_; lean_object* v_res_2171_; 
v_usedLetOnly_boxed_2168_ = lean_unbox(v_usedLetOnly_2159_);
v_skipConstInApp_boxed_2169_ = lean_unbox(v_skipConstInApp_2160_);
v_skipInstances_boxed_2170_ = lean_unbox(v_skipInstances_2161_);
v_res_2171_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__3(v___x_2150_, v_toApplicative_2151_, v_toBind_2152_, v___f_2153_, v_inst_2154_, v_inst_2155_, v_inst_2156_, v_pre_2157_, v_post_2158_, v_usedLetOnly_boxed_2168_, v_skipConstInApp_boxed_2169_, v_skipInstances_boxed_2170_, v_x_2162_, v_x_2163_, v_args_2164_, v___y_2165_, v___f_2166_, v_a_2167_);
lean_dec(v___y_2165_);
return v_res_2171_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__6(uint8_t v_skipInstances_2172_, lean_object* v_inst_2173_, lean_object* v_inst_2174_, lean_object* v_inst_2175_, lean_object* v_pre_2176_, lean_object* v_post_2177_, uint8_t v_usedLetOnly_2178_, uint8_t v_skipConstInApp_2179_, lean_object* v_x_2180_, lean_object* v_x_2181_, lean_object* v_args_2182_, lean_object* v___x_2183_, lean_object* v_toBind_2184_, lean_object* v_toApplicative_2185_, lean_object* v___f_2186_, lean_object* v_f_2187_, lean_object* v___y_2188_){
_start:
{
if (v_skipInstances_2172_ == 0)
{
lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___f_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; size_t v_sz_2197_; size_t v___x_2198_; lean_object* v___x_3257__overap_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; 
lean_dec(v___f_2186_);
lean_dec_ref(v_toApplicative_2185_);
v___x_2189_ = lean_box(v_usedLetOnly_2178_);
v___x_2190_ = lean_box(v_skipConstInApp_2179_);
v___x_2191_ = lean_box(v_skipInstances_2172_);
lean_inc_n(v___y_2188_, 2);
lean_inc(v_x_2181_);
lean_inc(v_post_2177_);
lean_inc(v_pre_2176_);
lean_inc_ref(v_inst_2175_);
lean_inc(v_inst_2174_);
lean_inc_ref(v_inst_2173_);
v___f_2192_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5___boxed), 13, 12);
lean_closure_set(v___f_2192_, 0, v_f_2187_);
lean_closure_set(v___f_2192_, 1, v_inst_2173_);
lean_closure_set(v___f_2192_, 2, v_inst_2174_);
lean_closure_set(v___f_2192_, 3, v_inst_2175_);
lean_closure_set(v___f_2192_, 4, v_pre_2176_);
lean_closure_set(v___f_2192_, 5, v_post_2177_);
lean_closure_set(v___f_2192_, 6, v___x_2189_);
lean_closure_set(v___f_2192_, 7, v___x_2190_);
lean_closure_set(v___f_2192_, 8, v___x_2191_);
lean_closure_set(v___f_2192_, 9, v_x_2180_);
lean_closure_set(v___f_2192_, 10, v_x_2181_);
lean_closure_set(v___f_2192_, 11, v___y_2188_);
v___x_2193_ = lean_box(v_usedLetOnly_2178_);
v___x_2194_ = lean_box(v_skipConstInApp_2179_);
v___x_2195_ = lean_box(v_skipInstances_2172_);
v___x_2196_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___boxed), 12, 10);
lean_closure_set(v___x_2196_, 0, v_inst_2173_);
lean_closure_set(v___x_2196_, 1, v_inst_2174_);
lean_closure_set(v___x_2196_, 2, v_inst_2175_);
lean_closure_set(v___x_2196_, 3, v_pre_2176_);
lean_closure_set(v___x_2196_, 4, v_post_2177_);
lean_closure_set(v___x_2196_, 5, v___x_2193_);
lean_closure_set(v___x_2196_, 6, v___x_2194_);
lean_closure_set(v___x_2196_, 7, v___x_2195_);
lean_closure_set(v___x_2196_, 8, v_x_2180_);
lean_closure_set(v___x_2196_, 9, v_x_2181_);
v_sz_2197_ = lean_array_size(v_args_2182_);
v___x_2198_ = ((size_t)0ULL);
v___x_3257__overap_2199_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2183_, v___x_2196_, v_sz_2197_, v___x_2198_, v_args_2182_);
v___x_2200_ = lean_apply_1(v___x_3257__overap_2199_, v___y_2188_);
v___x_2201_ = lean_apply_4(v_toBind_2184_, lean_box(0), lean_box(0), v___x_2200_, v___f_2192_);
return v___x_2201_;
}
else
{
lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___f_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___f_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; 
lean_dec_ref(v___x_2183_);
v___x_2202_ = lean_box(v_usedLetOnly_2178_);
v___x_2203_ = lean_box(v_skipConstInApp_2179_);
v___x_2204_ = lean_box(v_skipInstances_2172_);
lean_inc_n(v___y_2188_, 2);
lean_inc(v_x_2181_);
lean_inc(v_post_2177_);
lean_inc(v_pre_2176_);
lean_inc_ref(v_inst_2175_);
lean_inc_n(v_inst_2174_, 2);
lean_inc_ref(v_inst_2173_);
lean_inc_ref(v_f_2187_);
v___f_2205_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5___boxed), 13, 12);
lean_closure_set(v___f_2205_, 0, v_f_2187_);
lean_closure_set(v___f_2205_, 1, v_inst_2173_);
lean_closure_set(v___f_2205_, 2, v_inst_2174_);
lean_closure_set(v___f_2205_, 3, v_inst_2175_);
lean_closure_set(v___f_2205_, 4, v_pre_2176_);
lean_closure_set(v___f_2205_, 5, v_post_2177_);
lean_closure_set(v___f_2205_, 6, v___x_2202_);
lean_closure_set(v___f_2205_, 7, v___x_2203_);
lean_closure_set(v___f_2205_, 8, v___x_2204_);
lean_closure_set(v___f_2205_, 9, v_x_2180_);
lean_closure_set(v___f_2205_, 10, v_x_2181_);
lean_closure_set(v___f_2205_, 11, v___y_2188_);
v___x_2206_ = lean_array_get_size(v_args_2182_);
v___x_2207_ = lean_box(v_usedLetOnly_2178_);
v___x_2208_ = lean_box(v_skipConstInApp_2179_);
v___x_2209_ = lean_box(v_skipInstances_2172_);
lean_inc(v_toBind_2184_);
v___f_2210_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__3___boxed), 18, 17);
lean_closure_set(v___f_2210_, 0, v___x_2206_);
lean_closure_set(v___f_2210_, 1, v_toApplicative_2185_);
lean_closure_set(v___f_2210_, 2, v_toBind_2184_);
lean_closure_set(v___f_2210_, 3, v___f_2186_);
lean_closure_set(v___f_2210_, 4, v_inst_2173_);
lean_closure_set(v___f_2210_, 5, v_inst_2174_);
lean_closure_set(v___f_2210_, 6, v_inst_2175_);
lean_closure_set(v___f_2210_, 7, v_pre_2176_);
lean_closure_set(v___f_2210_, 8, v_post_2177_);
lean_closure_set(v___f_2210_, 9, v___x_2207_);
lean_closure_set(v___f_2210_, 10, v___x_2208_);
lean_closure_set(v___f_2210_, 11, v___x_2209_);
lean_closure_set(v___f_2210_, 12, v_x_2180_);
lean_closure_set(v___f_2210_, 13, v_x_2181_);
lean_closure_set(v___f_2210_, 14, v_args_2182_);
lean_closure_set(v___f_2210_, 15, v___y_2188_);
lean_closure_set(v___f_2210_, 16, v___f_2205_);
v___x_2211_ = lean_alloc_closure((void*)(l_Lean_Meta_getFunInfoNArgs___boxed), 7, 2);
lean_closure_set(v___x_2211_, 0, v_f_2187_);
lean_closure_set(v___x_2211_, 1, v___x_2206_);
v___x_2212_ = lean_apply_2(v_inst_2174_, lean_box(0), v___x_2211_);
v___x_2213_ = lean_apply_4(v_toBind_2184_, lean_box(0), lean_box(0), v___x_2212_, v___f_2210_);
return v___x_2213_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__6___boxed(lean_object** _args){
lean_object* v_skipInstances_2214_ = _args[0];
lean_object* v_inst_2215_ = _args[1];
lean_object* v_inst_2216_ = _args[2];
lean_object* v_inst_2217_ = _args[3];
lean_object* v_pre_2218_ = _args[4];
lean_object* v_post_2219_ = _args[5];
lean_object* v_usedLetOnly_2220_ = _args[6];
lean_object* v_skipConstInApp_2221_ = _args[7];
lean_object* v_x_2222_ = _args[8];
lean_object* v_x_2223_ = _args[9];
lean_object* v_args_2224_ = _args[10];
lean_object* v___x_2225_ = _args[11];
lean_object* v_toBind_2226_ = _args[12];
lean_object* v_toApplicative_2227_ = _args[13];
lean_object* v___f_2228_ = _args[14];
lean_object* v_f_2229_ = _args[15];
lean_object* v___y_2230_ = _args[16];
_start:
{
uint8_t v_skipInstances_boxed_2231_; uint8_t v_usedLetOnly_boxed_2232_; uint8_t v_skipConstInApp_boxed_2233_; lean_object* v_res_2234_; 
v_skipInstances_boxed_2231_ = lean_unbox(v_skipInstances_2214_);
v_usedLetOnly_boxed_2232_ = lean_unbox(v_usedLetOnly_2220_);
v_skipConstInApp_boxed_2233_ = lean_unbox(v_skipConstInApp_2221_);
v_res_2234_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__6(v_skipInstances_boxed_2231_, v_inst_2215_, v_inst_2216_, v_inst_2217_, v_pre_2218_, v_post_2219_, v_usedLetOnly_boxed_2232_, v_skipConstInApp_boxed_2233_, v_x_2222_, v_x_2223_, v_args_2224_, v___x_2225_, v_toBind_2226_, v_toApplicative_2227_, v___f_2228_, v_f_2229_, v___y_2230_);
lean_dec(v___y_2230_);
return v_res_2234_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__9(uint8_t v_skipInstances_2235_, lean_object* v_inst_2236_, lean_object* v_inst_2237_, lean_object* v_inst_2238_, lean_object* v_pre_2239_, lean_object* v_post_2240_, uint8_t v_usedLetOnly_2241_, uint8_t v_skipConstInApp_2242_, lean_object* v_x_2243_, lean_object* v_x_2244_, lean_object* v___x_2245_, lean_object* v_toBind_2246_, lean_object* v_toApplicative_2247_, lean_object* v___f_2248_, lean_object* v_f_2249_, lean_object* v_args_2250_, lean_object* v___y_2251_){
_start:
{
lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___f_2255_; lean_object* v___f_2256_; 
v___x_2252_ = lean_box(v_skipInstances_2235_);
v___x_2253_ = lean_box(v_usedLetOnly_2241_);
v___x_2254_ = lean_box(v_skipConstInApp_2242_);
lean_inc_ref(v_toApplicative_2247_);
lean_inc(v_toBind_2246_);
lean_inc(v_x_2244_);
lean_inc(v_post_2240_);
lean_inc(v_pre_2239_);
lean_inc_ref(v_inst_2238_);
lean_inc(v_inst_2237_);
lean_inc_ref(v_inst_2236_);
v___f_2255_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__6___boxed), 17, 15);
lean_closure_set(v___f_2255_, 0, v___x_2252_);
lean_closure_set(v___f_2255_, 1, v_inst_2236_);
lean_closure_set(v___f_2255_, 2, v_inst_2237_);
lean_closure_set(v___f_2255_, 3, v_inst_2238_);
lean_closure_set(v___f_2255_, 4, v_pre_2239_);
lean_closure_set(v___f_2255_, 5, v_post_2240_);
lean_closure_set(v___f_2255_, 6, v___x_2253_);
lean_closure_set(v___f_2255_, 7, v___x_2254_);
lean_closure_set(v___f_2255_, 8, v_x_2243_);
lean_closure_set(v___f_2255_, 9, v_x_2244_);
lean_closure_set(v___f_2255_, 10, v_args_2250_);
lean_closure_set(v___f_2255_, 11, v___x_2245_);
lean_closure_set(v___f_2255_, 12, v_toBind_2246_);
lean_closure_set(v___f_2255_, 13, v_toApplicative_2247_);
lean_closure_set(v___f_2255_, 14, v___f_2248_);
lean_inc(v___y_2251_);
v___f_2256_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__7___boxed), 3, 2);
lean_closure_set(v___f_2256_, 0, v___f_2255_);
lean_closure_set(v___f_2256_, 1, v___y_2251_);
if (v_skipConstInApp_2242_ == 0)
{
lean_dec_ref(v_toApplicative_2247_);
goto v___jp_2257_;
}
else
{
uint8_t v___x_2260_; 
v___x_2260_ = l_Lean_Expr_isConst(v_f_2249_);
if (v___x_2260_ == 0)
{
lean_dec_ref(v_toApplicative_2247_);
goto v___jp_2257_;
}
else
{
lean_object* v_toPure_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; 
lean_dec(v_x_2244_);
lean_dec(v_post_2240_);
lean_dec(v_pre_2239_);
lean_dec_ref(v_inst_2238_);
lean_dec(v_inst_2237_);
lean_dec_ref(v_inst_2236_);
v_toPure_2261_ = lean_ctor_get(v_toApplicative_2247_, 1);
lean_inc(v_toPure_2261_);
lean_dec_ref(v_toApplicative_2247_);
v___x_2262_ = lean_apply_2(v_toPure_2261_, lean_box(0), v_f_2249_);
v___x_2263_ = lean_apply_4(v_toBind_2246_, lean_box(0), lean_box(0), v___x_2262_, v___f_2256_);
return v___x_2263_;
}
}
v___jp_2257_:
{
lean_object* v___x_2258_; lean_object* v___x_2259_; 
v___x_2258_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2236_, v_inst_2237_, v_inst_2238_, v_pre_2239_, v_post_2240_, v_usedLetOnly_2241_, v_skipConstInApp_2242_, v_skipInstances_2235_, v_x_2243_, v_x_2244_, v_f_2249_, v___y_2251_);
v___x_2259_ = lean_apply_4(v_toBind_2246_, lean_box(0), lean_box(0), v___x_2258_, v___f_2256_);
return v___x_2259_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__9___boxed(lean_object** _args){
lean_object* v_skipInstances_2264_ = _args[0];
lean_object* v_inst_2265_ = _args[1];
lean_object* v_inst_2266_ = _args[2];
lean_object* v_inst_2267_ = _args[3];
lean_object* v_pre_2268_ = _args[4];
lean_object* v_post_2269_ = _args[5];
lean_object* v_usedLetOnly_2270_ = _args[6];
lean_object* v_skipConstInApp_2271_ = _args[7];
lean_object* v_x_2272_ = _args[8];
lean_object* v_x_2273_ = _args[9];
lean_object* v___x_2274_ = _args[10];
lean_object* v_toBind_2275_ = _args[11];
lean_object* v_toApplicative_2276_ = _args[12];
lean_object* v___f_2277_ = _args[13];
lean_object* v_f_2278_ = _args[14];
lean_object* v_args_2279_ = _args[15];
lean_object* v___y_2280_ = _args[16];
_start:
{
uint8_t v_skipInstances_boxed_2281_; uint8_t v_usedLetOnly_boxed_2282_; uint8_t v_skipConstInApp_boxed_2283_; lean_object* v_res_2284_; 
v_skipInstances_boxed_2281_ = lean_unbox(v_skipInstances_2264_);
v_usedLetOnly_boxed_2282_ = lean_unbox(v_usedLetOnly_2270_);
v_skipConstInApp_boxed_2283_ = lean_unbox(v_skipConstInApp_2271_);
v_res_2284_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__9(v_skipInstances_boxed_2281_, v_inst_2265_, v_inst_2266_, v_inst_2267_, v_pre_2268_, v_post_2269_, v_usedLetOnly_boxed_2282_, v_skipConstInApp_boxed_2283_, v_x_2272_, v_x_2273_, v___x_2274_, v_toBind_2275_, v_toApplicative_2276_, v___f_2277_, v_f_2278_, v_args_2279_, v___y_2280_);
lean_dec(v___y_2280_);
return v_res_2284_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__0(lean_object* v_fvars_2287_, lean_object* v_inst_2288_, lean_object* v_inst_2289_, lean_object* v_inst_2290_, lean_object* v_pre_2291_, lean_object* v_post_2292_, uint8_t v_usedLetOnly_2293_, uint8_t v_skipConstInApp_2294_, uint8_t v_skipInstances_2295_, lean_object* v_x_2296_, lean_object* v_x_2297_, lean_object* v_body_2298_, lean_object* v_x_2299_, lean_object* v___y_2300_){
_start:
{
lean_object* v___x_2301_; lean_object* v___x_2302_; 
v___x_2301_ = lean_array_push(v_fvars_2287_, v_x_2299_);
v___x_2302_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(v_inst_2288_, v_inst_2289_, v_inst_2290_, v_pre_2291_, v_post_2292_, v_usedLetOnly_2293_, v_skipConstInApp_2294_, v_skipInstances_2295_, v_x_2296_, v_x_2297_, v___x_2301_, v_body_2298_, v___y_2300_);
return v___x_2302_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__0___boxed(lean_object* v_fvars_2303_, lean_object* v_inst_2304_, lean_object* v_inst_2305_, lean_object* v_inst_2306_, lean_object* v_pre_2307_, lean_object* v_post_2308_, lean_object* v_usedLetOnly_2309_, lean_object* v_skipConstInApp_2310_, lean_object* v_skipInstances_2311_, lean_object* v_x_2312_, lean_object* v_x_2313_, lean_object* v_body_2314_, lean_object* v_x_2315_, lean_object* v___y_2316_){
_start:
{
uint8_t v_usedLetOnly_boxed_2317_; uint8_t v_skipConstInApp_boxed_2318_; uint8_t v_skipInstances_boxed_2319_; lean_object* v_res_2320_; 
v_usedLetOnly_boxed_2317_ = lean_unbox(v_usedLetOnly_2309_);
v_skipConstInApp_boxed_2318_ = lean_unbox(v_skipConstInApp_2310_);
v_skipInstances_boxed_2319_ = lean_unbox(v_skipInstances_2311_);
v_res_2320_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__0(v_fvars_2303_, v_inst_2304_, v_inst_2305_, v_inst_2306_, v_pre_2307_, v_post_2308_, v_usedLetOnly_boxed_2317_, v_skipConstInApp_boxed_2318_, v_skipInstances_boxed_2319_, v_x_2312_, v_x_2313_, v_body_2314_, v_x_2315_, v___y_2316_);
lean_dec(v___y_2316_);
return v_res_2320_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3___boxed(lean_object* v_inst_2321_, lean_object* v_inst_2322_, lean_object* v_inst_2323_, lean_object* v_pre_2324_, lean_object* v_post_2325_, lean_object* v_usedLetOnly_2326_, lean_object* v_skipConstInApp_2327_, lean_object* v_skipInstances_2328_, lean_object* v_x_2329_, lean_object* v_x_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_){
_start:
{
uint8_t v_usedLetOnly_boxed_2333_; uint8_t v_skipConstInApp_boxed_2334_; uint8_t v_skipInstances_boxed_2335_; lean_object* v_res_2336_; 
v_usedLetOnly_boxed_2333_ = lean_unbox(v_usedLetOnly_2326_);
v_skipConstInApp_boxed_2334_ = lean_unbox(v_skipConstInApp_2327_);
v_skipInstances_boxed_2335_ = lean_unbox(v_skipInstances_2328_);
v_res_2336_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3(v_inst_2321_, v_inst_2322_, v_inst_2323_, v_pre_2324_, v_post_2325_, v_usedLetOnly_boxed_2333_, v_skipConstInApp_boxed_2334_, v_skipInstances_boxed_2335_, v_x_2329_, v_x_2330_, v_a_2331_, v_a_2332_);
lean_dec(v_a_2331_);
return v_res_2336_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(lean_object* v_inst_2337_, lean_object* v_inst_2338_, lean_object* v_inst_2339_, lean_object* v_pre_2340_, lean_object* v_post_2341_, uint8_t v_usedLetOnly_2342_, uint8_t v_skipConstInApp_2343_, uint8_t v_skipInstances_2344_, lean_object* v_x_2345_, lean_object* v_x_2346_, lean_object* v_fvars_2347_, lean_object* v_e_2348_, lean_object* v_a_2349_){
_start:
{
lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___f_2354_; lean_object* v___f_2355_; lean_object* v___x_2356_; 
v___x_2350_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0));
v___x_2351_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1));
lean_inc_ref(v_inst_2337_);
v___x_2352_ = l_Lean_MonadCacheT_instMonad___redArg(v_x_2345_, v___x_2350_, v___x_2351_, v_inst_2337_);
v___x_2353_ = l_Lean_MonadCacheT_instMonadControl___redArg(v_x_2345_, v___x_2350_, v___x_2351_);
lean_inc_ref_n(v_inst_2339_, 2);
lean_inc_ref(v___x_2353_);
v___f_2354_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_2354_, 0, v___x_2353_);
lean_closure_set(v___f_2354_, 1, v_inst_2339_);
v___f_2355_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_2355_, 0, v___x_2353_);
lean_closure_set(v___f_2355_, 1, v_inst_2339_);
v___x_2356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2356_, 0, v___f_2354_);
lean_ctor_set(v___x_2356_, 1, v___f_2355_);
if (lean_obj_tag(v_e_2348_) == 7)
{
lean_object* v_binderName_2357_; lean_object* v_binderType_2358_; lean_object* v_body_2359_; uint8_t v_binderInfo_2360_; lean_object* v_toBind_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___f_2365_; lean_object* v___x_2366_; lean_object* v___f_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; 
v_binderName_2357_ = lean_ctor_get(v_e_2348_, 0);
lean_inc(v_binderName_2357_);
v_binderType_2358_ = lean_ctor_get(v_e_2348_, 1);
lean_inc_ref(v_binderType_2358_);
v_body_2359_ = lean_ctor_get(v_e_2348_, 2);
lean_inc_ref(v_body_2359_);
v_binderInfo_2360_ = lean_ctor_get_uint8(v_e_2348_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2348_, 3);
v_toBind_2361_ = lean_ctor_get(v_inst_2337_, 1);
lean_inc(v_toBind_2361_);
v___x_2362_ = lean_box(v_usedLetOnly_2342_);
v___x_2363_ = lean_box(v_skipConstInApp_2343_);
v___x_2364_ = lean_box(v_skipInstances_2344_);
lean_inc(v_x_2346_);
lean_inc(v_post_2341_);
lean_inc(v_pre_2340_);
lean_inc_ref(v_inst_2339_);
lean_inc(v_inst_2338_);
lean_inc_ref(v_inst_2337_);
lean_inc_ref(v_fvars_2347_);
v___f_2365_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__0___boxed), 14, 12);
lean_closure_set(v___f_2365_, 0, v_fvars_2347_);
lean_closure_set(v___f_2365_, 1, v_inst_2337_);
lean_closure_set(v___f_2365_, 2, v_inst_2338_);
lean_closure_set(v___f_2365_, 3, v_inst_2339_);
lean_closure_set(v___f_2365_, 4, v_pre_2340_);
lean_closure_set(v___f_2365_, 5, v_post_2341_);
lean_closure_set(v___f_2365_, 6, v___x_2362_);
lean_closure_set(v___f_2365_, 7, v___x_2363_);
lean_closure_set(v___f_2365_, 8, v___x_2364_);
lean_closure_set(v___f_2365_, 9, v_x_2345_);
lean_closure_set(v___f_2365_, 10, v_x_2346_);
lean_closure_set(v___f_2365_, 11, v_body_2359_);
v___x_2366_ = lean_box(v_binderInfo_2360_);
lean_inc(v_a_2349_);
v___f_2367_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_2367_, 0, v___x_2356_);
lean_closure_set(v___f_2367_, 1, v___x_2352_);
lean_closure_set(v___f_2367_, 2, v_binderName_2357_);
lean_closure_set(v___f_2367_, 3, v___x_2366_);
lean_closure_set(v___f_2367_, 4, v___f_2365_);
lean_closure_set(v___f_2367_, 5, v_a_2349_);
v___x_2368_ = lean_expr_instantiate_rev(v_binderType_2358_, v_fvars_2347_);
lean_dec_ref(v_fvars_2347_);
lean_dec_ref(v_binderType_2358_);
v___x_2369_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2337_, v_inst_2338_, v_inst_2339_, v_pre_2340_, v_post_2341_, v_usedLetOnly_2342_, v_skipConstInApp_2343_, v_skipInstances_2344_, v_x_2345_, v_x_2346_, v___x_2368_, v_a_2349_);
v___x_2370_ = lean_apply_4(v_toBind_2361_, lean_box(0), lean_box(0), v___x_2369_, v___f_2367_);
return v___x_2370_;
}
else
{
lean_object* v_toBind_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___f_2375_; lean_object* v___x_2376_; lean_object* v___f_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; 
lean_dec_ref_known(v___x_2356_, 2);
lean_dec_ref(v___x_2352_);
v_toBind_2371_ = lean_ctor_get(v_inst_2337_, 1);
lean_inc_n(v_toBind_2371_, 2);
v___x_2372_ = lean_box(v_usedLetOnly_2342_);
v___x_2373_ = lean_box(v_skipConstInApp_2343_);
v___x_2374_ = lean_box(v_skipInstances_2344_);
lean_inc(v_a_2349_);
lean_inc(v_x_2346_);
lean_inc(v_post_2341_);
lean_inc(v_pre_2340_);
lean_inc_ref(v_inst_2339_);
lean_inc_n(v_inst_2338_, 2);
lean_inc_ref(v_inst_2337_);
v___f_2375_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3___boxed), 12, 11);
lean_closure_set(v___f_2375_, 0, v_inst_2337_);
lean_closure_set(v___f_2375_, 1, v_inst_2338_);
lean_closure_set(v___f_2375_, 2, v_inst_2339_);
lean_closure_set(v___f_2375_, 3, v_pre_2340_);
lean_closure_set(v___f_2375_, 4, v_post_2341_);
lean_closure_set(v___f_2375_, 5, v___x_2372_);
lean_closure_set(v___f_2375_, 6, v___x_2373_);
lean_closure_set(v___f_2375_, 7, v___x_2374_);
lean_closure_set(v___f_2375_, 8, v_x_2345_);
lean_closure_set(v___f_2375_, 9, v_x_2346_);
lean_closure_set(v___f_2375_, 10, v_a_2349_);
v___x_2376_ = lean_box(v_usedLetOnly_2342_);
lean_inc_ref(v_fvars_2347_);
v___f_2377_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__3___boxed), 6, 5);
lean_closure_set(v___f_2377_, 0, v_fvars_2347_);
lean_closure_set(v___f_2377_, 1, v___x_2376_);
lean_closure_set(v___f_2377_, 2, v_inst_2338_);
lean_closure_set(v___f_2377_, 3, v_toBind_2371_);
lean_closure_set(v___f_2377_, 4, v___f_2375_);
v___x_2378_ = lean_expr_instantiate_rev(v_e_2348_, v_fvars_2347_);
lean_dec_ref(v_fvars_2347_);
lean_dec_ref(v_e_2348_);
v___x_2379_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2337_, v_inst_2338_, v_inst_2339_, v_pre_2340_, v_post_2341_, v_usedLetOnly_2342_, v_skipConstInApp_2343_, v_skipInstances_2344_, v_x_2345_, v_x_2346_, v___x_2378_, v_a_2349_);
v___x_2380_ = lean_apply_4(v_toBind_2371_, lean_box(0), lean_box(0), v___x_2379_, v___f_2377_);
return v___x_2380_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__0(lean_object* v_fvars_2381_, lean_object* v_inst_2382_, lean_object* v_inst_2383_, lean_object* v_inst_2384_, lean_object* v_pre_2385_, lean_object* v_post_2386_, uint8_t v_usedLetOnly_2387_, uint8_t v_skipConstInApp_2388_, uint8_t v_skipInstances_2389_, lean_object* v_x_2390_, lean_object* v_x_2391_, lean_object* v_body_2392_, lean_object* v_x_2393_, lean_object* v___y_2394_){
_start:
{
lean_object* v___x_2395_; lean_object* v___x_2396_; 
v___x_2395_ = lean_array_push(v_fvars_2381_, v_x_2393_);
v___x_2396_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(v_inst_2382_, v_inst_2383_, v_inst_2384_, v_pre_2385_, v_post_2386_, v_usedLetOnly_2387_, v_skipConstInApp_2388_, v_skipInstances_2389_, v_x_2390_, v_x_2391_, v___x_2395_, v_body_2392_, v___y_2394_);
return v___x_2396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__0___boxed(lean_object* v_fvars_2397_, lean_object* v_inst_2398_, lean_object* v_inst_2399_, lean_object* v_inst_2400_, lean_object* v_pre_2401_, lean_object* v_post_2402_, lean_object* v_usedLetOnly_2403_, lean_object* v_skipConstInApp_2404_, lean_object* v_skipInstances_2405_, lean_object* v_x_2406_, lean_object* v_x_2407_, lean_object* v_body_2408_, lean_object* v_x_2409_, lean_object* v___y_2410_){
_start:
{
uint8_t v_usedLetOnly_boxed_2411_; uint8_t v_skipConstInApp_boxed_2412_; uint8_t v_skipInstances_boxed_2413_; lean_object* v_res_2414_; 
v_usedLetOnly_boxed_2411_ = lean_unbox(v_usedLetOnly_2403_);
v_skipConstInApp_boxed_2412_ = lean_unbox(v_skipConstInApp_2404_);
v_skipInstances_boxed_2413_ = lean_unbox(v_skipInstances_2405_);
v_res_2414_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__0(v_fvars_2397_, v_inst_2398_, v_inst_2399_, v_inst_2400_, v_pre_2401_, v_post_2402_, v_usedLetOnly_boxed_2411_, v_skipConstInApp_boxed_2412_, v_skipInstances_boxed_2413_, v_x_2406_, v_x_2407_, v_body_2408_, v_x_2409_, v___y_2410_);
lean_dec(v___y_2410_);
return v_res_2414_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(lean_object* v_inst_2415_, lean_object* v_inst_2416_, lean_object* v_inst_2417_, lean_object* v_pre_2418_, lean_object* v_post_2419_, uint8_t v_usedLetOnly_2420_, uint8_t v_skipConstInApp_2421_, uint8_t v_skipInstances_2422_, lean_object* v_x_2423_, lean_object* v_x_2424_, lean_object* v_fvars_2425_, lean_object* v_e_2426_, lean_object* v_a_2427_){
_start:
{
lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___f_2432_; lean_object* v___f_2433_; lean_object* v___x_2434_; 
v___x_2428_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0));
v___x_2429_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1));
lean_inc_ref(v_inst_2415_);
v___x_2430_ = l_Lean_MonadCacheT_instMonad___redArg(v_x_2423_, v___x_2428_, v___x_2429_, v_inst_2415_);
v___x_2431_ = l_Lean_MonadCacheT_instMonadControl___redArg(v_x_2423_, v___x_2428_, v___x_2429_);
lean_inc_ref_n(v_inst_2417_, 2);
lean_inc_ref(v___x_2431_);
v___f_2432_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_2432_, 0, v___x_2431_);
lean_closure_set(v___f_2432_, 1, v_inst_2417_);
v___f_2433_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_2433_, 0, v___x_2431_);
lean_closure_set(v___f_2433_, 1, v_inst_2417_);
v___x_2434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2434_, 0, v___f_2432_);
lean_ctor_set(v___x_2434_, 1, v___f_2433_);
if (lean_obj_tag(v_e_2426_) == 6)
{
lean_object* v_binderName_2435_; lean_object* v_binderType_2436_; lean_object* v_body_2437_; uint8_t v_binderInfo_2438_; lean_object* v_toBind_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___f_2443_; lean_object* v___x_2444_; lean_object* v___f_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; 
v_binderName_2435_ = lean_ctor_get(v_e_2426_, 0);
lean_inc(v_binderName_2435_);
v_binderType_2436_ = lean_ctor_get(v_e_2426_, 1);
lean_inc_ref(v_binderType_2436_);
v_body_2437_ = lean_ctor_get(v_e_2426_, 2);
lean_inc_ref(v_body_2437_);
v_binderInfo_2438_ = lean_ctor_get_uint8(v_e_2426_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2426_, 3);
v_toBind_2439_ = lean_ctor_get(v_inst_2415_, 1);
lean_inc(v_toBind_2439_);
v___x_2440_ = lean_box(v_usedLetOnly_2420_);
v___x_2441_ = lean_box(v_skipConstInApp_2421_);
v___x_2442_ = lean_box(v_skipInstances_2422_);
lean_inc(v_x_2424_);
lean_inc(v_post_2419_);
lean_inc(v_pre_2418_);
lean_inc_ref(v_inst_2417_);
lean_inc(v_inst_2416_);
lean_inc_ref(v_inst_2415_);
lean_inc_ref(v_fvars_2425_);
v___f_2443_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__0___boxed), 14, 12);
lean_closure_set(v___f_2443_, 0, v_fvars_2425_);
lean_closure_set(v___f_2443_, 1, v_inst_2415_);
lean_closure_set(v___f_2443_, 2, v_inst_2416_);
lean_closure_set(v___f_2443_, 3, v_inst_2417_);
lean_closure_set(v___f_2443_, 4, v_pre_2418_);
lean_closure_set(v___f_2443_, 5, v_post_2419_);
lean_closure_set(v___f_2443_, 6, v___x_2440_);
lean_closure_set(v___f_2443_, 7, v___x_2441_);
lean_closure_set(v___f_2443_, 8, v___x_2442_);
lean_closure_set(v___f_2443_, 9, v_x_2423_);
lean_closure_set(v___f_2443_, 10, v_x_2424_);
lean_closure_set(v___f_2443_, 11, v_body_2437_);
v___x_2444_ = lean_box(v_binderInfo_2438_);
lean_inc(v_a_2427_);
v___f_2445_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_2445_, 0, v___x_2434_);
lean_closure_set(v___f_2445_, 1, v___x_2430_);
lean_closure_set(v___f_2445_, 2, v_binderName_2435_);
lean_closure_set(v___f_2445_, 3, v___x_2444_);
lean_closure_set(v___f_2445_, 4, v___f_2443_);
lean_closure_set(v___f_2445_, 5, v_a_2427_);
v___x_2446_ = lean_expr_instantiate_rev(v_binderType_2436_, v_fvars_2425_);
lean_dec_ref(v_fvars_2425_);
lean_dec_ref(v_binderType_2436_);
v___x_2447_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2415_, v_inst_2416_, v_inst_2417_, v_pre_2418_, v_post_2419_, v_usedLetOnly_2420_, v_skipConstInApp_2421_, v_skipInstances_2422_, v_x_2423_, v_x_2424_, v___x_2446_, v_a_2427_);
v___x_2448_ = lean_apply_4(v_toBind_2439_, lean_box(0), lean_box(0), v___x_2447_, v___f_2445_);
return v___x_2448_;
}
else
{
lean_object* v_toBind_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___f_2453_; lean_object* v___x_2454_; lean_object* v___f_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; 
lean_dec_ref_known(v___x_2434_, 2);
lean_dec_ref(v___x_2430_);
v_toBind_2449_ = lean_ctor_get(v_inst_2415_, 1);
lean_inc_n(v_toBind_2449_, 2);
v___x_2450_ = lean_box(v_usedLetOnly_2420_);
v___x_2451_ = lean_box(v_skipConstInApp_2421_);
v___x_2452_ = lean_box(v_skipInstances_2422_);
lean_inc(v_a_2427_);
lean_inc(v_x_2424_);
lean_inc(v_post_2419_);
lean_inc(v_pre_2418_);
lean_inc_ref(v_inst_2417_);
lean_inc_n(v_inst_2416_, 2);
lean_inc_ref(v_inst_2415_);
v___f_2453_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3___boxed), 12, 11);
lean_closure_set(v___f_2453_, 0, v_inst_2415_);
lean_closure_set(v___f_2453_, 1, v_inst_2416_);
lean_closure_set(v___f_2453_, 2, v_inst_2417_);
lean_closure_set(v___f_2453_, 3, v_pre_2418_);
lean_closure_set(v___f_2453_, 4, v_post_2419_);
lean_closure_set(v___f_2453_, 5, v___x_2450_);
lean_closure_set(v___f_2453_, 6, v___x_2451_);
lean_closure_set(v___f_2453_, 7, v___x_2452_);
lean_closure_set(v___f_2453_, 8, v_x_2423_);
lean_closure_set(v___f_2453_, 9, v_x_2424_);
lean_closure_set(v___f_2453_, 10, v_a_2427_);
v___x_2454_ = lean_box(v_usedLetOnly_2420_);
lean_inc_ref(v_fvars_2425_);
v___f_2455_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__3___boxed), 6, 5);
lean_closure_set(v___f_2455_, 0, v_fvars_2425_);
lean_closure_set(v___f_2455_, 1, v___x_2454_);
lean_closure_set(v___f_2455_, 2, v_inst_2416_);
lean_closure_set(v___f_2455_, 3, v_toBind_2449_);
lean_closure_set(v___f_2455_, 4, v___f_2453_);
v___x_2456_ = lean_expr_instantiate_rev(v_e_2426_, v_fvars_2425_);
lean_dec_ref(v_fvars_2425_);
lean_dec_ref(v_e_2426_);
v___x_2457_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2415_, v_inst_2416_, v_inst_2417_, v_pre_2418_, v_post_2419_, v_usedLetOnly_2420_, v_skipConstInApp_2421_, v_skipInstances_2422_, v_x_2423_, v_x_2424_, v___x_2456_, v_a_2427_);
v___x_2458_ = lean_apply_4(v_toBind_2449_, lean_box(0), lean_box(0), v___x_2457_, v___f_2455_);
return v___x_2458_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__0(lean_object* v_fvars_2459_, lean_object* v_inst_2460_, lean_object* v_inst_2461_, lean_object* v_inst_2462_, lean_object* v_pre_2463_, lean_object* v_post_2464_, uint8_t v_usedLetOnly_2465_, uint8_t v_skipConstInApp_2466_, uint8_t v_skipInstances_2467_, lean_object* v_x_2468_, lean_object* v_x_2469_, lean_object* v_body_2470_, lean_object* v_x_2471_, lean_object* v___y_2472_){
_start:
{
lean_object* v___x_2473_; lean_object* v___x_2474_; 
v___x_2473_ = lean_array_push(v_fvars_2459_, v_x_2471_);
v___x_2474_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(v_inst_2460_, v_inst_2461_, v_inst_2462_, v_pre_2463_, v_post_2464_, v_usedLetOnly_2465_, v_skipConstInApp_2466_, v_skipInstances_2467_, v_x_2468_, v_x_2469_, v___x_2473_, v_body_2470_, v___y_2472_);
return v___x_2474_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__0___boxed(lean_object* v_fvars_2475_, lean_object* v_inst_2476_, lean_object* v_inst_2477_, lean_object* v_inst_2478_, lean_object* v_pre_2479_, lean_object* v_post_2480_, lean_object* v_usedLetOnly_2481_, lean_object* v_skipConstInApp_2482_, lean_object* v_skipInstances_2483_, lean_object* v_x_2484_, lean_object* v_x_2485_, lean_object* v_body_2486_, lean_object* v_x_2487_, lean_object* v___y_2488_){
_start:
{
uint8_t v_usedLetOnly_boxed_2489_; uint8_t v_skipConstInApp_boxed_2490_; uint8_t v_skipInstances_boxed_2491_; lean_object* v_res_2492_; 
v_usedLetOnly_boxed_2489_ = lean_unbox(v_usedLetOnly_2481_);
v_skipConstInApp_boxed_2490_ = lean_unbox(v_skipConstInApp_2482_);
v_skipInstances_boxed_2491_ = lean_unbox(v_skipInstances_2483_);
v_res_2492_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__0(v_fvars_2475_, v_inst_2476_, v_inst_2477_, v_inst_2478_, v_pre_2479_, v_post_2480_, v_usedLetOnly_boxed_2489_, v_skipConstInApp_boxed_2490_, v_skipInstances_boxed_2491_, v_x_2484_, v_x_2485_, v_body_2486_, v_x_2487_, v___y_2488_);
lean_dec(v___y_2488_);
return v_res_2492_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__2(lean_object* v___x_2493_, lean_object* v___x_2494_, lean_object* v_declName_2495_, lean_object* v___f_2496_, uint8_t v_nondep_2497_, lean_object* v_a_2498_, lean_object* v_value_2499_, lean_object* v_fvars_2500_, lean_object* v_inst_2501_, lean_object* v_inst_2502_, lean_object* v_inst_2503_, lean_object* v_pre_2504_, lean_object* v_post_2505_, uint8_t v_usedLetOnly_2506_, uint8_t v_skipConstInApp_2507_, uint8_t v_skipInstances_2508_, lean_object* v_x_2509_, lean_object* v_x_2510_, lean_object* v_toBind_2511_, lean_object* v_a_2512_){
_start:
{
lean_object* v___x_2513_; lean_object* v___f_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; 
v___x_2513_ = lean_box(v_nondep_2497_);
lean_inc(v_a_2498_);
v___f_2514_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_2514_, 0, v___x_2493_);
lean_closure_set(v___f_2514_, 1, v___x_2494_);
lean_closure_set(v___f_2514_, 2, v_declName_2495_);
lean_closure_set(v___f_2514_, 3, v_a_2512_);
lean_closure_set(v___f_2514_, 4, v___f_2496_);
lean_closure_set(v___f_2514_, 5, v___x_2513_);
lean_closure_set(v___f_2514_, 6, v_a_2498_);
v___x_2515_ = lean_expr_instantiate_rev(v_value_2499_, v_fvars_2500_);
v___x_2516_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2501_, v_inst_2502_, v_inst_2503_, v_pre_2504_, v_post_2505_, v_usedLetOnly_2506_, v_skipConstInApp_2507_, v_skipInstances_2508_, v_x_2509_, v_x_2510_, v___x_2515_, v_a_2498_);
v___x_2517_ = lean_apply_4(v_toBind_2511_, lean_box(0), lean_box(0), v___x_2516_, v___f_2514_);
return v___x_2517_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__2___boxed(lean_object** _args){
lean_object* v___x_2518_ = _args[0];
lean_object* v___x_2519_ = _args[1];
lean_object* v_declName_2520_ = _args[2];
lean_object* v___f_2521_ = _args[3];
lean_object* v_nondep_2522_ = _args[4];
lean_object* v_a_2523_ = _args[5];
lean_object* v_value_2524_ = _args[6];
lean_object* v_fvars_2525_ = _args[7];
lean_object* v_inst_2526_ = _args[8];
lean_object* v_inst_2527_ = _args[9];
lean_object* v_inst_2528_ = _args[10];
lean_object* v_pre_2529_ = _args[11];
lean_object* v_post_2530_ = _args[12];
lean_object* v_usedLetOnly_2531_ = _args[13];
lean_object* v_skipConstInApp_2532_ = _args[14];
lean_object* v_skipInstances_2533_ = _args[15];
lean_object* v_x_2534_ = _args[16];
lean_object* v_x_2535_ = _args[17];
lean_object* v_toBind_2536_ = _args[18];
lean_object* v_a_2537_ = _args[19];
_start:
{
uint8_t v_nondep_3815__boxed_2538_; uint8_t v_usedLetOnly_boxed_2539_; uint8_t v_skipConstInApp_boxed_2540_; uint8_t v_skipInstances_boxed_2541_; lean_object* v_res_2542_; 
v_nondep_3815__boxed_2538_ = lean_unbox(v_nondep_2522_);
v_usedLetOnly_boxed_2539_ = lean_unbox(v_usedLetOnly_2531_);
v_skipConstInApp_boxed_2540_ = lean_unbox(v_skipConstInApp_2532_);
v_skipInstances_boxed_2541_ = lean_unbox(v_skipInstances_2533_);
v_res_2542_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__2(v___x_2518_, v___x_2519_, v_declName_2520_, v___f_2521_, v_nondep_3815__boxed_2538_, v_a_2523_, v_value_2524_, v_fvars_2525_, v_inst_2526_, v_inst_2527_, v_inst_2528_, v_pre_2529_, v_post_2530_, v_usedLetOnly_boxed_2539_, v_skipConstInApp_boxed_2540_, v_skipInstances_boxed_2541_, v_x_2534_, v_x_2535_, v_toBind_2536_, v_a_2537_);
lean_dec_ref(v_fvars_2525_);
lean_dec_ref(v_value_2524_);
lean_dec(v_a_2523_);
return v_res_2542_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(lean_object* v_inst_2543_, lean_object* v_inst_2544_, lean_object* v_inst_2545_, lean_object* v_pre_2546_, lean_object* v_post_2547_, uint8_t v_usedLetOnly_2548_, uint8_t v_skipConstInApp_2549_, uint8_t v_skipInstances_2550_, lean_object* v_x_2551_, lean_object* v_x_2552_, lean_object* v_fvars_2553_, lean_object* v_e_2554_, lean_object* v_a_2555_){
_start:
{
lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___f_2560_; lean_object* v___f_2561_; lean_object* v___x_2562_; 
v___x_2556_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0));
v___x_2557_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1));
lean_inc_ref(v_inst_2543_);
v___x_2558_ = l_Lean_MonadCacheT_instMonad___redArg(v_x_2551_, v___x_2556_, v___x_2557_, v_inst_2543_);
v___x_2559_ = l_Lean_MonadCacheT_instMonadControl___redArg(v_x_2551_, v___x_2556_, v___x_2557_);
lean_inc_ref_n(v_inst_2545_, 2);
lean_inc_ref(v___x_2559_);
v___f_2560_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_2560_, 0, v___x_2559_);
lean_closure_set(v___f_2560_, 1, v_inst_2545_);
v___f_2561_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_2561_, 0, v___x_2559_);
lean_closure_set(v___f_2561_, 1, v_inst_2545_);
v___x_2562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2562_, 0, v___f_2560_);
lean_ctor_set(v___x_2562_, 1, v___f_2561_);
if (lean_obj_tag(v_e_2554_) == 8)
{
lean_object* v_declName_2563_; lean_object* v_type_2564_; lean_object* v_value_2565_; lean_object* v_body_2566_; uint8_t v_nondep_2567_; lean_object* v_toBind_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___f_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___f_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; 
v_declName_2563_ = lean_ctor_get(v_e_2554_, 0);
lean_inc(v_declName_2563_);
v_type_2564_ = lean_ctor_get(v_e_2554_, 1);
lean_inc_ref(v_type_2564_);
v_value_2565_ = lean_ctor_get(v_e_2554_, 2);
lean_inc_ref(v_value_2565_);
v_body_2566_ = lean_ctor_get(v_e_2554_, 3);
lean_inc_ref(v_body_2566_);
v_nondep_2567_ = lean_ctor_get_uint8(v_e_2554_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_2554_, 4);
v_toBind_2568_ = lean_ctor_get(v_inst_2543_, 1);
lean_inc_n(v_toBind_2568_, 2);
v___x_2569_ = lean_box(v_usedLetOnly_2548_);
v___x_2570_ = lean_box(v_skipConstInApp_2549_);
v___x_2571_ = lean_box(v_skipInstances_2550_);
lean_inc_n(v_x_2552_, 2);
lean_inc_n(v_post_2547_, 2);
lean_inc_n(v_pre_2546_, 2);
lean_inc_ref_n(v_inst_2545_, 2);
lean_inc_n(v_inst_2544_, 2);
lean_inc_ref_n(v_inst_2543_, 2);
lean_inc_ref_n(v_fvars_2553_, 2);
v___f_2572_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__0___boxed), 14, 12);
lean_closure_set(v___f_2572_, 0, v_fvars_2553_);
lean_closure_set(v___f_2572_, 1, v_inst_2543_);
lean_closure_set(v___f_2572_, 2, v_inst_2544_);
lean_closure_set(v___f_2572_, 3, v_inst_2545_);
lean_closure_set(v___f_2572_, 4, v_pre_2546_);
lean_closure_set(v___f_2572_, 5, v_post_2547_);
lean_closure_set(v___f_2572_, 6, v___x_2569_);
lean_closure_set(v___f_2572_, 7, v___x_2570_);
lean_closure_set(v___f_2572_, 8, v___x_2571_);
lean_closure_set(v___f_2572_, 9, v_x_2551_);
lean_closure_set(v___f_2572_, 10, v_x_2552_);
lean_closure_set(v___f_2572_, 11, v_body_2566_);
v___x_2573_ = lean_box(v_nondep_2567_);
v___x_2574_ = lean_box(v_usedLetOnly_2548_);
v___x_2575_ = lean_box(v_skipConstInApp_2549_);
v___x_2576_ = lean_box(v_skipInstances_2550_);
lean_inc(v_a_2555_);
v___f_2577_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__2___boxed), 20, 19);
lean_closure_set(v___f_2577_, 0, v___x_2562_);
lean_closure_set(v___f_2577_, 1, v___x_2558_);
lean_closure_set(v___f_2577_, 2, v_declName_2563_);
lean_closure_set(v___f_2577_, 3, v___f_2572_);
lean_closure_set(v___f_2577_, 4, v___x_2573_);
lean_closure_set(v___f_2577_, 5, v_a_2555_);
lean_closure_set(v___f_2577_, 6, v_value_2565_);
lean_closure_set(v___f_2577_, 7, v_fvars_2553_);
lean_closure_set(v___f_2577_, 8, v_inst_2543_);
lean_closure_set(v___f_2577_, 9, v_inst_2544_);
lean_closure_set(v___f_2577_, 10, v_inst_2545_);
lean_closure_set(v___f_2577_, 11, v_pre_2546_);
lean_closure_set(v___f_2577_, 12, v_post_2547_);
lean_closure_set(v___f_2577_, 13, v___x_2574_);
lean_closure_set(v___f_2577_, 14, v___x_2575_);
lean_closure_set(v___f_2577_, 15, v___x_2576_);
lean_closure_set(v___f_2577_, 16, v_x_2551_);
lean_closure_set(v___f_2577_, 17, v_x_2552_);
lean_closure_set(v___f_2577_, 18, v_toBind_2568_);
v___x_2578_ = lean_expr_instantiate_rev(v_type_2564_, v_fvars_2553_);
lean_dec_ref(v_fvars_2553_);
lean_dec_ref(v_type_2564_);
v___x_2579_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2543_, v_inst_2544_, v_inst_2545_, v_pre_2546_, v_post_2547_, v_usedLetOnly_2548_, v_skipConstInApp_2549_, v_skipInstances_2550_, v_x_2551_, v_x_2552_, v___x_2578_, v_a_2555_);
v___x_2580_ = lean_apply_4(v_toBind_2568_, lean_box(0), lean_box(0), v___x_2579_, v___f_2577_);
return v___x_2580_;
}
else
{
lean_object* v_toBind_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___f_2585_; lean_object* v___x_2586_; lean_object* v___f_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; 
lean_dec_ref_known(v___x_2562_, 2);
lean_dec_ref(v___x_2558_);
v_toBind_2581_ = lean_ctor_get(v_inst_2543_, 1);
lean_inc_n(v_toBind_2581_, 2);
v___x_2582_ = lean_box(v_usedLetOnly_2548_);
v___x_2583_ = lean_box(v_skipConstInApp_2549_);
v___x_2584_ = lean_box(v_skipInstances_2550_);
lean_inc(v_a_2555_);
lean_inc(v_x_2552_);
lean_inc(v_post_2547_);
lean_inc(v_pre_2546_);
lean_inc_ref(v_inst_2545_);
lean_inc_n(v_inst_2544_, 2);
lean_inc_ref(v_inst_2543_);
v___f_2585_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3___boxed), 12, 11);
lean_closure_set(v___f_2585_, 0, v_inst_2543_);
lean_closure_set(v___f_2585_, 1, v_inst_2544_);
lean_closure_set(v___f_2585_, 2, v_inst_2545_);
lean_closure_set(v___f_2585_, 3, v_pre_2546_);
lean_closure_set(v___f_2585_, 4, v_post_2547_);
lean_closure_set(v___f_2585_, 5, v___x_2582_);
lean_closure_set(v___f_2585_, 6, v___x_2583_);
lean_closure_set(v___f_2585_, 7, v___x_2584_);
lean_closure_set(v___f_2585_, 8, v_x_2551_);
lean_closure_set(v___f_2585_, 9, v_x_2552_);
lean_closure_set(v___f_2585_, 10, v_a_2555_);
v___x_2586_ = lean_box(v_usedLetOnly_2548_);
lean_inc_ref(v_fvars_2553_);
v___f_2587_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__4___boxed), 6, 5);
lean_closure_set(v___f_2587_, 0, v_fvars_2553_);
lean_closure_set(v___f_2587_, 1, v___x_2586_);
lean_closure_set(v___f_2587_, 2, v_inst_2544_);
lean_closure_set(v___f_2587_, 3, v_toBind_2581_);
lean_closure_set(v___f_2587_, 4, v___f_2585_);
v___x_2588_ = lean_expr_instantiate_rev(v_e_2554_, v_fvars_2553_);
lean_dec_ref(v_fvars_2553_);
lean_dec_ref(v_e_2554_);
v___x_2589_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2543_, v_inst_2544_, v_inst_2545_, v_pre_2546_, v_post_2547_, v_usedLetOnly_2548_, v_skipConstInApp_2549_, v_skipInstances_2550_, v_x_2551_, v_x_2552_, v___x_2588_, v_a_2555_);
v___x_2590_ = lean_apply_4(v_toBind_2581_, lean_box(0), lean_box(0), v___x_2589_, v___f_2587_);
return v___x_2590_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__8(lean_object* v_expr_2591_, lean_object* v_data_2592_, lean_object* v_inst_2593_, lean_object* v_inst_2594_, lean_object* v_inst_2595_, lean_object* v_pre_2596_, lean_object* v_post_2597_, uint8_t v_usedLetOnly_2598_, uint8_t v_skipConstInApp_2599_, uint8_t v_skipInstances_2600_, lean_object* v_x_2601_, lean_object* v_x_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v_a_2605_){
_start:
{
size_t v___x_2606_; size_t v___x_2607_; uint8_t v___x_2608_; 
v___x_2606_ = lean_ptr_addr(v_expr_2591_);
v___x_2607_ = lean_ptr_addr(v_a_2605_);
v___x_2608_ = lean_usize_dec_eq(v___x_2606_, v___x_2607_);
if (v___x_2608_ == 0)
{
lean_object* v___x_2609_; lean_object* v___x_2610_; 
lean_dec_ref(v___y_2604_);
v___x_2609_ = l_Lean_Expr_mdata___override(v_data_2592_, v_a_2605_);
v___x_2610_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2593_, v_inst_2594_, v_inst_2595_, v_pre_2596_, v_post_2597_, v_usedLetOnly_2598_, v_skipConstInApp_2599_, v_skipInstances_2600_, v_x_2601_, v_x_2602_, v___x_2609_, v___y_2603_);
return v___x_2610_;
}
else
{
lean_object* v___x_2611_; 
lean_dec_ref(v_a_2605_);
lean_dec(v_data_2592_);
v___x_2611_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2593_, v_inst_2594_, v_inst_2595_, v_pre_2596_, v_post_2597_, v_usedLetOnly_2598_, v_skipConstInApp_2599_, v_skipInstances_2600_, v_x_2601_, v_x_2602_, v___y_2604_, v___y_2603_);
return v___x_2611_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__8___boxed(lean_object* v_expr_2612_, lean_object* v_data_2613_, lean_object* v_inst_2614_, lean_object* v_inst_2615_, lean_object* v_inst_2616_, lean_object* v_pre_2617_, lean_object* v_post_2618_, lean_object* v_usedLetOnly_2619_, lean_object* v_skipConstInApp_2620_, lean_object* v_skipInstances_2621_, lean_object* v_x_2622_, lean_object* v_x_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v_a_2626_){
_start:
{
uint8_t v_usedLetOnly_boxed_2627_; uint8_t v_skipConstInApp_boxed_2628_; uint8_t v_skipInstances_boxed_2629_; lean_object* v_res_2630_; 
v_usedLetOnly_boxed_2627_ = lean_unbox(v_usedLetOnly_2619_);
v_skipConstInApp_boxed_2628_ = lean_unbox(v_skipConstInApp_2620_);
v_skipInstances_boxed_2629_ = lean_unbox(v_skipInstances_2621_);
v_res_2630_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__8(v_expr_2612_, v_data_2613_, v_inst_2614_, v_inst_2615_, v_inst_2616_, v_pre_2617_, v_post_2618_, v_usedLetOnly_boxed_2627_, v_skipConstInApp_boxed_2628_, v_skipInstances_boxed_2629_, v_x_2622_, v_x_2623_, v___y_2624_, v___y_2625_, v_a_2626_);
lean_dec(v___y_2624_);
lean_dec_ref(v_expr_2612_);
return v_res_2630_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__10(lean_object* v_struct_2631_, lean_object* v_typeName_2632_, lean_object* v_idx_2633_, lean_object* v_inst_2634_, lean_object* v_inst_2635_, lean_object* v_inst_2636_, lean_object* v_pre_2637_, lean_object* v_post_2638_, uint8_t v_usedLetOnly_2639_, uint8_t v_skipConstInApp_2640_, uint8_t v_skipInstances_2641_, lean_object* v_x_2642_, lean_object* v_x_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v_a_2646_){
_start:
{
size_t v___x_2647_; size_t v___x_2648_; uint8_t v___x_2649_; 
v___x_2647_ = lean_ptr_addr(v_struct_2631_);
v___x_2648_ = lean_ptr_addr(v_a_2646_);
v___x_2649_ = lean_usize_dec_eq(v___x_2647_, v___x_2648_);
if (v___x_2649_ == 0)
{
lean_object* v___x_2650_; lean_object* v___x_2651_; 
lean_dec_ref(v___y_2645_);
v___x_2650_ = l_Lean_Expr_proj___override(v_typeName_2632_, v_idx_2633_, v_a_2646_);
v___x_2651_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2634_, v_inst_2635_, v_inst_2636_, v_pre_2637_, v_post_2638_, v_usedLetOnly_2639_, v_skipConstInApp_2640_, v_skipInstances_2641_, v_x_2642_, v_x_2643_, v___x_2650_, v___y_2644_);
return v___x_2651_;
}
else
{
lean_object* v___x_2652_; 
lean_dec_ref(v_a_2646_);
lean_dec(v_idx_2633_);
lean_dec(v_typeName_2632_);
v___x_2652_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2634_, v_inst_2635_, v_inst_2636_, v_pre_2637_, v_post_2638_, v_usedLetOnly_2639_, v_skipConstInApp_2640_, v_skipInstances_2641_, v_x_2642_, v_x_2643_, v___y_2645_, v___y_2644_);
return v___x_2652_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__10___boxed(lean_object* v_struct_2653_, lean_object* v_typeName_2654_, lean_object* v_idx_2655_, lean_object* v_inst_2656_, lean_object* v_inst_2657_, lean_object* v_inst_2658_, lean_object* v_pre_2659_, lean_object* v_post_2660_, lean_object* v_usedLetOnly_2661_, lean_object* v_skipConstInApp_2662_, lean_object* v_skipInstances_2663_, lean_object* v_x_2664_, lean_object* v_x_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v_a_2668_){
_start:
{
uint8_t v_usedLetOnly_boxed_2669_; uint8_t v_skipConstInApp_boxed_2670_; uint8_t v_skipInstances_boxed_2671_; lean_object* v_res_2672_; 
v_usedLetOnly_boxed_2669_ = lean_unbox(v_usedLetOnly_2661_);
v_skipConstInApp_boxed_2670_ = lean_unbox(v_skipConstInApp_2662_);
v_skipInstances_boxed_2671_ = lean_unbox(v_skipInstances_2663_);
v_res_2672_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__10(v_struct_2653_, v_typeName_2654_, v_idx_2655_, v_inst_2656_, v_inst_2657_, v_inst_2658_, v_pre_2659_, v_post_2660_, v_usedLetOnly_boxed_2669_, v_skipConstInApp_boxed_2670_, v_skipInstances_boxed_2671_, v_x_2664_, v_x_2665_, v___y_2666_, v___y_2667_, v_a_2668_);
lean_dec(v___y_2666_);
lean_dec_ref(v_struct_2653_);
return v_res_2672_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11(lean_object* v_toApplicative_2673_, lean_object* v_inst_2674_, lean_object* v_inst_2675_, lean_object* v_inst_2676_, lean_object* v_pre_2677_, lean_object* v_post_2678_, uint8_t v_usedLetOnly_2679_, uint8_t v_skipConstInApp_2680_, uint8_t v_skipInstances_2681_, lean_object* v_x_2682_, lean_object* v_x_2683_, lean_object* v___y_2684_, lean_object* v___f_2685_, lean_object* v_toBind_2686_, lean_object* v_e_2687_, lean_object* v_a_2688_){
_start:
{
lean_object* v___y_2690_; 
switch(lean_obj_tag(v_a_2688_))
{
case 0:
{
lean_object* v_e_2722_; lean_object* v_toPure_2723_; lean_object* v___x_2724_; 
lean_dec_ref(v_e_2687_);
lean_dec(v_toBind_2686_);
lean_dec(v___f_2685_);
lean_dec(v_x_2683_);
lean_dec(v_post_2678_);
lean_dec(v_pre_2677_);
lean_dec_ref(v_inst_2676_);
lean_dec(v_inst_2675_);
lean_dec_ref(v_inst_2674_);
v_e_2722_ = lean_ctor_get(v_a_2688_, 0);
lean_inc_ref(v_e_2722_);
lean_dec_ref_known(v_a_2688_, 1);
v_toPure_2723_ = lean_ctor_get(v_toApplicative_2673_, 1);
lean_inc(v_toPure_2723_);
lean_dec_ref(v_toApplicative_2673_);
v___x_2724_ = lean_apply_2(v_toPure_2723_, lean_box(0), v_e_2722_);
return v___x_2724_;
}
case 1:
{
lean_object* v_e_2725_; lean_object* v___x_2726_; 
lean_dec_ref(v_e_2687_);
lean_dec(v_toBind_2686_);
lean_dec(v___f_2685_);
lean_dec_ref(v_toApplicative_2673_);
v_e_2725_ = lean_ctor_get(v_a_2688_, 0);
lean_inc_ref(v_e_2725_);
lean_dec_ref_known(v_a_2688_, 1);
v___x_2726_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2674_, v_inst_2675_, v_inst_2676_, v_pre_2677_, v_post_2678_, v_usedLetOnly_2679_, v_skipConstInApp_2680_, v_skipInstances_2681_, v_x_2682_, v_x_2683_, v_e_2725_, v___y_2684_);
return v___x_2726_;
}
default: 
{
lean_object* v_e_x3f_2727_; 
lean_dec_ref(v_toApplicative_2673_);
v_e_x3f_2727_ = lean_ctor_get(v_a_2688_, 0);
lean_inc(v_e_x3f_2727_);
lean_dec_ref_known(v_a_2688_, 1);
if (lean_obj_tag(v_e_x3f_2727_) == 0)
{
v___y_2690_ = v_e_2687_;
goto v___jp_2689_;
}
else
{
lean_object* v_val_2728_; 
lean_dec_ref(v_e_2687_);
v_val_2728_ = lean_ctor_get(v_e_x3f_2727_, 0);
lean_inc(v_val_2728_);
lean_dec_ref_known(v_e_x3f_2727_, 1);
v___y_2690_ = v_val_2728_;
goto v___jp_2689_;
}
}
}
v___jp_2689_:
{
switch(lean_obj_tag(v___y_2690_))
{
case 7:
{
lean_object* v___x_2691_; lean_object* v___x_2692_; 
lean_dec(v_toBind_2686_);
lean_dec(v___f_2685_);
v___x_2691_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_2692_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(v_inst_2674_, v_inst_2675_, v_inst_2676_, v_pre_2677_, v_post_2678_, v_usedLetOnly_2679_, v_skipConstInApp_2680_, v_skipInstances_2681_, v_x_2682_, v_x_2683_, v___x_2691_, v___y_2690_, v___y_2684_);
return v___x_2692_;
}
case 6:
{
lean_object* v___x_2693_; lean_object* v___x_2694_; 
lean_dec(v_toBind_2686_);
lean_dec(v___f_2685_);
v___x_2693_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_2694_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(v_inst_2674_, v_inst_2675_, v_inst_2676_, v_pre_2677_, v_post_2678_, v_usedLetOnly_2679_, v_skipConstInApp_2680_, v_skipInstances_2681_, v_x_2682_, v_x_2683_, v___x_2693_, v___y_2690_, v___y_2684_);
return v___x_2694_;
}
case 8:
{
lean_object* v___x_2695_; lean_object* v___x_2696_; 
lean_dec(v_toBind_2686_);
lean_dec(v___f_2685_);
v___x_2695_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_2696_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(v_inst_2674_, v_inst_2675_, v_inst_2676_, v_pre_2677_, v_post_2678_, v_usedLetOnly_2679_, v_skipConstInApp_2680_, v_skipInstances_2681_, v_x_2682_, v_x_2683_, v___x_2695_, v___y_2690_, v___y_2684_);
return v___x_2696_;
}
case 5:
{
lean_object* v_dummy_2697_; lean_object* v_nargs_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_3361__overap_2702_; lean_object* v___x_2703_; 
lean_dec(v_toBind_2686_);
lean_dec(v_x_2683_);
lean_dec(v_post_2678_);
lean_dec(v_pre_2677_);
lean_dec_ref(v_inst_2676_);
lean_dec(v_inst_2675_);
lean_dec_ref(v_inst_2674_);
v_dummy_2697_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_2698_ = l_Lean_Expr_getAppNumArgs(v___y_2690_);
lean_inc(v_nargs_2698_);
v___x_2699_ = lean_mk_array(v_nargs_2698_, v_dummy_2697_);
v___x_2700_ = lean_unsigned_to_nat(1u);
v___x_2701_ = lean_nat_sub(v_nargs_2698_, v___x_2700_);
lean_dec(v_nargs_2698_);
v___x_3361__overap_2702_ = l_Lean_Expr_withAppAux___redArg(v___f_2685_, v___y_2690_, v___x_2699_, v___x_2701_);
lean_inc(v___y_2684_);
v___x_2703_ = lean_apply_1(v___x_3361__overap_2702_, v___y_2684_);
return v___x_2703_;
}
case 10:
{
lean_object* v_data_2704_; lean_object* v_expr_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___f_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; 
lean_dec(v___f_2685_);
v_data_2704_ = lean_ctor_get(v___y_2690_, 0);
lean_inc(v_data_2704_);
v_expr_2705_ = lean_ctor_get(v___y_2690_, 1);
lean_inc_ref_n(v_expr_2705_, 2);
v___x_2706_ = lean_box(v_usedLetOnly_2679_);
v___x_2707_ = lean_box(v_skipConstInApp_2680_);
v___x_2708_ = lean_box(v_skipInstances_2681_);
lean_inc(v___y_2684_);
lean_inc(v_x_2683_);
lean_inc(v_post_2678_);
lean_inc(v_pre_2677_);
lean_inc_ref(v_inst_2676_);
lean_inc(v_inst_2675_);
lean_inc_ref(v_inst_2674_);
v___f_2709_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__8___boxed), 15, 14);
lean_closure_set(v___f_2709_, 0, v_expr_2705_);
lean_closure_set(v___f_2709_, 1, v_data_2704_);
lean_closure_set(v___f_2709_, 2, v_inst_2674_);
lean_closure_set(v___f_2709_, 3, v_inst_2675_);
lean_closure_set(v___f_2709_, 4, v_inst_2676_);
lean_closure_set(v___f_2709_, 5, v_pre_2677_);
lean_closure_set(v___f_2709_, 6, v_post_2678_);
lean_closure_set(v___f_2709_, 7, v___x_2706_);
lean_closure_set(v___f_2709_, 8, v___x_2707_);
lean_closure_set(v___f_2709_, 9, v___x_2708_);
lean_closure_set(v___f_2709_, 10, v_x_2682_);
lean_closure_set(v___f_2709_, 11, v_x_2683_);
lean_closure_set(v___f_2709_, 12, v___y_2684_);
lean_closure_set(v___f_2709_, 13, v___y_2690_);
v___x_2710_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2674_, v_inst_2675_, v_inst_2676_, v_pre_2677_, v_post_2678_, v_usedLetOnly_2679_, v_skipConstInApp_2680_, v_skipInstances_2681_, v_x_2682_, v_x_2683_, v_expr_2705_, v___y_2684_);
v___x_2711_ = lean_apply_4(v_toBind_2686_, lean_box(0), lean_box(0), v___x_2710_, v___f_2709_);
return v___x_2711_;
}
case 11:
{
lean_object* v_typeName_2712_; lean_object* v_idx_2713_; lean_object* v_struct_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___f_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; 
lean_dec(v___f_2685_);
v_typeName_2712_ = lean_ctor_get(v___y_2690_, 0);
lean_inc(v_typeName_2712_);
v_idx_2713_ = lean_ctor_get(v___y_2690_, 1);
lean_inc(v_idx_2713_);
v_struct_2714_ = lean_ctor_get(v___y_2690_, 2);
lean_inc_ref_n(v_struct_2714_, 2);
v___x_2715_ = lean_box(v_usedLetOnly_2679_);
v___x_2716_ = lean_box(v_skipConstInApp_2680_);
v___x_2717_ = lean_box(v_skipInstances_2681_);
lean_inc(v___y_2684_);
lean_inc(v_x_2683_);
lean_inc(v_post_2678_);
lean_inc(v_pre_2677_);
lean_inc_ref(v_inst_2676_);
lean_inc(v_inst_2675_);
lean_inc_ref(v_inst_2674_);
v___f_2718_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__10___boxed), 16, 15);
lean_closure_set(v___f_2718_, 0, v_struct_2714_);
lean_closure_set(v___f_2718_, 1, v_typeName_2712_);
lean_closure_set(v___f_2718_, 2, v_idx_2713_);
lean_closure_set(v___f_2718_, 3, v_inst_2674_);
lean_closure_set(v___f_2718_, 4, v_inst_2675_);
lean_closure_set(v___f_2718_, 5, v_inst_2676_);
lean_closure_set(v___f_2718_, 6, v_pre_2677_);
lean_closure_set(v___f_2718_, 7, v_post_2678_);
lean_closure_set(v___f_2718_, 8, v___x_2715_);
lean_closure_set(v___f_2718_, 9, v___x_2716_);
lean_closure_set(v___f_2718_, 10, v___x_2717_);
lean_closure_set(v___f_2718_, 11, v_x_2682_);
lean_closure_set(v___f_2718_, 12, v_x_2683_);
lean_closure_set(v___f_2718_, 13, v___y_2684_);
lean_closure_set(v___f_2718_, 14, v___y_2690_);
v___x_2719_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2674_, v_inst_2675_, v_inst_2676_, v_pre_2677_, v_post_2678_, v_usedLetOnly_2679_, v_skipConstInApp_2680_, v_skipInstances_2681_, v_x_2682_, v_x_2683_, v_struct_2714_, v___y_2684_);
v___x_2720_ = lean_apply_4(v_toBind_2686_, lean_box(0), lean_box(0), v___x_2719_, v___f_2718_);
return v___x_2720_;
}
default: 
{
lean_object* v___x_2721_; 
lean_dec(v_toBind_2686_);
lean_dec(v___f_2685_);
v___x_2721_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2674_, v_inst_2675_, v_inst_2676_, v_pre_2677_, v_post_2678_, v_usedLetOnly_2679_, v_skipConstInApp_2680_, v_skipInstances_2681_, v_x_2682_, v_x_2683_, v___y_2690_, v___y_2684_);
return v___x_2721_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___boxed(lean_object* v_toApplicative_2729_, lean_object* v_inst_2730_, lean_object* v_inst_2731_, lean_object* v_inst_2732_, lean_object* v_pre_2733_, lean_object* v_post_2734_, lean_object* v_usedLetOnly_2735_, lean_object* v_skipConstInApp_2736_, lean_object* v_skipInstances_2737_, lean_object* v_x_2738_, lean_object* v_x_2739_, lean_object* v___y_2740_, lean_object* v___f_2741_, lean_object* v_toBind_2742_, lean_object* v_e_2743_, lean_object* v_a_2744_){
_start:
{
uint8_t v_usedLetOnly_boxed_2745_; uint8_t v_skipConstInApp_boxed_2746_; uint8_t v_skipInstances_boxed_2747_; lean_object* v_res_2748_; 
v_usedLetOnly_boxed_2745_ = lean_unbox(v_usedLetOnly_2735_);
v_skipConstInApp_boxed_2746_ = lean_unbox(v_skipConstInApp_2736_);
v_skipInstances_boxed_2747_ = lean_unbox(v_skipInstances_2737_);
v_res_2748_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11(v_toApplicative_2729_, v_inst_2730_, v_inst_2731_, v_inst_2732_, v_pre_2733_, v_post_2734_, v_usedLetOnly_boxed_2745_, v_skipConstInApp_boxed_2746_, v_skipInstances_boxed_2747_, v_x_2738_, v_x_2739_, v___y_2740_, v___f_2741_, v_toBind_2742_, v_e_2743_, v_a_2744_);
lean_dec(v___y_2740_);
return v_res_2748_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12(lean_object* v_toApplicative_2749_, lean_object* v_inst_2750_, lean_object* v_inst_2751_, lean_object* v_inst_2752_, lean_object* v_pre_2753_, lean_object* v_post_2754_, uint8_t v_usedLetOnly_2755_, uint8_t v_skipConstInApp_2756_, uint8_t v_skipInstances_2757_, lean_object* v_x_2758_, lean_object* v_x_2759_, lean_object* v___f_2760_, lean_object* v_toBind_2761_, lean_object* v_e_2762_, lean_object* v_____r_2763_, lean_object* v___y_2764_){
_start:
{
lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___f_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; 
v___x_2765_ = lean_box(v_usedLetOnly_2755_);
v___x_2766_ = lean_box(v_skipConstInApp_2756_);
v___x_2767_ = lean_box(v_skipInstances_2757_);
lean_inc_ref(v_e_2762_);
lean_inc(v_toBind_2761_);
lean_inc(v___y_2764_);
lean_inc(v_pre_2753_);
v___f_2768_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___boxed), 16, 15);
lean_closure_set(v___f_2768_, 0, v_toApplicative_2749_);
lean_closure_set(v___f_2768_, 1, v_inst_2750_);
lean_closure_set(v___f_2768_, 2, v_inst_2751_);
lean_closure_set(v___f_2768_, 3, v_inst_2752_);
lean_closure_set(v___f_2768_, 4, v_pre_2753_);
lean_closure_set(v___f_2768_, 5, v_post_2754_);
lean_closure_set(v___f_2768_, 6, v___x_2765_);
lean_closure_set(v___f_2768_, 7, v___x_2766_);
lean_closure_set(v___f_2768_, 8, v___x_2767_);
lean_closure_set(v___f_2768_, 9, v_x_2758_);
lean_closure_set(v___f_2768_, 10, v_x_2759_);
lean_closure_set(v___f_2768_, 11, v___y_2764_);
lean_closure_set(v___f_2768_, 12, v___f_2760_);
lean_closure_set(v___f_2768_, 13, v_toBind_2761_);
lean_closure_set(v___f_2768_, 14, v_e_2762_);
v___x_2769_ = lean_apply_1(v_pre_2753_, v_e_2762_);
v___x_2770_ = lean_apply_4(v_toBind_2761_, lean_box(0), lean_box(0), v___x_2769_, v___f_2768_);
return v___x_2770_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12___boxed(lean_object* v_toApplicative_2771_, lean_object* v_inst_2772_, lean_object* v_inst_2773_, lean_object* v_inst_2774_, lean_object* v_pre_2775_, lean_object* v_post_2776_, lean_object* v_usedLetOnly_2777_, lean_object* v_skipConstInApp_2778_, lean_object* v_skipInstances_2779_, lean_object* v_x_2780_, lean_object* v_x_2781_, lean_object* v___f_2782_, lean_object* v_toBind_2783_, lean_object* v_e_2784_, lean_object* v_____r_2785_, lean_object* v___y_2786_){
_start:
{
uint8_t v_usedLetOnly_boxed_2787_; uint8_t v_skipConstInApp_boxed_2788_; uint8_t v_skipInstances_boxed_2789_; lean_object* v_res_2790_; 
v_usedLetOnly_boxed_2787_ = lean_unbox(v_usedLetOnly_2777_);
v_skipConstInApp_boxed_2788_ = lean_unbox(v_skipConstInApp_2778_);
v_skipInstances_boxed_2789_ = lean_unbox(v_skipInstances_2779_);
v_res_2790_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12(v_toApplicative_2771_, v_inst_2772_, v_inst_2773_, v_inst_2774_, v_pre_2775_, v_post_2776_, v_usedLetOnly_boxed_2787_, v_skipConstInApp_boxed_2788_, v_skipInstances_boxed_2789_, v_x_2780_, v_x_2781_, v___f_2782_, v_toBind_2783_, v_e_2784_, v_____r_2785_, v___y_2786_);
lean_dec(v___y_2786_);
return v_res_2790_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(lean_object* v_inst_2791_, lean_object* v_inst_2792_, lean_object* v_inst_2793_, lean_object* v_pre_2794_, lean_object* v_post_2795_, uint8_t v_usedLetOnly_2796_, uint8_t v_skipConstInApp_2797_, uint8_t v_skipInstances_2798_, lean_object* v_x_2799_, lean_object* v_x_2800_, lean_object* v_e_2801_, lean_object* v_a_2802_){
_start:
{
lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___f_2807_; lean_object* v___f_2808_; lean_object* v___x_2809_; lean_object* v_toApplicative_2810_; lean_object* v_toBind_2811_; lean_object* v___f_2812_; lean_object* v___f_2813_; lean_object* v___f_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___f_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___f_2822_; lean_object* v___f_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; 
v___x_2803_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0));
v___x_2804_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1));
lean_inc_ref_n(v_inst_2791_, 3);
v___x_2805_ = l_Lean_MonadCacheT_instMonad___redArg(v_x_2799_, v___x_2803_, v___x_2804_, v_inst_2791_);
v___x_2806_ = l_Lean_MonadCacheT_instMonadControl___redArg(v_x_2799_, v___x_2803_, v___x_2804_);
lean_inc_ref_n(v_inst_2793_, 3);
lean_inc_ref(v___x_2806_);
v___f_2807_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_2807_, 0, v___x_2806_);
lean_closure_set(v___f_2807_, 1, v_inst_2793_);
v___f_2808_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_2808_, 0, v___x_2806_);
lean_closure_set(v___f_2808_, 1, v_inst_2793_);
v___x_2809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2809_, 0, v___f_2807_);
lean_ctor_set(v___x_2809_, 1, v___f_2808_);
v_toApplicative_2810_ = lean_ctor_get(v_inst_2791_, 0);
lean_inc_ref_n(v_toApplicative_2810_, 6);
v_toBind_2811_ = lean_ctor_get(v_inst_2791_, 1);
lean_inc_n(v_toBind_2811_, 6);
v___f_2812_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2812_, 0, v_toApplicative_2810_);
lean_inc_n(v_x_2800_, 3);
lean_inc_n(v_a_2802_, 3);
lean_inc_ref_n(v_e_2801_, 2);
v___f_2813_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_2813_, 0, v_toApplicative_2810_);
lean_closure_set(v___f_2813_, 1, v___x_2803_);
lean_closure_set(v___f_2813_, 2, v___x_2804_);
lean_closure_set(v___f_2813_, 3, v_e_2801_);
lean_closure_set(v___f_2813_, 4, v_a_2802_);
lean_closure_set(v___f_2813_, 5, v_x_2800_);
lean_closure_set(v___f_2813_, 6, v_toBind_2811_);
v___f_2814_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__3___boxed), 5, 4);
lean_closure_set(v___f_2814_, 0, v_toApplicative_2810_);
lean_closure_set(v___f_2814_, 1, v___x_2803_);
lean_closure_set(v___f_2814_, 2, v___x_2804_);
lean_closure_set(v___f_2814_, 3, v_e_2801_);
v___x_2815_ = lean_box(v_skipInstances_2798_);
v___x_2816_ = lean_box(v_usedLetOnly_2796_);
v___x_2817_ = lean_box(v_skipConstInApp_2797_);
lean_inc_ref(v___x_2805_);
lean_inc(v_post_2795_);
lean_inc(v_pre_2794_);
lean_inc_n(v_inst_2792_, 2);
v___f_2818_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__9___boxed), 17, 14);
lean_closure_set(v___f_2818_, 0, v___x_2815_);
lean_closure_set(v___f_2818_, 1, v_inst_2791_);
lean_closure_set(v___f_2818_, 2, v_inst_2792_);
lean_closure_set(v___f_2818_, 3, v_inst_2793_);
lean_closure_set(v___f_2818_, 4, v_pre_2794_);
lean_closure_set(v___f_2818_, 5, v_post_2795_);
lean_closure_set(v___f_2818_, 6, v___x_2816_);
lean_closure_set(v___f_2818_, 7, v___x_2817_);
lean_closure_set(v___f_2818_, 8, v_x_2799_);
lean_closure_set(v___f_2818_, 9, v_x_2800_);
lean_closure_set(v___f_2818_, 10, v___x_2805_);
lean_closure_set(v___f_2818_, 11, v_toBind_2811_);
lean_closure_set(v___f_2818_, 12, v_toApplicative_2810_);
lean_closure_set(v___f_2818_, 13, v___f_2812_);
v___x_2819_ = lean_box(v_usedLetOnly_2796_);
v___x_2820_ = lean_box(v_skipConstInApp_2797_);
v___x_2821_ = lean_box(v_skipInstances_2798_);
v___f_2822_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12___boxed), 16, 14);
lean_closure_set(v___f_2822_, 0, v_toApplicative_2810_);
lean_closure_set(v___f_2822_, 1, v_inst_2791_);
lean_closure_set(v___f_2822_, 2, v_inst_2792_);
lean_closure_set(v___f_2822_, 3, v_inst_2793_);
lean_closure_set(v___f_2822_, 4, v_pre_2794_);
lean_closure_set(v___f_2822_, 5, v_post_2795_);
lean_closure_set(v___f_2822_, 6, v___x_2819_);
lean_closure_set(v___f_2822_, 7, v___x_2820_);
lean_closure_set(v___f_2822_, 8, v___x_2821_);
lean_closure_set(v___f_2822_, 9, v_x_2799_);
lean_closure_set(v___f_2822_, 10, v_x_2800_);
lean_closure_set(v___f_2822_, 11, v___f_2818_);
lean_closure_set(v___f_2822_, 12, v_toBind_2811_);
lean_closure_set(v___f_2822_, 13, v_e_2801_);
v___f_2823_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14___boxed), 13, 12);
lean_closure_set(v___f_2823_, 0, v_inst_2792_);
lean_closure_set(v___f_2823_, 1, v_x_2799_);
lean_closure_set(v___f_2823_, 2, v___x_2803_);
lean_closure_set(v___f_2823_, 3, v___x_2804_);
lean_closure_set(v___f_2823_, 4, v_inst_2791_);
lean_closure_set(v___f_2823_, 5, v___f_2822_);
lean_closure_set(v___f_2823_, 6, v___x_2809_);
lean_closure_set(v___f_2823_, 7, v___x_2805_);
lean_closure_set(v___f_2823_, 8, v_a_2802_);
lean_closure_set(v___f_2823_, 9, v_toBind_2811_);
lean_closure_set(v___f_2823_, 10, v___f_2813_);
lean_closure_set(v___f_2823_, 11, v_toApplicative_2810_);
v___x_2824_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2824_, 0, lean_box(0));
lean_closure_set(v___x_2824_, 1, lean_box(0));
lean_closure_set(v___x_2824_, 2, v_a_2802_);
v___x_2825_ = lean_apply_2(v_x_2800_, lean_box(0), v___x_2824_);
v___x_2826_ = lean_apply_4(v_toBind_2811_, lean_box(0), lean_box(0), v___x_2825_, v___f_2814_);
v___x_2827_ = lean_apply_4(v_toBind_2811_, lean_box(0), lean_box(0), v___x_2826_, v___f_2823_);
return v___x_2827_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___lam__0(lean_object* v_toApplicative_2828_, lean_object* v_inst_2829_, lean_object* v_inst_2830_, lean_object* v_inst_2831_, lean_object* v_pre_2832_, lean_object* v_post_2833_, uint8_t v_usedLetOnly_2834_, uint8_t v_skipConstInApp_2835_, uint8_t v_skipInstances_2836_, lean_object* v_x_2837_, lean_object* v_x_2838_, lean_object* v_a_2839_, lean_object* v_e_2840_, lean_object* v_a_2841_){
_start:
{
lean_object* v___y_2843_; 
switch(lean_obj_tag(v_a_2841_))
{
case 0:
{
lean_object* v_e_2846_; lean_object* v_toPure_2847_; lean_object* v___x_2848_; 
lean_dec_ref(v_e_2840_);
lean_dec(v_x_2838_);
lean_dec(v_post_2833_);
lean_dec(v_pre_2832_);
lean_dec_ref(v_inst_2831_);
lean_dec(v_inst_2830_);
lean_dec_ref(v_inst_2829_);
v_e_2846_ = lean_ctor_get(v_a_2841_, 0);
lean_inc_ref(v_e_2846_);
lean_dec_ref_known(v_a_2841_, 1);
v_toPure_2847_ = lean_ctor_get(v_toApplicative_2828_, 1);
lean_inc(v_toPure_2847_);
lean_dec_ref(v_toApplicative_2828_);
v___x_2848_ = lean_apply_2(v_toPure_2847_, lean_box(0), v_e_2846_);
return v___x_2848_;
}
case 1:
{
lean_object* v_e_2849_; lean_object* v___x_2850_; 
lean_dec_ref(v_e_2840_);
lean_dec_ref(v_toApplicative_2828_);
v_e_2849_ = lean_ctor_get(v_a_2841_, 0);
lean_inc_ref(v_e_2849_);
lean_dec_ref_known(v_a_2841_, 1);
v___x_2850_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2829_, v_inst_2830_, v_inst_2831_, v_pre_2832_, v_post_2833_, v_usedLetOnly_2834_, v_skipConstInApp_2835_, v_skipInstances_2836_, v_x_2837_, v_x_2838_, v_e_2849_, v_a_2839_);
return v___x_2850_;
}
default: 
{
lean_object* v_e_x3f_2851_; 
lean_dec(v_x_2838_);
lean_dec(v_post_2833_);
lean_dec(v_pre_2832_);
lean_dec_ref(v_inst_2831_);
lean_dec(v_inst_2830_);
lean_dec_ref(v_inst_2829_);
v_e_x3f_2851_ = lean_ctor_get(v_a_2841_, 0);
lean_inc(v_e_x3f_2851_);
lean_dec_ref_known(v_a_2841_, 1);
if (lean_obj_tag(v_e_x3f_2851_) == 0)
{
v___y_2843_ = v_e_2840_;
goto v___jp_2842_;
}
else
{
lean_object* v_val_2852_; 
lean_dec_ref(v_e_2840_);
v_val_2852_ = lean_ctor_get(v_e_x3f_2851_, 0);
lean_inc(v_val_2852_);
lean_dec_ref_known(v_e_x3f_2851_, 1);
v___y_2843_ = v_val_2852_;
goto v___jp_2842_;
}
}
}
v___jp_2842_:
{
lean_object* v_toPure_2844_; lean_object* v___x_2845_; 
v_toPure_2844_ = lean_ctor_get(v_toApplicative_2828_, 1);
lean_inc(v_toPure_2844_);
lean_dec_ref(v_toApplicative_2828_);
v___x_2845_ = lean_apply_2(v_toPure_2844_, lean_box(0), v___y_2843_);
return v___x_2845_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___lam__0___boxed(lean_object* v_toApplicative_2853_, lean_object* v_inst_2854_, lean_object* v_inst_2855_, lean_object* v_inst_2856_, lean_object* v_pre_2857_, lean_object* v_post_2858_, lean_object* v_usedLetOnly_2859_, lean_object* v_skipConstInApp_2860_, lean_object* v_skipInstances_2861_, lean_object* v_x_2862_, lean_object* v_x_2863_, lean_object* v_a_2864_, lean_object* v_e_2865_, lean_object* v_a_2866_){
_start:
{
uint8_t v_usedLetOnly_boxed_2867_; uint8_t v_skipConstInApp_boxed_2868_; uint8_t v_skipInstances_boxed_2869_; lean_object* v_res_2870_; 
v_usedLetOnly_boxed_2867_ = lean_unbox(v_usedLetOnly_2859_);
v_skipConstInApp_boxed_2868_ = lean_unbox(v_skipConstInApp_2860_);
v_skipInstances_boxed_2869_ = lean_unbox(v_skipInstances_2861_);
v_res_2870_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___lam__0(v_toApplicative_2853_, v_inst_2854_, v_inst_2855_, v_inst_2856_, v_pre_2857_, v_post_2858_, v_usedLetOnly_boxed_2867_, v_skipConstInApp_boxed_2868_, v_skipInstances_boxed_2869_, v_x_2862_, v_x_2863_, v_a_2864_, v_e_2865_, v_a_2866_);
lean_dec(v_a_2864_);
return v_res_2870_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(lean_object* v_inst_2871_, lean_object* v_inst_2872_, lean_object* v_inst_2873_, lean_object* v_pre_2874_, lean_object* v_post_2875_, uint8_t v_usedLetOnly_2876_, uint8_t v_skipConstInApp_2877_, uint8_t v_skipInstances_2878_, lean_object* v_x_2879_, lean_object* v_x_2880_, lean_object* v_e_2881_, lean_object* v_a_2882_){
_start:
{
lean_object* v_toApplicative_2883_; lean_object* v_toBind_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___f_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; 
v_toApplicative_2883_ = lean_ctor_get(v_inst_2871_, 0);
lean_inc_ref(v_toApplicative_2883_);
v_toBind_2884_ = lean_ctor_get(v_inst_2871_, 1);
lean_inc(v_toBind_2884_);
v___x_2885_ = lean_box(v_usedLetOnly_2876_);
v___x_2886_ = lean_box(v_skipConstInApp_2877_);
v___x_2887_ = lean_box(v_skipInstances_2878_);
lean_inc_ref(v_e_2881_);
lean_inc(v_a_2882_);
lean_inc(v_post_2875_);
v___f_2888_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___lam__0___boxed), 14, 13);
lean_closure_set(v___f_2888_, 0, v_toApplicative_2883_);
lean_closure_set(v___f_2888_, 1, v_inst_2871_);
lean_closure_set(v___f_2888_, 2, v_inst_2872_);
lean_closure_set(v___f_2888_, 3, v_inst_2873_);
lean_closure_set(v___f_2888_, 4, v_pre_2874_);
lean_closure_set(v___f_2888_, 5, v_post_2875_);
lean_closure_set(v___f_2888_, 6, v___x_2885_);
lean_closure_set(v___f_2888_, 7, v___x_2886_);
lean_closure_set(v___f_2888_, 8, v___x_2887_);
lean_closure_set(v___f_2888_, 9, v_x_2879_);
lean_closure_set(v___f_2888_, 10, v_x_2880_);
lean_closure_set(v___f_2888_, 11, v_a_2882_);
lean_closure_set(v___f_2888_, 12, v_e_2881_);
v___x_2889_ = lean_apply_1(v_post_2875_, v_e_2881_);
v___x_2890_ = lean_apply_4(v_toBind_2884_, lean_box(0), lean_box(0), v___x_2889_, v___f_2888_);
return v___x_2890_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3(lean_object* v_inst_2891_, lean_object* v_inst_2892_, lean_object* v_inst_2893_, lean_object* v_pre_2894_, lean_object* v_post_2895_, uint8_t v_usedLetOnly_2896_, uint8_t v_skipConstInApp_2897_, uint8_t v_skipInstances_2898_, lean_object* v_x_2899_, lean_object* v_x_2900_, lean_object* v_a_2901_, lean_object* v_a_2902_){
_start:
{
lean_object* v___x_2903_; 
v___x_2903_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2891_, v_inst_2892_, v_inst_2893_, v_pre_2894_, v_post_2895_, v_usedLetOnly_2896_, v_skipConstInApp_2897_, v_skipInstances_2898_, v_x_2899_, v_x_2900_, v_a_2902_, v_a_2901_);
return v___x_2903_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___boxed(lean_object* v_inst_2904_, lean_object* v_inst_2905_, lean_object* v_inst_2906_, lean_object* v_pre_2907_, lean_object* v_post_2908_, lean_object* v_usedLetOnly_2909_, lean_object* v_skipConstInApp_2910_, lean_object* v_skipInstances_2911_, lean_object* v_x_2912_, lean_object* v_x_2913_, lean_object* v_e_2914_, lean_object* v_a_2915_){
_start:
{
uint8_t v_usedLetOnly_boxed_2916_; uint8_t v_skipConstInApp_boxed_2917_; uint8_t v_skipInstances_boxed_2918_; lean_object* v_res_2919_; 
v_usedLetOnly_boxed_2916_ = lean_unbox(v_usedLetOnly_2909_);
v_skipConstInApp_boxed_2917_ = lean_unbox(v_skipConstInApp_2910_);
v_skipInstances_boxed_2918_ = lean_unbox(v_skipInstances_2911_);
v_res_2919_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2904_, v_inst_2905_, v_inst_2906_, v_pre_2907_, v_post_2908_, v_usedLetOnly_boxed_2916_, v_skipConstInApp_boxed_2917_, v_skipInstances_boxed_2918_, v_x_2912_, v_x_2913_, v_e_2914_, v_a_2915_);
lean_dec(v_a_2915_);
return v_res_2919_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___boxed(lean_object* v_inst_2920_, lean_object* v_inst_2921_, lean_object* v_inst_2922_, lean_object* v_pre_2923_, lean_object* v_post_2924_, lean_object* v_usedLetOnly_2925_, lean_object* v_skipConstInApp_2926_, lean_object* v_skipInstances_2927_, lean_object* v_x_2928_, lean_object* v_x_2929_, lean_object* v_fvars_2930_, lean_object* v_e_2931_, lean_object* v_a_2932_){
_start:
{
uint8_t v_usedLetOnly_boxed_2933_; uint8_t v_skipConstInApp_boxed_2934_; uint8_t v_skipInstances_boxed_2935_; lean_object* v_res_2936_; 
v_usedLetOnly_boxed_2933_ = lean_unbox(v_usedLetOnly_2925_);
v_skipConstInApp_boxed_2934_ = lean_unbox(v_skipConstInApp_2926_);
v_skipInstances_boxed_2935_ = lean_unbox(v_skipInstances_2927_);
v_res_2936_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(v_inst_2920_, v_inst_2921_, v_inst_2922_, v_pre_2923_, v_post_2924_, v_usedLetOnly_boxed_2933_, v_skipConstInApp_boxed_2934_, v_skipInstances_boxed_2935_, v_x_2928_, v_x_2929_, v_fvars_2930_, v_e_2931_, v_a_2932_);
lean_dec(v_a_2932_);
return v_res_2936_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___boxed(lean_object* v_inst_2937_, lean_object* v_inst_2938_, lean_object* v_inst_2939_, lean_object* v_pre_2940_, lean_object* v_post_2941_, lean_object* v_usedLetOnly_2942_, lean_object* v_skipConstInApp_2943_, lean_object* v_skipInstances_2944_, lean_object* v_x_2945_, lean_object* v_x_2946_, lean_object* v_fvars_2947_, lean_object* v_e_2948_, lean_object* v_a_2949_){
_start:
{
uint8_t v_usedLetOnly_boxed_2950_; uint8_t v_skipConstInApp_boxed_2951_; uint8_t v_skipInstances_boxed_2952_; lean_object* v_res_2953_; 
v_usedLetOnly_boxed_2950_ = lean_unbox(v_usedLetOnly_2942_);
v_skipConstInApp_boxed_2951_ = lean_unbox(v_skipConstInApp_2943_);
v_skipInstances_boxed_2952_ = lean_unbox(v_skipInstances_2944_);
v_res_2953_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(v_inst_2937_, v_inst_2938_, v_inst_2939_, v_pre_2940_, v_post_2941_, v_usedLetOnly_boxed_2950_, v_skipConstInApp_boxed_2951_, v_skipInstances_boxed_2952_, v_x_2945_, v_x_2946_, v_fvars_2947_, v_e_2948_, v_a_2949_);
lean_dec(v_a_2949_);
return v_res_2953_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___boxed(lean_object* v_inst_2954_, lean_object* v_inst_2955_, lean_object* v_inst_2956_, lean_object* v_pre_2957_, lean_object* v_post_2958_, lean_object* v_usedLetOnly_2959_, lean_object* v_skipConstInApp_2960_, lean_object* v_skipInstances_2961_, lean_object* v_x_2962_, lean_object* v_x_2963_, lean_object* v_fvars_2964_, lean_object* v_e_2965_, lean_object* v_a_2966_){
_start:
{
uint8_t v_usedLetOnly_boxed_2967_; uint8_t v_skipConstInApp_boxed_2968_; uint8_t v_skipInstances_boxed_2969_; lean_object* v_res_2970_; 
v_usedLetOnly_boxed_2967_ = lean_unbox(v_usedLetOnly_2959_);
v_skipConstInApp_boxed_2968_ = lean_unbox(v_skipConstInApp_2960_);
v_skipInstances_boxed_2969_ = lean_unbox(v_skipInstances_2961_);
v_res_2970_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(v_inst_2954_, v_inst_2955_, v_inst_2956_, v_pre_2957_, v_post_2958_, v_usedLetOnly_boxed_2967_, v_skipConstInApp_boxed_2968_, v_skipInstances_boxed_2969_, v_x_2962_, v_x_2963_, v_fvars_2964_, v_e_2965_, v_a_2966_);
lean_dec(v_a_2966_);
return v_res_2970_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit(lean_object* v_m_2971_, lean_object* v_inst_2972_, lean_object* v_inst_2973_, lean_object* v_inst_2974_, lean_object* v_pre_2975_, lean_object* v_post_2976_, uint8_t v_usedLetOnly_2977_, uint8_t v_skipConstInApp_2978_, uint8_t v_skipInstances_2979_, lean_object* v_x_2980_, lean_object* v_x_2981_, lean_object* v_e_2982_, lean_object* v_a_2983_){
_start:
{
lean_object* v___x_2984_; 
v___x_2984_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2972_, v_inst_2973_, v_inst_2974_, v_pre_2975_, v_post_2976_, v_usedLetOnly_2977_, v_skipConstInApp_2978_, v_skipInstances_2979_, v_x_2980_, v_x_2981_, v_e_2982_, v_a_2983_);
return v___x_2984_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___boxed(lean_object* v_m_2985_, lean_object* v_inst_2986_, lean_object* v_inst_2987_, lean_object* v_inst_2988_, lean_object* v_pre_2989_, lean_object* v_post_2990_, lean_object* v_usedLetOnly_2991_, lean_object* v_skipConstInApp_2992_, lean_object* v_skipInstances_2993_, lean_object* v_x_2994_, lean_object* v_x_2995_, lean_object* v_e_2996_, lean_object* v_a_2997_){
_start:
{
uint8_t v_usedLetOnly_boxed_2998_; uint8_t v_skipConstInApp_boxed_2999_; uint8_t v_skipInstances_boxed_3000_; lean_object* v_res_3001_; 
v_usedLetOnly_boxed_2998_ = lean_unbox(v_usedLetOnly_2991_);
v_skipConstInApp_boxed_2999_ = lean_unbox(v_skipConstInApp_2992_);
v_skipInstances_boxed_3000_ = lean_unbox(v_skipInstances_2993_);
v_res_3001_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit(v_m_2985_, v_inst_2986_, v_inst_2987_, v_inst_2988_, v_pre_2989_, v_post_2990_, v_usedLetOnly_boxed_2998_, v_skipConstInApp_boxed_2999_, v_skipInstances_boxed_3000_, v_x_2994_, v_x_2995_, v_e_2996_, v_a_2997_);
lean_dec(v_a_2997_);
return v_res_3001_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet(lean_object* v_m_3002_, lean_object* v_inst_3003_, lean_object* v_inst_3004_, lean_object* v_inst_3005_, lean_object* v_pre_3006_, lean_object* v_post_3007_, uint8_t v_usedLetOnly_3008_, uint8_t v_skipConstInApp_3009_, uint8_t v_skipInstances_3010_, lean_object* v_x_3011_, lean_object* v_x_3012_, lean_object* v_fvars_3013_, lean_object* v_e_3014_, lean_object* v_a_3015_){
_start:
{
lean_object* v___x_3016_; 
v___x_3016_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(v_inst_3003_, v_inst_3004_, v_inst_3005_, v_pre_3006_, v_post_3007_, v_usedLetOnly_3008_, v_skipConstInApp_3009_, v_skipInstances_3010_, v_x_3011_, v_x_3012_, v_fvars_3013_, v_e_3014_, v_a_3015_);
return v___x_3016_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___boxed(lean_object* v_m_3017_, lean_object* v_inst_3018_, lean_object* v_inst_3019_, lean_object* v_inst_3020_, lean_object* v_pre_3021_, lean_object* v_post_3022_, lean_object* v_usedLetOnly_3023_, lean_object* v_skipConstInApp_3024_, lean_object* v_skipInstances_3025_, lean_object* v_x_3026_, lean_object* v_x_3027_, lean_object* v_fvars_3028_, lean_object* v_e_3029_, lean_object* v_a_3030_){
_start:
{
uint8_t v_usedLetOnly_boxed_3031_; uint8_t v_skipConstInApp_boxed_3032_; uint8_t v_skipInstances_boxed_3033_; lean_object* v_res_3034_; 
v_usedLetOnly_boxed_3031_ = lean_unbox(v_usedLetOnly_3023_);
v_skipConstInApp_boxed_3032_ = lean_unbox(v_skipConstInApp_3024_);
v_skipInstances_boxed_3033_ = lean_unbox(v_skipInstances_3025_);
v_res_3034_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet(v_m_3017_, v_inst_3018_, v_inst_3019_, v_inst_3020_, v_pre_3021_, v_post_3022_, v_usedLetOnly_boxed_3031_, v_skipConstInApp_boxed_3032_, v_skipInstances_boxed_3033_, v_x_3026_, v_x_3027_, v_fvars_3028_, v_e_3029_, v_a_3030_);
lean_dec(v_a_3030_);
return v_res_3034_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost(lean_object* v_m_3035_, lean_object* v_inst_3036_, lean_object* v_inst_3037_, lean_object* v_inst_3038_, lean_object* v_pre_3039_, lean_object* v_post_3040_, uint8_t v_usedLetOnly_3041_, uint8_t v_skipConstInApp_3042_, uint8_t v_skipInstances_3043_, lean_object* v_x_3044_, lean_object* v_x_3045_, lean_object* v_e_3046_, lean_object* v_a_3047_){
_start:
{
lean_object* v___x_3048_; 
v___x_3048_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_3036_, v_inst_3037_, v_inst_3038_, v_pre_3039_, v_post_3040_, v_usedLetOnly_3041_, v_skipConstInApp_3042_, v_skipInstances_3043_, v_x_3044_, v_x_3045_, v_e_3046_, v_a_3047_);
return v___x_3048_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___boxed(lean_object* v_m_3049_, lean_object* v_inst_3050_, lean_object* v_inst_3051_, lean_object* v_inst_3052_, lean_object* v_pre_3053_, lean_object* v_post_3054_, lean_object* v_usedLetOnly_3055_, lean_object* v_skipConstInApp_3056_, lean_object* v_skipInstances_3057_, lean_object* v_x_3058_, lean_object* v_x_3059_, lean_object* v_e_3060_, lean_object* v_a_3061_){
_start:
{
uint8_t v_usedLetOnly_boxed_3062_; uint8_t v_skipConstInApp_boxed_3063_; uint8_t v_skipInstances_boxed_3064_; lean_object* v_res_3065_; 
v_usedLetOnly_boxed_3062_ = lean_unbox(v_usedLetOnly_3055_);
v_skipConstInApp_boxed_3063_ = lean_unbox(v_skipConstInApp_3056_);
v_skipInstances_boxed_3064_ = lean_unbox(v_skipInstances_3057_);
v_res_3065_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost(v_m_3049_, v_inst_3050_, v_inst_3051_, v_inst_3052_, v_pre_3053_, v_post_3054_, v_usedLetOnly_boxed_3062_, v_skipConstInApp_boxed_3063_, v_skipInstances_boxed_3064_, v_x_3058_, v_x_3059_, v_e_3060_, v_a_3061_);
lean_dec(v_a_3061_);
return v_res_3065_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda(lean_object* v_m_3066_, lean_object* v_inst_3067_, lean_object* v_inst_3068_, lean_object* v_inst_3069_, lean_object* v_pre_3070_, lean_object* v_post_3071_, uint8_t v_usedLetOnly_3072_, uint8_t v_skipConstInApp_3073_, uint8_t v_skipInstances_3074_, lean_object* v_x_3075_, lean_object* v_x_3076_, lean_object* v_fvars_3077_, lean_object* v_e_3078_, lean_object* v_a_3079_){
_start:
{
lean_object* v___x_3080_; 
v___x_3080_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(v_inst_3067_, v_inst_3068_, v_inst_3069_, v_pre_3070_, v_post_3071_, v_usedLetOnly_3072_, v_skipConstInApp_3073_, v_skipInstances_3074_, v_x_3075_, v_x_3076_, v_fvars_3077_, v_e_3078_, v_a_3079_);
return v___x_3080_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___boxed(lean_object* v_m_3081_, lean_object* v_inst_3082_, lean_object* v_inst_3083_, lean_object* v_inst_3084_, lean_object* v_pre_3085_, lean_object* v_post_3086_, lean_object* v_usedLetOnly_3087_, lean_object* v_skipConstInApp_3088_, lean_object* v_skipInstances_3089_, lean_object* v_x_3090_, lean_object* v_x_3091_, lean_object* v_fvars_3092_, lean_object* v_e_3093_, lean_object* v_a_3094_){
_start:
{
uint8_t v_usedLetOnly_boxed_3095_; uint8_t v_skipConstInApp_boxed_3096_; uint8_t v_skipInstances_boxed_3097_; lean_object* v_res_3098_; 
v_usedLetOnly_boxed_3095_ = lean_unbox(v_usedLetOnly_3087_);
v_skipConstInApp_boxed_3096_ = lean_unbox(v_skipConstInApp_3088_);
v_skipInstances_boxed_3097_ = lean_unbox(v_skipInstances_3089_);
v_res_3098_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda(v_m_3081_, v_inst_3082_, v_inst_3083_, v_inst_3084_, v_pre_3085_, v_post_3086_, v_usedLetOnly_boxed_3095_, v_skipConstInApp_boxed_3096_, v_skipInstances_boxed_3097_, v_x_3090_, v_x_3091_, v_fvars_3092_, v_e_3093_, v_a_3094_);
lean_dec(v_a_3094_);
return v_res_3098_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall(lean_object* v_m_3099_, lean_object* v_inst_3100_, lean_object* v_inst_3101_, lean_object* v_inst_3102_, lean_object* v_pre_3103_, lean_object* v_post_3104_, uint8_t v_usedLetOnly_3105_, uint8_t v_skipConstInApp_3106_, uint8_t v_skipInstances_3107_, lean_object* v_x_3108_, lean_object* v_x_3109_, lean_object* v_fvars_3110_, lean_object* v_e_3111_, lean_object* v_a_3112_){
_start:
{
lean_object* v___x_3113_; 
v___x_3113_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(v_inst_3100_, v_inst_3101_, v_inst_3102_, v_pre_3103_, v_post_3104_, v_usedLetOnly_3105_, v_skipConstInApp_3106_, v_skipInstances_3107_, v_x_3108_, v_x_3109_, v_fvars_3110_, v_e_3111_, v_a_3112_);
return v___x_3113_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___boxed(lean_object* v_m_3114_, lean_object* v_inst_3115_, lean_object* v_inst_3116_, lean_object* v_inst_3117_, lean_object* v_pre_3118_, lean_object* v_post_3119_, lean_object* v_usedLetOnly_3120_, lean_object* v_skipConstInApp_3121_, lean_object* v_skipInstances_3122_, lean_object* v_x_3123_, lean_object* v_x_3124_, lean_object* v_fvars_3125_, lean_object* v_e_3126_, lean_object* v_a_3127_){
_start:
{
uint8_t v_usedLetOnly_boxed_3128_; uint8_t v_skipConstInApp_boxed_3129_; uint8_t v_skipInstances_boxed_3130_; lean_object* v_res_3131_; 
v_usedLetOnly_boxed_3128_ = lean_unbox(v_usedLetOnly_3120_);
v_skipConstInApp_boxed_3129_ = lean_unbox(v_skipConstInApp_3121_);
v_skipInstances_boxed_3130_ = lean_unbox(v_skipInstances_3122_);
v_res_3131_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall(v_m_3114_, v_inst_3115_, v_inst_3116_, v_inst_3117_, v_pre_3118_, v_post_3119_, v_usedLetOnly_boxed_3128_, v_skipConstInApp_boxed_3129_, v_skipInstances_boxed_3130_, v_x_3123_, v_x_3124_, v_fvars_3125_, v_e_3126_, v_a_3127_);
lean_dec(v_a_3127_);
return v_res_3131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__0(lean_object* v_x_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_){
_start:
{
lean_object* v___x_3138_; lean_object* v___x_3139_; 
v___x_3138_ = lean_apply_1(v_x_3132_, lean_box(0));
v___x_3139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3139_, 0, v___x_3138_);
return v___x_3139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__0___boxed(lean_object* v_x_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_){
_start:
{
lean_object* v_res_3146_; 
v_res_3146_ = l_Lean_Meta_transformWithCache___redArg___lam__0(v_x_3140_, v___y_3141_, v___y_3142_, v___y_3143_, v___y_3144_);
lean_dec(v___y_3144_);
lean_dec_ref(v___y_3143_);
lean_dec(v___y_3142_);
lean_dec_ref(v___y_3141_);
return v_res_3146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__1(lean_object* v_inst_3147_, lean_object* v_00_u03b1_3148_, lean_object* v_x_3149_){
_start:
{
lean_object* v___f_3150_; lean_object* v___x_3151_; 
v___f_3150_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_3150_, 0, v_x_3149_);
v___x_3151_ = lean_apply_2(v_inst_3147_, lean_box(0), v___f_3150_);
return v___x_3151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__4(lean_object* v_toPure_3152_, lean_object* v_x_3153_, lean_object* v_toBind_3154_, lean_object* v_inst_3155_, lean_object* v_inst_3156_, lean_object* v_inst_3157_, lean_object* v_pre_3158_, lean_object* v_post_3159_, uint8_t v_usedLetOnly_3160_, uint8_t v_skipConstInApp_3161_, uint8_t v_skipInstances_3162_, lean_object* v_x_3163_, lean_object* v_input_3164_, lean_object* v_ref_3165_){
_start:
{
lean_object* v___f_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; 
lean_inc(v_toBind_3154_);
lean_inc(v_x_3153_);
lean_inc(v_ref_3165_);
v___f_3166_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__4), 5, 4);
lean_closure_set(v___f_3166_, 0, v_toPure_3152_);
lean_closure_set(v___f_3166_, 1, v_ref_3165_);
lean_closure_set(v___f_3166_, 2, v_x_3153_);
lean_closure_set(v___f_3166_, 3, v_toBind_3154_);
v___x_3167_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_3155_, v_inst_3156_, v_inst_3157_, v_pre_3158_, v_post_3159_, v_usedLetOnly_3160_, v_skipConstInApp_3161_, v_skipInstances_3162_, v_x_3163_, v_x_3153_, v_input_3164_, v_ref_3165_);
lean_dec(v_ref_3165_);
v___x_3168_ = lean_apply_4(v_toBind_3154_, lean_box(0), lean_box(0), v___x_3167_, v___f_3166_);
return v___x_3168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__4___boxed(lean_object* v_toPure_3169_, lean_object* v_x_3170_, lean_object* v_toBind_3171_, lean_object* v_inst_3172_, lean_object* v_inst_3173_, lean_object* v_inst_3174_, lean_object* v_pre_3175_, lean_object* v_post_3176_, lean_object* v_usedLetOnly_3177_, lean_object* v_skipConstInApp_3178_, lean_object* v_skipInstances_3179_, lean_object* v_x_3180_, lean_object* v_input_3181_, lean_object* v_ref_3182_){
_start:
{
uint8_t v_usedLetOnly_boxed_3183_; uint8_t v_skipConstInApp_boxed_3184_; uint8_t v_skipInstances_boxed_3185_; lean_object* v_res_3186_; 
v_usedLetOnly_boxed_3183_ = lean_unbox(v_usedLetOnly_3177_);
v_skipConstInApp_boxed_3184_ = lean_unbox(v_skipConstInApp_3178_);
v_skipInstances_boxed_3185_ = lean_unbox(v_skipInstances_3179_);
v_res_3186_ = l_Lean_Meta_transformWithCache___redArg___lam__4(v_toPure_3169_, v_x_3170_, v_toBind_3171_, v_inst_3172_, v_inst_3173_, v_inst_3174_, v_pre_3175_, v_post_3176_, v_usedLetOnly_boxed_3183_, v_skipConstInApp_boxed_3184_, v_skipInstances_boxed_3185_, v_x_3180_, v_input_3181_, v_ref_3182_);
return v_res_3186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg(lean_object* v_inst_3187_, lean_object* v_inst_3188_, lean_object* v_inst_3189_, lean_object* v_input_3190_, lean_object* v_cache_3191_, lean_object* v_pre_3192_, lean_object* v_post_3193_, uint8_t v_usedLetOnly_3194_, uint8_t v_skipConstInApp_3195_, uint8_t v_skipInstances_3196_){
_start:
{
lean_object* v_x_3197_; lean_object* v_toApplicative_3198_; lean_object* v_toBind_3199_; lean_object* v_toPure_3200_; lean_object* v_x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___f_3207_; lean_object* v___x_3208_; 
v_x_3197_ = lean_box(0);
v_toApplicative_3198_ = lean_ctor_get(v_inst_3187_, 0);
v_toBind_3199_ = lean_ctor_get(v_inst_3187_, 1);
lean_inc_n(v_toBind_3199_, 2);
v_toPure_3200_ = lean_ctor_get(v_toApplicative_3198_, 1);
lean_inc(v_toPure_3200_);
lean_inc_n(v_inst_3188_, 2);
v_x_3201_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__1), 3, 1);
lean_closure_set(v_x_3201_, 0, v_inst_3188_);
v___x_3202_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_3202_, 0, lean_box(0));
lean_closure_set(v___x_3202_, 1, lean_box(0));
lean_closure_set(v___x_3202_, 2, v_cache_3191_);
v___x_3203_ = l_Lean_Meta_transformWithCache___redArg___lam__1(v_inst_3188_, lean_box(0), v___x_3202_);
v___x_3204_ = lean_box(v_usedLetOnly_3194_);
v___x_3205_ = lean_box(v_skipConstInApp_3195_);
v___x_3206_ = lean_box(v_skipInstances_3196_);
v___f_3207_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__4___boxed), 14, 13);
lean_closure_set(v___f_3207_, 0, v_toPure_3200_);
lean_closure_set(v___f_3207_, 1, v_x_3201_);
lean_closure_set(v___f_3207_, 2, v_toBind_3199_);
lean_closure_set(v___f_3207_, 3, v_inst_3187_);
lean_closure_set(v___f_3207_, 4, v_inst_3188_);
lean_closure_set(v___f_3207_, 5, v_inst_3189_);
lean_closure_set(v___f_3207_, 6, v_pre_3192_);
lean_closure_set(v___f_3207_, 7, v_post_3193_);
lean_closure_set(v___f_3207_, 8, v___x_3204_);
lean_closure_set(v___f_3207_, 9, v___x_3205_);
lean_closure_set(v___f_3207_, 10, v___x_3206_);
lean_closure_set(v___f_3207_, 11, v_x_3197_);
lean_closure_set(v___f_3207_, 12, v_input_3190_);
v___x_3208_ = lean_apply_4(v_toBind_3199_, lean_box(0), lean_box(0), v___x_3203_, v___f_3207_);
return v___x_3208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___boxed(lean_object* v_inst_3209_, lean_object* v_inst_3210_, lean_object* v_inst_3211_, lean_object* v_input_3212_, lean_object* v_cache_3213_, lean_object* v_pre_3214_, lean_object* v_post_3215_, lean_object* v_usedLetOnly_3216_, lean_object* v_skipConstInApp_3217_, lean_object* v_skipInstances_3218_){
_start:
{
uint8_t v_usedLetOnly_boxed_3219_; uint8_t v_skipConstInApp_boxed_3220_; uint8_t v_skipInstances_boxed_3221_; lean_object* v_res_3222_; 
v_usedLetOnly_boxed_3219_ = lean_unbox(v_usedLetOnly_3216_);
v_skipConstInApp_boxed_3220_ = lean_unbox(v_skipConstInApp_3217_);
v_skipInstances_boxed_3221_ = lean_unbox(v_skipInstances_3218_);
v_res_3222_ = l_Lean_Meta_transformWithCache___redArg(v_inst_3209_, v_inst_3210_, v_inst_3211_, v_input_3212_, v_cache_3213_, v_pre_3214_, v_post_3215_, v_usedLetOnly_boxed_3219_, v_skipConstInApp_boxed_3220_, v_skipInstances_boxed_3221_);
return v_res_3222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache(lean_object* v_m_3223_, lean_object* v_inst_3224_, lean_object* v_inst_3225_, lean_object* v_inst_3226_, lean_object* v_input_3227_, lean_object* v_cache_3228_, lean_object* v_pre_3229_, lean_object* v_post_3230_, uint8_t v_usedLetOnly_3231_, uint8_t v_skipConstInApp_3232_, uint8_t v_skipInstances_3233_){
_start:
{
lean_object* v_x_3234_; lean_object* v_toApplicative_3235_; lean_object* v_toBind_3236_; lean_object* v_toPure_3237_; lean_object* v_x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___f_3244_; lean_object* v___x_3245_; 
v_x_3234_ = lean_box(0);
v_toApplicative_3235_ = lean_ctor_get(v_inst_3224_, 0);
v_toBind_3236_ = lean_ctor_get(v_inst_3224_, 1);
lean_inc_n(v_toBind_3236_, 2);
v_toPure_3237_ = lean_ctor_get(v_toApplicative_3235_, 1);
lean_inc(v_toPure_3237_);
lean_inc_n(v_inst_3225_, 2);
v_x_3238_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__1), 3, 1);
lean_closure_set(v_x_3238_, 0, v_inst_3225_);
v___x_3239_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_3239_, 0, lean_box(0));
lean_closure_set(v___x_3239_, 1, lean_box(0));
lean_closure_set(v___x_3239_, 2, v_cache_3228_);
v___x_3240_ = l_Lean_Meta_transformWithCache___redArg___lam__1(v_inst_3225_, lean_box(0), v___x_3239_);
v___x_3241_ = lean_box(v_usedLetOnly_3231_);
v___x_3242_ = lean_box(v_skipConstInApp_3232_);
v___x_3243_ = lean_box(v_skipInstances_3233_);
v___f_3244_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__4___boxed), 14, 13);
lean_closure_set(v___f_3244_, 0, v_toPure_3237_);
lean_closure_set(v___f_3244_, 1, v_x_3238_);
lean_closure_set(v___f_3244_, 2, v_toBind_3236_);
lean_closure_set(v___f_3244_, 3, v_inst_3224_);
lean_closure_set(v___f_3244_, 4, v_inst_3225_);
lean_closure_set(v___f_3244_, 5, v_inst_3226_);
lean_closure_set(v___f_3244_, 6, v_pre_3229_);
lean_closure_set(v___f_3244_, 7, v_post_3230_);
lean_closure_set(v___f_3244_, 8, v___x_3241_);
lean_closure_set(v___f_3244_, 9, v___x_3242_);
lean_closure_set(v___f_3244_, 10, v___x_3243_);
lean_closure_set(v___f_3244_, 11, v_x_3234_);
lean_closure_set(v___f_3244_, 12, v_input_3227_);
v___x_3245_ = lean_apply_4(v_toBind_3236_, lean_box(0), lean_box(0), v___x_3240_, v___f_3244_);
return v___x_3245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___boxed(lean_object* v_m_3246_, lean_object* v_inst_3247_, lean_object* v_inst_3248_, lean_object* v_inst_3249_, lean_object* v_input_3250_, lean_object* v_cache_3251_, lean_object* v_pre_3252_, lean_object* v_post_3253_, lean_object* v_usedLetOnly_3254_, lean_object* v_skipConstInApp_3255_, lean_object* v_skipInstances_3256_){
_start:
{
uint8_t v_usedLetOnly_boxed_3257_; uint8_t v_skipConstInApp_boxed_3258_; uint8_t v_skipInstances_boxed_3259_; lean_object* v_res_3260_; 
v_usedLetOnly_boxed_3257_ = lean_unbox(v_usedLetOnly_3254_);
v_skipConstInApp_boxed_3258_ = lean_unbox(v_skipConstInApp_3255_);
v_skipInstances_boxed_3259_ = lean_unbox(v_skipInstances_3256_);
v_res_3260_ = l_Lean_Meta_transformWithCache(v_m_3246_, v_inst_3247_, v_inst_3248_, v_inst_3249_, v_input_3250_, v_cache_3251_, v_pre_3252_, v_post_3253_, v_usedLetOnly_boxed_3257_, v_skipConstInApp_boxed_3258_, v_skipInstances_boxed_3259_);
return v_res_3260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___redArg___lam__5(lean_object* v_toPure_3261_, lean_object* v_x_3262_, lean_object* v_toBind_3263_, lean_object* v_inst_3264_, lean_object* v_inst_3265_, lean_object* v_inst_3266_, lean_object* v_pre_3267_, lean_object* v_post_3268_, uint8_t v_usedLetOnly_3269_, uint8_t v_skipConstInApp_3270_, uint8_t v___x_3271_, lean_object* v_x_3272_, lean_object* v_input_3273_, lean_object* v_ref_3274_){
_start:
{
lean_object* v___f_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; 
lean_inc(v_toBind_3263_);
lean_inc(v_x_3262_);
lean_inc(v_ref_3274_);
v___f_3275_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__4), 5, 4);
lean_closure_set(v___f_3275_, 0, v_toPure_3261_);
lean_closure_set(v___f_3275_, 1, v_ref_3274_);
lean_closure_set(v___f_3275_, 2, v_x_3262_);
lean_closure_set(v___f_3275_, 3, v_toBind_3263_);
v___x_3276_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_3264_, v_inst_3265_, v_inst_3266_, v_pre_3267_, v_post_3268_, v_usedLetOnly_3269_, v_skipConstInApp_3270_, v___x_3271_, v_x_3272_, v_x_3262_, v_input_3273_, v_ref_3274_);
lean_dec(v_ref_3274_);
v___x_3277_ = lean_apply_4(v_toBind_3263_, lean_box(0), lean_box(0), v___x_3276_, v___f_3275_);
return v___x_3277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___redArg___lam__5___boxed(lean_object* v_toPure_3278_, lean_object* v_x_3279_, lean_object* v_toBind_3280_, lean_object* v_inst_3281_, lean_object* v_inst_3282_, lean_object* v_inst_3283_, lean_object* v_pre_3284_, lean_object* v_post_3285_, lean_object* v_usedLetOnly_3286_, lean_object* v_skipConstInApp_3287_, lean_object* v___x_3288_, lean_object* v_x_3289_, lean_object* v_input_3290_, lean_object* v_ref_3291_){
_start:
{
uint8_t v_usedLetOnly_boxed_3292_; uint8_t v_skipConstInApp_boxed_3293_; uint8_t v___x_114__boxed_3294_; lean_object* v_res_3295_; 
v_usedLetOnly_boxed_3292_ = lean_unbox(v_usedLetOnly_3286_);
v_skipConstInApp_boxed_3293_ = lean_unbox(v_skipConstInApp_3287_);
v___x_114__boxed_3294_ = lean_unbox(v___x_3288_);
v_res_3295_ = l_Lean_Meta_transform___redArg___lam__5(v_toPure_3278_, v_x_3279_, v_toBind_3280_, v_inst_3281_, v_inst_3282_, v_inst_3283_, v_pre_3284_, v_post_3285_, v_usedLetOnly_boxed_3292_, v_skipConstInApp_boxed_3293_, v___x_114__boxed_3294_, v_x_3289_, v_input_3290_, v_ref_3291_);
return v_res_3295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___redArg(lean_object* v_inst_3296_, lean_object* v_inst_3297_, lean_object* v_inst_3298_, lean_object* v_input_3299_, lean_object* v_pre_3300_, lean_object* v_post_3301_, uint8_t v_usedLetOnly_3302_, uint8_t v_skipConstInApp_3303_){
_start:
{
lean_object* v_toApplicative_3304_; lean_object* v_toBind_3305_; lean_object* v_x_3306_; lean_object* v_toPure_3307_; lean_object* v_x_3308_; uint8_t v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___f_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___f_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; 
v_toApplicative_3304_ = lean_ctor_get(v_inst_3296_, 0);
v_toBind_3305_ = lean_ctor_get(v_inst_3296_, 1);
lean_inc_n(v_toBind_3305_, 3);
v_x_3306_ = lean_box(0);
v_toPure_3307_ = lean_ctor_get(v_toApplicative_3304_, 1);
lean_inc_n(v_toPure_3307_, 2);
lean_inc_n(v_inst_3297_, 2);
v_x_3308_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__1), 3, 1);
lean_closure_set(v_x_3308_, 0, v_inst_3297_);
v___x_3309_ = 0;
v___x_3310_ = lean_obj_once(&l_Lean_Core_transform___redArg___closed__2, &l_Lean_Core_transform___redArg___closed__2_once, _init_l_Lean_Core_transform___redArg___closed__2);
v___x_3311_ = l_Lean_Meta_transformWithCache___redArg___lam__1(v_inst_3297_, lean_box(0), v___x_3310_);
v___f_3312_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__2), 2, 1);
lean_closure_set(v___f_3312_, 0, v_toPure_3307_);
v___x_3313_ = lean_box(v_usedLetOnly_3302_);
v___x_3314_ = lean_box(v_skipConstInApp_3303_);
v___x_3315_ = lean_box(v___x_3309_);
v___f_3316_ = lean_alloc_closure((void*)(l_Lean_Meta_transform___redArg___lam__5___boxed), 14, 13);
lean_closure_set(v___f_3316_, 0, v_toPure_3307_);
lean_closure_set(v___f_3316_, 1, v_x_3308_);
lean_closure_set(v___f_3316_, 2, v_toBind_3305_);
lean_closure_set(v___f_3316_, 3, v_inst_3296_);
lean_closure_set(v___f_3316_, 4, v_inst_3297_);
lean_closure_set(v___f_3316_, 5, v_inst_3298_);
lean_closure_set(v___f_3316_, 6, v_pre_3300_);
lean_closure_set(v___f_3316_, 7, v_post_3301_);
lean_closure_set(v___f_3316_, 8, v___x_3313_);
lean_closure_set(v___f_3316_, 9, v___x_3314_);
lean_closure_set(v___f_3316_, 10, v___x_3315_);
lean_closure_set(v___f_3316_, 11, v_x_3306_);
lean_closure_set(v___f_3316_, 12, v_input_3299_);
v___x_3317_ = lean_apply_4(v_toBind_3305_, lean_box(0), lean_box(0), v___x_3311_, v___f_3316_);
v___x_3318_ = lean_apply_4(v_toBind_3305_, lean_box(0), lean_box(0), v___x_3317_, v___f_3312_);
return v___x_3318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___redArg___boxed(lean_object* v_inst_3319_, lean_object* v_inst_3320_, lean_object* v_inst_3321_, lean_object* v_input_3322_, lean_object* v_pre_3323_, lean_object* v_post_3324_, lean_object* v_usedLetOnly_3325_, lean_object* v_skipConstInApp_3326_){
_start:
{
uint8_t v_usedLetOnly_boxed_3327_; uint8_t v_skipConstInApp_boxed_3328_; lean_object* v_res_3329_; 
v_usedLetOnly_boxed_3327_ = lean_unbox(v_usedLetOnly_3325_);
v_skipConstInApp_boxed_3328_ = lean_unbox(v_skipConstInApp_3326_);
v_res_3329_ = l_Lean_Meta_transform___redArg(v_inst_3319_, v_inst_3320_, v_inst_3321_, v_input_3322_, v_pre_3323_, v_post_3324_, v_usedLetOnly_boxed_3327_, v_skipConstInApp_boxed_3328_);
return v_res_3329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform(lean_object* v_m_3330_, lean_object* v_inst_3331_, lean_object* v_inst_3332_, lean_object* v_inst_3333_, lean_object* v_input_3334_, lean_object* v_pre_3335_, lean_object* v_post_3336_, uint8_t v_usedLetOnly_3337_, uint8_t v_skipConstInApp_3338_){
_start:
{
lean_object* v___x_3339_; 
v___x_3339_ = l_Lean_Meta_transform___redArg(v_inst_3331_, v_inst_3332_, v_inst_3333_, v_input_3334_, v_pre_3335_, v_post_3336_, v_usedLetOnly_3337_, v_skipConstInApp_3338_);
return v___x_3339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___boxed(lean_object* v_m_3340_, lean_object* v_inst_3341_, lean_object* v_inst_3342_, lean_object* v_inst_3343_, lean_object* v_input_3344_, lean_object* v_pre_3345_, lean_object* v_post_3346_, lean_object* v_usedLetOnly_3347_, lean_object* v_skipConstInApp_3348_){
_start:
{
uint8_t v_usedLetOnly_boxed_3349_; uint8_t v_skipConstInApp_boxed_3350_; lean_object* v_res_3351_; 
v_usedLetOnly_boxed_3349_ = lean_unbox(v_usedLetOnly_3347_);
v_skipConstInApp_boxed_3350_ = lean_unbox(v_skipConstInApp_3348_);
v_res_3351_ = l_Lean_Meta_transform(v_m_3340_, v_inst_3341_, v_inst_3342_, v_inst_3343_, v_input_3344_, v_pre_3345_, v_post_3346_, v_usedLetOnly_boxed_3349_, v_skipConstInApp_boxed_3350_);
return v_res_3351_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(lean_object* v_e_3352_, lean_object* v___y_3353_){
_start:
{
uint8_t v___x_3355_; 
v___x_3355_ = l_Lean_Expr_hasMVar(v_e_3352_);
if (v___x_3355_ == 0)
{
lean_object* v___x_3356_; 
v___x_3356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3356_, 0, v_e_3352_);
return v___x_3356_;
}
else
{
lean_object* v___x_3357_; lean_object* v_mctx_3358_; lean_object* v___x_3359_; lean_object* v_fst_3360_; lean_object* v_snd_3361_; lean_object* v___x_3362_; lean_object* v_cache_3363_; lean_object* v_zetaDeltaFVarIds_3364_; lean_object* v_postponed_3365_; lean_object* v_diag_3366_; lean_object* v___x_3368_; uint8_t v_isShared_3369_; uint8_t v_isSharedCheck_3375_; 
v___x_3357_ = lean_st_ref_get(v___y_3353_);
v_mctx_3358_ = lean_ctor_get(v___x_3357_, 0);
lean_inc_ref(v_mctx_3358_);
lean_dec(v___x_3357_);
v___x_3359_ = l_Lean_instantiateMVarsCore(v_mctx_3358_, v_e_3352_);
v_fst_3360_ = lean_ctor_get(v___x_3359_, 0);
lean_inc(v_fst_3360_);
v_snd_3361_ = lean_ctor_get(v___x_3359_, 1);
lean_inc(v_snd_3361_);
lean_dec_ref(v___x_3359_);
v___x_3362_ = lean_st_ref_take(v___y_3353_);
v_cache_3363_ = lean_ctor_get(v___x_3362_, 1);
v_zetaDeltaFVarIds_3364_ = lean_ctor_get(v___x_3362_, 2);
v_postponed_3365_ = lean_ctor_get(v___x_3362_, 3);
v_diag_3366_ = lean_ctor_get(v___x_3362_, 4);
v_isSharedCheck_3375_ = !lean_is_exclusive(v___x_3362_);
if (v_isSharedCheck_3375_ == 0)
{
lean_object* v_unused_3376_; 
v_unused_3376_ = lean_ctor_get(v___x_3362_, 0);
lean_dec(v_unused_3376_);
v___x_3368_ = v___x_3362_;
v_isShared_3369_ = v_isSharedCheck_3375_;
goto v_resetjp_3367_;
}
else
{
lean_inc(v_diag_3366_);
lean_inc(v_postponed_3365_);
lean_inc(v_zetaDeltaFVarIds_3364_);
lean_inc(v_cache_3363_);
lean_dec(v___x_3362_);
v___x_3368_ = lean_box(0);
v_isShared_3369_ = v_isSharedCheck_3375_;
goto v_resetjp_3367_;
}
v_resetjp_3367_:
{
lean_object* v___x_3371_; 
if (v_isShared_3369_ == 0)
{
lean_ctor_set(v___x_3368_, 0, v_snd_3361_);
v___x_3371_ = v___x_3368_;
goto v_reusejp_3370_;
}
else
{
lean_object* v_reuseFailAlloc_3374_; 
v_reuseFailAlloc_3374_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3374_, 0, v_snd_3361_);
lean_ctor_set(v_reuseFailAlloc_3374_, 1, v_cache_3363_);
lean_ctor_set(v_reuseFailAlloc_3374_, 2, v_zetaDeltaFVarIds_3364_);
lean_ctor_set(v_reuseFailAlloc_3374_, 3, v_postponed_3365_);
lean_ctor_set(v_reuseFailAlloc_3374_, 4, v_diag_3366_);
v___x_3371_ = v_reuseFailAlloc_3374_;
goto v_reusejp_3370_;
}
v_reusejp_3370_:
{
lean_object* v___x_3372_; lean_object* v___x_3373_; 
v___x_3372_ = lean_st_ref_put(v___y_3353_, v___x_3371_);
v___x_3373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3373_, 0, v_fst_3360_);
return v___x_3373_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg___boxed(lean_object* v_e_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_){
_start:
{
lean_object* v_res_3380_; 
v_res_3380_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(v_e_3377_, v___y_3378_);
lean_dec(v___y_3378_);
return v_res_3380_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0(lean_object* v_e_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_){
_start:
{
lean_object* v___x_3387_; 
v___x_3387_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(v_e_3381_, v___y_3383_);
return v___x_3387_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___boxed(lean_object* v_e_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_){
_start:
{
lean_object* v_res_3394_; 
v_res_3394_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0(v_e_3388_, v___y_3389_, v___y_3390_, v___y_3391_, v___y_3392_);
lean_dec(v___y_3392_);
lean_dec_ref(v___y_3391_);
lean_dec(v___y_3390_);
lean_dec_ref(v___y_3389_);
return v_res_3394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__0(uint8_t v_zetaHave_3395_, lean_object* v___x_3396_, uint8_t v_zetaDelta_3397_, lean_object* v_fvarId_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_){
_start:
{
lean_object* v___x_3404_; 
v___x_3404_ = l_Lean_FVarId_findDecl_x3f___redArg(v_fvarId_3398_, v___y_3399_);
if (lean_obj_tag(v___x_3404_) == 0)
{
lean_object* v_a_3405_; lean_object* v___x_3407_; uint8_t v_isShared_3408_; uint8_t v_isSharedCheck_3433_; 
v_a_3405_ = lean_ctor_get(v___x_3404_, 0);
v_isSharedCheck_3433_ = !lean_is_exclusive(v___x_3404_);
if (v_isSharedCheck_3433_ == 0)
{
v___x_3407_ = v___x_3404_;
v_isShared_3408_ = v_isSharedCheck_3433_;
goto v_resetjp_3406_;
}
else
{
lean_inc(v_a_3405_);
lean_dec(v___x_3404_);
v___x_3407_ = lean_box(0);
v_isShared_3408_ = v_isSharedCheck_3433_;
goto v_resetjp_3406_;
}
v_resetjp_3406_:
{
if (lean_obj_tag(v_a_3405_) == 1)
{
lean_object* v_val_3409_; lean_object* v___x_3411_; uint8_t v_isShared_3412_; uint8_t v_isSharedCheck_3428_; 
v_val_3409_ = lean_ctor_get(v_a_3405_, 0);
v_isSharedCheck_3428_ = !lean_is_exclusive(v_a_3405_);
if (v_isSharedCheck_3428_ == 0)
{
v___x_3411_ = v_a_3405_;
v_isShared_3412_ = v_isSharedCheck_3428_;
goto v_resetjp_3410_;
}
else
{
lean_inc(v_val_3409_);
lean_dec(v_a_3405_);
v___x_3411_ = lean_box(0);
v_isShared_3412_ = v_isSharedCheck_3428_;
goto v_resetjp_3410_;
}
v_resetjp_3410_:
{
uint8_t v___y_3414_; 
if (v_zetaDelta_3397_ == 0)
{
lean_object* v___x_3422_; uint8_t v___x_3423_; 
v___x_3422_ = l_Lean_LocalDecl_index(v_val_3409_);
v___x_3423_ = lean_nat_dec_lt(v___x_3422_, v___x_3396_);
lean_dec(v___x_3422_);
if (v___x_3423_ == 0)
{
lean_del_object(v___x_3411_);
goto v___jp_3419_;
}
else
{
lean_object* v___x_3424_; lean_object* v___x_3426_; 
lean_dec(v_val_3409_);
lean_del_object(v___x_3407_);
v___x_3424_ = lean_box(0);
if (v_isShared_3412_ == 0)
{
lean_ctor_set_tag(v___x_3411_, 0);
lean_ctor_set(v___x_3411_, 0, v___x_3424_);
v___x_3426_ = v___x_3411_;
goto v_reusejp_3425_;
}
else
{
lean_object* v_reuseFailAlloc_3427_; 
v_reuseFailAlloc_3427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3427_, 0, v___x_3424_);
v___x_3426_ = v_reuseFailAlloc_3427_;
goto v_reusejp_3425_;
}
v_reusejp_3425_:
{
return v___x_3426_;
}
}
}
else
{
lean_del_object(v___x_3411_);
goto v___jp_3419_;
}
v___jp_3413_:
{
lean_object* v___x_3415_; lean_object* v___x_3417_; 
v___x_3415_ = l_Lean_LocalDecl_value_x3f(v_val_3409_, v___y_3414_);
lean_dec(v_val_3409_);
if (v_isShared_3408_ == 0)
{
lean_ctor_set(v___x_3407_, 0, v___x_3415_);
v___x_3417_ = v___x_3407_;
goto v_reusejp_3416_;
}
else
{
lean_object* v_reuseFailAlloc_3418_; 
v_reuseFailAlloc_3418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3418_, 0, v___x_3415_);
v___x_3417_ = v_reuseFailAlloc_3418_;
goto v_reusejp_3416_;
}
v_reusejp_3416_:
{
return v___x_3417_;
}
}
v___jp_3419_:
{
if (v_zetaHave_3395_ == 0)
{
v___y_3414_ = v_zetaHave_3395_;
goto v___jp_3413_;
}
else
{
lean_object* v___x_3420_; uint8_t v___x_3421_; 
v___x_3420_ = l_Lean_LocalDecl_index(v_val_3409_);
v___x_3421_ = lean_nat_dec_le(v___x_3396_, v___x_3420_);
lean_dec(v___x_3420_);
v___y_3414_ = v___x_3421_;
goto v___jp_3413_;
}
}
}
}
else
{
lean_object* v___x_3429_; lean_object* v___x_3431_; 
lean_dec(v_a_3405_);
v___x_3429_ = lean_box(0);
if (v_isShared_3408_ == 0)
{
lean_ctor_set(v___x_3407_, 0, v___x_3429_);
v___x_3431_ = v___x_3407_;
goto v_reusejp_3430_;
}
else
{
lean_object* v_reuseFailAlloc_3432_; 
v_reuseFailAlloc_3432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3432_, 0, v___x_3429_);
v___x_3431_ = v_reuseFailAlloc_3432_;
goto v_reusejp_3430_;
}
v_reusejp_3430_:
{
return v___x_3431_;
}
}
}
}
else
{
lean_object* v_a_3434_; lean_object* v___x_3436_; uint8_t v_isShared_3437_; uint8_t v_isSharedCheck_3441_; 
v_a_3434_ = lean_ctor_get(v___x_3404_, 0);
v_isSharedCheck_3441_ = !lean_is_exclusive(v___x_3404_);
if (v_isSharedCheck_3441_ == 0)
{
v___x_3436_ = v___x_3404_;
v_isShared_3437_ = v_isSharedCheck_3441_;
goto v_resetjp_3435_;
}
else
{
lean_inc(v_a_3434_);
lean_dec(v___x_3404_);
v___x_3436_ = lean_box(0);
v_isShared_3437_ = v_isSharedCheck_3441_;
goto v_resetjp_3435_;
}
v_resetjp_3435_:
{
lean_object* v___x_3439_; 
if (v_isShared_3437_ == 0)
{
v___x_3439_ = v___x_3436_;
goto v_reusejp_3438_;
}
else
{
lean_object* v_reuseFailAlloc_3440_; 
v_reuseFailAlloc_3440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3440_, 0, v_a_3434_);
v___x_3439_ = v_reuseFailAlloc_3440_;
goto v_reusejp_3438_;
}
v_reusejp_3438_:
{
return v___x_3439_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__0___boxed(lean_object* v_zetaHave_3442_, lean_object* v___x_3443_, lean_object* v_zetaDelta_3444_, lean_object* v_fvarId_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_){
_start:
{
uint8_t v_zetaHave_boxed_3451_; uint8_t v_zetaDelta_boxed_3452_; lean_object* v_res_3453_; 
v_zetaHave_boxed_3451_ = lean_unbox(v_zetaHave_3442_);
v_zetaDelta_boxed_3452_ = lean_unbox(v_zetaDelta_3444_);
v_res_3453_ = l_Lean_Meta_zetaReduce___lam__0(v_zetaHave_boxed_3451_, v___x_3443_, v_zetaDelta_boxed_3452_, v_fvarId_3445_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_);
lean_dec(v___y_3449_);
lean_dec_ref(v___y_3448_);
lean_dec(v___y_3447_);
lean_dec_ref(v___y_3446_);
lean_dec(v___x_3443_);
return v_res_3453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__1(lean_object* v_e_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_){
_start:
{
lean_object* v___x_3460_; lean_object* v___x_3461_; 
v___x_3460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3460_, 0, v_e_3454_);
v___x_3461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3461_, 0, v___x_3460_);
return v___x_3461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__1___boxed(lean_object* v_e_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_){
_start:
{
lean_object* v_res_3468_; 
v_res_3468_ = l_Lean_Meta_zetaReduce___lam__1(v_e_3462_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_);
lean_dec(v___y_3466_);
lean_dec_ref(v___y_3465_);
lean_dec(v___y_3464_);
lean_dec_ref(v___y_3463_);
return v_res_3468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__2(lean_object* v___f_3469_, lean_object* v_e_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_){
_start:
{
if (lean_obj_tag(v_e_3470_) == 1)
{
lean_object* v_fvarId_3476_; lean_object* v___x_3477_; 
v_fvarId_3476_ = lean_ctor_get(v_e_3470_, 0);
lean_inc(v___y_3474_);
lean_inc_ref(v___y_3473_);
lean_inc(v___y_3472_);
lean_inc_ref(v___y_3471_);
lean_inc(v_fvarId_3476_);
v___x_3477_ = lean_apply_6(v___f_3469_, v_fvarId_3476_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_, lean_box(0));
if (lean_obj_tag(v___x_3477_) == 0)
{
lean_object* v_a_3478_; lean_object* v___x_3480_; uint8_t v_isShared_3481_; uint8_t v_isSharedCheck_3503_; 
v_a_3478_ = lean_ctor_get(v___x_3477_, 0);
v_isSharedCheck_3503_ = !lean_is_exclusive(v___x_3477_);
if (v_isSharedCheck_3503_ == 0)
{
v___x_3480_ = v___x_3477_;
v_isShared_3481_ = v_isSharedCheck_3503_;
goto v_resetjp_3479_;
}
else
{
lean_inc(v_a_3478_);
lean_dec(v___x_3477_);
v___x_3480_ = lean_box(0);
v_isShared_3481_ = v_isSharedCheck_3503_;
goto v_resetjp_3479_;
}
v_resetjp_3479_:
{
if (lean_obj_tag(v_a_3478_) == 1)
{
lean_object* v_val_3482_; lean_object* v___x_3484_; uint8_t v_isShared_3485_; uint8_t v_isSharedCheck_3498_; 
lean_del_object(v___x_3480_);
lean_dec_ref_known(v_e_3470_, 1);
v_val_3482_ = lean_ctor_get(v_a_3478_, 0);
v_isSharedCheck_3498_ = !lean_is_exclusive(v_a_3478_);
if (v_isSharedCheck_3498_ == 0)
{
v___x_3484_ = v_a_3478_;
v_isShared_3485_ = v_isSharedCheck_3498_;
goto v_resetjp_3483_;
}
else
{
lean_inc(v_val_3482_);
lean_dec(v_a_3478_);
v___x_3484_ = lean_box(0);
v_isShared_3485_ = v_isSharedCheck_3498_;
goto v_resetjp_3483_;
}
v_resetjp_3483_:
{
lean_object* v___x_3486_; lean_object* v_a_3487_; lean_object* v___x_3489_; uint8_t v_isShared_3490_; uint8_t v_isSharedCheck_3497_; 
v___x_3486_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(v_val_3482_, v___y_3472_);
v_a_3487_ = lean_ctor_get(v___x_3486_, 0);
v_isSharedCheck_3497_ = !lean_is_exclusive(v___x_3486_);
if (v_isSharedCheck_3497_ == 0)
{
v___x_3489_ = v___x_3486_;
v_isShared_3490_ = v_isSharedCheck_3497_;
goto v_resetjp_3488_;
}
else
{
lean_inc(v_a_3487_);
lean_dec(v___x_3486_);
v___x_3489_ = lean_box(0);
v_isShared_3490_ = v_isSharedCheck_3497_;
goto v_resetjp_3488_;
}
v_resetjp_3488_:
{
lean_object* v___x_3492_; 
if (v_isShared_3485_ == 0)
{
lean_ctor_set(v___x_3484_, 0, v_a_3487_);
v___x_3492_ = v___x_3484_;
goto v_reusejp_3491_;
}
else
{
lean_object* v_reuseFailAlloc_3496_; 
v_reuseFailAlloc_3496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3496_, 0, v_a_3487_);
v___x_3492_ = v_reuseFailAlloc_3496_;
goto v_reusejp_3491_;
}
v_reusejp_3491_:
{
lean_object* v___x_3494_; 
if (v_isShared_3490_ == 0)
{
lean_ctor_set(v___x_3489_, 0, v___x_3492_);
v___x_3494_ = v___x_3489_;
goto v_reusejp_3493_;
}
else
{
lean_object* v_reuseFailAlloc_3495_; 
v_reuseFailAlloc_3495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3495_, 0, v___x_3492_);
v___x_3494_ = v_reuseFailAlloc_3495_;
goto v_reusejp_3493_;
}
v_reusejp_3493_:
{
return v___x_3494_;
}
}
}
}
}
else
{
lean_object* v___x_3499_; lean_object* v___x_3501_; 
lean_dec(v_a_3478_);
v___x_3499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3499_, 0, v_e_3470_);
if (v_isShared_3481_ == 0)
{
lean_ctor_set(v___x_3480_, 0, v___x_3499_);
v___x_3501_ = v___x_3480_;
goto v_reusejp_3500_;
}
else
{
lean_object* v_reuseFailAlloc_3502_; 
v_reuseFailAlloc_3502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3502_, 0, v___x_3499_);
v___x_3501_ = v_reuseFailAlloc_3502_;
goto v_reusejp_3500_;
}
v_reusejp_3500_:
{
return v___x_3501_;
}
}
}
}
else
{
lean_object* v_a_3504_; lean_object* v___x_3506_; uint8_t v_isShared_3507_; uint8_t v_isSharedCheck_3511_; 
lean_dec_ref_known(v_e_3470_, 1);
v_a_3504_ = lean_ctor_get(v___x_3477_, 0);
v_isSharedCheck_3511_ = !lean_is_exclusive(v___x_3477_);
if (v_isSharedCheck_3511_ == 0)
{
v___x_3506_ = v___x_3477_;
v_isShared_3507_ = v_isSharedCheck_3511_;
goto v_resetjp_3505_;
}
else
{
lean_inc(v_a_3504_);
lean_dec(v___x_3477_);
v___x_3506_ = lean_box(0);
v_isShared_3507_ = v_isSharedCheck_3511_;
goto v_resetjp_3505_;
}
v_resetjp_3505_:
{
lean_object* v___x_3509_; 
if (v_isShared_3507_ == 0)
{
v___x_3509_ = v___x_3506_;
goto v_reusejp_3508_;
}
else
{
lean_object* v_reuseFailAlloc_3510_; 
v_reuseFailAlloc_3510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3510_, 0, v_a_3504_);
v___x_3509_ = v_reuseFailAlloc_3510_;
goto v_reusejp_3508_;
}
v_reusejp_3508_:
{
return v___x_3509_;
}
}
}
}
else
{
lean_object* v___x_3512_; lean_object* v___x_3513_; 
lean_dec_ref(v_e_3470_);
lean_dec_ref(v___f_3469_);
v___x_3512_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_3513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3513_, 0, v___x_3512_);
return v___x_3513_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__2___boxed(lean_object* v___f_3514_, lean_object* v_e_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_){
_start:
{
lean_object* v_res_3521_; 
v_res_3521_ = l_Lean_Meta_zetaReduce___lam__2(v___f_3514_, v_e_3515_, v___y_3516_, v___y_3517_, v___y_3518_, v___y_3519_);
lean_dec(v___y_3519_);
lean_dec_ref(v___y_3518_);
lean_dec(v___y_3517_);
lean_dec_ref(v___y_3516_);
return v_res_3521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__4(lean_object* v___f_3522_, lean_object* v_e_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_){
_start:
{
lean_object* v___x_3529_; 
v___x_3529_ = l_Lean_Expr_getAppFn(v_e_3523_);
if (lean_obj_tag(v___x_3529_) == 1)
{
lean_object* v_fvarId_3530_; lean_object* v___x_3531_; 
v_fvarId_3530_ = lean_ctor_get(v___x_3529_, 0);
lean_inc(v_fvarId_3530_);
lean_dec_ref_known(v___x_3529_, 1);
lean_inc(v___y_3527_);
lean_inc_ref(v___y_3526_);
lean_inc(v___y_3525_);
lean_inc_ref(v___y_3524_);
v___x_3531_ = lean_apply_6(v___f_3522_, v_fvarId_3530_, v___y_3524_, v___y_3525_, v___y_3526_, v___y_3527_, lean_box(0));
if (lean_obj_tag(v___x_3531_) == 0)
{
lean_object* v_a_3532_; lean_object* v___x_3534_; uint8_t v_isShared_3535_; uint8_t v_isSharedCheck_3564_; 
v_a_3532_ = lean_ctor_get(v___x_3531_, 0);
v_isSharedCheck_3564_ = !lean_is_exclusive(v___x_3531_);
if (v_isSharedCheck_3564_ == 0)
{
v___x_3534_ = v___x_3531_;
v_isShared_3535_ = v_isSharedCheck_3564_;
goto v_resetjp_3533_;
}
else
{
lean_inc(v_a_3532_);
lean_dec(v___x_3531_);
v___x_3534_ = lean_box(0);
v_isShared_3535_ = v_isSharedCheck_3564_;
goto v_resetjp_3533_;
}
v_resetjp_3533_:
{
if (lean_obj_tag(v_a_3532_) == 1)
{
lean_object* v_val_3536_; lean_object* v___x_3538_; uint8_t v_isShared_3539_; uint8_t v_isSharedCheck_3559_; 
lean_del_object(v___x_3534_);
v_val_3536_ = lean_ctor_get(v_a_3532_, 0);
v_isSharedCheck_3559_ = !lean_is_exclusive(v_a_3532_);
if (v_isSharedCheck_3559_ == 0)
{
v___x_3538_ = v_a_3532_;
v_isShared_3539_ = v_isSharedCheck_3559_;
goto v_resetjp_3537_;
}
else
{
lean_inc(v_val_3536_);
lean_dec(v_a_3532_);
v___x_3538_ = lean_box(0);
v_isShared_3539_ = v_isSharedCheck_3559_;
goto v_resetjp_3537_;
}
v_resetjp_3537_:
{
lean_object* v___x_3540_; lean_object* v_a_3541_; lean_object* v___x_3543_; uint8_t v_isShared_3544_; uint8_t v_isSharedCheck_3558_; 
v___x_3540_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(v_val_3536_, v___y_3525_);
v_a_3541_ = lean_ctor_get(v___x_3540_, 0);
v_isSharedCheck_3558_ = !lean_is_exclusive(v___x_3540_);
if (v_isSharedCheck_3558_ == 0)
{
v___x_3543_ = v___x_3540_;
v_isShared_3544_ = v_isSharedCheck_3558_;
goto v_resetjp_3542_;
}
else
{
lean_inc(v_a_3541_);
lean_dec(v___x_3540_);
v___x_3543_ = lean_box(0);
v_isShared_3544_ = v_isSharedCheck_3558_;
goto v_resetjp_3542_;
}
v_resetjp_3542_:
{
lean_object* v_dummy_3545_; lean_object* v_nargs_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3553_; 
v_dummy_3545_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_3546_ = l_Lean_Expr_getAppNumArgs(v_e_3523_);
lean_inc(v_nargs_3546_);
v___x_3547_ = lean_mk_array(v_nargs_3546_, v_dummy_3545_);
v___x_3548_ = lean_unsigned_to_nat(1u);
v___x_3549_ = lean_nat_sub(v_nargs_3546_, v___x_3548_);
lean_dec(v_nargs_3546_);
v___x_3550_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3523_, v___x_3547_, v___x_3549_);
v___x_3551_ = l_Lean_Expr_beta(v_a_3541_, v___x_3550_);
if (v_isShared_3539_ == 0)
{
lean_ctor_set(v___x_3538_, 0, v___x_3551_);
v___x_3553_ = v___x_3538_;
goto v_reusejp_3552_;
}
else
{
lean_object* v_reuseFailAlloc_3557_; 
v_reuseFailAlloc_3557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3557_, 0, v___x_3551_);
v___x_3553_ = v_reuseFailAlloc_3557_;
goto v_reusejp_3552_;
}
v_reusejp_3552_:
{
lean_object* v___x_3555_; 
if (v_isShared_3544_ == 0)
{
lean_ctor_set(v___x_3543_, 0, v___x_3553_);
v___x_3555_ = v___x_3543_;
goto v_reusejp_3554_;
}
else
{
lean_object* v_reuseFailAlloc_3556_; 
v_reuseFailAlloc_3556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3556_, 0, v___x_3553_);
v___x_3555_ = v_reuseFailAlloc_3556_;
goto v_reusejp_3554_;
}
v_reusejp_3554_:
{
return v___x_3555_;
}
}
}
}
}
else
{
lean_object* v___x_3560_; lean_object* v___x_3562_; 
lean_dec(v_a_3532_);
lean_dec_ref(v_e_3523_);
v___x_3560_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
if (v_isShared_3535_ == 0)
{
lean_ctor_set(v___x_3534_, 0, v___x_3560_);
v___x_3562_ = v___x_3534_;
goto v_reusejp_3561_;
}
else
{
lean_object* v_reuseFailAlloc_3563_; 
v_reuseFailAlloc_3563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3563_, 0, v___x_3560_);
v___x_3562_ = v_reuseFailAlloc_3563_;
goto v_reusejp_3561_;
}
v_reusejp_3561_:
{
return v___x_3562_;
}
}
}
}
else
{
lean_object* v_a_3565_; lean_object* v___x_3567_; uint8_t v_isShared_3568_; uint8_t v_isSharedCheck_3572_; 
lean_dec_ref(v_e_3523_);
v_a_3565_ = lean_ctor_get(v___x_3531_, 0);
v_isSharedCheck_3572_ = !lean_is_exclusive(v___x_3531_);
if (v_isSharedCheck_3572_ == 0)
{
v___x_3567_ = v___x_3531_;
v_isShared_3568_ = v_isSharedCheck_3572_;
goto v_resetjp_3566_;
}
else
{
lean_inc(v_a_3565_);
lean_dec(v___x_3531_);
v___x_3567_ = lean_box(0);
v_isShared_3568_ = v_isSharedCheck_3572_;
goto v_resetjp_3566_;
}
v_resetjp_3566_:
{
lean_object* v___x_3570_; 
if (v_isShared_3568_ == 0)
{
v___x_3570_ = v___x_3567_;
goto v_reusejp_3569_;
}
else
{
lean_object* v_reuseFailAlloc_3571_; 
v_reuseFailAlloc_3571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3571_, 0, v_a_3565_);
v___x_3570_ = v_reuseFailAlloc_3571_;
goto v_reusejp_3569_;
}
v_reusejp_3569_:
{
return v___x_3570_;
}
}
}
}
else
{
lean_object* v___x_3573_; lean_object* v___x_3574_; 
lean_dec_ref(v___x_3529_);
lean_dec_ref(v_e_3523_);
lean_dec_ref(v___f_3522_);
v___x_3573_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_3574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3574_, 0, v___x_3573_);
return v___x_3574_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__4___boxed(lean_object* v___f_3575_, lean_object* v_e_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_){
_start:
{
lean_object* v_res_3582_; 
v_res_3582_ = l_Lean_Meta_zetaReduce___lam__4(v___f_3575_, v_e_3576_, v___y_3577_, v___y_3578_, v___y_3579_, v___y_3580_);
lean_dec(v___y_3580_);
lean_dec_ref(v___y_3579_);
lean_dec(v___y_3578_);
lean_dec_ref(v___y_3577_);
return v_res_3582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0(lean_object* v_00_u03b1_3583_, lean_object* v_x_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_){
_start:
{
lean_object* v___x_3590_; lean_object* v___x_3591_; 
v___x_3590_ = lean_apply_1(v_x_3584_, lean_box(0));
v___x_3591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3591_, 0, v___x_3590_);
return v___x_3591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0___boxed(lean_object* v_00_u03b1_3592_, lean_object* v_x_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_){
_start:
{
lean_object* v_res_3599_; 
v_res_3599_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0(v_00_u03b1_3592_, v_x_3593_, v___y_3594_, v___y_3595_, v___y_3596_, v___y_3597_);
lean_dec(v___y_3597_);
lean_dec_ref(v___y_3596_);
lean_dec(v___y_3595_);
lean_dec_ref(v___y_3594_);
return v_res_3599_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__2(lean_object* v___x_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_){
_start:
{
lean_object* v___x_3606_; 
v___x_3606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3606_, 0, v___x_3600_);
return v___x_3606_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__2___boxed(lean_object* v___x_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_){
_start:
{
lean_object* v_res_3613_; 
v_res_3613_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__2(v___x_3607_, v___y_3608_, v___y_3609_, v___y_3610_, v___y_3611_);
lean_dec(v___y_3611_);
lean_dec_ref(v___y_3610_);
lean_dec(v___y_3609_);
lean_dec_ref(v___y_3608_);
return v_res_3613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0(lean_object* v_k_3614_, lean_object* v___y_3615_, lean_object* v_b_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_){
_start:
{
lean_object* v___x_3622_; 
lean_inc(v___y_3620_);
lean_inc_ref(v___y_3619_);
lean_inc(v___y_3618_);
lean_inc_ref(v___y_3617_);
lean_inc(v___y_3615_);
v___x_3622_ = lean_apply_7(v_k_3614_, v_b_3616_, v___y_3615_, v___y_3617_, v___y_3618_, v___y_3619_, v___y_3620_, lean_box(0));
return v___x_3622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0___boxed(lean_object* v_k_3623_, lean_object* v___y_3624_, lean_object* v_b_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_){
_start:
{
lean_object* v_res_3631_; 
v_res_3631_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0(v_k_3623_, v___y_3624_, v_b_3625_, v___y_3626_, v___y_3627_, v___y_3628_, v___y_3629_);
lean_dec(v___y_3629_);
lean_dec_ref(v___y_3628_);
lean_dec(v___y_3627_);
lean_dec_ref(v___y_3626_);
lean_dec(v___y_3624_);
return v_res_3631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(lean_object* v_name_3632_, uint8_t v_bi_3633_, lean_object* v_type_3634_, lean_object* v_k_3635_, uint8_t v_kind_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_){
_start:
{
lean_object* v___f_3643_; lean_object* v___x_3644_; 
lean_inc(v___y_3637_);
v___f_3643_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3643_, 0, v_k_3635_);
lean_closure_set(v___f_3643_, 1, v___y_3637_);
v___x_3644_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3632_, v_bi_3633_, v_type_3634_, v___f_3643_, v_kind_3636_, v___y_3638_, v___y_3639_, v___y_3640_, v___y_3641_);
if (lean_obj_tag(v___x_3644_) == 0)
{
return v___x_3644_;
}
else
{
lean_object* v_a_3645_; lean_object* v___x_3647_; uint8_t v_isShared_3648_; uint8_t v_isSharedCheck_3652_; 
v_a_3645_ = lean_ctor_get(v___x_3644_, 0);
v_isSharedCheck_3652_ = !lean_is_exclusive(v___x_3644_);
if (v_isSharedCheck_3652_ == 0)
{
v___x_3647_ = v___x_3644_;
v_isShared_3648_ = v_isSharedCheck_3652_;
goto v_resetjp_3646_;
}
else
{
lean_inc(v_a_3645_);
lean_dec(v___x_3644_);
v___x_3647_ = lean_box(0);
v_isShared_3648_ = v_isSharedCheck_3652_;
goto v_resetjp_3646_;
}
v_resetjp_3646_:
{
lean_object* v___x_3650_; 
if (v_isShared_3648_ == 0)
{
v___x_3650_ = v___x_3647_;
goto v_reusejp_3649_;
}
else
{
lean_object* v_reuseFailAlloc_3651_; 
v_reuseFailAlloc_3651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3651_, 0, v_a_3645_);
v___x_3650_ = v_reuseFailAlloc_3651_;
goto v_reusejp_3649_;
}
v_reusejp_3649_:
{
return v___x_3650_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___boxed(lean_object* v_name_3653_, lean_object* v_bi_3654_, lean_object* v_type_3655_, lean_object* v_k_3656_, lean_object* v_kind_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_){
_start:
{
uint8_t v_bi_boxed_3664_; uint8_t v_kind_boxed_3665_; lean_object* v_res_3666_; 
v_bi_boxed_3664_ = lean_unbox(v_bi_3654_);
v_kind_boxed_3665_ = lean_unbox(v_kind_3657_);
v_res_3666_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_name_3653_, v_bi_boxed_3664_, v_type_3655_, v_k_3656_, v_kind_boxed_3665_, v___y_3658_, v___y_3659_, v___y_3660_, v___y_3661_, v___y_3662_);
lean_dec(v___y_3662_);
lean_dec_ref(v___y_3661_);
lean_dec(v___y_3660_);
lean_dec_ref(v___y_3659_);
lean_dec(v___y_3658_);
return v_res_3666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg(lean_object* v_name_3667_, lean_object* v_type_3668_, lean_object* v_val_3669_, lean_object* v_k_3670_, uint8_t v_nondep_3671_, uint8_t v_kind_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_){
_start:
{
lean_object* v___f_3679_; lean_object* v___x_3680_; 
lean_inc(v___y_3673_);
v___f_3679_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3679_, 0, v_k_3670_);
lean_closure_set(v___f_3679_, 1, v___y_3673_);
v___x_3680_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_3667_, v_type_3668_, v_val_3669_, v___f_3679_, v_nondep_3671_, v_kind_3672_, v___y_3674_, v___y_3675_, v___y_3676_, v___y_3677_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg___boxed(lean_object* v_name_3689_, lean_object* v_type_3690_, lean_object* v_val_3691_, lean_object* v_k_3692_, lean_object* v_nondep_3693_, lean_object* v_kind_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_){
_start:
{
uint8_t v_nondep_boxed_3701_; uint8_t v_kind_boxed_3702_; lean_object* v_res_3703_; 
v_nondep_boxed_3701_ = lean_unbox(v_nondep_3693_);
v_kind_boxed_3702_ = lean_unbox(v_kind_3694_);
v_res_3703_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg(v_name_3689_, v_type_3690_, v_val_3691_, v_k_3692_, v_nondep_boxed_3701_, v_kind_boxed_3702_, v___y_3695_, v___y_3696_, v___y_3697_, v___y_3698_, v___y_3699_);
lean_dec(v___y_3699_);
lean_dec_ref(v___y_3698_);
lean_dec(v___y_3697_);
lean_dec_ref(v___y_3696_);
lean_dec(v___y_3695_);
return v_res_3703_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0(lean_object* v_00_u03b1_3704_, lean_object* v_x_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_){
_start:
{
lean_object* v___x_3711_; lean_object* v___x_3712_; 
v___x_3711_ = lean_apply_1(v_x_3705_, lean_box(0));
v___x_3712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3712_, 0, v___x_3711_);
return v___x_3712_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0___boxed(lean_object* v_00_u03b1_3713_, lean_object* v_x_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_){
_start:
{
lean_object* v_res_3720_; 
v_res_3720_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0(v_00_u03b1_3713_, v_x_3714_, v___y_3715_, v___y_3716_, v___y_3717_, v___y_3718_);
lean_dec(v___y_3718_);
lean_dec_ref(v___y_3717_);
lean_dec(v___y_3716_);
lean_dec_ref(v___y_3715_);
return v_res_3720_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg(lean_object* v_ref_3721_){
_start:
{
lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; 
v___x_3723_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5);
v___x_3724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3724_, 0, v_ref_3721_);
lean_ctor_set(v___x_3724_, 1, v___x_3723_);
v___x_3725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3725_, 0, v___x_3724_);
return v___x_3725_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg___boxed(lean_object* v_ref_3726_, lean_object* v___y_3727_){
_start:
{
lean_object* v_res_3728_; 
v_res_3728_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg(v_ref_3726_);
return v_res_3728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg(lean_object* v_x_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_){
_start:
{
lean_object* v___y_3737_; lean_object* v_toCold_3746_; lean_object* v_currRecDepth_3747_; lean_object* v_ref_3748_; uint8_t v_diag_3749_; uint8_t v_suppressElabErrors_3750_; lean_object* v_maxRecDepth_3756_; lean_object* v___x_3757_; uint8_t v___x_3758_; 
v_toCold_3746_ = lean_ctor_get(v___y_3733_, 0);
v_currRecDepth_3747_ = lean_ctor_get(v___y_3733_, 1);
v_ref_3748_ = lean_ctor_get(v___y_3733_, 2);
v_diag_3749_ = lean_ctor_get_uint8(v___y_3733_, sizeof(void*)*3);
v_suppressElabErrors_3750_ = lean_ctor_get_uint8(v___y_3733_, sizeof(void*)*3 + 1);
v_maxRecDepth_3756_ = lean_ctor_get(v_toCold_3746_, 3);
v___x_3757_ = lean_unsigned_to_nat(0u);
v___x_3758_ = lean_nat_dec_eq(v_maxRecDepth_3756_, v___x_3757_);
if (v___x_3758_ == 0)
{
uint8_t v___x_3759_; 
v___x_3759_ = lean_nat_dec_eq(v_currRecDepth_3747_, v_maxRecDepth_3756_);
if (v___x_3759_ == 0)
{
goto v___jp_3751_;
}
else
{
lean_object* v___x_3760_; 
lean_dec_ref(v_x_3729_);
lean_inc(v_ref_3748_);
v___x_3760_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg(v_ref_3748_);
v___y_3737_ = v___x_3760_;
goto v___jp_3736_;
}
}
else
{
goto v___jp_3751_;
}
v___jp_3736_:
{
if (lean_obj_tag(v___y_3737_) == 0)
{
return v___y_3737_;
}
else
{
lean_object* v_a_3738_; lean_object* v___x_3740_; uint8_t v_isShared_3741_; uint8_t v_isSharedCheck_3745_; 
v_a_3738_ = lean_ctor_get(v___y_3737_, 0);
v_isSharedCheck_3745_ = !lean_is_exclusive(v___y_3737_);
if (v_isSharedCheck_3745_ == 0)
{
v___x_3740_ = v___y_3737_;
v_isShared_3741_ = v_isSharedCheck_3745_;
goto v_resetjp_3739_;
}
else
{
lean_inc(v_a_3738_);
lean_dec(v___y_3737_);
v___x_3740_ = lean_box(0);
v_isShared_3741_ = v_isSharedCheck_3745_;
goto v_resetjp_3739_;
}
v_resetjp_3739_:
{
lean_object* v___x_3743_; 
if (v_isShared_3741_ == 0)
{
v___x_3743_ = v___x_3740_;
goto v_reusejp_3742_;
}
else
{
lean_object* v_reuseFailAlloc_3744_; 
v_reuseFailAlloc_3744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3744_, 0, v_a_3738_);
v___x_3743_ = v_reuseFailAlloc_3744_;
goto v_reusejp_3742_;
}
v_reusejp_3742_:
{
return v___x_3743_;
}
}
}
}
v___jp_3751_:
{
lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; 
v___x_3752_ = lean_unsigned_to_nat(1u);
v___x_3753_ = lean_nat_add(v_currRecDepth_3747_, v___x_3752_);
lean_inc(v_ref_3748_);
lean_inc_ref(v_toCold_3746_);
v___x_3754_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_3754_, 0, v_toCold_3746_);
lean_ctor_set(v___x_3754_, 1, v___x_3753_);
lean_ctor_set(v___x_3754_, 2, v_ref_3748_);
lean_ctor_set_uint8(v___x_3754_, sizeof(void*)*3, v_diag_3749_);
lean_ctor_set_uint8(v___x_3754_, sizeof(void*)*3 + 1, v_suppressElabErrors_3750_);
lean_inc(v___y_3734_);
lean_inc(v___y_3732_);
lean_inc_ref(v___y_3731_);
lean_inc(v___y_3730_);
v___x_3755_ = lean_apply_6(v_x_3729_, v___y_3730_, v___y_3731_, v___y_3732_, v___x_3754_, v___y_3734_, lean_box(0));
v___y_3737_ = v___x_3755_;
goto v___jp_3736_;
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
lean_dec_ref_known(v_a_3816_, 1);
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
lean_dec_ref_known(v_a_3816_, 1);
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
lean_dec_ref_known(v_a_3816_, 1);
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
lean_dec_ref_known(v_e_x3f_3826_, 1);
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
lean_dec_ref_known(v_e_3849_, 3);
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
lean_dec_ref_known(v___x_3861_, 1);
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
lean_dec_ref_known(v___x_3870_, 1);
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
lean_dec_ref_known(v___x_3875_, 1);
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
lean_dec_ref_known(v_e_3918_, 4);
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
lean_dec_ref_known(v___x_3931_, 1);
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
lean_dec_ref_known(v___x_3934_, 1);
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
lean_dec_ref_known(v___x_3943_, 1);
v___x_3945_ = 0;
v___x_3946_ = 1;
v___x_3947_ = l_Lean_Meta_mkLetFVars(v_fvars_3917_, v_a_3944_, v_usedLetOnly_3914_, v___x_3945_, v___x_3946_, v___y_3920_, v___y_3921_, v___y_3922_, v___y_3923_);
lean_dec_ref(v_fvars_3917_);
if (lean_obj_tag(v___x_3947_) == 0)
{
lean_object* v_a_3948_; lean_object* v___x_3949_; 
v_a_3948_ = lean_ctor_get(v___x_3947_, 0);
lean_inc(v_a_3948_);
lean_dec_ref_known(v___x_3947_, 1);
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
lean_dec_ref_known(v___x_3967_, 1);
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
lean_dec_ref_known(v_a_4052_, 1);
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
lean_dec_ref_known(v_a_4052_, 1);
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
lean_dec_ref_known(v_x_4095_, 2);
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
lean_dec_ref_known(v___x_4113_, 1);
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
lean_dec_ref_known(v___x_4126_, 1);
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
lean_dec_ref_known(v___x_4130_, 1);
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
lean_dec_ref_known(v___x_4151_, 1);
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
lean_dec_ref_known(v___x_4173_, 1);
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
lean_dec_ref_known(v_a_4175_, 1);
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
lean_dec_ref_known(v_a_4175_, 1);
v___x_4220_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4161_, v_post_4163_, v_usedLetOnly_4164_, v_skipConstInApp_4165_, v_skipInstances_4166_, v_e_4219_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_);
return v___x_4220_;
}
default: 
{
lean_object* v_e_x3f_4221_; 
lean_del_object(v___x_4177_);
v_e_x3f_4221_ = lean_ctor_get(v_a_4175_, 0);
lean_inc(v_e_x3f_4221_);
lean_dec_ref_known(v_a_4175_, 1);
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
lean_dec_ref_known(v_e_x3f_4221_, 1);
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
lean_dec_ref_known(v___x_4195_, 1);
v___x_4197_ = lean_ptr_addr(v_expr_4194_);
v___x_4198_ = lean_ptr_addr(v_a_4196_);
v___x_4199_ = lean_usize_dec_eq(v___x_4197_, v___x_4198_);
if (v___x_4199_ == 0)
{
lean_object* v___x_4200_; lean_object* v___x_4201_; 
lean_inc(v_data_4193_);
lean_dec_ref_known(v___y_4180_, 2);
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
lean_dec_ref_known(v___y_4180_, 2);
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
lean_dec_ref_known(v___x_4206_, 1);
v___x_4208_ = lean_ptr_addr(v_struct_4205_);
v___x_4209_ = lean_ptr_addr(v_a_4207_);
v___x_4210_ = lean_usize_dec_eq(v___x_4208_, v___x_4209_);
if (v___x_4210_ == 0)
{
lean_object* v___x_4211_; lean_object* v___x_4212_; 
lean_inc(v_idx_4204_);
lean_inc(v_typeName_4203_);
lean_dec_ref_known(v___y_4180_, 3);
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
lean_dec_ref_known(v___y_4180_, 3);
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
lean_dec_ref_known(v___x_4281_, 1);
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
lean_dec_ref_known(v___x_4275_, 1);
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
lean_dec_ref_known(v_e_4338_, 3);
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
lean_dec_ref_known(v___x_4350_, 1);
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
lean_dec_ref_known(v___x_4359_, 1);
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
lean_dec_ref_known(v___x_4364_, 1);
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
lean_dec_ref_known(v___x_4537_, 1);
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
lean_dec_ref_known(v___x_4774_, 1);
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
lean_dec_ref_known(v___x_4778_, 1);
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
v___x_4863_ = lean_st_ref_put(v___y_4847_, v___x_4862_);
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
lean_dec_ref_known(v_e_4887_, 2);
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
uint8_t v___x_1992__boxed_4939_; lean_object* v_res_4940_; 
v___x_1992__boxed_4939_ = lean_unbox(v___x_4934_);
v_res_4940_ = l_Lean_Meta_unfoldDeclsFrom___lam__1(v_env_4932_, v___x_4933_, v___x_1992__boxed_4939_, v_e_4935_, v___y_4936_, v___y_4937_);
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
lean_dec_ref_known(v___x_4981_, 1);
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
lean_dec_ref_known(v___x_4981_, 1);
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
lean_dec_ref_known(v_x_5061_, 2);
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
lean_dec_ref_known(v_x_5086_, 2);
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
lean_dec_ref_known(v_x_5147_, 2);
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
lean_dec_ref_known(v___x_5168_, 1);
if (lean_obj_tag(v_val_5169_) == 2)
{
lean_object* v___x_5170_; lean_object* v___x_5171_; lean_object* v___x_5173_; uint8_t v_isShared_5174_; uint8_t v_isSharedCheck_5195_; 
v___x_5170_ = l_Lean_Expr_constLevels_x21(v_x_5147_);
lean_dec_ref(v_x_5147_);
v___x_5171_ = l_Lean_Core_instantiateValueLevelParams(v_val_5169_, v___x_5170_, v___x_5162_, v___y_5149_, v___y_5150_);
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
v___x_5263_ = lean_st_ref_put(v___y_5243_, v___x_5262_);
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
lean_object* v___x_5281_; lean_object* v_env_5282_; lean_object* v___x_5283_; uint8_t v_isModule_5284_; 
v___x_5281_ = lean_st_ref_get(v___y_5279_);
v_env_5282_ = lean_ctor_get(v___x_5281_, 0);
lean_inc_ref(v_env_5282_);
lean_dec(v___x_5281_);
v___x_5283_ = l_Lean_Environment_header(v_env_5282_);
v_isModule_5284_ = lean_ctor_get_uint8(v___x_5283_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_5283_);
if (v_isModule_5284_ == 0)
{
lean_object* v___x_5285_; 
lean_dec_ref(v_env_5282_);
lean_inc(v___y_5279_);
lean_inc_ref(v___y_5278_);
v___x_5285_ = lean_apply_3(v_x_5276_, v___y_5278_, v___y_5279_, lean_box(0));
return v___x_5285_;
}
else
{
uint8_t v_isExporting_5286_; 
v_isExporting_5286_ = lean_ctor_get_uint8(v_env_5282_, sizeof(void*)*8);
lean_dec_ref(v_env_5282_);
if (v_isExporting_5277_ == 0)
{
if (v_isExporting_5286_ == 0)
{
lean_object* v___x_5337_; 
lean_inc(v___y_5279_);
lean_inc_ref(v___y_5278_);
v___x_5337_ = lean_apply_3(v_x_5276_, v___y_5278_, v___y_5279_, lean_box(0));
return v___x_5337_;
}
else
{
goto v___jp_5287_;
}
}
else
{
if (v_isExporting_5286_ == 0)
{
goto v___jp_5287_;
}
else
{
lean_object* v___x_5338_; 
lean_inc(v___y_5279_);
lean_inc_ref(v___y_5278_);
v___x_5338_ = lean_apply_3(v_x_5276_, v___y_5278_, v___y_5279_, lean_box(0));
return v___x_5338_;
}
}
v___jp_5287_:
{
lean_object* v___x_5288_; lean_object* v_env_5289_; lean_object* v_nextMacroScope_5290_; lean_object* v_ngen_5291_; lean_object* v_auxDeclNGen_5292_; lean_object* v_traceState_5293_; lean_object* v_messages_5294_; lean_object* v_infoState_5295_; lean_object* v_snapshotTasks_5296_; lean_object* v___x_5298_; uint8_t v_isShared_5299_; uint8_t v_isSharedCheck_5335_; 
v___x_5288_ = lean_st_ref_take(v___y_5279_);
v_env_5289_ = lean_ctor_get(v___x_5288_, 0);
v_nextMacroScope_5290_ = lean_ctor_get(v___x_5288_, 1);
v_ngen_5291_ = lean_ctor_get(v___x_5288_, 2);
v_auxDeclNGen_5292_ = lean_ctor_get(v___x_5288_, 3);
v_traceState_5293_ = lean_ctor_get(v___x_5288_, 4);
v_messages_5294_ = lean_ctor_get(v___x_5288_, 6);
v_infoState_5295_ = lean_ctor_get(v___x_5288_, 7);
v_snapshotTasks_5296_ = lean_ctor_get(v___x_5288_, 8);
v_isSharedCheck_5335_ = !lean_is_exclusive(v___x_5288_);
if (v_isSharedCheck_5335_ == 0)
{
lean_object* v_unused_5336_; 
v_unused_5336_ = lean_ctor_get(v___x_5288_, 5);
lean_dec(v_unused_5336_);
v___x_5298_ = v___x_5288_;
v_isShared_5299_ = v_isSharedCheck_5335_;
goto v_resetjp_5297_;
}
else
{
lean_inc(v_snapshotTasks_5296_);
lean_inc(v_infoState_5295_);
lean_inc(v_messages_5294_);
lean_inc(v_traceState_5293_);
lean_inc(v_auxDeclNGen_5292_);
lean_inc(v_ngen_5291_);
lean_inc(v_nextMacroScope_5290_);
lean_inc(v_env_5289_);
lean_dec(v___x_5288_);
v___x_5298_ = lean_box(0);
v_isShared_5299_ = v_isSharedCheck_5335_;
goto v_resetjp_5297_;
}
v_resetjp_5297_:
{
lean_object* v___x_5300_; lean_object* v___x_5301_; lean_object* v___x_5303_; 
v___x_5300_ = l_Lean_Environment_setExporting(v_env_5289_, v_isExporting_5277_);
v___x_5301_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2, &l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2);
if (v_isShared_5299_ == 0)
{
lean_ctor_set(v___x_5298_, 5, v___x_5301_);
lean_ctor_set(v___x_5298_, 0, v___x_5300_);
v___x_5303_ = v___x_5298_;
goto v_reusejp_5302_;
}
else
{
lean_object* v_reuseFailAlloc_5334_; 
v_reuseFailAlloc_5334_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5334_, 0, v___x_5300_);
lean_ctor_set(v_reuseFailAlloc_5334_, 1, v_nextMacroScope_5290_);
lean_ctor_set(v_reuseFailAlloc_5334_, 2, v_ngen_5291_);
lean_ctor_set(v_reuseFailAlloc_5334_, 3, v_auxDeclNGen_5292_);
lean_ctor_set(v_reuseFailAlloc_5334_, 4, v_traceState_5293_);
lean_ctor_set(v_reuseFailAlloc_5334_, 5, v___x_5301_);
lean_ctor_set(v_reuseFailAlloc_5334_, 6, v_messages_5294_);
lean_ctor_set(v_reuseFailAlloc_5334_, 7, v_infoState_5295_);
lean_ctor_set(v_reuseFailAlloc_5334_, 8, v_snapshotTasks_5296_);
v___x_5303_ = v_reuseFailAlloc_5334_;
goto v_reusejp_5302_;
}
v_reusejp_5302_:
{
lean_object* v___x_5304_; lean_object* v_r_5305_; 
v___x_5304_ = lean_st_ref_put(v___y_5279_, v___x_5303_);
lean_inc(v___y_5279_);
lean_inc_ref(v___y_5278_);
v_r_5305_ = lean_apply_3(v_x_5276_, v___y_5278_, v___y_5279_, lean_box(0));
if (lean_obj_tag(v_r_5305_) == 0)
{
lean_object* v_a_5306_; lean_object* v___x_5308_; uint8_t v_isShared_5309_; uint8_t v_isSharedCheck_5322_; 
v_a_5306_ = lean_ctor_get(v_r_5305_, 0);
v_isSharedCheck_5322_ = !lean_is_exclusive(v_r_5305_);
if (v_isSharedCheck_5322_ == 0)
{
v___x_5308_ = v_r_5305_;
v_isShared_5309_ = v_isSharedCheck_5322_;
goto v_resetjp_5307_;
}
else
{
lean_inc(v_a_5306_);
lean_dec(v_r_5305_);
v___x_5308_ = lean_box(0);
v_isShared_5309_ = v_isSharedCheck_5322_;
goto v_resetjp_5307_;
}
v_resetjp_5307_:
{
lean_object* v___x_5311_; 
lean_inc(v_a_5306_);
if (v_isShared_5309_ == 0)
{
lean_ctor_set_tag(v___x_5308_, 1);
v___x_5311_ = v___x_5308_;
goto v_reusejp_5310_;
}
else
{
lean_object* v_reuseFailAlloc_5321_; 
v_reuseFailAlloc_5321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5321_, 0, v_a_5306_);
v___x_5311_ = v_reuseFailAlloc_5321_;
goto v_reusejp_5310_;
}
v_reusejp_5310_:
{
lean_object* v___x_5312_; lean_object* v___x_5314_; uint8_t v_isShared_5315_; uint8_t v_isSharedCheck_5319_; 
v___x_5312_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0(v___y_5279_, v_isExporting_5286_, v___x_5301_, v___x_5311_);
lean_dec_ref(v___x_5311_);
v_isSharedCheck_5319_ = !lean_is_exclusive(v___x_5312_);
if (v_isSharedCheck_5319_ == 0)
{
lean_object* v_unused_5320_; 
v_unused_5320_ = lean_ctor_get(v___x_5312_, 0);
lean_dec(v_unused_5320_);
v___x_5314_ = v___x_5312_;
v_isShared_5315_ = v_isSharedCheck_5319_;
goto v_resetjp_5313_;
}
else
{
lean_dec(v___x_5312_);
v___x_5314_ = lean_box(0);
v_isShared_5315_ = v_isSharedCheck_5319_;
goto v_resetjp_5313_;
}
v_resetjp_5313_:
{
lean_object* v___x_5317_; 
if (v_isShared_5315_ == 0)
{
lean_ctor_set(v___x_5314_, 0, v_a_5306_);
v___x_5317_ = v___x_5314_;
goto v_reusejp_5316_;
}
else
{
lean_object* v_reuseFailAlloc_5318_; 
v_reuseFailAlloc_5318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5318_, 0, v_a_5306_);
v___x_5317_ = v_reuseFailAlloc_5318_;
goto v_reusejp_5316_;
}
v_reusejp_5316_:
{
return v___x_5317_;
}
}
}
}
}
else
{
lean_object* v_a_5323_; lean_object* v___x_5324_; lean_object* v___x_5325_; lean_object* v___x_5327_; uint8_t v_isShared_5328_; uint8_t v_isSharedCheck_5332_; 
v_a_5323_ = lean_ctor_get(v_r_5305_, 0);
lean_inc(v_a_5323_);
lean_dec_ref_known(v_r_5305_, 1);
v___x_5324_ = lean_box(0);
v___x_5325_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0(v___y_5279_, v_isExporting_5286_, v___x_5301_, v___x_5324_);
v_isSharedCheck_5332_ = !lean_is_exclusive(v___x_5325_);
if (v_isSharedCheck_5332_ == 0)
{
lean_object* v_unused_5333_; 
v_unused_5333_ = lean_ctor_get(v___x_5325_, 0);
lean_dec(v_unused_5333_);
v___x_5327_ = v___x_5325_;
v_isShared_5328_ = v_isSharedCheck_5332_;
goto v_resetjp_5326_;
}
else
{
lean_dec(v___x_5325_);
v___x_5327_ = lean_box(0);
v_isShared_5328_ = v_isSharedCheck_5332_;
goto v_resetjp_5326_;
}
v_resetjp_5326_:
{
lean_object* v___x_5330_; 
if (v_isShared_5328_ == 0)
{
lean_ctor_set_tag(v___x_5327_, 1);
lean_ctor_set(v___x_5327_, 0, v_a_5323_);
v___x_5330_ = v___x_5327_;
goto v_reusejp_5329_;
}
else
{
lean_object* v_reuseFailAlloc_5331_; 
v_reuseFailAlloc_5331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5331_, 0, v_a_5323_);
v___x_5330_ = v_reuseFailAlloc_5331_;
goto v_reusejp_5329_;
}
v_reusejp_5329_:
{
return v___x_5330_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___boxed(lean_object* v_x_5339_, lean_object* v_isExporting_5340_, lean_object* v___y_5341_, lean_object* v___y_5342_, lean_object* v___y_5343_){
_start:
{
uint8_t v_isExporting_boxed_5344_; lean_object* v_res_5345_; 
v_isExporting_boxed_5344_ = lean_unbox(v_isExporting_5340_);
v_res_5345_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg(v_x_5339_, v_isExporting_boxed_5344_, v___y_5341_, v___y_5342_);
lean_dec(v___y_5342_);
lean_dec_ref(v___y_5341_);
return v_res_5345_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg(lean_object* v_x_5346_, uint8_t v_when_5347_, lean_object* v___y_5348_, lean_object* v___y_5349_){
_start:
{
if (v_when_5347_ == 0)
{
lean_object* v___x_5351_; 
lean_inc(v___y_5349_);
lean_inc_ref(v___y_5348_);
v___x_5351_ = lean_apply_3(v_x_5346_, v___y_5348_, v___y_5349_, lean_box(0));
return v___x_5351_;
}
else
{
uint8_t v___x_5352_; lean_object* v___x_5353_; 
v___x_5352_ = 0;
v___x_5353_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg(v_x_5346_, v___x_5352_, v___y_5348_, v___y_5349_);
return v___x_5353_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg___boxed(lean_object* v_x_5354_, lean_object* v_when_5355_, lean_object* v___y_5356_, lean_object* v___y_5357_, lean_object* v___y_5358_){
_start:
{
uint8_t v_when_boxed_5359_; lean_object* v_res_5360_; 
v_when_boxed_5359_ = lean_unbox(v_when_5355_);
v_res_5360_ = l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg(v_x_5354_, v_when_boxed_5359_, v___y_5356_, v___y_5357_);
lean_dec(v___y_5357_);
lean_dec_ref(v___y_5356_);
return v_res_5360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf(lean_object* v_fnNames_5361_, lean_object* v_numSectionVars_5362_, lean_object* v_e_5363_, lean_object* v_a_5364_, lean_object* v_a_5365_){
_start:
{
lean_object* v___f_5367_; lean_object* v___f_5368_; uint8_t v___x_5369_; lean_object* v___x_5370_; 
v___f_5367_ = ((lean_object*)(l_Lean_Core_betaReduce___closed__1));
v___f_5368_ = lean_alloc_closure((void*)(l_Lean_Meta_unfoldIfArgIsAppOf___lam__0___boxed), 7, 4);
lean_closure_set(v___f_5368_, 0, v_fnNames_5361_);
lean_closure_set(v___f_5368_, 1, v_numSectionVars_5362_);
lean_closure_set(v___f_5368_, 2, v_e_5363_);
lean_closure_set(v___f_5368_, 3, v___f_5367_);
v___x_5369_ = 1;
v___x_5370_ = l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg(v___f_5368_, v___x_5369_, v_a_5364_, v_a_5365_);
return v___x_5370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___boxed(lean_object* v_fnNames_5371_, lean_object* v_numSectionVars_5372_, lean_object* v_e_5373_, lean_object* v_a_5374_, lean_object* v_a_5375_, lean_object* v_a_5376_){
_start:
{
lean_object* v_res_5377_; 
v_res_5377_ = l_Lean_Meta_unfoldIfArgIsAppOf(v_fnNames_5371_, v_numSectionVars_5372_, v_e_5373_, v_a_5374_, v_a_5375_);
lean_dec(v_a_5375_);
lean_dec_ref(v_a_5374_);
return v_res_5377_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2(lean_object* v_00_u03b1_5378_, lean_object* v_x_5379_, uint8_t v_isExporting_5380_, lean_object* v___y_5381_, lean_object* v___y_5382_){
_start:
{
lean_object* v___x_5384_; 
v___x_5384_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg(v_x_5379_, v_isExporting_5380_, v___y_5381_, v___y_5382_);
return v___x_5384_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___boxed(lean_object* v_00_u03b1_5385_, lean_object* v_x_5386_, lean_object* v_isExporting_5387_, lean_object* v___y_5388_, lean_object* v___y_5389_, lean_object* v___y_5390_){
_start:
{
uint8_t v_isExporting_boxed_5391_; lean_object* v_res_5392_; 
v_isExporting_boxed_5391_ = lean_unbox(v_isExporting_5387_);
v_res_5392_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2(v_00_u03b1_5385_, v_x_5386_, v_isExporting_boxed_5391_, v___y_5388_, v___y_5389_);
lean_dec(v___y_5389_);
lean_dec_ref(v___y_5388_);
return v_res_5392_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2(lean_object* v_00_u03b1_5393_, lean_object* v_x_5394_, uint8_t v_when_5395_, lean_object* v___y_5396_, lean_object* v___y_5397_){
_start:
{
lean_object* v___x_5399_; 
v___x_5399_ = l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg(v_x_5394_, v_when_5395_, v___y_5396_, v___y_5397_);
return v___x_5399_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___boxed(lean_object* v_00_u03b1_5400_, lean_object* v_x_5401_, lean_object* v_when_5402_, lean_object* v___y_5403_, lean_object* v___y_5404_, lean_object* v___y_5405_){
_start:
{
uint8_t v_when_boxed_5406_; lean_object* v_res_5407_; 
v_when_boxed_5406_ = lean_unbox(v_when_5402_);
v_res_5407_ = l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2(v_00_u03b1_5400_, v_x_5401_, v_when_boxed_5406_, v___y_5403_, v___y_5404_);
lean_dec(v___y_5404_);
lean_dec_ref(v___y_5403_);
return v_res_5407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___lam__0(lean_object* v_x_5408_, lean_object* v___y_5409_, lean_object* v___y_5410_){
_start:
{
lean_object* v___x_5412_; lean_object* v___x_5413_; 
v___x_5412_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_5413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5413_, 0, v___x_5412_);
return v___x_5413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___lam__0___boxed(lean_object* v_x_5414_, lean_object* v___y_5415_, lean_object* v___y_5416_, lean_object* v___y_5417_){
_start:
{
lean_object* v_res_5418_; 
v_res_5418_ = l_Lean_Meta_eraseInaccessibleAnnotations___lam__0(v_x_5414_, v___y_5415_, v___y_5416_);
lean_dec(v___y_5416_);
lean_dec_ref(v___y_5415_);
lean_dec_ref(v_x_5414_);
return v_res_5418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___lam__1(lean_object* v_e_5419_, lean_object* v___y_5420_, lean_object* v___y_5421_){
_start:
{
lean_object* v___y_5424_; lean_object* v___x_5427_; 
v___x_5427_ = l_Lean_inaccessible_x3f(v_e_5419_);
if (lean_obj_tag(v___x_5427_) == 1)
{
lean_object* v_val_5428_; 
lean_dec_ref(v_e_5419_);
v_val_5428_ = lean_ctor_get(v___x_5427_, 0);
lean_inc(v_val_5428_);
lean_dec_ref_known(v___x_5427_, 1);
v___y_5424_ = v_val_5428_;
goto v___jp_5423_;
}
else
{
lean_dec(v___x_5427_);
v___y_5424_ = v_e_5419_;
goto v___jp_5423_;
}
v___jp_5423_:
{
lean_object* v___x_5425_; lean_object* v___x_5426_; 
v___x_5425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5425_, 0, v___y_5424_);
v___x_5426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5426_, 0, v___x_5425_);
return v___x_5426_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___lam__1___boxed(lean_object* v_e_5429_, lean_object* v___y_5430_, lean_object* v___y_5431_, lean_object* v___y_5432_){
_start:
{
lean_object* v_res_5433_; 
v_res_5433_ = l_Lean_Meta_eraseInaccessibleAnnotations___lam__1(v_e_5429_, v___y_5430_, v___y_5431_);
lean_dec(v___y_5431_);
lean_dec_ref(v___y_5430_);
return v_res_5433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations(lean_object* v_e_5436_, lean_object* v_a_5437_, lean_object* v_a_5438_){
_start:
{
lean_object* v___f_5440_; lean_object* v___f_5441_; lean_object* v___x_5442_; 
v___f_5440_ = ((lean_object*)(l_Lean_Meta_eraseInaccessibleAnnotations___closed__0));
v___f_5441_ = ((lean_object*)(l_Lean_Meta_eraseInaccessibleAnnotations___closed__1));
v___x_5442_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_5436_, v___f_5440_, v___f_5441_, v_a_5437_, v_a_5438_);
return v___x_5442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___boxed(lean_object* v_e_5443_, lean_object* v_a_5444_, lean_object* v_a_5445_, lean_object* v_a_5446_){
_start:
{
lean_object* v_res_5447_; 
v_res_5447_ = l_Lean_Meta_eraseInaccessibleAnnotations(v_e_5443_, v_a_5444_, v_a_5445_);
lean_dec(v_a_5445_);
lean_dec_ref(v_a_5444_);
return v_res_5447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_erasePatternRefAnnotations___lam__1(lean_object* v_e_5448_, lean_object* v___y_5449_, lean_object* v___y_5450_){
_start:
{
lean_object* v___y_5453_; lean_object* v___x_5456_; 
v___x_5456_ = l_Lean_patternWithRef_x3f(v_e_5448_);
if (lean_obj_tag(v___x_5456_) == 1)
{
lean_object* v_val_5457_; lean_object* v_snd_5458_; 
lean_dec_ref(v_e_5448_);
v_val_5457_ = lean_ctor_get(v___x_5456_, 0);
lean_inc(v_val_5457_);
lean_dec_ref_known(v___x_5456_, 1);
v_snd_5458_ = lean_ctor_get(v_val_5457_, 1);
lean_inc(v_snd_5458_);
lean_dec(v_val_5457_);
v___y_5453_ = v_snd_5458_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_erasePatternRefAnnotations___lam__1___boxed(lean_object* v_e_5459_, lean_object* v___y_5460_, lean_object* v___y_5461_, lean_object* v___y_5462_){
_start:
{
lean_object* v_res_5463_; 
v_res_5463_ = l_Lean_Meta_erasePatternRefAnnotations___lam__1(v_e_5459_, v___y_5460_, v___y_5461_);
lean_dec(v___y_5461_);
lean_dec_ref(v___y_5460_);
return v_res_5463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_erasePatternRefAnnotations(lean_object* v_e_5465_, lean_object* v_a_5466_, lean_object* v_a_5467_){
_start:
{
lean_object* v___f_5469_; lean_object* v___f_5470_; lean_object* v___x_5471_; 
v___f_5469_ = ((lean_object*)(l_Lean_Meta_eraseInaccessibleAnnotations___closed__0));
v___f_5470_ = ((lean_object*)(l_Lean_Meta_erasePatternRefAnnotations___closed__0));
v___x_5471_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_5465_, v___f_5469_, v___f_5470_, v_a_5466_, v_a_5467_);
return v___x_5471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_erasePatternRefAnnotations___boxed(lean_object* v_e_5472_, lean_object* v_a_5473_, lean_object* v_a_5474_, lean_object* v_a_5475_){
_start:
{
lean_object* v_res_5476_; 
v_res_5476_ = l_Lean_Meta_erasePatternRefAnnotations(v_e_5472_, v_a_5473_, v_a_5474_);
lean_dec(v_a_5474_);
lean_dec_ref(v_a_5473_);
return v_res_5476_;
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
