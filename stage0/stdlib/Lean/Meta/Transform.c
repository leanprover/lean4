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
lean_object* lean_array_uget(lean_object*, size_t);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_2533__overap_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
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
v___x_2533__overap_220_ = l_Lean_Core_withIncRecDepth___redArg(v___x_209_, v___x_210_, v___x_219_);
lean_inc(v_a_211_);
v___x_221_ = lean_apply_1(v___x_2533__overap_220_, v_a_211_);
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
lean_object* v___f_287_; lean_object* v___x_288_; size_t v_sz_289_; size_t v___x_290_; lean_object* v___x_2263__overap_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
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
v___x_2263__overap_291_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_284_, v___x_288_, v_sz_289_, v___x_290_, v_args_283_);
v___x_292_ = lean_apply_1(v___x_2263__overap_291_, v___y_282_);
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
uint8_t v_binderInfo_2857__boxed_389_; lean_object* v_res_390_; 
v_binderInfo_2857__boxed_389_ = lean_unbox(v_binderInfo_377_);
v_res_390_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__8(v_binderType_374_, v_a_375_, v_binderName_376_, v_binderInfo_2857__boxed_389_, v_inst_378_, v_inst_379_, v_inst_380_, v_pre_381_, v_post_382_, v_x_383_, v_x_384_, v___y_385_, v_body_386_, v___y_387_, v_a_388_);
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
uint8_t v_binderInfo_2718__boxed_425_; lean_object* v_res_426_; 
v_binderInfo_2718__boxed_425_ = lean_unbox(v_binderInfo_412_);
v_res_426_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__9(v_binderType_410_, v_binderName_411_, v_binderInfo_2718__boxed_425_, v_inst_413_, v_inst_414_, v_inst_415_, v_pre_416_, v_post_417_, v_x_418_, v_x_419_, v___y_420_, v_body_421_, v___y_422_, v_toBind_423_, v_a_424_);
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
uint8_t v_binderInfo_2832__boxed_471_; lean_object* v_res_472_; 
v_binderInfo_2832__boxed_471_ = lean_unbox(v_binderInfo_459_);
v_res_472_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__10(v_binderType_456_, v_a_457_, v_binderName_458_, v_binderInfo_2832__boxed_471_, v_inst_460_, v_inst_461_, v_inst_462_, v_pre_463_, v_post_464_, v_x_465_, v_x_466_, v___y_467_, v_body_468_, v___y_469_, v_a_470_);
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
uint8_t v_binderInfo_2664__boxed_507_; lean_object* v_res_508_; 
v_binderInfo_2664__boxed_507_ = lean_unbox(v_binderInfo_494_);
v_res_508_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__11(v_binderType_492_, v_binderName_493_, v_binderInfo_2664__boxed_507_, v_inst_495_, v_inst_496_, v_inst_497_, v_pre_498_, v_post_499_, v_x_500_, v_x_501_, v___y_502_, v_body_503_, v___y_504_, v_toBind_505_, v_a_506_);
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
uint8_t v_nondep_2882__boxed_559_; lean_object* v_res_560_; 
v_nondep_2882__boxed_559_ = lean_unbox(v_nondep_546_);
v_res_560_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__12(v_type_542_, v_a_543_, v_declName_544_, v_a_545_, v_nondep_2882__boxed_559_, v_inst_547_, v_inst_548_, v_inst_549_, v_pre_550_, v_post_551_, v_x_552_, v_x_553_, v___y_554_, v_value_555_, v_body_556_, v___y_557_, v_a_558_);
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
uint8_t v_nondep_2678__boxed_599_; lean_object* v_res_600_; 
v_nondep_2678__boxed_599_ = lean_unbox(v_nondep_585_);
v_res_600_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__13(v_type_582_, v_a_583_, v_declName_584_, v_nondep_2678__boxed_599_, v_inst_586_, v_inst_587_, v_inst_588_, v_pre_589_, v_post_590_, v_x_591_, v_x_592_, v___y_593_, v_value_594_, v_body_595_, v___y_596_, v_toBind_597_, v_a_598_);
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
uint8_t v_nondep_2693__boxed_637_; lean_object* v_res_638_; 
v_nondep_2693__boxed_637_ = lean_unbox(v_nondep_623_);
v_res_638_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__14(v_type_621_, v_declName_622_, v_nondep_2693__boxed_637_, v_inst_624_, v_inst_625_, v_inst_626_, v_pre_627_, v_post_628_, v_x_629_, v_x_630_, v___y_631_, v_value_632_, v_body_633_, v___y_634_, v_toBind_635_, v_a_636_);
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
lean_object* v_dummy_746_; lean_object* v_nargs_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_2493__overap_751_; lean_object* v___x_752_; 
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
v___x_2493__overap_751_ = l_Lean_Expr_withAppAux___redArg(v___f_716_, v___y_720_, v___x_748_, v___x_750_);
lean_inc(v___y_713_);
v___x_752_ = lean_apply_1(v___x_2493__overap_751_, v___y_713_);
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
lean_object* v___y_1099_; uint16_t v___y_1109_; lean_object* v___y_1110_; lean_object* v___y_1111_; lean_object* v___y_1112_; uint8_t v___y_1113_; uint8_t v___y_1114_; lean_object* v_toCold_1119_; lean_object* v_currRecDepth_1120_; lean_object* v_ref_1121_; uint16_t v_optionFlags_1122_; uint8_t v_suppressElabErrors_1123_; uint8_t v_isRecordingDeps_1124_; lean_object* v_maxRecDepth_1125_; lean_object* v_cancelTk_x3f_1126_; 
v_toCold_1119_ = lean_ctor_get(v___y_1095_, 0);
v_currRecDepth_1120_ = lean_ctor_get(v___y_1095_, 1);
v_ref_1121_ = lean_ctor_get(v___y_1095_, 2);
v_optionFlags_1122_ = lean_ctor_get_uint16(v___y_1095_, sizeof(void*)*3);
v_suppressElabErrors_1123_ = lean_ctor_get_uint8(v___y_1095_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1124_ = lean_ctor_get_uint8(v___y_1095_, sizeof(void*)*3 + 3);
v_maxRecDepth_1125_ = lean_ctor_get(v_toCold_1119_, 3);
v_cancelTk_x3f_1126_ = lean_ctor_get(v_toCold_1119_, 10);
if (lean_obj_tag(v_cancelTk_x3f_1126_) == 1)
{
lean_object* v_val_1132_; uint8_t v___x_1133_; 
v_val_1132_ = lean_ctor_get(v_cancelTk_x3f_1126_, 0);
v___x_1133_ = l_IO_CancelToken_isSet(v_val_1132_);
if (v___x_1133_ == 0)
{
goto v___jp_1127_;
}
else
{
lean_object* v___x_1134_; lean_object* v_a_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1142_; 
lean_dec_ref(v_x_1093_);
v___x_1134_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___redArg();
v_a_1135_ = lean_ctor_get(v___x_1134_, 0);
v_isSharedCheck_1142_ = !lean_is_exclusive(v___x_1134_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1137_ = v___x_1134_;
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_a_1135_);
lean_dec(v___x_1134_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1140_; 
if (v_isShared_1138_ == 0)
{
v___x_1140_ = v___x_1137_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v_a_1135_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
return v___x_1140_;
}
}
}
}
else
{
goto v___jp_1127_;
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
lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1115_ = lean_unsigned_to_nat(1u);
v___x_1116_ = lean_nat_add(v___y_1111_, v___x_1115_);
lean_inc_ref(v___y_1112_);
v___x_1117_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1117_, 0, v___y_1112_);
lean_ctor_set(v___x_1117_, 1, v___x_1116_);
lean_ctor_set(v___x_1117_, 2, v___y_1110_);
lean_ctor_set_uint16(v___x_1117_, sizeof(void*)*3, v___y_1109_);
lean_ctor_set_uint8(v___x_1117_, sizeof(void*)*3 + 2, v___y_1114_);
lean_ctor_set_uint8(v___x_1117_, sizeof(void*)*3 + 3, v___y_1113_);
lean_inc(v___y_1096_);
lean_inc(v___y_1094_);
v___x_1118_ = lean_apply_4(v_x_1093_, v___y_1094_, v___x_1117_, v___y_1096_, lean_box(0));
v___y_1099_ = v___x_1118_;
goto v___jp_1098_;
}
v___jp_1127_:
{
lean_object* v___x_1128_; uint8_t v___x_1129_; 
v___x_1128_ = lean_unsigned_to_nat(0u);
v___x_1129_ = lean_nat_dec_eq(v_maxRecDepth_1125_, v___x_1128_);
if (v___x_1129_ == 0)
{
uint8_t v___x_1130_; 
v___x_1130_ = lean_nat_dec_eq(v_currRecDepth_1120_, v_maxRecDepth_1125_);
if (v___x_1130_ == 0)
{
lean_inc(v_ref_1121_);
v___y_1109_ = v_optionFlags_1122_;
v___y_1110_ = v_ref_1121_;
v___y_1111_ = v_currRecDepth_1120_;
v___y_1112_ = v_toCold_1119_;
v___y_1113_ = v_isRecordingDeps_1124_;
v___y_1114_ = v_suppressElabErrors_1123_;
goto v___jp_1108_;
}
else
{
lean_object* v___x_1131_; 
lean_dec_ref(v_x_1093_);
lean_inc(v_ref_1121_);
v___x_1131_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_1121_);
v___y_1099_ = v___x_1131_;
goto v___jp_1098_;
}
}
else
{
lean_inc(v_ref_1121_);
v___y_1109_ = v_optionFlags_1122_;
v___y_1110_ = v_ref_1121_;
v___y_1111_ = v_currRecDepth_1120_;
v___y_1112_ = v_toCold_1119_;
v___y_1113_ = v_isRecordingDeps_1124_;
v___y_1114_ = v_suppressElabErrors_1123_;
goto v___jp_1108_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___redArg___boxed(lean_object* v_x_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_){
_start:
{
lean_object* v_res_1148_; 
v_res_1148_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___redArg(v_x_1143_, v___y_1144_, v___y_1145_, v___y_1146_);
lean_dec(v___y_1146_);
lean_dec_ref(v___y_1145_);
lean_dec(v___y_1144_);
return v_res_1148_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_1149_, lean_object* v_x_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_){
_start:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; 
v___x_1154_ = lean_apply_1(v_x_1150_, lean_box(0));
v___x_1155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1154_);
return v___x_1155_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_1156_, lean_object* v_x_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_){
_start:
{
lean_object* v_res_1161_; 
v_res_1161_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__0(v_00_u03b1_1156_, v_x_1157_, v___y_1158_, v___y_1159_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
return v_res_1161_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___redArg(lean_object* v_a_1162_, lean_object* v_x_1163_){
_start:
{
if (lean_obj_tag(v_x_1163_) == 0)
{
uint8_t v___x_1164_; 
v___x_1164_ = 0;
return v___x_1164_;
}
else
{
lean_object* v_key_1165_; lean_object* v_tail_1166_; uint8_t v___x_1167_; 
v_key_1165_ = lean_ctor_get(v_x_1163_, 0);
v_tail_1166_ = lean_ctor_get(v_x_1163_, 2);
v___x_1167_ = l_Lean_ExprStructEq_beq(v_key_1165_, v_a_1162_);
if (v___x_1167_ == 0)
{
v_x_1163_ = v_tail_1166_;
goto _start;
}
else
{
return v___x_1167_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___redArg___boxed(lean_object* v_a_1169_, lean_object* v_x_1170_){
_start:
{
uint8_t v_res_1171_; lean_object* v_r_1172_; 
v_res_1171_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___redArg(v_a_1169_, v_x_1170_);
lean_dec(v_x_1170_);
lean_dec_ref(v_a_1169_);
v_r_1172_ = lean_box(v_res_1171_);
return v_r_1172_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(lean_object* v_x_1173_, lean_object* v_x_1174_){
_start:
{
if (lean_obj_tag(v_x_1174_) == 0)
{
return v_x_1173_;
}
else
{
lean_object* v_key_1175_; lean_object* v_value_1176_; lean_object* v_tail_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1200_; 
v_key_1175_ = lean_ctor_get(v_x_1174_, 0);
v_value_1176_ = lean_ctor_get(v_x_1174_, 1);
v_tail_1177_ = lean_ctor_get(v_x_1174_, 2);
v_isSharedCheck_1200_ = !lean_is_exclusive(v_x_1174_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1179_ = v_x_1174_;
v_isShared_1180_ = v_isSharedCheck_1200_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_tail_1177_);
lean_inc(v_value_1176_);
lean_inc(v_key_1175_);
lean_dec(v_x_1174_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1200_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v___x_1181_; uint64_t v___x_1182_; uint64_t v___x_1183_; uint64_t v___x_1184_; uint64_t v_fold_1185_; uint64_t v___x_1186_; uint64_t v___x_1187_; uint64_t v___x_1188_; size_t v___x_1189_; size_t v___x_1190_; size_t v___x_1191_; size_t v___x_1192_; size_t v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1196_; 
v___x_1181_ = lean_array_get_size(v_x_1173_);
v___x_1182_ = l_Lean_ExprStructEq_hash(v_key_1175_);
v___x_1183_ = 32ULL;
v___x_1184_ = lean_uint64_shift_right(v___x_1182_, v___x_1183_);
v_fold_1185_ = lean_uint64_xor(v___x_1182_, v___x_1184_);
v___x_1186_ = 16ULL;
v___x_1187_ = lean_uint64_shift_right(v_fold_1185_, v___x_1186_);
v___x_1188_ = lean_uint64_xor(v_fold_1185_, v___x_1187_);
v___x_1189_ = lean_uint64_to_usize(v___x_1188_);
v___x_1190_ = lean_usize_of_nat(v___x_1181_);
v___x_1191_ = ((size_t)1ULL);
v___x_1192_ = lean_usize_sub(v___x_1190_, v___x_1191_);
v___x_1193_ = lean_usize_land(v___x_1189_, v___x_1192_);
v___x_1194_ = lean_array_uget_borrowed(v_x_1173_, v___x_1193_);
lean_inc(v___x_1194_);
if (v_isShared_1180_ == 0)
{
lean_ctor_set(v___x_1179_, 2, v___x_1194_);
v___x_1196_ = v___x_1179_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v_key_1175_);
lean_ctor_set(v_reuseFailAlloc_1199_, 1, v_value_1176_);
lean_ctor_set(v_reuseFailAlloc_1199_, 2, v___x_1194_);
v___x_1196_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
lean_object* v___x_1197_; 
v___x_1197_ = lean_array_uset(v_x_1173_, v___x_1193_, v___x_1196_);
v_x_1173_ = v___x_1197_;
v_x_1174_ = v_tail_1177_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(lean_object* v_i_1201_, lean_object* v_source_1202_, lean_object* v_target_1203_){
_start:
{
lean_object* v___x_1204_; uint8_t v___x_1205_; 
v___x_1204_ = lean_array_get_size(v_source_1202_);
v___x_1205_ = lean_nat_dec_lt(v_i_1201_, v___x_1204_);
if (v___x_1205_ == 0)
{
lean_dec_ref(v_source_1202_);
lean_dec(v_i_1201_);
return v_target_1203_;
}
else
{
lean_object* v_es_1206_; lean_object* v___x_1207_; lean_object* v_source_1208_; lean_object* v_target_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; 
v_es_1206_ = lean_array_fget(v_source_1202_, v_i_1201_);
v___x_1207_ = lean_box(0);
v_source_1208_ = lean_array_fset(v_source_1202_, v_i_1201_, v___x_1207_);
v_target_1209_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_target_1203_, v_es_1206_);
v___x_1210_ = lean_unsigned_to_nat(1u);
v___x_1211_ = lean_nat_add(v_i_1201_, v___x_1210_);
lean_dec(v_i_1201_);
v_i_1201_ = v___x_1211_;
v_source_1202_ = v_source_1208_;
v_target_1203_ = v_target_1209_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11___redArg(lean_object* v_data_1213_){
_start:
{
lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v_nbuckets_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
v___x_1214_ = lean_array_get_size(v_data_1213_);
v___x_1215_ = lean_unsigned_to_nat(2u);
v_nbuckets_1216_ = lean_nat_mul(v___x_1214_, v___x_1215_);
v___x_1217_ = lean_unsigned_to_nat(0u);
v___x_1218_ = lean_box(0);
v___x_1219_ = lean_mk_array(v_nbuckets_1216_, v___x_1218_);
v___x_1220_ = lean_array_propagate_mark(v_data_1213_, v___x_1219_);
v___x_1221_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v___x_1217_, v_data_1213_, v___x_1220_);
return v___x_1221_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__12___redArg(lean_object* v_a_1222_, lean_object* v_b_1223_, lean_object* v_x_1224_){
_start:
{
if (lean_obj_tag(v_x_1224_) == 0)
{
lean_dec(v_b_1223_);
lean_dec_ref(v_a_1222_);
return v_x_1224_;
}
else
{
lean_object* v_key_1225_; lean_object* v_value_1226_; lean_object* v_tail_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1239_; 
v_key_1225_ = lean_ctor_get(v_x_1224_, 0);
v_value_1226_ = lean_ctor_get(v_x_1224_, 1);
v_tail_1227_ = lean_ctor_get(v_x_1224_, 2);
v_isSharedCheck_1239_ = !lean_is_exclusive(v_x_1224_);
if (v_isSharedCheck_1239_ == 0)
{
v___x_1229_ = v_x_1224_;
v_isShared_1230_ = v_isSharedCheck_1239_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_tail_1227_);
lean_inc(v_value_1226_);
lean_inc(v_key_1225_);
lean_dec(v_x_1224_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1239_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
uint8_t v___x_1231_; 
v___x_1231_ = l_Lean_ExprStructEq_beq(v_key_1225_, v_a_1222_);
if (v___x_1231_ == 0)
{
lean_object* v___x_1232_; lean_object* v___x_1234_; 
v___x_1232_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__12___redArg(v_a_1222_, v_b_1223_, v_tail_1227_);
if (v_isShared_1230_ == 0)
{
lean_ctor_set(v___x_1229_, 2, v___x_1232_);
v___x_1234_ = v___x_1229_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v_key_1225_);
lean_ctor_set(v_reuseFailAlloc_1235_, 1, v_value_1226_);
lean_ctor_set(v_reuseFailAlloc_1235_, 2, v___x_1232_);
v___x_1234_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
return v___x_1234_;
}
}
else
{
lean_object* v___x_1237_; 
lean_dec(v_value_1226_);
lean_dec(v_key_1225_);
if (v_isShared_1230_ == 0)
{
lean_ctor_set(v___x_1229_, 1, v_b_1223_);
lean_ctor_set(v___x_1229_, 0, v_a_1222_);
v___x_1237_ = v___x_1229_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v_a_1222_);
lean_ctor_set(v_reuseFailAlloc_1238_, 1, v_b_1223_);
lean_ctor_set(v_reuseFailAlloc_1238_, 2, v_tail_1227_);
v___x_1237_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
return v___x_1237_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6___redArg(lean_object* v_m_1240_, lean_object* v_a_1241_, lean_object* v_b_1242_){
_start:
{
lean_object* v_size_1243_; lean_object* v_buckets_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1287_; 
v_size_1243_ = lean_ctor_get(v_m_1240_, 0);
v_buckets_1244_ = lean_ctor_get(v_m_1240_, 1);
v_isSharedCheck_1287_ = !lean_is_exclusive(v_m_1240_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1246_ = v_m_1240_;
v_isShared_1247_ = v_isSharedCheck_1287_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_buckets_1244_);
lean_inc(v_size_1243_);
lean_dec(v_m_1240_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1287_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v___x_1248_; uint64_t v___x_1249_; uint64_t v___x_1250_; uint64_t v___x_1251_; uint64_t v_fold_1252_; uint64_t v___x_1253_; uint64_t v___x_1254_; uint64_t v___x_1255_; size_t v___x_1256_; size_t v___x_1257_; size_t v___x_1258_; size_t v___x_1259_; size_t v___x_1260_; lean_object* v_bkt_1261_; uint8_t v___x_1262_; 
v___x_1248_ = lean_array_get_size(v_buckets_1244_);
v___x_1249_ = l_Lean_ExprStructEq_hash(v_a_1241_);
v___x_1250_ = 32ULL;
v___x_1251_ = lean_uint64_shift_right(v___x_1249_, v___x_1250_);
v_fold_1252_ = lean_uint64_xor(v___x_1249_, v___x_1251_);
v___x_1253_ = 16ULL;
v___x_1254_ = lean_uint64_shift_right(v_fold_1252_, v___x_1253_);
v___x_1255_ = lean_uint64_xor(v_fold_1252_, v___x_1254_);
v___x_1256_ = lean_uint64_to_usize(v___x_1255_);
v___x_1257_ = lean_usize_of_nat(v___x_1248_);
v___x_1258_ = ((size_t)1ULL);
v___x_1259_ = lean_usize_sub(v___x_1257_, v___x_1258_);
v___x_1260_ = lean_usize_land(v___x_1256_, v___x_1259_);
v_bkt_1261_ = lean_array_uget_borrowed(v_buckets_1244_, v___x_1260_);
v___x_1262_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___redArg(v_a_1241_, v_bkt_1261_);
if (v___x_1262_ == 0)
{
lean_object* v___x_1263_; lean_object* v_size_x27_1264_; lean_object* v___x_1265_; lean_object* v_buckets_x27_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; uint8_t v___x_1272_; 
v___x_1263_ = lean_unsigned_to_nat(1u);
v_size_x27_1264_ = lean_nat_add(v_size_1243_, v___x_1263_);
lean_dec(v_size_1243_);
lean_inc(v_bkt_1261_);
v___x_1265_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1265_, 0, v_a_1241_);
lean_ctor_set(v___x_1265_, 1, v_b_1242_);
lean_ctor_set(v___x_1265_, 2, v_bkt_1261_);
v_buckets_x27_1266_ = lean_array_uset(v_buckets_1244_, v___x_1260_, v___x_1265_);
v___x_1267_ = lean_unsigned_to_nat(4u);
v___x_1268_ = lean_nat_mul(v_size_x27_1264_, v___x_1267_);
v___x_1269_ = lean_unsigned_to_nat(3u);
v___x_1270_ = lean_nat_div(v___x_1268_, v___x_1269_);
lean_dec(v___x_1268_);
v___x_1271_ = lean_array_get_size(v_buckets_x27_1266_);
v___x_1272_ = lean_nat_dec_le(v___x_1270_, v___x_1271_);
lean_dec(v___x_1270_);
if (v___x_1272_ == 0)
{
lean_object* v_val_1273_; lean_object* v___x_1275_; 
v_val_1273_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11___redArg(v_buckets_x27_1266_);
if (v_isShared_1247_ == 0)
{
lean_ctor_set(v___x_1246_, 1, v_val_1273_);
lean_ctor_set(v___x_1246_, 0, v_size_x27_1264_);
v___x_1275_ = v___x_1246_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v_size_x27_1264_);
lean_ctor_set(v_reuseFailAlloc_1276_, 1, v_val_1273_);
v___x_1275_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
return v___x_1275_;
}
}
else
{
lean_object* v___x_1278_; 
if (v_isShared_1247_ == 0)
{
lean_ctor_set(v___x_1246_, 1, v_buckets_x27_1266_);
lean_ctor_set(v___x_1246_, 0, v_size_x27_1264_);
v___x_1278_ = v___x_1246_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v_size_x27_1264_);
lean_ctor_set(v_reuseFailAlloc_1279_, 1, v_buckets_x27_1266_);
v___x_1278_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
return v___x_1278_;
}
}
}
else
{
lean_object* v___x_1280_; lean_object* v_buckets_x27_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1285_; 
lean_inc(v_bkt_1261_);
v___x_1280_ = lean_box(0);
v_buckets_x27_1281_ = lean_array_uset(v_buckets_1244_, v___x_1260_, v___x_1280_);
v___x_1282_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__12___redArg(v_a_1241_, v_b_1242_, v_bkt_1261_);
v___x_1283_ = lean_array_uset(v_buckets_x27_1281_, v___x_1260_, v___x_1282_);
if (v_isShared_1247_ == 0)
{
lean_ctor_set(v___x_1246_, 1, v___x_1283_);
v___x_1285_ = v___x_1246_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v_size_1243_);
lean_ctor_set(v_reuseFailAlloc_1286_, 1, v___x_1283_);
v___x_1285_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
return v___x_1285_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__2(lean_object* v_a_1288_, lean_object* v_e_1289_, lean_object* v_a_1290_){
_start:
{
lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1292_ = lean_st_ref_take(v_a_1288_);
v___x_1293_ = lean_box(0);
v___x_1294_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6___redArg(v___x_1292_, v_e_1289_, v_a_1290_);
v___x_1295_ = lean_st_ref_put(v_a_1288_, v___x_1294_);
return v___x_1293_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__2___boxed(lean_object* v_a_1296_, lean_object* v_e_1297_, lean_object* v_a_1298_, lean_object* v___y_1299_){
_start:
{
lean_object* v_res_1300_; 
v_res_1300_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__2(v_a_1296_, v_e_1297_, v_a_1298_);
lean_dec(v_a_1296_);
return v_res_1300_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___redArg(lean_object* v_a_1301_, lean_object* v_x_1302_){
_start:
{
if (lean_obj_tag(v_x_1302_) == 0)
{
lean_object* v___x_1303_; 
v___x_1303_ = lean_box(0);
return v___x_1303_;
}
else
{
lean_object* v_key_1304_; lean_object* v_value_1305_; lean_object* v_tail_1306_; uint8_t v___x_1307_; 
v_key_1304_ = lean_ctor_get(v_x_1302_, 0);
v_value_1305_ = lean_ctor_get(v_x_1302_, 1);
v_tail_1306_ = lean_ctor_get(v_x_1302_, 2);
v___x_1307_ = l_Lean_ExprStructEq_beq(v_key_1304_, v_a_1301_);
if (v___x_1307_ == 0)
{
v_x_1302_ = v_tail_1306_;
goto _start;
}
else
{
lean_object* v___x_1309_; 
lean_inc(v_value_1305_);
v___x_1309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1309_, 0, v_value_1305_);
return v___x_1309_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___redArg___boxed(lean_object* v_a_1310_, lean_object* v_x_1311_){
_start:
{
lean_object* v_res_1312_; 
v_res_1312_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___redArg(v_a_1310_, v_x_1311_);
lean_dec(v_x_1311_);
lean_dec_ref(v_a_1310_);
return v_res_1312_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg(lean_object* v_m_1313_, lean_object* v_a_1314_){
_start:
{
lean_object* v_buckets_1315_; lean_object* v___x_1316_; uint64_t v___x_1317_; uint64_t v___x_1318_; uint64_t v___x_1319_; uint64_t v_fold_1320_; uint64_t v___x_1321_; uint64_t v___x_1322_; uint64_t v___x_1323_; size_t v___x_1324_; size_t v___x_1325_; size_t v___x_1326_; size_t v___x_1327_; size_t v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; 
v_buckets_1315_ = lean_ctor_get(v_m_1313_, 1);
v___x_1316_ = lean_array_get_size(v_buckets_1315_);
v___x_1317_ = l_Lean_ExprStructEq_hash(v_a_1314_);
v___x_1318_ = 32ULL;
v___x_1319_ = lean_uint64_shift_right(v___x_1317_, v___x_1318_);
v_fold_1320_ = lean_uint64_xor(v___x_1317_, v___x_1319_);
v___x_1321_ = 16ULL;
v___x_1322_ = lean_uint64_shift_right(v_fold_1320_, v___x_1321_);
v___x_1323_ = lean_uint64_xor(v_fold_1320_, v___x_1322_);
v___x_1324_ = lean_uint64_to_usize(v___x_1323_);
v___x_1325_ = lean_usize_of_nat(v___x_1316_);
v___x_1326_ = ((size_t)1ULL);
v___x_1327_ = lean_usize_sub(v___x_1325_, v___x_1326_);
v___x_1328_ = lean_usize_land(v___x_1324_, v___x_1327_);
v___x_1329_ = lean_array_uget_borrowed(v_buckets_1315_, v___x_1328_);
v___x_1330_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___redArg(v_a_1314_, v___x_1329_);
return v___x_1330_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_m_1331_, lean_object* v_a_1332_){
_start:
{
lean_object* v_res_1333_; 
v_res_1333_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg(v_m_1331_, v_a_1332_);
lean_dec_ref(v_a_1332_);
lean_dec_ref(v_m_1331_);
return v_res_1333_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1(lean_object* v_pre_1334_, lean_object* v_post_1335_, size_t v_sz_1336_, size_t v_i_1337_, lean_object* v_bs_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_){
_start:
{
uint8_t v___x_1343_; 
v___x_1343_ = lean_usize_dec_lt(v_i_1337_, v_sz_1336_);
if (v___x_1343_ == 0)
{
lean_object* v___x_1344_; 
lean_dec_ref(v_post_1335_);
lean_dec_ref(v_pre_1334_);
v___x_1344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1344_, 0, v_bs_1338_);
return v___x_1344_;
}
else
{
lean_object* v_v_1345_; lean_object* v___x_1346_; lean_object* v_bs_x27_1347_; lean_object* v___x_1348_; 
v_v_1345_ = lean_array_uget(v_bs_1338_, v_i_1337_);
v___x_1346_ = lean_unsigned_to_nat(0u);
v_bs_x27_1347_ = lean_array_uset(v_bs_1338_, v_i_1337_, v___x_1346_);
lean_inc_ref(v_post_1335_);
lean_inc_ref(v_pre_1334_);
v___x_1348_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1334_, v_post_1335_, v_v_1345_, v___y_1339_, v___y_1340_, v___y_1341_);
if (lean_obj_tag(v___x_1348_) == 0)
{
lean_object* v_a_1349_; size_t v___x_1350_; size_t v___x_1351_; lean_object* v___x_1352_; 
v_a_1349_ = lean_ctor_get(v___x_1348_, 0);
lean_inc(v_a_1349_);
lean_dec_ref_known(v___x_1348_, 1);
v___x_1350_ = ((size_t)1ULL);
v___x_1351_ = lean_usize_add(v_i_1337_, v___x_1350_);
v___x_1352_ = lean_array_uset(v_bs_x27_1347_, v_i_1337_, v_a_1349_);
v_i_1337_ = v___x_1351_;
v_bs_1338_ = v___x_1352_;
goto _start;
}
else
{
lean_object* v_a_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1361_; 
lean_dec_ref(v_bs_x27_1347_);
lean_dec_ref(v_post_1335_);
lean_dec_ref(v_pre_1334_);
v_a_1354_ = lean_ctor_get(v___x_1348_, 0);
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1348_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1356_ = v___x_1348_;
v_isShared_1357_ = v_isSharedCheck_1361_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_a_1354_);
lean_dec(v___x_1348_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1361_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
lean_object* v___x_1359_; 
if (v_isShared_1357_ == 0)
{
v___x_1359_ = v___x_1356_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v_a_1354_);
v___x_1359_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
return v___x_1359_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__4(lean_object* v_pre_1362_, lean_object* v_post_1363_, lean_object* v_x_1364_, lean_object* v_x_1365_, lean_object* v_x_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_){
_start:
{
if (lean_obj_tag(v_x_1364_) == 5)
{
lean_object* v_fn_1371_; lean_object* v_arg_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; 
v_fn_1371_ = lean_ctor_get(v_x_1364_, 0);
lean_inc_ref(v_fn_1371_);
v_arg_1372_ = lean_ctor_get(v_x_1364_, 1);
lean_inc_ref(v_arg_1372_);
lean_dec_ref_known(v_x_1364_, 2);
v___x_1373_ = lean_array_set(v_x_1365_, v_x_1366_, v_arg_1372_);
v___x_1374_ = lean_unsigned_to_nat(1u);
v___x_1375_ = lean_nat_sub(v_x_1366_, v___x_1374_);
lean_dec(v_x_1366_);
v_x_1364_ = v_fn_1371_;
v_x_1365_ = v___x_1373_;
v_x_1366_ = v___x_1375_;
goto _start;
}
else
{
lean_object* v___x_1377_; 
lean_dec(v_x_1366_);
lean_inc_ref(v_post_1363_);
lean_inc_ref(v_pre_1362_);
v___x_1377_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1362_, v_post_1363_, v_x_1364_, v___y_1367_, v___y_1368_, v___y_1369_);
if (lean_obj_tag(v___x_1377_) == 0)
{
lean_object* v_a_1378_; size_t v_sz_1379_; size_t v___x_1380_; lean_object* v___x_1381_; 
v_a_1378_ = lean_ctor_get(v___x_1377_, 0);
lean_inc(v_a_1378_);
lean_dec_ref_known(v___x_1377_, 1);
v_sz_1379_ = lean_array_size(v_x_1365_);
v___x_1380_ = ((size_t)0ULL);
lean_inc_ref(v_post_1363_);
lean_inc_ref(v_pre_1362_);
v___x_1381_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1(v_pre_1362_, v_post_1363_, v_sz_1379_, v___x_1380_, v_x_1365_, v___y_1367_, v___y_1368_, v___y_1369_);
if (lean_obj_tag(v___x_1381_) == 0)
{
lean_object* v_a_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; 
v_a_1382_ = lean_ctor_get(v___x_1381_, 0);
lean_inc(v_a_1382_);
lean_dec_ref_known(v___x_1381_, 1);
v___x_1383_ = l_Lean_mkAppN(v_a_1378_, v_a_1382_);
lean_dec(v_a_1382_);
v___x_1384_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1362_, v_post_1363_, v___x_1383_, v___y_1367_, v___y_1368_, v___y_1369_);
return v___x_1384_;
}
else
{
lean_object* v_a_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1392_; 
lean_dec(v_a_1378_);
lean_dec_ref(v_post_1363_);
lean_dec_ref(v_pre_1362_);
v_a_1385_ = lean_ctor_get(v___x_1381_, 0);
v_isSharedCheck_1392_ = !lean_is_exclusive(v___x_1381_);
if (v_isSharedCheck_1392_ == 0)
{
v___x_1387_ = v___x_1381_;
v_isShared_1388_ = v_isSharedCheck_1392_;
goto v_resetjp_1386_;
}
else
{
lean_inc(v_a_1385_);
lean_dec(v___x_1381_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1392_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v___x_1390_; 
if (v_isShared_1388_ == 0)
{
v___x_1390_ = v___x_1387_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v_a_1385_);
v___x_1390_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
return v___x_1390_;
}
}
}
}
else
{
lean_dec_ref(v_x_1365_);
lean_dec_ref(v_post_1363_);
lean_dec_ref(v_pre_1362_);
return v___x_1377_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__1(lean_object* v___x_1393_, lean_object* v_pre_1394_, lean_object* v_e_1395_, lean_object* v_post_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_){
_start:
{
lean_object* v___x_1401_; 
v___x_1401_ = l_Lean_Core_checkSystem(v___x_1393_, v___y_1398_, v___y_1399_);
if (lean_obj_tag(v___x_1401_) == 0)
{
lean_object* v___x_1402_; 
lean_dec_ref_known(v___x_1401_, 1);
lean_inc_ref(v_pre_1394_);
lean_inc(v___y_1399_);
lean_inc_ref(v___y_1398_);
lean_inc_ref(v_e_1395_);
v___x_1402_ = lean_apply_4(v_pre_1394_, v_e_1395_, v___y_1398_, v___y_1399_, lean_box(0));
if (lean_obj_tag(v___x_1402_) == 0)
{
lean_object* v_a_1403_; lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1518_; 
v_a_1403_ = lean_ctor_get(v___x_1402_, 0);
v_isSharedCheck_1518_ = !lean_is_exclusive(v___x_1402_);
if (v_isSharedCheck_1518_ == 0)
{
v___x_1405_ = v___x_1402_;
v_isShared_1406_ = v_isSharedCheck_1518_;
goto v_resetjp_1404_;
}
else
{
lean_inc(v_a_1403_);
lean_dec(v___x_1402_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1518_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
lean_object* v___y_1408_; 
switch(lean_obj_tag(v_a_1403_))
{
case 0:
{
lean_object* v_e_1508_; lean_object* v___x_1510_; 
lean_dec_ref(v_post_1396_);
lean_dec_ref(v_e_1395_);
lean_dec_ref(v_pre_1394_);
v_e_1508_ = lean_ctor_get(v_a_1403_, 0);
lean_inc_ref(v_e_1508_);
lean_dec_ref_known(v_a_1403_, 1);
if (v_isShared_1406_ == 0)
{
lean_ctor_set(v___x_1405_, 0, v_e_1508_);
v___x_1510_ = v___x_1405_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v_e_1508_);
v___x_1510_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
return v___x_1510_;
}
}
case 1:
{
lean_object* v_e_1512_; lean_object* v___x_1513_; 
lean_del_object(v___x_1405_);
lean_dec_ref(v_e_1395_);
v_e_1512_ = lean_ctor_get(v_a_1403_, 0);
lean_inc_ref(v_e_1512_);
lean_dec_ref_known(v_a_1403_, 1);
lean_inc_ref(v_post_1396_);
lean_inc_ref(v_pre_1394_);
v___x_1513_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1394_, v_post_1396_, v_e_1512_, v___y_1397_, v___y_1398_, v___y_1399_);
if (lean_obj_tag(v___x_1513_) == 0)
{
lean_object* v_a_1514_; lean_object* v___x_1515_; 
v_a_1514_ = lean_ctor_get(v___x_1513_, 0);
lean_inc(v_a_1514_);
lean_dec_ref_known(v___x_1513_, 1);
v___x_1515_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1394_, v_post_1396_, v_a_1514_, v___y_1397_, v___y_1398_, v___y_1399_);
return v___x_1515_;
}
else
{
lean_dec_ref(v_post_1396_);
lean_dec_ref(v_pre_1394_);
return v___x_1513_;
}
}
default: 
{
lean_object* v_e_x3f_1516_; 
lean_del_object(v___x_1405_);
v_e_x3f_1516_ = lean_ctor_get(v_a_1403_, 0);
lean_inc(v_e_x3f_1516_);
lean_dec_ref_known(v_a_1403_, 1);
if (lean_obj_tag(v_e_x3f_1516_) == 0)
{
v___y_1408_ = v_e_1395_;
goto v___jp_1407_;
}
else
{
lean_object* v_val_1517_; 
lean_dec_ref(v_e_1395_);
v_val_1517_ = lean_ctor_get(v_e_x3f_1516_, 0);
lean_inc(v_val_1517_);
lean_dec_ref_known(v_e_x3f_1516_, 1);
v___y_1408_ = v_val_1517_;
goto v___jp_1407_;
}
}
}
v___jp_1407_:
{
switch(lean_obj_tag(v___y_1408_))
{
case 7:
{
lean_object* v_binderName_1409_; lean_object* v_binderType_1410_; lean_object* v_body_1411_; uint8_t v_binderInfo_1412_; lean_object* v___x_1413_; 
v_binderName_1409_ = lean_ctor_get(v___y_1408_, 0);
v_binderType_1410_ = lean_ctor_get(v___y_1408_, 1);
v_body_1411_ = lean_ctor_get(v___y_1408_, 2);
v_binderInfo_1412_ = lean_ctor_get_uint8(v___y_1408_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1410_);
lean_inc_ref(v_post_1396_);
lean_inc_ref(v_pre_1394_);
v___x_1413_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1394_, v_post_1396_, v_binderType_1410_, v___y_1397_, v___y_1398_, v___y_1399_);
if (lean_obj_tag(v___x_1413_) == 0)
{
lean_object* v_a_1414_; lean_object* v___x_1415_; 
v_a_1414_ = lean_ctor_get(v___x_1413_, 0);
lean_inc(v_a_1414_);
lean_dec_ref_known(v___x_1413_, 1);
lean_inc_ref(v_body_1411_);
lean_inc_ref(v_post_1396_);
lean_inc_ref(v_pre_1394_);
v___x_1415_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1394_, v_post_1396_, v_body_1411_, v___y_1397_, v___y_1398_, v___y_1399_);
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_object* v_a_1416_; size_t v___x_1417_; size_t v___x_1418_; uint8_t v___x_1419_; 
v_a_1416_ = lean_ctor_get(v___x_1415_, 0);
lean_inc(v_a_1416_);
lean_dec_ref_known(v___x_1415_, 1);
v___x_1417_ = lean_ptr_addr(v_binderType_1410_);
v___x_1418_ = lean_ptr_addr(v_a_1414_);
v___x_1419_ = lean_usize_dec_eq(v___x_1417_, v___x_1418_);
if (v___x_1419_ == 0)
{
lean_object* v___x_1420_; lean_object* v___x_1421_; 
lean_inc(v_binderName_1409_);
lean_dec_ref_known(v___y_1408_, 3);
v___x_1420_ = l_Lean_Expr_forallE___override(v_binderName_1409_, v_a_1414_, v_a_1416_, v_binderInfo_1412_);
v___x_1421_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1394_, v_post_1396_, v___x_1420_, v___y_1397_, v___y_1398_, v___y_1399_);
return v___x_1421_;
}
else
{
size_t v___x_1422_; size_t v___x_1423_; uint8_t v___x_1424_; 
v___x_1422_ = lean_ptr_addr(v_body_1411_);
v___x_1423_ = lean_ptr_addr(v_a_1416_);
v___x_1424_ = lean_usize_dec_eq(v___x_1422_, v___x_1423_);
if (v___x_1424_ == 0)
{
lean_object* v___x_1425_; lean_object* v___x_1426_; 
lean_inc(v_binderName_1409_);
lean_dec_ref_known(v___y_1408_, 3);
v___x_1425_ = l_Lean_Expr_forallE___override(v_binderName_1409_, v_a_1414_, v_a_1416_, v_binderInfo_1412_);
v___x_1426_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1394_, v_post_1396_, v___x_1425_, v___y_1397_, v___y_1398_, v___y_1399_);
return v___x_1426_;
}
else
{
uint8_t v___x_1427_; 
v___x_1427_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1412_, v_binderInfo_1412_);
if (v___x_1427_ == 0)
{
lean_object* v___x_1428_; lean_object* v___x_1429_; 
lean_inc(v_binderName_1409_);
lean_dec_ref_known(v___y_1408_, 3);
v___x_1428_ = l_Lean_Expr_forallE___override(v_binderName_1409_, v_a_1414_, v_a_1416_, v_binderInfo_1412_);
v___x_1429_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1394_, v_post_1396_, v___x_1428_, v___y_1397_, v___y_1398_, v___y_1399_);
return v___x_1429_;
}
else
{
lean_object* v___x_1430_; 
lean_dec(v_a_1416_);
lean_dec(v_a_1414_);
v___x_1430_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1394_, v_post_1396_, v___y_1408_, v___y_1397_, v___y_1398_, v___y_1399_);
return v___x_1430_;
}
}
}
}
else
{
lean_dec(v_a_1414_);
lean_dec_ref_known(v___y_1408_, 3);
lean_dec_ref(v_post_1396_);
lean_dec_ref(v_pre_1394_);
return v___x_1415_;
}
}
else
{
lean_dec_ref_known(v___y_1408_, 3);
lean_dec_ref(v_post_1396_);
lean_dec_ref(v_pre_1394_);
return v___x_1413_;
}
}
case 6:
{
lean_object* v_binderName_1431_; lean_object* v_binderType_1432_; lean_object* v_body_1433_; uint8_t v_binderInfo_1434_; lean_object* v___x_1435_; 
v_binderName_1431_ = lean_ctor_get(v___y_1408_, 0);
v_binderType_1432_ = lean_ctor_get(v___y_1408_, 1);
v_body_1433_ = lean_ctor_get(v___y_1408_, 2);
v_binderInfo_1434_ = lean_ctor_get_uint8(v___y_1408_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1432_);
lean_inc_ref(v_post_1396_);
lean_inc_ref(v_pre_1394_);
v___x_1435_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1394_, v_post_1396_, v_binderType_1432_, v___y_1397_, v___y_1398_, v___y_1399_);
if (lean_obj_tag(v___x_1435_) == 0)
{
lean_object* v_a_1436_; lean_object* v___x_1437_; 
v_a_1436_ = lean_ctor_get(v___x_1435_, 0);
lean_inc(v_a_1436_);
lean_dec_ref_known(v___x_1435_, 1);
lean_inc_ref(v_body_1433_);
lean_inc_ref(v_post_1396_);
lean_inc_ref(v_pre_1394_);
v___x_1437_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1394_, v_post_1396_, v_body_1433_, v___y_1397_, v___y_1398_, v___y_1399_);
if (lean_obj_tag(v___x_1437_) == 0)
{
lean_object* v_a_1438_; size_t v___x_1439_; size_t v___x_1440_; uint8_t v___x_1441_; 
v_a_1438_ = lean_ctor_get(v___x_1437_, 0);
lean_inc(v_a_1438_);
lean_dec_ref_known(v___x_1437_, 1);
v___x_1439_ = lean_ptr_addr(v_binderType_1432_);
v___x_1440_ = lean_ptr_addr(v_a_1436_);
v___x_1441_ = lean_usize_dec_eq(v___x_1439_, v___x_1440_);
if (v___x_1441_ == 0)
{
lean_object* v___x_1442_; lean_object* v___x_1443_; 
lean_inc(v_binderName_1431_);
lean_dec_ref_known(v___y_1408_, 3);
v___x_1442_ = l_Lean_Expr_lam___override(v_binderName_1431_, v_a_1436_, v_a_1438_, v_binderInfo_1434_);
v___x_1443_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1394_, v_post_1396_, v___x_1442_, v___y_1397_, v___y_1398_, v___y_1399_);
return v___x_1443_;
}
else
{
size_t v___x_1444_; size_t v___x_1445_; uint8_t v___x_1446_; 
v___x_1444_ = lean_ptr_addr(v_body_1433_);
v___x_1445_ = lean_ptr_addr(v_a_1438_);
v___x_1446_ = lean_usize_dec_eq(v___x_1444_, v___x_1445_);
if (v___x_1446_ == 0)
{
lean_object* v___x_1447_; lean_object* v___x_1448_; 
lean_inc(v_binderName_1431_);
lean_dec_ref_known(v___y_1408_, 3);
v___x_1447_ = l_Lean_Expr_lam___override(v_binderName_1431_, v_a_1436_, v_a_1438_, v_binderInfo_1434_);
v___x_1448_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1394_, v_post_1396_, v___x_1447_, v___y_1397_, v___y_1398_, v___y_1399_);
return v___x_1448_;
}
else
{
uint8_t v___x_1449_; 
v___x_1449_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1434_, v_binderInfo_1434_);
if (v___x_1449_ == 0)
{
lean_object* v___x_1450_; lean_object* v___x_1451_; 
lean_inc(v_binderName_1431_);
lean_dec_ref_known(v___y_1408_, 3);
v___x_1450_ = l_Lean_Expr_lam___override(v_binderName_1431_, v_a_1436_, v_a_1438_, v_binderInfo_1434_);
v___x_1451_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1394_, v_post_1396_, v___x_1450_, v___y_1397_, v___y_1398_, v___y_1399_);
return v___x_1451_;
}
else
{
lean_object* v___x_1452_; 
lean_dec(v_a_1438_);
lean_dec(v_a_1436_);
v___x_1452_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1394_, v_post_1396_, v___y_1408_, v___y_1397_, v___y_1398_, v___y_1399_);
return v___x_1452_;
}
}
}
}
else
{
lean_dec(v_a_1436_);
lean_dec_ref_known(v___y_1408_, 3);
lean_dec_ref(v_post_1396_);
lean_dec_ref(v_pre_1394_);
return v___x_1437_;
}
}
else
{
lean_dec_ref_known(v___y_1408_, 3);
lean_dec_ref(v_post_1396_);
lean_dec_ref(v_pre_1394_);
return v___x_1435_;
}
}
case 8:
{
lean_object* v_declName_1453_; lean_object* v_type_1454_; lean_object* v_value_1455_; lean_object* v_body_1456_; uint8_t v_nondep_1457_; lean_object* v___x_1458_; 
v_declName_1453_ = lean_ctor_get(v___y_1408_, 0);
v_type_1454_ = lean_ctor_get(v___y_1408_, 1);
v_value_1455_ = lean_ctor_get(v___y_1408_, 2);
v_body_1456_ = lean_ctor_get(v___y_1408_, 3);
v_nondep_1457_ = lean_ctor_get_uint8(v___y_1408_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_1454_);
lean_inc_ref(v_post_1396_);
lean_inc_ref(v_pre_1394_);
v___x_1458_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1394_, v_post_1396_, v_type_1454_, v___y_1397_, v___y_1398_, v___y_1399_);
if (lean_obj_tag(v___x_1458_) == 0)
{
lean_object* v_a_1459_; lean_object* v___x_1460_; 
v_a_1459_ = lean_ctor_get(v___x_1458_, 0);
lean_inc(v_a_1459_);
lean_dec_ref_known(v___x_1458_, 1);
lean_inc_ref(v_value_1455_);
lean_inc_ref(v_post_1396_);
lean_inc_ref(v_pre_1394_);
v___x_1460_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1394_, v_post_1396_, v_value_1455_, v___y_1397_, v___y_1398_, v___y_1399_);
if (lean_obj_tag(v___x_1460_) == 0)
{
lean_object* v_a_1461_; lean_object* v___x_1462_; 
v_a_1461_ = lean_ctor_get(v___x_1460_, 0);
lean_inc(v_a_1461_);
lean_dec_ref_known(v___x_1460_, 1);
lean_inc_ref(v_body_1456_);
lean_inc_ref(v_post_1396_);
lean_inc_ref(v_pre_1394_);
v___x_1462_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1394_, v_post_1396_, v_body_1456_, v___y_1397_, v___y_1398_, v___y_1399_);
if (lean_obj_tag(v___x_1462_) == 0)
{
lean_object* v_a_1463_; size_t v___x_1464_; size_t v___x_1465_; uint8_t v___x_1466_; 
v_a_1463_ = lean_ctor_get(v___x_1462_, 0);
lean_inc(v_a_1463_);
lean_dec_ref_known(v___x_1462_, 1);
v___x_1464_ = lean_ptr_addr(v_type_1454_);
v___x_1465_ = lean_ptr_addr(v_a_1459_);
v___x_1466_ = lean_usize_dec_eq(v___x_1464_, v___x_1465_);
if (v___x_1466_ == 0)
{
lean_object* v___x_1467_; lean_object* v___x_1468_; 
lean_inc(v_declName_1453_);
lean_dec_ref_known(v___y_1408_, 4);
v___x_1467_ = l_Lean_Expr_letE___override(v_declName_1453_, v_a_1459_, v_a_1461_, v_a_1463_, v_nondep_1457_);
v___x_1468_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1394_, v_post_1396_, v___x_1467_, v___y_1397_, v___y_1398_, v___y_1399_);
return v___x_1468_;
}
else
{
size_t v___x_1469_; size_t v___x_1470_; uint8_t v___x_1471_; 
v___x_1469_ = lean_ptr_addr(v_value_1455_);
v___x_1470_ = lean_ptr_addr(v_a_1461_);
v___x_1471_ = lean_usize_dec_eq(v___x_1469_, v___x_1470_);
if (v___x_1471_ == 0)
{
lean_object* v___x_1472_; lean_object* v___x_1473_; 
lean_inc(v_declName_1453_);
lean_dec_ref_known(v___y_1408_, 4);
v___x_1472_ = l_Lean_Expr_letE___override(v_declName_1453_, v_a_1459_, v_a_1461_, v_a_1463_, v_nondep_1457_);
v___x_1473_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1394_, v_post_1396_, v___x_1472_, v___y_1397_, v___y_1398_, v___y_1399_);
return v___x_1473_;
}
else
{
size_t v___x_1474_; size_t v___x_1475_; uint8_t v___x_1476_; 
v___x_1474_ = lean_ptr_addr(v_body_1456_);
v___x_1475_ = lean_ptr_addr(v_a_1463_);
v___x_1476_ = lean_usize_dec_eq(v___x_1474_, v___x_1475_);
if (v___x_1476_ == 0)
{
lean_object* v___x_1477_; lean_object* v___x_1478_; 
lean_inc(v_declName_1453_);
lean_dec_ref_known(v___y_1408_, 4);
v___x_1477_ = l_Lean_Expr_letE___override(v_declName_1453_, v_a_1459_, v_a_1461_, v_a_1463_, v_nondep_1457_);
v___x_1478_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1394_, v_post_1396_, v___x_1477_, v___y_1397_, v___y_1398_, v___y_1399_);
return v___x_1478_;
}
else
{
lean_object* v___x_1479_; 
lean_dec(v_a_1463_);
lean_dec(v_a_1461_);
lean_dec(v_a_1459_);
v___x_1479_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1394_, v_post_1396_, v___y_1408_, v___y_1397_, v___y_1398_, v___y_1399_);
return v___x_1479_;
}
}
}
}
else
{
lean_dec(v_a_1461_);
lean_dec(v_a_1459_);
lean_dec_ref_known(v___y_1408_, 4);
lean_dec_ref(v_post_1396_);
lean_dec_ref(v_pre_1394_);
return v___x_1462_;
}
}
else
{
lean_dec(v_a_1459_);
lean_dec_ref_known(v___y_1408_, 4);
lean_dec_ref(v_post_1396_);
lean_dec_ref(v_pre_1394_);
return v___x_1460_;
}
}
else
{
lean_dec_ref_known(v___y_1408_, 4);
lean_dec_ref(v_post_1396_);
lean_dec_ref(v_pre_1394_);
return v___x_1458_;
}
}
case 5:
{
lean_object* v_dummy_1480_; lean_object* v_nargs_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; 
v_dummy_1480_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_1481_ = l_Lean_Expr_getAppNumArgs(v___y_1408_);
lean_inc(v_nargs_1481_);
v___x_1482_ = lean_mk_array(v_nargs_1481_, v_dummy_1480_);
v___x_1483_ = lean_unsigned_to_nat(1u);
v___x_1484_ = lean_nat_sub(v_nargs_1481_, v___x_1483_);
lean_dec(v_nargs_1481_);
v___x_1485_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__4(v_pre_1394_, v_post_1396_, v___y_1408_, v___x_1482_, v___x_1484_, v___y_1397_, v___y_1398_, v___y_1399_);
return v___x_1485_;
}
case 10:
{
lean_object* v_data_1486_; lean_object* v_expr_1487_; lean_object* v___x_1488_; 
v_data_1486_ = lean_ctor_get(v___y_1408_, 0);
v_expr_1487_ = lean_ctor_get(v___y_1408_, 1);
lean_inc_ref(v_expr_1487_);
lean_inc_ref(v_post_1396_);
lean_inc_ref(v_pre_1394_);
v___x_1488_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1394_, v_post_1396_, v_expr_1487_, v___y_1397_, v___y_1398_, v___y_1399_);
if (lean_obj_tag(v___x_1488_) == 0)
{
lean_object* v_a_1489_; size_t v___x_1490_; size_t v___x_1491_; uint8_t v___x_1492_; 
v_a_1489_ = lean_ctor_get(v___x_1488_, 0);
lean_inc(v_a_1489_);
lean_dec_ref_known(v___x_1488_, 1);
v___x_1490_ = lean_ptr_addr(v_expr_1487_);
v___x_1491_ = lean_ptr_addr(v_a_1489_);
v___x_1492_ = lean_usize_dec_eq(v___x_1490_, v___x_1491_);
if (v___x_1492_ == 0)
{
lean_object* v___x_1493_; lean_object* v___x_1494_; 
lean_inc(v_data_1486_);
lean_dec_ref_known(v___y_1408_, 2);
v___x_1493_ = l_Lean_Expr_mdata___override(v_data_1486_, v_a_1489_);
v___x_1494_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1394_, v_post_1396_, v___x_1493_, v___y_1397_, v___y_1398_, v___y_1399_);
return v___x_1494_;
}
else
{
lean_object* v___x_1495_; 
lean_dec(v_a_1489_);
v___x_1495_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1394_, v_post_1396_, v___y_1408_, v___y_1397_, v___y_1398_, v___y_1399_);
return v___x_1495_;
}
}
else
{
lean_dec_ref_known(v___y_1408_, 2);
lean_dec_ref(v_post_1396_);
lean_dec_ref(v_pre_1394_);
return v___x_1488_;
}
}
case 11:
{
lean_object* v_typeName_1496_; lean_object* v_idx_1497_; lean_object* v_struct_1498_; lean_object* v___x_1499_; 
v_typeName_1496_ = lean_ctor_get(v___y_1408_, 0);
v_idx_1497_ = lean_ctor_get(v___y_1408_, 1);
v_struct_1498_ = lean_ctor_get(v___y_1408_, 2);
lean_inc_ref(v_struct_1498_);
lean_inc_ref(v_post_1396_);
lean_inc_ref(v_pre_1394_);
v___x_1499_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1394_, v_post_1396_, v_struct_1498_, v___y_1397_, v___y_1398_, v___y_1399_);
if (lean_obj_tag(v___x_1499_) == 0)
{
lean_object* v_a_1500_; size_t v___x_1501_; size_t v___x_1502_; uint8_t v___x_1503_; 
v_a_1500_ = lean_ctor_get(v___x_1499_, 0);
lean_inc(v_a_1500_);
lean_dec_ref_known(v___x_1499_, 1);
v___x_1501_ = lean_ptr_addr(v_struct_1498_);
v___x_1502_ = lean_ptr_addr(v_a_1500_);
v___x_1503_ = lean_usize_dec_eq(v___x_1501_, v___x_1502_);
if (v___x_1503_ == 0)
{
lean_object* v___x_1504_; lean_object* v___x_1505_; 
lean_inc(v_idx_1497_);
lean_inc(v_typeName_1496_);
lean_dec_ref_known(v___y_1408_, 3);
v___x_1504_ = l_Lean_Expr_proj___override(v_typeName_1496_, v_idx_1497_, v_a_1500_);
v___x_1505_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1394_, v_post_1396_, v___x_1504_, v___y_1397_, v___y_1398_, v___y_1399_);
return v___x_1505_;
}
else
{
lean_object* v___x_1506_; 
lean_dec(v_a_1500_);
v___x_1506_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1394_, v_post_1396_, v___y_1408_, v___y_1397_, v___y_1398_, v___y_1399_);
return v___x_1506_;
}
}
else
{
lean_dec_ref_known(v___y_1408_, 3);
lean_dec_ref(v_post_1396_);
lean_dec_ref(v_pre_1394_);
return v___x_1499_;
}
}
default: 
{
lean_object* v___x_1507_; 
v___x_1507_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1394_, v_post_1396_, v___y_1408_, v___y_1397_, v___y_1398_, v___y_1399_);
return v___x_1507_;
}
}
}
}
}
else
{
lean_object* v_a_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1526_; 
lean_dec_ref(v_post_1396_);
lean_dec_ref(v_e_1395_);
lean_dec_ref(v_pre_1394_);
v_a_1519_ = lean_ctor_get(v___x_1402_, 0);
v_isSharedCheck_1526_ = !lean_is_exclusive(v___x_1402_);
if (v_isSharedCheck_1526_ == 0)
{
v___x_1521_ = v___x_1402_;
v_isShared_1522_ = v_isSharedCheck_1526_;
goto v_resetjp_1520_;
}
else
{
lean_inc(v_a_1519_);
lean_dec(v___x_1402_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1526_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
lean_object* v___x_1524_; 
if (v_isShared_1522_ == 0)
{
v___x_1524_ = v___x_1521_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v_a_1519_);
v___x_1524_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
return v___x_1524_;
}
}
}
}
else
{
lean_object* v_a_1527_; lean_object* v___x_1529_; uint8_t v_isShared_1530_; uint8_t v_isSharedCheck_1534_; 
lean_dec_ref(v_post_1396_);
lean_dec_ref(v_e_1395_);
lean_dec_ref(v_pre_1394_);
v_a_1527_ = lean_ctor_get(v___x_1401_, 0);
v_isSharedCheck_1534_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1534_ == 0)
{
v___x_1529_ = v___x_1401_;
v_isShared_1530_ = v_isSharedCheck_1534_;
goto v_resetjp_1528_;
}
else
{
lean_inc(v_a_1527_);
lean_dec(v___x_1401_);
v___x_1529_ = lean_box(0);
v_isShared_1530_ = v_isSharedCheck_1534_;
goto v_resetjp_1528_;
}
v_resetjp_1528_:
{
lean_object* v___x_1532_; 
if (v_isShared_1530_ == 0)
{
v___x_1532_ = v___x_1529_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v_a_1527_);
v___x_1532_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
return v___x_1532_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__1___boxed(lean_object* v___x_1535_, lean_object* v_pre_1536_, lean_object* v_e_1537_, lean_object* v_post_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_){
_start:
{
lean_object* v_res_1543_; 
v_res_1543_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__1(v___x_1535_, v_pre_1536_, v_e_1537_, v_post_1538_, v___y_1539_, v___y_1540_, v___y_1541_);
lean_dec(v___y_1541_);
lean_dec_ref(v___y_1540_);
lean_dec(v___y_1539_);
return v_res_1543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(lean_object* v_pre_1544_, lean_object* v_post_1545_, lean_object* v_e_1546_, lean_object* v_a_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_){
_start:
{
lean_object* v___x_1551_; lean_object* v___x_1552_; 
lean_inc(v_a_1547_);
v___x_1551_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1551_, 0, lean_box(0));
lean_closure_set(v___x_1551_, 1, lean_box(0));
lean_closure_set(v___x_1551_, 2, v_a_1547_);
v___x_1552_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__0(lean_box(0), v___x_1551_, v___y_1548_, v___y_1549_);
if (lean_obj_tag(v___x_1552_) == 0)
{
lean_object* v_a_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1584_; 
v_a_1553_ = lean_ctor_get(v___x_1552_, 0);
v_isSharedCheck_1584_ = !lean_is_exclusive(v___x_1552_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1555_ = v___x_1552_;
v_isShared_1556_ = v_isSharedCheck_1584_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_a_1553_);
lean_dec(v___x_1552_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1584_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v___x_1557_; 
v___x_1557_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg(v_a_1553_, v_e_1546_);
lean_dec(v_a_1553_);
if (lean_obj_tag(v___x_1557_) == 0)
{
lean_object* v___x_1558_; lean_object* v___f_1559_; lean_object* v___x_1560_; 
lean_del_object(v___x_1555_);
v___x_1558_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__19___closed__0));
lean_inc_ref(v_e_1546_);
v___f_1559_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__1___boxed), 8, 4);
lean_closure_set(v___f_1559_, 0, v___x_1558_);
lean_closure_set(v___f_1559_, 1, v_pre_1544_);
lean_closure_set(v___f_1559_, 2, v_e_1546_);
lean_closure_set(v___f_1559_, 3, v_post_1545_);
v___x_1560_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___redArg(v___f_1559_, v_a_1547_, v___y_1548_, v___y_1549_);
if (lean_obj_tag(v___x_1560_) == 0)
{
lean_object* v_a_1561_; lean_object* v___f_1562_; lean_object* v___x_1563_; 
v_a_1561_ = lean_ctor_get(v___x_1560_, 0);
lean_inc_n(v_a_1561_, 2);
lean_dec_ref_known(v___x_1560_, 1);
lean_inc(v_a_1547_);
v___f_1562_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1562_, 0, v_a_1547_);
lean_closure_set(v___f_1562_, 1, v_e_1546_);
lean_closure_set(v___f_1562_, 2, v_a_1561_);
v___x_1563_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__0(lean_box(0), v___f_1562_, v___y_1548_, v___y_1549_);
if (lean_obj_tag(v___x_1563_) == 0)
{
lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1570_; 
v_isSharedCheck_1570_ = !lean_is_exclusive(v___x_1563_);
if (v_isSharedCheck_1570_ == 0)
{
lean_object* v_unused_1571_; 
v_unused_1571_ = lean_ctor_get(v___x_1563_, 0);
lean_dec(v_unused_1571_);
v___x_1565_ = v___x_1563_;
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
else
{
lean_dec(v___x_1563_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
lean_object* v___x_1568_; 
if (v_isShared_1566_ == 0)
{
lean_ctor_set(v___x_1565_, 0, v_a_1561_);
v___x_1568_ = v___x_1565_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v_a_1561_);
v___x_1568_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
return v___x_1568_;
}
}
}
else
{
lean_object* v_a_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1579_; 
lean_dec(v_a_1561_);
v_a_1572_ = lean_ctor_get(v___x_1563_, 0);
v_isSharedCheck_1579_ = !lean_is_exclusive(v___x_1563_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1574_ = v___x_1563_;
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_a_1572_);
lean_dec(v___x_1563_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
lean_object* v___x_1577_; 
if (v_isShared_1575_ == 0)
{
v___x_1577_ = v___x_1574_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v_a_1572_);
v___x_1577_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
return v___x_1577_;
}
}
}
}
else
{
lean_dec_ref(v_e_1546_);
return v___x_1560_;
}
}
else
{
lean_object* v_val_1580_; lean_object* v___x_1582_; 
lean_dec_ref(v_e_1546_);
lean_dec_ref(v_post_1545_);
lean_dec_ref(v_pre_1544_);
v_val_1580_ = lean_ctor_get(v___x_1557_, 0);
lean_inc(v_val_1580_);
lean_dec_ref_known(v___x_1557_, 1);
if (v_isShared_1556_ == 0)
{
lean_ctor_set(v___x_1555_, 0, v_val_1580_);
v___x_1582_ = v___x_1555_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v_val_1580_);
v___x_1582_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
return v___x_1582_;
}
}
}
}
else
{
lean_object* v_a_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1592_; 
lean_dec_ref(v_e_1546_);
lean_dec_ref(v_post_1545_);
lean_dec_ref(v_pre_1544_);
v_a_1585_ = lean_ctor_get(v___x_1552_, 0);
v_isSharedCheck_1592_ = !lean_is_exclusive(v___x_1552_);
if (v_isSharedCheck_1592_ == 0)
{
v___x_1587_ = v___x_1552_;
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_a_1585_);
lean_dec(v___x_1552_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
lean_object* v___x_1590_; 
if (v_isShared_1588_ == 0)
{
v___x_1590_ = v___x_1587_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v_a_1585_);
v___x_1590_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
return v___x_1590_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(lean_object* v_pre_1593_, lean_object* v_post_1594_, lean_object* v_e_1595_, lean_object* v_a_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_){
_start:
{
lean_object* v___x_1600_; 
lean_inc_ref(v_post_1594_);
lean_inc(v___y_1598_);
lean_inc_ref(v___y_1597_);
lean_inc_ref(v_e_1595_);
v___x_1600_ = lean_apply_4(v_post_1594_, v_e_1595_, v___y_1597_, v___y_1598_, lean_box(0));
if (lean_obj_tag(v___x_1600_) == 0)
{
lean_object* v_a_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1619_; 
v_a_1601_ = lean_ctor_get(v___x_1600_, 0);
v_isSharedCheck_1619_ = !lean_is_exclusive(v___x_1600_);
if (v_isSharedCheck_1619_ == 0)
{
v___x_1603_ = v___x_1600_;
v_isShared_1604_ = v_isSharedCheck_1619_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_a_1601_);
lean_dec(v___x_1600_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1619_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
switch(lean_obj_tag(v_a_1601_))
{
case 0:
{
lean_object* v_e_1605_; lean_object* v___x_1607_; 
lean_dec_ref(v_e_1595_);
lean_dec_ref(v_post_1594_);
lean_dec_ref(v_pre_1593_);
v_e_1605_ = lean_ctor_get(v_a_1601_, 0);
lean_inc_ref(v_e_1605_);
lean_dec_ref_known(v_a_1601_, 1);
if (v_isShared_1604_ == 0)
{
lean_ctor_set(v___x_1603_, 0, v_e_1605_);
v___x_1607_ = v___x_1603_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v_e_1605_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
return v___x_1607_;
}
}
case 1:
{
lean_object* v_e_1609_; lean_object* v___x_1610_; 
lean_del_object(v___x_1603_);
lean_dec_ref(v_e_1595_);
v_e_1609_ = lean_ctor_get(v_a_1601_, 0);
lean_inc_ref(v_e_1609_);
lean_dec_ref_known(v_a_1601_, 1);
v___x_1610_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1593_, v_post_1594_, v_e_1609_, v_a_1596_, v___y_1597_, v___y_1598_);
return v___x_1610_;
}
default: 
{
lean_object* v_e_x3f_1611_; 
lean_dec_ref(v_post_1594_);
lean_dec_ref(v_pre_1593_);
v_e_x3f_1611_ = lean_ctor_get(v_a_1601_, 0);
lean_inc(v_e_x3f_1611_);
lean_dec_ref_known(v_a_1601_, 1);
if (lean_obj_tag(v_e_x3f_1611_) == 0)
{
lean_object* v___x_1613_; 
if (v_isShared_1604_ == 0)
{
lean_ctor_set(v___x_1603_, 0, v_e_1595_);
v___x_1613_ = v___x_1603_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v_e_1595_);
v___x_1613_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
return v___x_1613_;
}
}
else
{
lean_object* v_val_1615_; lean_object* v___x_1617_; 
lean_dec_ref(v_e_1595_);
v_val_1615_ = lean_ctor_get(v_e_x3f_1611_, 0);
lean_inc(v_val_1615_);
lean_dec_ref_known(v_e_x3f_1611_, 1);
if (v_isShared_1604_ == 0)
{
lean_ctor_set(v___x_1603_, 0, v_val_1615_);
v___x_1617_ = v___x_1603_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v_val_1615_);
v___x_1617_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
return v___x_1617_;
}
}
}
}
}
}
else
{
lean_object* v_a_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1627_; 
lean_dec_ref(v_e_1595_);
lean_dec_ref(v_post_1594_);
lean_dec_ref(v_pre_1593_);
v_a_1620_ = lean_ctor_get(v___x_1600_, 0);
v_isSharedCheck_1627_ = !lean_is_exclusive(v___x_1600_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1622_ = v___x_1600_;
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_a_1620_);
lean_dec(v___x_1600_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v___x_1625_; 
if (v_isShared_1623_ == 0)
{
v___x_1625_ = v___x_1622_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v_a_1620_);
v___x_1625_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
return v___x_1625_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_1628_, lean_object* v_post_1629_, lean_object* v_e_1630_, lean_object* v_a_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_){
_start:
{
lean_object* v_res_1635_; 
v_res_1635_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1628_, v_post_1629_, v_e_1630_, v_a_1631_, v___y_1632_, v___y_1633_);
lean_dec(v___y_1633_);
lean_dec_ref(v___y_1632_);
lean_dec(v_a_1631_);
return v_res_1635_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_1636_, lean_object* v_post_1637_, lean_object* v_sz_1638_, lean_object* v_i_1639_, lean_object* v_bs_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_){
_start:
{
size_t v_sz_boxed_1645_; size_t v_i_boxed_1646_; lean_object* v_res_1647_; 
v_sz_boxed_1645_ = lean_unbox_usize(v_sz_1638_);
lean_dec(v_sz_1638_);
v_i_boxed_1646_ = lean_unbox_usize(v_i_1639_);
lean_dec(v_i_1639_);
v_res_1647_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1(v_pre_1636_, v_post_1637_, v_sz_boxed_1645_, v_i_boxed_1646_, v_bs_1640_, v___y_1641_, v___y_1642_, v___y_1643_);
lean_dec(v___y_1643_);
lean_dec_ref(v___y_1642_);
lean_dec(v___y_1641_);
return v_res_1647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__4___boxed(lean_object* v_pre_1648_, lean_object* v_post_1649_, lean_object* v_x_1650_, lean_object* v_x_1651_, lean_object* v_x_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_){
_start:
{
lean_object* v_res_1657_; 
v_res_1657_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__4(v_pre_1648_, v_post_1649_, v_x_1650_, v_x_1651_, v_x_1652_, v___y_1653_, v___y_1654_, v___y_1655_);
lean_dec(v___y_1655_);
lean_dec_ref(v___y_1654_);
lean_dec(v___y_1653_);
return v_res_1657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___boxed(lean_object* v_pre_1658_, lean_object* v_post_1659_, lean_object* v_e_1660_, lean_object* v_a_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_){
_start:
{
lean_object* v_res_1665_; 
v_res_1665_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1658_, v_post_1659_, v_e_1660_, v_a_1661_, v___y_1662_, v___y_1663_);
lean_dec(v___y_1663_);
lean_dec_ref(v___y_1662_);
lean_dec(v_a_1661_);
return v_res_1665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___lam__0(lean_object* v_00_u03b1_1666_, lean_object* v_x_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_){
_start:
{
lean_object* v___x_1671_; lean_object* v___x_1672_; 
v___x_1671_ = lean_apply_1(v_x_1667_, lean_box(0));
v___x_1672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1672_, 0, v___x_1671_);
return v___x_1672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___lam__0___boxed(lean_object* v_00_u03b1_1673_, lean_object* v_x_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_){
_start:
{
lean_object* v_res_1678_; 
v_res_1678_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___lam__0(v_00_u03b1_1673_, v_x_1674_, v___y_1675_, v___y_1676_);
lean_dec(v___y_1676_);
lean_dec_ref(v___y_1675_);
return v_res_1678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(lean_object* v_input_1679_, lean_object* v_pre_1680_, lean_object* v_post_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_){
_start:
{
lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v_a_1687_; lean_object* v___x_1688_; 
v___x_1685_ = lean_obj_once(&l_Lean_Core_transform___redArg___closed__2, &l_Lean_Core_transform___redArg___closed__2_once, _init_l_Lean_Core_transform___redArg___closed__2);
v___x_1686_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___lam__0(lean_box(0), v___x_1685_, v___y_1682_, v___y_1683_);
v_a_1687_ = lean_ctor_get(v___x_1686_, 0);
lean_inc(v_a_1687_);
lean_dec_ref(v___x_1686_);
v___x_1688_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1680_, v_post_1681_, v_input_1679_, v_a_1687_, v___y_1682_, v___y_1683_);
if (lean_obj_tag(v___x_1688_) == 0)
{
lean_object* v_a_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1698_; 
v_a_1689_ = lean_ctor_get(v___x_1688_, 0);
lean_inc(v_a_1689_);
lean_dec_ref_known(v___x_1688_, 1);
v___x_1690_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1690_, 0, lean_box(0));
lean_closure_set(v___x_1690_, 1, lean_box(0));
lean_closure_set(v___x_1690_, 2, v_a_1687_);
v___x_1691_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___lam__0(lean_box(0), v___x_1690_, v___y_1682_, v___y_1683_);
v_isSharedCheck_1698_ = !lean_is_exclusive(v___x_1691_);
if (v_isSharedCheck_1698_ == 0)
{
lean_object* v_unused_1699_; 
v_unused_1699_ = lean_ctor_get(v___x_1691_, 0);
lean_dec(v_unused_1699_);
v___x_1693_ = v___x_1691_;
v_isShared_1694_ = v_isSharedCheck_1698_;
goto v_resetjp_1692_;
}
else
{
lean_dec(v___x_1691_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1698_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
lean_object* v___x_1696_; 
if (v_isShared_1694_ == 0)
{
lean_ctor_set(v___x_1693_, 0, v_a_1689_);
v___x_1696_ = v___x_1693_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v_a_1689_);
v___x_1696_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
return v___x_1696_;
}
}
}
else
{
lean_dec(v_a_1687_);
return v___x_1688_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___boxed(lean_object* v_input_1700_, lean_object* v_pre_1701_, lean_object* v_post_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_){
_start:
{
lean_object* v_res_1706_; 
v_res_1706_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_input_1700_, v_pre_1701_, v_post_1702_, v___y_1703_, v___y_1704_);
lean_dec(v___y_1704_);
lean_dec_ref(v___y_1703_);
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_betaReduce(lean_object* v_e_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_){
_start:
{
lean_object* v___f_1713_; lean_object* v___f_1714_; lean_object* v___x_1715_; 
v___f_1713_ = ((lean_object*)(l_Lean_Core_betaReduce___closed__0));
v___f_1714_ = ((lean_object*)(l_Lean_Core_betaReduce___closed__1));
v___x_1715_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_1709_, v___f_1713_, v___f_1714_, v_a_1710_, v_a_1711_);
return v___x_1715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_betaReduce___boxed(lean_object* v_e_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_){
_start:
{
lean_object* v_res_1720_; 
v_res_1720_ = l_Lean_Core_betaReduce(v_e_1716_, v_a_1717_, v_a_1718_);
lean_dec(v_a_1718_);
lean_dec_ref(v_a_1717_);
return v_res_1720_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_1721_, lean_object* v_m_1722_, lean_object* v_a_1723_){
_start:
{
lean_object* v___x_1724_; 
v___x_1724_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg(v_m_1722_, v_a_1723_);
return v___x_1724_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_1725_, lean_object* v_m_1726_, lean_object* v_a_1727_){
_start:
{
lean_object* v_res_1728_; 
v_res_1728_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3(v_00_u03b2_1725_, v_m_1726_, v_a_1727_);
lean_dec_ref(v_a_1727_);
lean_dec_ref(v_m_1726_);
return v_res_1728_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_1729_, lean_object* v_ref_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_){
_start:
{
lean_object* v___x_1734_; 
v___x_1734_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_1730_);
return v___x_1734_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1735_, lean_object* v_ref_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_){
_start:
{
lean_object* v_res_1740_; 
v_res_1740_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_1735_, v_ref_1736_, v___y_1737_, v___y_1738_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
return v_res_1740_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8(lean_object* v_00_u03b1_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_){
_start:
{
lean_object* v___x_1745_; 
v___x_1745_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___redArg();
return v___x_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___boxed(lean_object* v_00_u03b1_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_){
_start:
{
lean_object* v_res_1750_; 
v_res_1750_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8(v_00_u03b1_1746_, v___y_1747_, v___y_1748_);
lean_dec(v___y_1748_);
lean_dec_ref(v___y_1747_);
return v_res_1750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5(lean_object* v_00_u03b1_1751_, lean_object* v_x_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_){
_start:
{
lean_object* v___x_1757_; 
v___x_1757_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___redArg(v_x_1752_, v___y_1753_, v___y_1754_, v___y_1755_);
return v___x_1757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b1_1758_, lean_object* v_x_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_){
_start:
{
lean_object* v_res_1764_; 
v_res_1764_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5(v_00_u03b1_1758_, v_x_1759_, v___y_1760_, v___y_1761_, v___y_1762_);
lean_dec(v___y_1762_);
lean_dec_ref(v___y_1761_);
lean_dec(v___y_1760_);
return v_res_1764_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6(lean_object* v_00_u03b2_1765_, lean_object* v_m_1766_, lean_object* v_a_1767_, lean_object* v_b_1768_){
_start:
{
lean_object* v___x_1769_; 
v___x_1769_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6___redArg(v_m_1766_, v_a_1767_, v_b_1768_);
return v___x_1769_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4(lean_object* v_00_u03b2_1770_, lean_object* v_a_1771_, lean_object* v_x_1772_){
_start:
{
lean_object* v___x_1773_; 
v___x_1773_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___redArg(v_a_1771_, v_x_1772_);
return v___x_1773_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___boxed(lean_object* v_00_u03b2_1774_, lean_object* v_a_1775_, lean_object* v_x_1776_){
_start:
{
lean_object* v_res_1777_; 
v_res_1777_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4(v_00_u03b2_1774_, v_a_1775_, v_x_1776_);
lean_dec(v_x_1776_);
lean_dec_ref(v_a_1775_);
return v_res_1777_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10(lean_object* v_00_u03b2_1778_, lean_object* v_a_1779_, lean_object* v_x_1780_){
_start:
{
uint8_t v___x_1781_; 
v___x_1781_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___redArg(v_a_1779_, v_x_1780_);
return v___x_1781_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___boxed(lean_object* v_00_u03b2_1782_, lean_object* v_a_1783_, lean_object* v_x_1784_){
_start:
{
uint8_t v_res_1785_; lean_object* v_r_1786_; 
v_res_1785_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10(v_00_u03b2_1782_, v_a_1783_, v_x_1784_);
lean_dec(v_x_1784_);
lean_dec_ref(v_a_1783_);
v_r_1786_ = lean_box(v_res_1785_);
return v_r_1786_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11(lean_object* v_00_u03b2_1787_, lean_object* v_data_1788_){
_start:
{
lean_object* v___x_1789_; 
v___x_1789_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11___redArg(v_data_1788_);
return v___x_1789_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__12(lean_object* v_00_u03b2_1790_, lean_object* v_a_1791_, lean_object* v_b_1792_, lean_object* v_x_1793_){
_start:
{
lean_object* v___x_1794_; 
v___x_1794_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__12___redArg(v_a_1791_, v_b_1792_, v_x_1793_);
return v___x_1794_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12(lean_object* v_00_u03b2_1795_, lean_object* v_i_1796_, lean_object* v_source_1797_, lean_object* v_target_1798_){
_start:
{
lean_object* v___x_1799_; 
v___x_1799_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v_i_1796_, v_source_1797_, v_target_1798_);
return v___x_1799_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13(lean_object* v_00_u03b2_1800_, lean_object* v_x_1801_, lean_object* v_x_1802_){
_start:
{
lean_object* v___x_1803_; 
v___x_1803_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_x_1801_, v_x_1802_);
return v___x_1803_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__0(lean_object* v_toApplicative_1804_, lean_object* v_a_1805_){
_start:
{
lean_object* v_toPure_1806_; lean_object* v___x_1807_; 
v_toPure_1806_ = lean_ctor_get(v_toApplicative_1804_, 1);
lean_inc(v_toPure_1806_);
lean_dec_ref(v_toApplicative_1804_);
v___x_1807_ = lean_apply_2(v_toPure_1806_, lean_box(0), v_a_1805_);
return v___x_1807_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__13(lean_object* v___x_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_){
_start:
{
lean_object* v___x_1814_; 
v___x_1814_ = l_Lean_Core_checkSystem(v___x_1808_, v___y_1811_, v___y_1812_);
return v___x_1814_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__13___boxed(lean_object* v___x_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_){
_start:
{
lean_object* v_res_1821_; 
v_res_1821_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__13(v___x_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_);
lean_dec(v___y_1819_);
lean_dec_ref(v___y_1818_);
lean_dec(v___y_1817_);
lean_dec_ref(v___y_1816_);
return v_res_1821_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14(lean_object* v_inst_1824_, lean_object* v_x_1825_, lean_object* v___x_1826_, lean_object* v___x_1827_, lean_object* v_inst_1828_, lean_object* v___f_1829_, lean_object* v___x_1830_, lean_object* v___x_1831_, lean_object* v_a_1832_, lean_object* v_toBind_1833_, lean_object* v___f_1834_, lean_object* v_toApplicative_1835_, lean_object* v_a_1836_){
_start:
{
if (lean_obj_tag(v_a_1836_) == 0)
{
lean_object* v___f_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_3431__overap_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; 
lean_dec_ref(v_toApplicative_1835_);
v___f_1837_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14___closed__0));
v___x_1838_ = lean_apply_2(v_inst_1824_, lean_box(0), v___f_1837_);
lean_inc_ref(v___x_1827_);
lean_inc_ref(v___x_1826_);
v___x_1839_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonadLift___aux__1___boxed), 10, 9);
lean_closure_set(v___x_1839_, 0, lean_box(0));
lean_closure_set(v___x_1839_, 1, lean_box(0));
lean_closure_set(v___x_1839_, 2, lean_box(0));
lean_closure_set(v___x_1839_, 3, lean_box(0));
lean_closure_set(v___x_1839_, 4, v_x_1825_);
lean_closure_set(v___x_1839_, 5, v___x_1826_);
lean_closure_set(v___x_1839_, 6, v___x_1827_);
lean_closure_set(v___x_1839_, 7, lean_box(0));
lean_closure_set(v___x_1839_, 8, v___x_1838_);
v___x_1840_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonad___aux__13___boxed), 13, 12);
lean_closure_set(v___x_1840_, 0, lean_box(0));
lean_closure_set(v___x_1840_, 1, lean_box(0));
lean_closure_set(v___x_1840_, 2, lean_box(0));
lean_closure_set(v___x_1840_, 3, lean_box(0));
lean_closure_set(v___x_1840_, 4, v_x_1825_);
lean_closure_set(v___x_1840_, 5, v___x_1826_);
lean_closure_set(v___x_1840_, 6, v___x_1827_);
lean_closure_set(v___x_1840_, 7, v_inst_1828_);
lean_closure_set(v___x_1840_, 8, lean_box(0));
lean_closure_set(v___x_1840_, 9, lean_box(0));
lean_closure_set(v___x_1840_, 10, v___x_1839_);
lean_closure_set(v___x_1840_, 11, v___f_1829_);
v___x_3431__overap_1841_ = l_Lean_Meta_withIncRecDepth___redArg(v___x_1830_, v___x_1831_, v___x_1840_);
lean_inc(v_a_1832_);
v___x_1842_ = lean_apply_1(v___x_3431__overap_1841_, v_a_1832_);
v___x_1843_ = lean_apply_4(v_toBind_1833_, lean_box(0), lean_box(0), v___x_1842_, v___f_1834_);
return v___x_1843_;
}
else
{
lean_object* v_val_1844_; lean_object* v_toPure_1845_; lean_object* v___x_1846_; 
lean_dec(v___f_1834_);
lean_dec(v_toBind_1833_);
lean_dec_ref(v___x_1831_);
lean_dec_ref(v___x_1830_);
lean_dec(v___f_1829_);
lean_dec_ref(v_inst_1828_);
lean_dec_ref(v___x_1827_);
lean_dec_ref(v___x_1826_);
lean_dec(v_inst_1824_);
v_val_1844_ = lean_ctor_get(v_a_1836_, 0);
lean_inc(v_val_1844_);
lean_dec_ref_known(v_a_1836_, 1);
v_toPure_1845_ = lean_ctor_get(v_toApplicative_1835_, 1);
lean_inc(v_toPure_1845_);
lean_dec_ref(v_toApplicative_1835_);
v___x_1846_ = lean_apply_2(v_toPure_1845_, lean_box(0), v_val_1844_);
return v___x_1846_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14___boxed(lean_object* v_inst_1847_, lean_object* v_x_1848_, lean_object* v___x_1849_, lean_object* v___x_1850_, lean_object* v_inst_1851_, lean_object* v___f_1852_, lean_object* v___x_1853_, lean_object* v___x_1854_, lean_object* v_a_1855_, lean_object* v_toBind_1856_, lean_object* v___f_1857_, lean_object* v_toApplicative_1858_, lean_object* v_a_1859_){
_start:
{
lean_object* v_res_1860_; 
v_res_1860_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14(v_inst_1847_, v_x_1848_, v___x_1849_, v___x_1850_, v_inst_1851_, v___f_1852_, v___x_1853_, v___x_1854_, v_a_1855_, v_toBind_1856_, v___f_1857_, v_toApplicative_1858_, v_a_1859_);
lean_dec(v_a_1855_);
return v_res_1860_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__1(lean_object* v___x_1861_, lean_object* v___x_1862_, lean_object* v_declName_1863_, lean_object* v_a_1864_, lean_object* v___f_1865_, uint8_t v_nondep_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_){
_start:
{
uint8_t v___x_1869_; lean_object* v___x_3450__overap_1870_; lean_object* v___x_1871_; 
v___x_1869_ = 0;
v___x_3450__overap_1870_ = l_Lean_Meta_withLetDecl___redArg(v___x_1861_, v___x_1862_, v_declName_1863_, v_a_1864_, v_a_1868_, v___f_1865_, v_nondep_1866_, v___x_1869_);
lean_inc(v_a_1867_);
v___x_1871_ = lean_apply_1(v___x_3450__overap_1870_, v_a_1867_);
return v___x_1871_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__1___boxed(lean_object* v___x_1872_, lean_object* v___x_1873_, lean_object* v_declName_1874_, lean_object* v_a_1875_, lean_object* v___f_1876_, lean_object* v_nondep_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_){
_start:
{
uint8_t v_nondep_3629__boxed_1880_; lean_object* v_res_1881_; 
v_nondep_3629__boxed_1880_ = lean_unbox(v_nondep_1877_);
v_res_1881_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__1(v___x_1872_, v___x_1873_, v_declName_1874_, v_a_1875_, v___f_1876_, v_nondep_3629__boxed_1880_, v_a_1878_, v_a_1879_);
lean_dec(v_a_1878_);
return v_res_1881_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__4(lean_object* v_fvars_1882_, uint8_t v_usedLetOnly_1883_, lean_object* v_inst_1884_, lean_object* v_toBind_1885_, lean_object* v___f_1886_, lean_object* v_a_1887_){
_start:
{
uint8_t v___x_1888_; uint8_t v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; 
v___x_1888_ = 0;
v___x_1889_ = 1;
v___x_1890_ = lean_box(v_usedLetOnly_1883_);
v___x_1891_ = lean_box(v___x_1888_);
v___x_1892_ = lean_box(v___x_1889_);
v___x_1893_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLetFVars___boxed), 10, 5);
lean_closure_set(v___x_1893_, 0, v_fvars_1882_);
lean_closure_set(v___x_1893_, 1, v_a_1887_);
lean_closure_set(v___x_1893_, 2, v___x_1890_);
lean_closure_set(v___x_1893_, 3, v___x_1891_);
lean_closure_set(v___x_1893_, 4, v___x_1892_);
v___x_1894_ = lean_apply_2(v_inst_1884_, lean_box(0), v___x_1893_);
v___x_1895_ = lean_apply_4(v_toBind_1885_, lean_box(0), lean_box(0), v___x_1894_, v___f_1886_);
return v___x_1895_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__4___boxed(lean_object* v_fvars_1896_, lean_object* v_usedLetOnly_1897_, lean_object* v_inst_1898_, lean_object* v_toBind_1899_, lean_object* v___f_1900_, lean_object* v_a_1901_){
_start:
{
uint8_t v_usedLetOnly_boxed_1902_; lean_object* v_res_1903_; 
v_usedLetOnly_boxed_1902_ = lean_unbox(v_usedLetOnly_1897_);
v_res_1903_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__4(v_fvars_1896_, v_usedLetOnly_boxed_1902_, v_inst_1898_, v_toBind_1899_, v___f_1900_, v_a_1901_);
return v_res_1903_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__3(lean_object* v_fvars_1904_, uint8_t v_usedLetOnly_1905_, lean_object* v_inst_1906_, lean_object* v_toBind_1907_, lean_object* v___f_1908_, lean_object* v_a_1909_){
_start:
{
uint8_t v___x_1910_; uint8_t v___x_1911_; uint8_t v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; 
v___x_1910_ = 0;
v___x_1911_ = 1;
v___x_1912_ = 1;
v___x_1913_ = lean_box(v___x_1910_);
v___x_1914_ = lean_box(v_usedLetOnly_1905_);
v___x_1915_ = lean_box(v___x_1910_);
v___x_1916_ = lean_box(v___x_1911_);
v___x_1917_ = lean_box(v___x_1912_);
v___x_1918_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(v___x_1918_, 0, v_fvars_1904_);
lean_closure_set(v___x_1918_, 1, v_a_1909_);
lean_closure_set(v___x_1918_, 2, v___x_1913_);
lean_closure_set(v___x_1918_, 3, v___x_1914_);
lean_closure_set(v___x_1918_, 4, v___x_1915_);
lean_closure_set(v___x_1918_, 5, v___x_1916_);
lean_closure_set(v___x_1918_, 6, v___x_1917_);
v___x_1919_ = lean_apply_2(v_inst_1906_, lean_box(0), v___x_1918_);
v___x_1920_ = lean_apply_4(v_toBind_1907_, lean_box(0), lean_box(0), v___x_1919_, v___f_1908_);
return v___x_1920_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__3___boxed(lean_object* v_fvars_1921_, lean_object* v_usedLetOnly_1922_, lean_object* v_inst_1923_, lean_object* v_toBind_1924_, lean_object* v___f_1925_, lean_object* v_a_1926_){
_start:
{
uint8_t v_usedLetOnly_boxed_1927_; lean_object* v_res_1928_; 
v_usedLetOnly_boxed_1927_ = lean_unbox(v_usedLetOnly_1922_);
v_res_1928_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__3(v_fvars_1921_, v_usedLetOnly_boxed_1927_, v_inst_1923_, v_toBind_1924_, v___f_1925_, v_a_1926_);
return v_res_1928_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1(lean_object* v___x_1929_, lean_object* v___x_1930_, lean_object* v_binderName_1931_, uint8_t v_binderInfo_1932_, lean_object* v___f_1933_, lean_object* v_a_1934_, lean_object* v_a_1935_){
_start:
{
uint8_t v___x_1936_; lean_object* v___x_3508__overap_1937_; lean_object* v___x_1938_; 
v___x_1936_ = 0;
v___x_3508__overap_1937_ = l_Lean_Meta_withLocalDecl___redArg(v___x_1929_, v___x_1930_, v_binderName_1931_, v_binderInfo_1932_, v_a_1935_, v___f_1933_, v___x_1936_);
lean_inc(v_a_1934_);
v___x_1938_ = lean_apply_1(v___x_3508__overap_1937_, v_a_1934_);
return v___x_1938_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1___boxed(lean_object* v___x_1939_, lean_object* v___x_1940_, lean_object* v_binderName_1941_, lean_object* v_binderInfo_1942_, lean_object* v___f_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_){
_start:
{
uint8_t v_binderInfo_3697__boxed_1946_; lean_object* v_res_1947_; 
v_binderInfo_3697__boxed_1946_ = lean_unbox(v_binderInfo_1942_);
v_res_1947_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1(v___x_1939_, v___x_1940_, v_binderName_1941_, v_binderInfo_3697__boxed_1946_, v___f_1943_, v_a_1944_, v_a_1945_);
lean_dec(v_a_1944_);
return v_res_1947_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__3(lean_object* v_fvars_1948_, uint8_t v_usedLetOnly_1949_, lean_object* v_inst_1950_, lean_object* v_toBind_1951_, lean_object* v___f_1952_, lean_object* v_a_1953_){
_start:
{
uint8_t v___x_1954_; uint8_t v___x_1955_; uint8_t v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; 
v___x_1954_ = 0;
v___x_1955_ = 1;
v___x_1956_ = 1;
v___x_1957_ = lean_box(v___x_1954_);
v___x_1958_ = lean_box(v_usedLetOnly_1949_);
v___x_1959_ = lean_box(v___x_1955_);
v___x_1960_ = lean_box(v___x_1956_);
v___x_1961_ = lean_alloc_closure((void*)(l_Lean_Meta_mkForallFVars___boxed), 11, 6);
lean_closure_set(v___x_1961_, 0, v_fvars_1948_);
lean_closure_set(v___x_1961_, 1, v_a_1953_);
lean_closure_set(v___x_1961_, 2, v___x_1957_);
lean_closure_set(v___x_1961_, 3, v___x_1958_);
lean_closure_set(v___x_1961_, 4, v___x_1959_);
lean_closure_set(v___x_1961_, 5, v___x_1960_);
v___x_1962_ = lean_apply_2(v_inst_1950_, lean_box(0), v___x_1961_);
v___x_1963_ = lean_apply_4(v_toBind_1951_, lean_box(0), lean_box(0), v___x_1962_, v___f_1952_);
return v___x_1963_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__3___boxed(lean_object* v_fvars_1964_, lean_object* v_usedLetOnly_1965_, lean_object* v_inst_1966_, lean_object* v_toBind_1967_, lean_object* v___f_1968_, lean_object* v_a_1969_){
_start:
{
uint8_t v_usedLetOnly_boxed_1970_; lean_object* v_res_1971_; 
v_usedLetOnly_boxed_1970_ = lean_unbox(v_usedLetOnly_1965_);
v_res_1971_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__3(v_fvars_1964_, v_usedLetOnly_boxed_1970_, v_inst_1966_, v_toBind_1967_, v___f_1968_, v_a_1969_);
return v_res_1971_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__7(lean_object* v___f_1972_, lean_object* v___y_1973_, lean_object* v_a_1974_){
_start:
{
lean_object* v___x_1975_; 
lean_inc(v___y_1973_);
v___x_1975_ = lean_apply_2(v___f_1972_, v_a_1974_, v___y_1973_);
return v___x_1975_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__7___boxed(lean_object* v___f_1976_, lean_object* v___y_1977_, lean_object* v_a_1978_){
_start:
{
lean_object* v_res_1979_; 
v_res_1979_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__7(v___f_1976_, v___y_1977_, v_a_1978_);
lean_dec(v___y_1977_);
return v_res_1979_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1(lean_object* v_toApplicative_1980_, lean_object* v_acc_1981_, lean_object* v_next_1982_, lean_object* v_a_1983_){
_start:
{
lean_object* v_toPure_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; 
v_toPure_1984_ = lean_ctor_get(v_toApplicative_1980_, 1);
lean_inc(v_toPure_1984_);
lean_dec_ref(v_toApplicative_1980_);
v___x_1985_ = lean_array_fset(v_acc_1981_, v_next_1982_, v_a_1983_);
v___x_1986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1986_, 0, v___x_1985_);
v___x_1987_ = lean_apply_2(v_toPure_1984_, lean_box(0), v___x_1986_);
return v___x_1987_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1___boxed(lean_object* v_toApplicative_1988_, lean_object* v_acc_1989_, lean_object* v_next_1990_, lean_object* v_a_1991_){
_start:
{
lean_object* v_res_1992_; 
v_res_1992_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1(v_toApplicative_1988_, v_acc_1989_, v_next_1990_, v_a_1991_);
lean_dec(v_next_1990_);
return v_res_1992_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__2(lean_object* v_toApplicative_1993_, lean_object* v_next_1994_, lean_object* v_G_1995_, lean_object* v___y_1996_, lean_object* v_a_1997_){
_start:
{
if (lean_obj_tag(v_a_1997_) == 0)
{
lean_object* v_a_1998_; lean_object* v_toPure_1999_; lean_object* v___x_2000_; 
lean_dec(v_G_1995_);
v_a_1998_ = lean_ctor_get(v_a_1997_, 0);
lean_inc(v_a_1998_);
lean_dec_ref_known(v_a_1997_, 1);
v_toPure_1999_ = lean_ctor_get(v_toApplicative_1993_, 1);
lean_inc(v_toPure_1999_);
lean_dec_ref(v_toApplicative_1993_);
v___x_2000_ = lean_apply_2(v_toPure_1999_, lean_box(0), v_a_1998_);
return v___x_2000_;
}
else
{
lean_object* v_a_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; 
lean_dec_ref(v_toApplicative_1993_);
v_a_2001_ = lean_ctor_get(v_a_1997_, 0);
lean_inc(v_a_2001_);
lean_dec_ref_known(v_a_1997_, 1);
v___x_2002_ = lean_unsigned_to_nat(1u);
v___x_2003_ = lean_nat_add(v_next_1994_, v___x_2002_);
lean_inc(v___y_1996_);
v___x_2004_ = lean_apply_5(v_G_1995_, v___x_2003_, v_a_2001_, lean_box(0), lean_box(0), v___y_1996_);
return v___x_2004_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__2___boxed(lean_object* v_toApplicative_2005_, lean_object* v_next_2006_, lean_object* v_G_2007_, lean_object* v___y_2008_, lean_object* v_a_2009_){
_start:
{
lean_object* v_res_2010_; 
v_res_2010_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__2(v_toApplicative_2005_, v_next_2006_, v_G_2007_, v___y_2008_, v_a_2009_);
lean_dec(v___y_2008_);
lean_dec(v_next_2006_);
return v_res_2010_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5(lean_object* v_f_2011_, lean_object* v_inst_2012_, lean_object* v_inst_2013_, lean_object* v_inst_2014_, lean_object* v_pre_2015_, lean_object* v_post_2016_, uint8_t v_usedLetOnly_2017_, uint8_t v_skipConstInApp_2018_, uint8_t v_skipInstances_2019_, lean_object* v_x_2020_, lean_object* v_x_2021_, lean_object* v___y_2022_, lean_object* v_a_2023_){
_start:
{
lean_object* v___x_2024_; lean_object* v___x_2025_; 
v___x_2024_ = l_Lean_mkAppN(v_f_2011_, v_a_2023_);
v___x_2025_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2012_, v_inst_2013_, v_inst_2014_, v_pre_2015_, v_post_2016_, v_usedLetOnly_2017_, v_skipConstInApp_2018_, v_skipInstances_2019_, v_x_2020_, v_x_2021_, v___x_2024_, v___y_2022_);
return v___x_2025_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5___boxed(lean_object* v_f_2026_, lean_object* v_inst_2027_, lean_object* v_inst_2028_, lean_object* v_inst_2029_, lean_object* v_pre_2030_, lean_object* v_post_2031_, lean_object* v_usedLetOnly_2032_, lean_object* v_skipConstInApp_2033_, lean_object* v_skipInstances_2034_, lean_object* v_x_2035_, lean_object* v_x_2036_, lean_object* v___y_2037_, lean_object* v_a_2038_){
_start:
{
uint8_t v_usedLetOnly_boxed_2039_; uint8_t v_skipConstInApp_boxed_2040_; uint8_t v_skipInstances_boxed_2041_; lean_object* v_res_2042_; 
v_usedLetOnly_boxed_2039_ = lean_unbox(v_usedLetOnly_2032_);
v_skipConstInApp_boxed_2040_ = lean_unbox(v_skipConstInApp_2033_);
v_skipInstances_boxed_2041_ = lean_unbox(v_skipInstances_2034_);
v_res_2042_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5(v_f_2026_, v_inst_2027_, v_inst_2028_, v_inst_2029_, v_pre_2030_, v_post_2031_, v_usedLetOnly_boxed_2039_, v_skipConstInApp_boxed_2040_, v_skipInstances_boxed_2041_, v_x_2035_, v_x_2036_, v___y_2037_, v_a_2038_);
lean_dec_ref(v_a_2038_);
lean_dec(v___y_2037_);
return v_res_2042_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___boxed(lean_object* v_inst_2043_, lean_object* v_inst_2044_, lean_object* v_inst_2045_, lean_object* v_pre_2046_, lean_object* v_post_2047_, lean_object* v_usedLetOnly_2048_, lean_object* v_skipConstInApp_2049_, lean_object* v_skipInstances_2050_, lean_object* v_x_2051_, lean_object* v_x_2052_, lean_object* v_e_2053_, lean_object* v_a_2054_){
_start:
{
uint8_t v_usedLetOnly_boxed_2055_; uint8_t v_skipConstInApp_boxed_2056_; uint8_t v_skipInstances_boxed_2057_; lean_object* v_res_2058_; 
v_usedLetOnly_boxed_2055_ = lean_unbox(v_usedLetOnly_2048_);
v_skipConstInApp_boxed_2056_ = lean_unbox(v_skipConstInApp_2049_);
v_skipInstances_boxed_2057_ = lean_unbox(v_skipInstances_2050_);
v_res_2058_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2043_, v_inst_2044_, v_inst_2045_, v_pre_2046_, v_post_2047_, v_usedLetOnly_boxed_2055_, v_skipConstInApp_boxed_2056_, v_skipInstances_boxed_2057_, v_x_2051_, v_x_2052_, v_e_2053_, v_a_2054_);
lean_dec(v_a_2054_);
return v_res_2058_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__4(lean_object* v___x_2059_, lean_object* v_toApplicative_2060_, lean_object* v_toBind_2061_, lean_object* v___f_2062_, lean_object* v_paramInfo_2063_, lean_object* v_inst_2064_, lean_object* v_inst_2065_, lean_object* v_inst_2066_, lean_object* v_pre_2067_, lean_object* v_post_2068_, uint8_t v_usedLetOnly_2069_, uint8_t v_skipConstInApp_2070_, uint8_t v_skipInstances_2071_, lean_object* v_x_2072_, lean_object* v_x_2073_, lean_object* v_next_2074_, lean_object* v_acc_2075_, lean_object* v_h_2076_, lean_object* v_G_2077_, lean_object* v___y_2078_){
_start:
{
uint8_t v___x_2079_; 
v___x_2079_ = lean_nat_dec_lt(v_next_2074_, v___x_2059_);
if (v___x_2079_ == 0)
{
lean_object* v_toPure_2080_; lean_object* v___x_2081_; 
lean_dec(v_G_2077_);
lean_dec(v_next_2074_);
lean_dec(v_x_2073_);
lean_dec(v_post_2068_);
lean_dec(v_pre_2067_);
lean_dec_ref(v_inst_2066_);
lean_dec(v_inst_2065_);
lean_dec_ref(v_inst_2064_);
lean_dec(v___f_2062_);
lean_dec(v_toBind_2061_);
v_toPure_2080_ = lean_ctor_get(v_toApplicative_2060_, 1);
lean_inc(v_toPure_2080_);
lean_dec_ref(v_toApplicative_2060_);
v___x_2081_ = lean_apply_2(v_toPure_2080_, lean_box(0), v_acc_2075_);
return v___x_2081_;
}
else
{
lean_object* v___f_2082_; lean_object* v___y_2084_; lean_object* v___x_2087_; lean_object* v___x_2088_; uint8_t v___x_2089_; 
lean_inc(v___y_2078_);
lean_inc(v_next_2074_);
lean_inc_ref(v_toApplicative_2060_);
v___f_2082_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__2___boxed), 5, 4);
lean_closure_set(v___f_2082_, 0, v_toApplicative_2060_);
lean_closure_set(v___f_2082_, 1, v_next_2074_);
lean_closure_set(v___f_2082_, 2, v_G_2077_);
lean_closure_set(v___f_2082_, 3, v___y_2078_);
v___x_2087_ = lean_array_fget_borrowed(v_acc_2075_, v_next_2074_);
v___x_2088_ = lean_array_get_size(v_paramInfo_2063_);
v___x_2089_ = lean_nat_dec_lt(v_next_2074_, v___x_2088_);
if (v___x_2089_ == 0)
{
lean_object* v___f_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; 
lean_inc(v___x_2087_);
v___f_2090_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2090_, 0, v_toApplicative_2060_);
lean_closure_set(v___f_2090_, 1, v_acc_2075_);
lean_closure_set(v___f_2090_, 2, v_next_2074_);
v___x_2091_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2064_, v_inst_2065_, v_inst_2066_, v_pre_2067_, v_post_2068_, v_usedLetOnly_2069_, v_skipConstInApp_2070_, v_skipInstances_2071_, v_x_2072_, v_x_2073_, v___x_2087_, v___y_2078_);
lean_inc(v_toBind_2061_);
v___x_2092_ = lean_apply_4(v_toBind_2061_, lean_box(0), lean_box(0), v___x_2091_, v___f_2090_);
v___y_2084_ = v___x_2092_;
goto v___jp_2083_;
}
else
{
lean_object* v___x_2093_; uint8_t v_isInstance_2094_; 
v___x_2093_ = lean_array_fget_borrowed(v_paramInfo_2063_, v_next_2074_);
v_isInstance_2094_ = lean_ctor_get_uint8(v___x_2093_, sizeof(void*)*1 + 4);
if (v_isInstance_2094_ == 0)
{
lean_object* v___f_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; 
lean_inc(v___x_2087_);
v___f_2095_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2095_, 0, v_toApplicative_2060_);
lean_closure_set(v___f_2095_, 1, v_acc_2075_);
lean_closure_set(v___f_2095_, 2, v_next_2074_);
v___x_2096_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2064_, v_inst_2065_, v_inst_2066_, v_pre_2067_, v_post_2068_, v_usedLetOnly_2069_, v_skipConstInApp_2070_, v_skipInstances_2071_, v_x_2072_, v_x_2073_, v___x_2087_, v___y_2078_);
lean_inc(v_toBind_2061_);
v___x_2097_ = lean_apply_4(v_toBind_2061_, lean_box(0), lean_box(0), v___x_2096_, v___f_2095_);
v___y_2084_ = v___x_2097_;
goto v___jp_2083_;
}
else
{
lean_object* v_toPure_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; 
lean_dec(v_next_2074_);
lean_dec(v_x_2073_);
lean_dec(v_post_2068_);
lean_dec(v_pre_2067_);
lean_dec_ref(v_inst_2066_);
lean_dec(v_inst_2065_);
lean_dec_ref(v_inst_2064_);
v_toPure_2098_ = lean_ctor_get(v_toApplicative_2060_, 1);
lean_inc(v_toPure_2098_);
lean_dec_ref(v_toApplicative_2060_);
v___x_2099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2099_, 0, v_acc_2075_);
v___x_2100_ = lean_apply_2(v_toPure_2098_, lean_box(0), v___x_2099_);
v___y_2084_ = v___x_2100_;
goto v___jp_2083_;
}
}
v___jp_2083_:
{
lean_object* v___x_2085_; lean_object* v___x_2086_; 
lean_inc(v_toBind_2061_);
v___x_2085_ = lean_apply_4(v_toBind_2061_, lean_box(0), lean_box(0), v___y_2084_, v___f_2062_);
v___x_2086_ = lean_apply_4(v_toBind_2061_, lean_box(0), lean_box(0), v___x_2085_, v___f_2082_);
return v___x_2086_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__4___boxed(lean_object** _args){
lean_object* v___x_2101_ = _args[0];
lean_object* v_toApplicative_2102_ = _args[1];
lean_object* v_toBind_2103_ = _args[2];
lean_object* v___f_2104_ = _args[3];
lean_object* v_paramInfo_2105_ = _args[4];
lean_object* v_inst_2106_ = _args[5];
lean_object* v_inst_2107_ = _args[6];
lean_object* v_inst_2108_ = _args[7];
lean_object* v_pre_2109_ = _args[8];
lean_object* v_post_2110_ = _args[9];
lean_object* v_usedLetOnly_2111_ = _args[10];
lean_object* v_skipConstInApp_2112_ = _args[11];
lean_object* v_skipInstances_2113_ = _args[12];
lean_object* v_x_2114_ = _args[13];
lean_object* v_x_2115_ = _args[14];
lean_object* v_next_2116_ = _args[15];
lean_object* v_acc_2117_ = _args[16];
lean_object* v_h_2118_ = _args[17];
lean_object* v_G_2119_ = _args[18];
lean_object* v___y_2120_ = _args[19];
_start:
{
uint8_t v_usedLetOnly_boxed_2121_; uint8_t v_skipConstInApp_boxed_2122_; uint8_t v_skipInstances_boxed_2123_; lean_object* v_res_2124_; 
v_usedLetOnly_boxed_2121_ = lean_unbox(v_usedLetOnly_2111_);
v_skipConstInApp_boxed_2122_ = lean_unbox(v_skipConstInApp_2112_);
v_skipInstances_boxed_2123_ = lean_unbox(v_skipInstances_2113_);
v_res_2124_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__4(v___x_2101_, v_toApplicative_2102_, v_toBind_2103_, v___f_2104_, v_paramInfo_2105_, v_inst_2106_, v_inst_2107_, v_inst_2108_, v_pre_2109_, v_post_2110_, v_usedLetOnly_boxed_2121_, v_skipConstInApp_boxed_2122_, v_skipInstances_boxed_2123_, v_x_2114_, v_x_2115_, v_next_2116_, v_acc_2117_, v_h_2118_, v_G_2119_, v___y_2120_);
lean_dec(v___y_2120_);
lean_dec_ref(v_paramInfo_2105_);
lean_dec(v___x_2101_);
return v_res_2124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__3(lean_object* v___x_2125_, lean_object* v_toApplicative_2126_, lean_object* v_toBind_2127_, lean_object* v___f_2128_, lean_object* v_inst_2129_, lean_object* v_inst_2130_, lean_object* v_inst_2131_, lean_object* v_pre_2132_, lean_object* v_post_2133_, uint8_t v_usedLetOnly_2134_, uint8_t v_skipConstInApp_2135_, uint8_t v_skipInstances_2136_, lean_object* v_x_2137_, lean_object* v_x_2138_, lean_object* v_args_2139_, lean_object* v___y_2140_, lean_object* v___f_2141_, lean_object* v_a_2142_){
_start:
{
lean_object* v_paramInfo_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___f_2148_; lean_object* v___x_3268__overap_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; 
v_paramInfo_2143_ = lean_ctor_get(v_a_2142_, 0);
lean_inc_ref(v_paramInfo_2143_);
lean_dec_ref(v_a_2142_);
v___x_2144_ = lean_unsigned_to_nat(0u);
v___x_2145_ = lean_box(v_usedLetOnly_2134_);
v___x_2146_ = lean_box(v_skipConstInApp_2135_);
v___x_2147_ = lean_box(v_skipInstances_2136_);
lean_inc(v_toBind_2127_);
v___f_2148_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__4___boxed), 20, 15);
lean_closure_set(v___f_2148_, 0, v___x_2125_);
lean_closure_set(v___f_2148_, 1, v_toApplicative_2126_);
lean_closure_set(v___f_2148_, 2, v_toBind_2127_);
lean_closure_set(v___f_2148_, 3, v___f_2128_);
lean_closure_set(v___f_2148_, 4, v_paramInfo_2143_);
lean_closure_set(v___f_2148_, 5, v_inst_2129_);
lean_closure_set(v___f_2148_, 6, v_inst_2130_);
lean_closure_set(v___f_2148_, 7, v_inst_2131_);
lean_closure_set(v___f_2148_, 8, v_pre_2132_);
lean_closure_set(v___f_2148_, 9, v_post_2133_);
lean_closure_set(v___f_2148_, 10, v___x_2145_);
lean_closure_set(v___f_2148_, 11, v___x_2146_);
lean_closure_set(v___f_2148_, 12, v___x_2147_);
lean_closure_set(v___f_2148_, 13, v_x_2137_);
lean_closure_set(v___f_2148_, 14, v_x_2138_);
v___x_3268__overap_2149_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_2148_, v___x_2144_, v_args_2139_, lean_box(0));
lean_inc(v___y_2140_);
v___x_2150_ = lean_apply_1(v___x_3268__overap_2149_, v___y_2140_);
v___x_2151_ = lean_apply_4(v_toBind_2127_, lean_box(0), lean_box(0), v___x_2150_, v___f_2141_);
return v___x_2151_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__3___boxed(lean_object** _args){
lean_object* v___x_2152_ = _args[0];
lean_object* v_toApplicative_2153_ = _args[1];
lean_object* v_toBind_2154_ = _args[2];
lean_object* v___f_2155_ = _args[3];
lean_object* v_inst_2156_ = _args[4];
lean_object* v_inst_2157_ = _args[5];
lean_object* v_inst_2158_ = _args[6];
lean_object* v_pre_2159_ = _args[7];
lean_object* v_post_2160_ = _args[8];
lean_object* v_usedLetOnly_2161_ = _args[9];
lean_object* v_skipConstInApp_2162_ = _args[10];
lean_object* v_skipInstances_2163_ = _args[11];
lean_object* v_x_2164_ = _args[12];
lean_object* v_x_2165_ = _args[13];
lean_object* v_args_2166_ = _args[14];
lean_object* v___y_2167_ = _args[15];
lean_object* v___f_2168_ = _args[16];
lean_object* v_a_2169_ = _args[17];
_start:
{
uint8_t v_usedLetOnly_boxed_2170_; uint8_t v_skipConstInApp_boxed_2171_; uint8_t v_skipInstances_boxed_2172_; lean_object* v_res_2173_; 
v_usedLetOnly_boxed_2170_ = lean_unbox(v_usedLetOnly_2161_);
v_skipConstInApp_boxed_2171_ = lean_unbox(v_skipConstInApp_2162_);
v_skipInstances_boxed_2172_ = lean_unbox(v_skipInstances_2163_);
v_res_2173_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__3(v___x_2152_, v_toApplicative_2153_, v_toBind_2154_, v___f_2155_, v_inst_2156_, v_inst_2157_, v_inst_2158_, v_pre_2159_, v_post_2160_, v_usedLetOnly_boxed_2170_, v_skipConstInApp_boxed_2171_, v_skipInstances_boxed_2172_, v_x_2164_, v_x_2165_, v_args_2166_, v___y_2167_, v___f_2168_, v_a_2169_);
lean_dec(v___y_2167_);
return v_res_2173_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__6(uint8_t v_skipInstances_2174_, lean_object* v_inst_2175_, lean_object* v_inst_2176_, lean_object* v_inst_2177_, lean_object* v_pre_2178_, lean_object* v_post_2179_, uint8_t v_usedLetOnly_2180_, uint8_t v_skipConstInApp_2181_, lean_object* v_x_2182_, lean_object* v_x_2183_, lean_object* v_args_2184_, lean_object* v___x_2185_, lean_object* v_toBind_2186_, lean_object* v_toApplicative_2187_, lean_object* v___f_2188_, lean_object* v_f_2189_, lean_object* v___y_2190_){
_start:
{
if (v_skipInstances_2174_ == 0)
{
lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___f_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; size_t v_sz_2199_; size_t v___x_2200_; lean_object* v___x_3281__overap_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; 
lean_dec(v___f_2188_);
lean_dec_ref(v_toApplicative_2187_);
v___x_2191_ = lean_box(v_usedLetOnly_2180_);
v___x_2192_ = lean_box(v_skipConstInApp_2181_);
v___x_2193_ = lean_box(v_skipInstances_2174_);
lean_inc_n(v___y_2190_, 2);
lean_inc(v_x_2183_);
lean_inc(v_post_2179_);
lean_inc(v_pre_2178_);
lean_inc_ref(v_inst_2177_);
lean_inc(v_inst_2176_);
lean_inc_ref(v_inst_2175_);
v___f_2194_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5___boxed), 13, 12);
lean_closure_set(v___f_2194_, 0, v_f_2189_);
lean_closure_set(v___f_2194_, 1, v_inst_2175_);
lean_closure_set(v___f_2194_, 2, v_inst_2176_);
lean_closure_set(v___f_2194_, 3, v_inst_2177_);
lean_closure_set(v___f_2194_, 4, v_pre_2178_);
lean_closure_set(v___f_2194_, 5, v_post_2179_);
lean_closure_set(v___f_2194_, 6, v___x_2191_);
lean_closure_set(v___f_2194_, 7, v___x_2192_);
lean_closure_set(v___f_2194_, 8, v___x_2193_);
lean_closure_set(v___f_2194_, 9, v_x_2182_);
lean_closure_set(v___f_2194_, 10, v_x_2183_);
lean_closure_set(v___f_2194_, 11, v___y_2190_);
v___x_2195_ = lean_box(v_usedLetOnly_2180_);
v___x_2196_ = lean_box(v_skipConstInApp_2181_);
v___x_2197_ = lean_box(v_skipInstances_2174_);
v___x_2198_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___boxed), 12, 10);
lean_closure_set(v___x_2198_, 0, v_inst_2175_);
lean_closure_set(v___x_2198_, 1, v_inst_2176_);
lean_closure_set(v___x_2198_, 2, v_inst_2177_);
lean_closure_set(v___x_2198_, 3, v_pre_2178_);
lean_closure_set(v___x_2198_, 4, v_post_2179_);
lean_closure_set(v___x_2198_, 5, v___x_2195_);
lean_closure_set(v___x_2198_, 6, v___x_2196_);
lean_closure_set(v___x_2198_, 7, v___x_2197_);
lean_closure_set(v___x_2198_, 8, v_x_2182_);
lean_closure_set(v___x_2198_, 9, v_x_2183_);
v_sz_2199_ = lean_array_size(v_args_2184_);
v___x_2200_ = ((size_t)0ULL);
v___x_3281__overap_2201_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2185_, v___x_2198_, v_sz_2199_, v___x_2200_, v_args_2184_);
v___x_2202_ = lean_apply_1(v___x_3281__overap_2201_, v___y_2190_);
v___x_2203_ = lean_apply_4(v_toBind_2186_, lean_box(0), lean_box(0), v___x_2202_, v___f_2194_);
return v___x_2203_;
}
else
{
lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___f_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___f_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; 
lean_dec_ref(v___x_2185_);
v___x_2204_ = lean_box(v_usedLetOnly_2180_);
v___x_2205_ = lean_box(v_skipConstInApp_2181_);
v___x_2206_ = lean_box(v_skipInstances_2174_);
lean_inc_n(v___y_2190_, 2);
lean_inc(v_x_2183_);
lean_inc(v_post_2179_);
lean_inc(v_pre_2178_);
lean_inc_ref(v_inst_2177_);
lean_inc_n(v_inst_2176_, 2);
lean_inc_ref(v_inst_2175_);
lean_inc_ref(v_f_2189_);
v___f_2207_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5___boxed), 13, 12);
lean_closure_set(v___f_2207_, 0, v_f_2189_);
lean_closure_set(v___f_2207_, 1, v_inst_2175_);
lean_closure_set(v___f_2207_, 2, v_inst_2176_);
lean_closure_set(v___f_2207_, 3, v_inst_2177_);
lean_closure_set(v___f_2207_, 4, v_pre_2178_);
lean_closure_set(v___f_2207_, 5, v_post_2179_);
lean_closure_set(v___f_2207_, 6, v___x_2204_);
lean_closure_set(v___f_2207_, 7, v___x_2205_);
lean_closure_set(v___f_2207_, 8, v___x_2206_);
lean_closure_set(v___f_2207_, 9, v_x_2182_);
lean_closure_set(v___f_2207_, 10, v_x_2183_);
lean_closure_set(v___f_2207_, 11, v___y_2190_);
v___x_2208_ = lean_array_get_size(v_args_2184_);
v___x_2209_ = lean_box(v_usedLetOnly_2180_);
v___x_2210_ = lean_box(v_skipConstInApp_2181_);
v___x_2211_ = lean_box(v_skipInstances_2174_);
lean_inc(v_toBind_2186_);
v___f_2212_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__3___boxed), 18, 17);
lean_closure_set(v___f_2212_, 0, v___x_2208_);
lean_closure_set(v___f_2212_, 1, v_toApplicative_2187_);
lean_closure_set(v___f_2212_, 2, v_toBind_2186_);
lean_closure_set(v___f_2212_, 3, v___f_2188_);
lean_closure_set(v___f_2212_, 4, v_inst_2175_);
lean_closure_set(v___f_2212_, 5, v_inst_2176_);
lean_closure_set(v___f_2212_, 6, v_inst_2177_);
lean_closure_set(v___f_2212_, 7, v_pre_2178_);
lean_closure_set(v___f_2212_, 8, v_post_2179_);
lean_closure_set(v___f_2212_, 9, v___x_2209_);
lean_closure_set(v___f_2212_, 10, v___x_2210_);
lean_closure_set(v___f_2212_, 11, v___x_2211_);
lean_closure_set(v___f_2212_, 12, v_x_2182_);
lean_closure_set(v___f_2212_, 13, v_x_2183_);
lean_closure_set(v___f_2212_, 14, v_args_2184_);
lean_closure_set(v___f_2212_, 15, v___y_2190_);
lean_closure_set(v___f_2212_, 16, v___f_2207_);
v___x_2213_ = lean_alloc_closure((void*)(l_Lean_Meta_getFunInfoNArgs___boxed), 7, 2);
lean_closure_set(v___x_2213_, 0, v_f_2189_);
lean_closure_set(v___x_2213_, 1, v___x_2208_);
v___x_2214_ = lean_apply_2(v_inst_2176_, lean_box(0), v___x_2213_);
v___x_2215_ = lean_apply_4(v_toBind_2186_, lean_box(0), lean_box(0), v___x_2214_, v___f_2212_);
return v___x_2215_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__6___boxed(lean_object** _args){
lean_object* v_skipInstances_2216_ = _args[0];
lean_object* v_inst_2217_ = _args[1];
lean_object* v_inst_2218_ = _args[2];
lean_object* v_inst_2219_ = _args[3];
lean_object* v_pre_2220_ = _args[4];
lean_object* v_post_2221_ = _args[5];
lean_object* v_usedLetOnly_2222_ = _args[6];
lean_object* v_skipConstInApp_2223_ = _args[7];
lean_object* v_x_2224_ = _args[8];
lean_object* v_x_2225_ = _args[9];
lean_object* v_args_2226_ = _args[10];
lean_object* v___x_2227_ = _args[11];
lean_object* v_toBind_2228_ = _args[12];
lean_object* v_toApplicative_2229_ = _args[13];
lean_object* v___f_2230_ = _args[14];
lean_object* v_f_2231_ = _args[15];
lean_object* v___y_2232_ = _args[16];
_start:
{
uint8_t v_skipInstances_boxed_2233_; uint8_t v_usedLetOnly_boxed_2234_; uint8_t v_skipConstInApp_boxed_2235_; lean_object* v_res_2236_; 
v_skipInstances_boxed_2233_ = lean_unbox(v_skipInstances_2216_);
v_usedLetOnly_boxed_2234_ = lean_unbox(v_usedLetOnly_2222_);
v_skipConstInApp_boxed_2235_ = lean_unbox(v_skipConstInApp_2223_);
v_res_2236_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__6(v_skipInstances_boxed_2233_, v_inst_2217_, v_inst_2218_, v_inst_2219_, v_pre_2220_, v_post_2221_, v_usedLetOnly_boxed_2234_, v_skipConstInApp_boxed_2235_, v_x_2224_, v_x_2225_, v_args_2226_, v___x_2227_, v_toBind_2228_, v_toApplicative_2229_, v___f_2230_, v_f_2231_, v___y_2232_);
lean_dec(v___y_2232_);
return v_res_2236_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__9(uint8_t v_skipInstances_2237_, lean_object* v_inst_2238_, lean_object* v_inst_2239_, lean_object* v_inst_2240_, lean_object* v_pre_2241_, lean_object* v_post_2242_, uint8_t v_usedLetOnly_2243_, uint8_t v_skipConstInApp_2244_, lean_object* v_x_2245_, lean_object* v_x_2246_, lean_object* v___x_2247_, lean_object* v_toBind_2248_, lean_object* v_toApplicative_2249_, lean_object* v___f_2250_, lean_object* v_f_2251_, lean_object* v_args_2252_, lean_object* v___y_2253_){
_start:
{
lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___f_2257_; lean_object* v___f_2258_; 
v___x_2254_ = lean_box(v_skipInstances_2237_);
v___x_2255_ = lean_box(v_usedLetOnly_2243_);
v___x_2256_ = lean_box(v_skipConstInApp_2244_);
lean_inc_ref(v_toApplicative_2249_);
lean_inc(v_toBind_2248_);
lean_inc(v_x_2246_);
lean_inc(v_post_2242_);
lean_inc(v_pre_2241_);
lean_inc_ref(v_inst_2240_);
lean_inc(v_inst_2239_);
lean_inc_ref(v_inst_2238_);
v___f_2257_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__6___boxed), 17, 15);
lean_closure_set(v___f_2257_, 0, v___x_2254_);
lean_closure_set(v___f_2257_, 1, v_inst_2238_);
lean_closure_set(v___f_2257_, 2, v_inst_2239_);
lean_closure_set(v___f_2257_, 3, v_inst_2240_);
lean_closure_set(v___f_2257_, 4, v_pre_2241_);
lean_closure_set(v___f_2257_, 5, v_post_2242_);
lean_closure_set(v___f_2257_, 6, v___x_2255_);
lean_closure_set(v___f_2257_, 7, v___x_2256_);
lean_closure_set(v___f_2257_, 8, v_x_2245_);
lean_closure_set(v___f_2257_, 9, v_x_2246_);
lean_closure_set(v___f_2257_, 10, v_args_2252_);
lean_closure_set(v___f_2257_, 11, v___x_2247_);
lean_closure_set(v___f_2257_, 12, v_toBind_2248_);
lean_closure_set(v___f_2257_, 13, v_toApplicative_2249_);
lean_closure_set(v___f_2257_, 14, v___f_2250_);
lean_inc(v___y_2253_);
v___f_2258_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__7___boxed), 3, 2);
lean_closure_set(v___f_2258_, 0, v___f_2257_);
lean_closure_set(v___f_2258_, 1, v___y_2253_);
if (v_skipConstInApp_2244_ == 0)
{
lean_dec_ref(v_toApplicative_2249_);
goto v___jp_2259_;
}
else
{
uint8_t v___x_2262_; 
v___x_2262_ = l_Lean_Expr_isConst(v_f_2251_);
if (v___x_2262_ == 0)
{
lean_dec_ref(v_toApplicative_2249_);
goto v___jp_2259_;
}
else
{
lean_object* v_toPure_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; 
lean_dec(v_x_2246_);
lean_dec(v_post_2242_);
lean_dec(v_pre_2241_);
lean_dec_ref(v_inst_2240_);
lean_dec(v_inst_2239_);
lean_dec_ref(v_inst_2238_);
v_toPure_2263_ = lean_ctor_get(v_toApplicative_2249_, 1);
lean_inc(v_toPure_2263_);
lean_dec_ref(v_toApplicative_2249_);
v___x_2264_ = lean_apply_2(v_toPure_2263_, lean_box(0), v_f_2251_);
v___x_2265_ = lean_apply_4(v_toBind_2248_, lean_box(0), lean_box(0), v___x_2264_, v___f_2258_);
return v___x_2265_;
}
}
v___jp_2259_:
{
lean_object* v___x_2260_; lean_object* v___x_2261_; 
v___x_2260_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2238_, v_inst_2239_, v_inst_2240_, v_pre_2241_, v_post_2242_, v_usedLetOnly_2243_, v_skipConstInApp_2244_, v_skipInstances_2237_, v_x_2245_, v_x_2246_, v_f_2251_, v___y_2253_);
v___x_2261_ = lean_apply_4(v_toBind_2248_, lean_box(0), lean_box(0), v___x_2260_, v___f_2258_);
return v___x_2261_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__9___boxed(lean_object** _args){
lean_object* v_skipInstances_2266_ = _args[0];
lean_object* v_inst_2267_ = _args[1];
lean_object* v_inst_2268_ = _args[2];
lean_object* v_inst_2269_ = _args[3];
lean_object* v_pre_2270_ = _args[4];
lean_object* v_post_2271_ = _args[5];
lean_object* v_usedLetOnly_2272_ = _args[6];
lean_object* v_skipConstInApp_2273_ = _args[7];
lean_object* v_x_2274_ = _args[8];
lean_object* v_x_2275_ = _args[9];
lean_object* v___x_2276_ = _args[10];
lean_object* v_toBind_2277_ = _args[11];
lean_object* v_toApplicative_2278_ = _args[12];
lean_object* v___f_2279_ = _args[13];
lean_object* v_f_2280_ = _args[14];
lean_object* v_args_2281_ = _args[15];
lean_object* v___y_2282_ = _args[16];
_start:
{
uint8_t v_skipInstances_boxed_2283_; uint8_t v_usedLetOnly_boxed_2284_; uint8_t v_skipConstInApp_boxed_2285_; lean_object* v_res_2286_; 
v_skipInstances_boxed_2283_ = lean_unbox(v_skipInstances_2266_);
v_usedLetOnly_boxed_2284_ = lean_unbox(v_usedLetOnly_2272_);
v_skipConstInApp_boxed_2285_ = lean_unbox(v_skipConstInApp_2273_);
v_res_2286_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__9(v_skipInstances_boxed_2283_, v_inst_2267_, v_inst_2268_, v_inst_2269_, v_pre_2270_, v_post_2271_, v_usedLetOnly_boxed_2284_, v_skipConstInApp_boxed_2285_, v_x_2274_, v_x_2275_, v___x_2276_, v_toBind_2277_, v_toApplicative_2278_, v___f_2279_, v_f_2280_, v_args_2281_, v___y_2282_);
lean_dec(v___y_2282_);
return v_res_2286_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__0(lean_object* v_fvars_2289_, lean_object* v_inst_2290_, lean_object* v_inst_2291_, lean_object* v_inst_2292_, lean_object* v_pre_2293_, lean_object* v_post_2294_, uint8_t v_usedLetOnly_2295_, uint8_t v_skipConstInApp_2296_, uint8_t v_skipInstances_2297_, lean_object* v_x_2298_, lean_object* v_x_2299_, lean_object* v_body_2300_, lean_object* v_x_2301_, lean_object* v___y_2302_){
_start:
{
lean_object* v___x_2303_; lean_object* v___x_2304_; 
v___x_2303_ = lean_array_push(v_fvars_2289_, v_x_2301_);
v___x_2304_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(v_inst_2290_, v_inst_2291_, v_inst_2292_, v_pre_2293_, v_post_2294_, v_usedLetOnly_2295_, v_skipConstInApp_2296_, v_skipInstances_2297_, v_x_2298_, v_x_2299_, v___x_2303_, v_body_2300_, v___y_2302_);
return v___x_2304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__0___boxed(lean_object* v_fvars_2305_, lean_object* v_inst_2306_, lean_object* v_inst_2307_, lean_object* v_inst_2308_, lean_object* v_pre_2309_, lean_object* v_post_2310_, lean_object* v_usedLetOnly_2311_, lean_object* v_skipConstInApp_2312_, lean_object* v_skipInstances_2313_, lean_object* v_x_2314_, lean_object* v_x_2315_, lean_object* v_body_2316_, lean_object* v_x_2317_, lean_object* v___y_2318_){
_start:
{
uint8_t v_usedLetOnly_boxed_2319_; uint8_t v_skipConstInApp_boxed_2320_; uint8_t v_skipInstances_boxed_2321_; lean_object* v_res_2322_; 
v_usedLetOnly_boxed_2319_ = lean_unbox(v_usedLetOnly_2311_);
v_skipConstInApp_boxed_2320_ = lean_unbox(v_skipConstInApp_2312_);
v_skipInstances_boxed_2321_ = lean_unbox(v_skipInstances_2313_);
v_res_2322_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__0(v_fvars_2305_, v_inst_2306_, v_inst_2307_, v_inst_2308_, v_pre_2309_, v_post_2310_, v_usedLetOnly_boxed_2319_, v_skipConstInApp_boxed_2320_, v_skipInstances_boxed_2321_, v_x_2314_, v_x_2315_, v_body_2316_, v_x_2317_, v___y_2318_);
lean_dec(v___y_2318_);
return v_res_2322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3___boxed(lean_object* v_inst_2323_, lean_object* v_inst_2324_, lean_object* v_inst_2325_, lean_object* v_pre_2326_, lean_object* v_post_2327_, lean_object* v_usedLetOnly_2328_, lean_object* v_skipConstInApp_2329_, lean_object* v_skipInstances_2330_, lean_object* v_x_2331_, lean_object* v_x_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_){
_start:
{
uint8_t v_usedLetOnly_boxed_2335_; uint8_t v_skipConstInApp_boxed_2336_; uint8_t v_skipInstances_boxed_2337_; lean_object* v_res_2338_; 
v_usedLetOnly_boxed_2335_ = lean_unbox(v_usedLetOnly_2328_);
v_skipConstInApp_boxed_2336_ = lean_unbox(v_skipConstInApp_2329_);
v_skipInstances_boxed_2337_ = lean_unbox(v_skipInstances_2330_);
v_res_2338_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3(v_inst_2323_, v_inst_2324_, v_inst_2325_, v_pre_2326_, v_post_2327_, v_usedLetOnly_boxed_2335_, v_skipConstInApp_boxed_2336_, v_skipInstances_boxed_2337_, v_x_2331_, v_x_2332_, v_a_2333_, v_a_2334_);
lean_dec(v_a_2333_);
return v_res_2338_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(lean_object* v_inst_2339_, lean_object* v_inst_2340_, lean_object* v_inst_2341_, lean_object* v_pre_2342_, lean_object* v_post_2343_, uint8_t v_usedLetOnly_2344_, uint8_t v_skipConstInApp_2345_, uint8_t v_skipInstances_2346_, lean_object* v_x_2347_, lean_object* v_x_2348_, lean_object* v_fvars_2349_, lean_object* v_e_2350_, lean_object* v_a_2351_){
_start:
{
lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___f_2356_; lean_object* v___f_2357_; lean_object* v___x_2358_; 
v___x_2352_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0));
v___x_2353_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1));
lean_inc_ref(v_inst_2339_);
v___x_2354_ = l_Lean_MonadCacheT_instMonad___redArg(v_x_2347_, v___x_2352_, v___x_2353_, v_inst_2339_);
v___x_2355_ = l_Lean_MonadCacheT_instMonadControl___redArg(v_x_2347_, v___x_2352_, v___x_2353_);
lean_inc_ref_n(v_inst_2341_, 2);
lean_inc_ref(v___x_2355_);
v___f_2356_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_2356_, 0, v___x_2355_);
lean_closure_set(v___f_2356_, 1, v_inst_2341_);
v___f_2357_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_2357_, 0, v___x_2355_);
lean_closure_set(v___f_2357_, 1, v_inst_2341_);
v___x_2358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2358_, 0, v___f_2356_);
lean_ctor_set(v___x_2358_, 1, v___f_2357_);
if (lean_obj_tag(v_e_2350_) == 7)
{
lean_object* v_binderName_2359_; lean_object* v_binderType_2360_; lean_object* v_body_2361_; uint8_t v_binderInfo_2362_; lean_object* v_toBind_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___f_2367_; lean_object* v___x_2368_; lean_object* v___f_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; 
v_binderName_2359_ = lean_ctor_get(v_e_2350_, 0);
lean_inc(v_binderName_2359_);
v_binderType_2360_ = lean_ctor_get(v_e_2350_, 1);
lean_inc_ref(v_binderType_2360_);
v_body_2361_ = lean_ctor_get(v_e_2350_, 2);
lean_inc_ref(v_body_2361_);
v_binderInfo_2362_ = lean_ctor_get_uint8(v_e_2350_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2350_, 3);
v_toBind_2363_ = lean_ctor_get(v_inst_2339_, 1);
lean_inc(v_toBind_2363_);
v___x_2364_ = lean_box(v_usedLetOnly_2344_);
v___x_2365_ = lean_box(v_skipConstInApp_2345_);
v___x_2366_ = lean_box(v_skipInstances_2346_);
lean_inc(v_x_2348_);
lean_inc(v_post_2343_);
lean_inc(v_pre_2342_);
lean_inc_ref(v_inst_2341_);
lean_inc(v_inst_2340_);
lean_inc_ref(v_inst_2339_);
lean_inc_ref(v_fvars_2349_);
v___f_2367_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__0___boxed), 14, 12);
lean_closure_set(v___f_2367_, 0, v_fvars_2349_);
lean_closure_set(v___f_2367_, 1, v_inst_2339_);
lean_closure_set(v___f_2367_, 2, v_inst_2340_);
lean_closure_set(v___f_2367_, 3, v_inst_2341_);
lean_closure_set(v___f_2367_, 4, v_pre_2342_);
lean_closure_set(v___f_2367_, 5, v_post_2343_);
lean_closure_set(v___f_2367_, 6, v___x_2364_);
lean_closure_set(v___f_2367_, 7, v___x_2365_);
lean_closure_set(v___f_2367_, 8, v___x_2366_);
lean_closure_set(v___f_2367_, 9, v_x_2347_);
lean_closure_set(v___f_2367_, 10, v_x_2348_);
lean_closure_set(v___f_2367_, 11, v_body_2361_);
v___x_2368_ = lean_box(v_binderInfo_2362_);
lean_inc(v_a_2351_);
v___f_2369_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_2369_, 0, v___x_2358_);
lean_closure_set(v___f_2369_, 1, v___x_2354_);
lean_closure_set(v___f_2369_, 2, v_binderName_2359_);
lean_closure_set(v___f_2369_, 3, v___x_2368_);
lean_closure_set(v___f_2369_, 4, v___f_2367_);
lean_closure_set(v___f_2369_, 5, v_a_2351_);
v___x_2370_ = lean_expr_instantiate_rev(v_binderType_2360_, v_fvars_2349_);
lean_dec_ref(v_fvars_2349_);
lean_dec_ref(v_binderType_2360_);
v___x_2371_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2339_, v_inst_2340_, v_inst_2341_, v_pre_2342_, v_post_2343_, v_usedLetOnly_2344_, v_skipConstInApp_2345_, v_skipInstances_2346_, v_x_2347_, v_x_2348_, v___x_2370_, v_a_2351_);
v___x_2372_ = lean_apply_4(v_toBind_2363_, lean_box(0), lean_box(0), v___x_2371_, v___f_2369_);
return v___x_2372_;
}
else
{
lean_object* v_toBind_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___f_2377_; lean_object* v___x_2378_; lean_object* v___f_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; 
lean_dec_ref_known(v___x_2358_, 2);
lean_dec_ref(v___x_2354_);
v_toBind_2373_ = lean_ctor_get(v_inst_2339_, 1);
lean_inc_n(v_toBind_2373_, 2);
v___x_2374_ = lean_box(v_usedLetOnly_2344_);
v___x_2375_ = lean_box(v_skipConstInApp_2345_);
v___x_2376_ = lean_box(v_skipInstances_2346_);
lean_inc(v_a_2351_);
lean_inc(v_x_2348_);
lean_inc(v_post_2343_);
lean_inc(v_pre_2342_);
lean_inc_ref(v_inst_2341_);
lean_inc_n(v_inst_2340_, 2);
lean_inc_ref(v_inst_2339_);
v___f_2377_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3___boxed), 12, 11);
lean_closure_set(v___f_2377_, 0, v_inst_2339_);
lean_closure_set(v___f_2377_, 1, v_inst_2340_);
lean_closure_set(v___f_2377_, 2, v_inst_2341_);
lean_closure_set(v___f_2377_, 3, v_pre_2342_);
lean_closure_set(v___f_2377_, 4, v_post_2343_);
lean_closure_set(v___f_2377_, 5, v___x_2374_);
lean_closure_set(v___f_2377_, 6, v___x_2375_);
lean_closure_set(v___f_2377_, 7, v___x_2376_);
lean_closure_set(v___f_2377_, 8, v_x_2347_);
lean_closure_set(v___f_2377_, 9, v_x_2348_);
lean_closure_set(v___f_2377_, 10, v_a_2351_);
v___x_2378_ = lean_box(v_usedLetOnly_2344_);
lean_inc_ref(v_fvars_2349_);
v___f_2379_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__3___boxed), 6, 5);
lean_closure_set(v___f_2379_, 0, v_fvars_2349_);
lean_closure_set(v___f_2379_, 1, v___x_2378_);
lean_closure_set(v___f_2379_, 2, v_inst_2340_);
lean_closure_set(v___f_2379_, 3, v_toBind_2373_);
lean_closure_set(v___f_2379_, 4, v___f_2377_);
v___x_2380_ = lean_expr_instantiate_rev(v_e_2350_, v_fvars_2349_);
lean_dec_ref(v_fvars_2349_);
lean_dec_ref(v_e_2350_);
v___x_2381_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2339_, v_inst_2340_, v_inst_2341_, v_pre_2342_, v_post_2343_, v_usedLetOnly_2344_, v_skipConstInApp_2345_, v_skipInstances_2346_, v_x_2347_, v_x_2348_, v___x_2380_, v_a_2351_);
v___x_2382_ = lean_apply_4(v_toBind_2373_, lean_box(0), lean_box(0), v___x_2381_, v___f_2379_);
return v___x_2382_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__0(lean_object* v_fvars_2383_, lean_object* v_inst_2384_, lean_object* v_inst_2385_, lean_object* v_inst_2386_, lean_object* v_pre_2387_, lean_object* v_post_2388_, uint8_t v_usedLetOnly_2389_, uint8_t v_skipConstInApp_2390_, uint8_t v_skipInstances_2391_, lean_object* v_x_2392_, lean_object* v_x_2393_, lean_object* v_body_2394_, lean_object* v_x_2395_, lean_object* v___y_2396_){
_start:
{
lean_object* v___x_2397_; lean_object* v___x_2398_; 
v___x_2397_ = lean_array_push(v_fvars_2383_, v_x_2395_);
v___x_2398_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(v_inst_2384_, v_inst_2385_, v_inst_2386_, v_pre_2387_, v_post_2388_, v_usedLetOnly_2389_, v_skipConstInApp_2390_, v_skipInstances_2391_, v_x_2392_, v_x_2393_, v___x_2397_, v_body_2394_, v___y_2396_);
return v___x_2398_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__0___boxed(lean_object* v_fvars_2399_, lean_object* v_inst_2400_, lean_object* v_inst_2401_, lean_object* v_inst_2402_, lean_object* v_pre_2403_, lean_object* v_post_2404_, lean_object* v_usedLetOnly_2405_, lean_object* v_skipConstInApp_2406_, lean_object* v_skipInstances_2407_, lean_object* v_x_2408_, lean_object* v_x_2409_, lean_object* v_body_2410_, lean_object* v_x_2411_, lean_object* v___y_2412_){
_start:
{
uint8_t v_usedLetOnly_boxed_2413_; uint8_t v_skipConstInApp_boxed_2414_; uint8_t v_skipInstances_boxed_2415_; lean_object* v_res_2416_; 
v_usedLetOnly_boxed_2413_ = lean_unbox(v_usedLetOnly_2405_);
v_skipConstInApp_boxed_2414_ = lean_unbox(v_skipConstInApp_2406_);
v_skipInstances_boxed_2415_ = lean_unbox(v_skipInstances_2407_);
v_res_2416_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__0(v_fvars_2399_, v_inst_2400_, v_inst_2401_, v_inst_2402_, v_pre_2403_, v_post_2404_, v_usedLetOnly_boxed_2413_, v_skipConstInApp_boxed_2414_, v_skipInstances_boxed_2415_, v_x_2408_, v_x_2409_, v_body_2410_, v_x_2411_, v___y_2412_);
lean_dec(v___y_2412_);
return v_res_2416_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(lean_object* v_inst_2417_, lean_object* v_inst_2418_, lean_object* v_inst_2419_, lean_object* v_pre_2420_, lean_object* v_post_2421_, uint8_t v_usedLetOnly_2422_, uint8_t v_skipConstInApp_2423_, uint8_t v_skipInstances_2424_, lean_object* v_x_2425_, lean_object* v_x_2426_, lean_object* v_fvars_2427_, lean_object* v_e_2428_, lean_object* v_a_2429_){
_start:
{
lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___f_2434_; lean_object* v___f_2435_; lean_object* v___x_2436_; 
v___x_2430_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0));
v___x_2431_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1));
lean_inc_ref(v_inst_2417_);
v___x_2432_ = l_Lean_MonadCacheT_instMonad___redArg(v_x_2425_, v___x_2430_, v___x_2431_, v_inst_2417_);
v___x_2433_ = l_Lean_MonadCacheT_instMonadControl___redArg(v_x_2425_, v___x_2430_, v___x_2431_);
lean_inc_ref_n(v_inst_2419_, 2);
lean_inc_ref(v___x_2433_);
v___f_2434_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_2434_, 0, v___x_2433_);
lean_closure_set(v___f_2434_, 1, v_inst_2419_);
v___f_2435_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_2435_, 0, v___x_2433_);
lean_closure_set(v___f_2435_, 1, v_inst_2419_);
v___x_2436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2436_, 0, v___f_2434_);
lean_ctor_set(v___x_2436_, 1, v___f_2435_);
if (lean_obj_tag(v_e_2428_) == 6)
{
lean_object* v_binderName_2437_; lean_object* v_binderType_2438_; lean_object* v_body_2439_; uint8_t v_binderInfo_2440_; lean_object* v_toBind_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___f_2445_; lean_object* v___x_2446_; lean_object* v___f_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; 
v_binderName_2437_ = lean_ctor_get(v_e_2428_, 0);
lean_inc(v_binderName_2437_);
v_binderType_2438_ = lean_ctor_get(v_e_2428_, 1);
lean_inc_ref(v_binderType_2438_);
v_body_2439_ = lean_ctor_get(v_e_2428_, 2);
lean_inc_ref(v_body_2439_);
v_binderInfo_2440_ = lean_ctor_get_uint8(v_e_2428_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2428_, 3);
v_toBind_2441_ = lean_ctor_get(v_inst_2417_, 1);
lean_inc(v_toBind_2441_);
v___x_2442_ = lean_box(v_usedLetOnly_2422_);
v___x_2443_ = lean_box(v_skipConstInApp_2423_);
v___x_2444_ = lean_box(v_skipInstances_2424_);
lean_inc(v_x_2426_);
lean_inc(v_post_2421_);
lean_inc(v_pre_2420_);
lean_inc_ref(v_inst_2419_);
lean_inc(v_inst_2418_);
lean_inc_ref(v_inst_2417_);
lean_inc_ref(v_fvars_2427_);
v___f_2445_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__0___boxed), 14, 12);
lean_closure_set(v___f_2445_, 0, v_fvars_2427_);
lean_closure_set(v___f_2445_, 1, v_inst_2417_);
lean_closure_set(v___f_2445_, 2, v_inst_2418_);
lean_closure_set(v___f_2445_, 3, v_inst_2419_);
lean_closure_set(v___f_2445_, 4, v_pre_2420_);
lean_closure_set(v___f_2445_, 5, v_post_2421_);
lean_closure_set(v___f_2445_, 6, v___x_2442_);
lean_closure_set(v___f_2445_, 7, v___x_2443_);
lean_closure_set(v___f_2445_, 8, v___x_2444_);
lean_closure_set(v___f_2445_, 9, v_x_2425_);
lean_closure_set(v___f_2445_, 10, v_x_2426_);
lean_closure_set(v___f_2445_, 11, v_body_2439_);
v___x_2446_ = lean_box(v_binderInfo_2440_);
lean_inc(v_a_2429_);
v___f_2447_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_2447_, 0, v___x_2436_);
lean_closure_set(v___f_2447_, 1, v___x_2432_);
lean_closure_set(v___f_2447_, 2, v_binderName_2437_);
lean_closure_set(v___f_2447_, 3, v___x_2446_);
lean_closure_set(v___f_2447_, 4, v___f_2445_);
lean_closure_set(v___f_2447_, 5, v_a_2429_);
v___x_2448_ = lean_expr_instantiate_rev(v_binderType_2438_, v_fvars_2427_);
lean_dec_ref(v_fvars_2427_);
lean_dec_ref(v_binderType_2438_);
v___x_2449_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2417_, v_inst_2418_, v_inst_2419_, v_pre_2420_, v_post_2421_, v_usedLetOnly_2422_, v_skipConstInApp_2423_, v_skipInstances_2424_, v_x_2425_, v_x_2426_, v___x_2448_, v_a_2429_);
v___x_2450_ = lean_apply_4(v_toBind_2441_, lean_box(0), lean_box(0), v___x_2449_, v___f_2447_);
return v___x_2450_;
}
else
{
lean_object* v_toBind_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___f_2455_; lean_object* v___x_2456_; lean_object* v___f_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; 
lean_dec_ref_known(v___x_2436_, 2);
lean_dec_ref(v___x_2432_);
v_toBind_2451_ = lean_ctor_get(v_inst_2417_, 1);
lean_inc_n(v_toBind_2451_, 2);
v___x_2452_ = lean_box(v_usedLetOnly_2422_);
v___x_2453_ = lean_box(v_skipConstInApp_2423_);
v___x_2454_ = lean_box(v_skipInstances_2424_);
lean_inc(v_a_2429_);
lean_inc(v_x_2426_);
lean_inc(v_post_2421_);
lean_inc(v_pre_2420_);
lean_inc_ref(v_inst_2419_);
lean_inc_n(v_inst_2418_, 2);
lean_inc_ref(v_inst_2417_);
v___f_2455_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3___boxed), 12, 11);
lean_closure_set(v___f_2455_, 0, v_inst_2417_);
lean_closure_set(v___f_2455_, 1, v_inst_2418_);
lean_closure_set(v___f_2455_, 2, v_inst_2419_);
lean_closure_set(v___f_2455_, 3, v_pre_2420_);
lean_closure_set(v___f_2455_, 4, v_post_2421_);
lean_closure_set(v___f_2455_, 5, v___x_2452_);
lean_closure_set(v___f_2455_, 6, v___x_2453_);
lean_closure_set(v___f_2455_, 7, v___x_2454_);
lean_closure_set(v___f_2455_, 8, v_x_2425_);
lean_closure_set(v___f_2455_, 9, v_x_2426_);
lean_closure_set(v___f_2455_, 10, v_a_2429_);
v___x_2456_ = lean_box(v_usedLetOnly_2422_);
lean_inc_ref(v_fvars_2427_);
v___f_2457_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__3___boxed), 6, 5);
lean_closure_set(v___f_2457_, 0, v_fvars_2427_);
lean_closure_set(v___f_2457_, 1, v___x_2456_);
lean_closure_set(v___f_2457_, 2, v_inst_2418_);
lean_closure_set(v___f_2457_, 3, v_toBind_2451_);
lean_closure_set(v___f_2457_, 4, v___f_2455_);
v___x_2458_ = lean_expr_instantiate_rev(v_e_2428_, v_fvars_2427_);
lean_dec_ref(v_fvars_2427_);
lean_dec_ref(v_e_2428_);
v___x_2459_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2417_, v_inst_2418_, v_inst_2419_, v_pre_2420_, v_post_2421_, v_usedLetOnly_2422_, v_skipConstInApp_2423_, v_skipInstances_2424_, v_x_2425_, v_x_2426_, v___x_2458_, v_a_2429_);
v___x_2460_ = lean_apply_4(v_toBind_2451_, lean_box(0), lean_box(0), v___x_2459_, v___f_2457_);
return v___x_2460_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__0(lean_object* v_fvars_2461_, lean_object* v_inst_2462_, lean_object* v_inst_2463_, lean_object* v_inst_2464_, lean_object* v_pre_2465_, lean_object* v_post_2466_, uint8_t v_usedLetOnly_2467_, uint8_t v_skipConstInApp_2468_, uint8_t v_skipInstances_2469_, lean_object* v_x_2470_, lean_object* v_x_2471_, lean_object* v_body_2472_, lean_object* v_x_2473_, lean_object* v___y_2474_){
_start:
{
lean_object* v___x_2475_; lean_object* v___x_2476_; 
v___x_2475_ = lean_array_push(v_fvars_2461_, v_x_2473_);
v___x_2476_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(v_inst_2462_, v_inst_2463_, v_inst_2464_, v_pre_2465_, v_post_2466_, v_usedLetOnly_2467_, v_skipConstInApp_2468_, v_skipInstances_2469_, v_x_2470_, v_x_2471_, v___x_2475_, v_body_2472_, v___y_2474_);
return v___x_2476_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__0___boxed(lean_object* v_fvars_2477_, lean_object* v_inst_2478_, lean_object* v_inst_2479_, lean_object* v_inst_2480_, lean_object* v_pre_2481_, lean_object* v_post_2482_, lean_object* v_usedLetOnly_2483_, lean_object* v_skipConstInApp_2484_, lean_object* v_skipInstances_2485_, lean_object* v_x_2486_, lean_object* v_x_2487_, lean_object* v_body_2488_, lean_object* v_x_2489_, lean_object* v___y_2490_){
_start:
{
uint8_t v_usedLetOnly_boxed_2491_; uint8_t v_skipConstInApp_boxed_2492_; uint8_t v_skipInstances_boxed_2493_; lean_object* v_res_2494_; 
v_usedLetOnly_boxed_2491_ = lean_unbox(v_usedLetOnly_2483_);
v_skipConstInApp_boxed_2492_ = lean_unbox(v_skipConstInApp_2484_);
v_skipInstances_boxed_2493_ = lean_unbox(v_skipInstances_2485_);
v_res_2494_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__0(v_fvars_2477_, v_inst_2478_, v_inst_2479_, v_inst_2480_, v_pre_2481_, v_post_2482_, v_usedLetOnly_boxed_2491_, v_skipConstInApp_boxed_2492_, v_skipInstances_boxed_2493_, v_x_2486_, v_x_2487_, v_body_2488_, v_x_2489_, v___y_2490_);
lean_dec(v___y_2490_);
return v_res_2494_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__2(lean_object* v___x_2495_, lean_object* v___x_2496_, lean_object* v_declName_2497_, lean_object* v___f_2498_, uint8_t v_nondep_2499_, lean_object* v_a_2500_, lean_object* v_value_2501_, lean_object* v_fvars_2502_, lean_object* v_inst_2503_, lean_object* v_inst_2504_, lean_object* v_inst_2505_, lean_object* v_pre_2506_, lean_object* v_post_2507_, uint8_t v_usedLetOnly_2508_, uint8_t v_skipConstInApp_2509_, uint8_t v_skipInstances_2510_, lean_object* v_x_2511_, lean_object* v_x_2512_, lean_object* v_toBind_2513_, lean_object* v_a_2514_){
_start:
{
lean_object* v___x_2515_; lean_object* v___f_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; 
v___x_2515_ = lean_box(v_nondep_2499_);
lean_inc(v_a_2500_);
v___f_2516_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_2516_, 0, v___x_2495_);
lean_closure_set(v___f_2516_, 1, v___x_2496_);
lean_closure_set(v___f_2516_, 2, v_declName_2497_);
lean_closure_set(v___f_2516_, 3, v_a_2514_);
lean_closure_set(v___f_2516_, 4, v___f_2498_);
lean_closure_set(v___f_2516_, 5, v___x_2515_);
lean_closure_set(v___f_2516_, 6, v_a_2500_);
v___x_2517_ = lean_expr_instantiate_rev(v_value_2501_, v_fvars_2502_);
v___x_2518_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2503_, v_inst_2504_, v_inst_2505_, v_pre_2506_, v_post_2507_, v_usedLetOnly_2508_, v_skipConstInApp_2509_, v_skipInstances_2510_, v_x_2511_, v_x_2512_, v___x_2517_, v_a_2500_);
v___x_2519_ = lean_apply_4(v_toBind_2513_, lean_box(0), lean_box(0), v___x_2518_, v___f_2516_);
return v___x_2519_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__2___boxed(lean_object** _args){
lean_object* v___x_2520_ = _args[0];
lean_object* v___x_2521_ = _args[1];
lean_object* v_declName_2522_ = _args[2];
lean_object* v___f_2523_ = _args[3];
lean_object* v_nondep_2524_ = _args[4];
lean_object* v_a_2525_ = _args[5];
lean_object* v_value_2526_ = _args[6];
lean_object* v_fvars_2527_ = _args[7];
lean_object* v_inst_2528_ = _args[8];
lean_object* v_inst_2529_ = _args[9];
lean_object* v_inst_2530_ = _args[10];
lean_object* v_pre_2531_ = _args[11];
lean_object* v_post_2532_ = _args[12];
lean_object* v_usedLetOnly_2533_ = _args[13];
lean_object* v_skipConstInApp_2534_ = _args[14];
lean_object* v_skipInstances_2535_ = _args[15];
lean_object* v_x_2536_ = _args[16];
lean_object* v_x_2537_ = _args[17];
lean_object* v_toBind_2538_ = _args[18];
lean_object* v_a_2539_ = _args[19];
_start:
{
uint8_t v_nondep_3839__boxed_2540_; uint8_t v_usedLetOnly_boxed_2541_; uint8_t v_skipConstInApp_boxed_2542_; uint8_t v_skipInstances_boxed_2543_; lean_object* v_res_2544_; 
v_nondep_3839__boxed_2540_ = lean_unbox(v_nondep_2524_);
v_usedLetOnly_boxed_2541_ = lean_unbox(v_usedLetOnly_2533_);
v_skipConstInApp_boxed_2542_ = lean_unbox(v_skipConstInApp_2534_);
v_skipInstances_boxed_2543_ = lean_unbox(v_skipInstances_2535_);
v_res_2544_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__2(v___x_2520_, v___x_2521_, v_declName_2522_, v___f_2523_, v_nondep_3839__boxed_2540_, v_a_2525_, v_value_2526_, v_fvars_2527_, v_inst_2528_, v_inst_2529_, v_inst_2530_, v_pre_2531_, v_post_2532_, v_usedLetOnly_boxed_2541_, v_skipConstInApp_boxed_2542_, v_skipInstances_boxed_2543_, v_x_2536_, v_x_2537_, v_toBind_2538_, v_a_2539_);
lean_dec_ref(v_fvars_2527_);
lean_dec_ref(v_value_2526_);
lean_dec(v_a_2525_);
return v_res_2544_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(lean_object* v_inst_2545_, lean_object* v_inst_2546_, lean_object* v_inst_2547_, lean_object* v_pre_2548_, lean_object* v_post_2549_, uint8_t v_usedLetOnly_2550_, uint8_t v_skipConstInApp_2551_, uint8_t v_skipInstances_2552_, lean_object* v_x_2553_, lean_object* v_x_2554_, lean_object* v_fvars_2555_, lean_object* v_e_2556_, lean_object* v_a_2557_){
_start:
{
lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___f_2562_; lean_object* v___f_2563_; lean_object* v___x_2564_; 
v___x_2558_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0));
v___x_2559_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1));
lean_inc_ref(v_inst_2545_);
v___x_2560_ = l_Lean_MonadCacheT_instMonad___redArg(v_x_2553_, v___x_2558_, v___x_2559_, v_inst_2545_);
v___x_2561_ = l_Lean_MonadCacheT_instMonadControl___redArg(v_x_2553_, v___x_2558_, v___x_2559_);
lean_inc_ref_n(v_inst_2547_, 2);
lean_inc_ref(v___x_2561_);
v___f_2562_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_2562_, 0, v___x_2561_);
lean_closure_set(v___f_2562_, 1, v_inst_2547_);
v___f_2563_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_2563_, 0, v___x_2561_);
lean_closure_set(v___f_2563_, 1, v_inst_2547_);
v___x_2564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2564_, 0, v___f_2562_);
lean_ctor_set(v___x_2564_, 1, v___f_2563_);
if (lean_obj_tag(v_e_2556_) == 8)
{
lean_object* v_declName_2565_; lean_object* v_type_2566_; lean_object* v_value_2567_; lean_object* v_body_2568_; uint8_t v_nondep_2569_; lean_object* v_toBind_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___f_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___f_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; 
v_declName_2565_ = lean_ctor_get(v_e_2556_, 0);
lean_inc(v_declName_2565_);
v_type_2566_ = lean_ctor_get(v_e_2556_, 1);
lean_inc_ref(v_type_2566_);
v_value_2567_ = lean_ctor_get(v_e_2556_, 2);
lean_inc_ref(v_value_2567_);
v_body_2568_ = lean_ctor_get(v_e_2556_, 3);
lean_inc_ref(v_body_2568_);
v_nondep_2569_ = lean_ctor_get_uint8(v_e_2556_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_2556_, 4);
v_toBind_2570_ = lean_ctor_get(v_inst_2545_, 1);
lean_inc_n(v_toBind_2570_, 2);
v___x_2571_ = lean_box(v_usedLetOnly_2550_);
v___x_2572_ = lean_box(v_skipConstInApp_2551_);
v___x_2573_ = lean_box(v_skipInstances_2552_);
lean_inc_n(v_x_2554_, 2);
lean_inc_n(v_post_2549_, 2);
lean_inc_n(v_pre_2548_, 2);
lean_inc_ref_n(v_inst_2547_, 2);
lean_inc_n(v_inst_2546_, 2);
lean_inc_ref_n(v_inst_2545_, 2);
lean_inc_ref_n(v_fvars_2555_, 2);
v___f_2574_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__0___boxed), 14, 12);
lean_closure_set(v___f_2574_, 0, v_fvars_2555_);
lean_closure_set(v___f_2574_, 1, v_inst_2545_);
lean_closure_set(v___f_2574_, 2, v_inst_2546_);
lean_closure_set(v___f_2574_, 3, v_inst_2547_);
lean_closure_set(v___f_2574_, 4, v_pre_2548_);
lean_closure_set(v___f_2574_, 5, v_post_2549_);
lean_closure_set(v___f_2574_, 6, v___x_2571_);
lean_closure_set(v___f_2574_, 7, v___x_2572_);
lean_closure_set(v___f_2574_, 8, v___x_2573_);
lean_closure_set(v___f_2574_, 9, v_x_2553_);
lean_closure_set(v___f_2574_, 10, v_x_2554_);
lean_closure_set(v___f_2574_, 11, v_body_2568_);
v___x_2575_ = lean_box(v_nondep_2569_);
v___x_2576_ = lean_box(v_usedLetOnly_2550_);
v___x_2577_ = lean_box(v_skipConstInApp_2551_);
v___x_2578_ = lean_box(v_skipInstances_2552_);
lean_inc(v_a_2557_);
v___f_2579_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__2___boxed), 20, 19);
lean_closure_set(v___f_2579_, 0, v___x_2564_);
lean_closure_set(v___f_2579_, 1, v___x_2560_);
lean_closure_set(v___f_2579_, 2, v_declName_2565_);
lean_closure_set(v___f_2579_, 3, v___f_2574_);
lean_closure_set(v___f_2579_, 4, v___x_2575_);
lean_closure_set(v___f_2579_, 5, v_a_2557_);
lean_closure_set(v___f_2579_, 6, v_value_2567_);
lean_closure_set(v___f_2579_, 7, v_fvars_2555_);
lean_closure_set(v___f_2579_, 8, v_inst_2545_);
lean_closure_set(v___f_2579_, 9, v_inst_2546_);
lean_closure_set(v___f_2579_, 10, v_inst_2547_);
lean_closure_set(v___f_2579_, 11, v_pre_2548_);
lean_closure_set(v___f_2579_, 12, v_post_2549_);
lean_closure_set(v___f_2579_, 13, v___x_2576_);
lean_closure_set(v___f_2579_, 14, v___x_2577_);
lean_closure_set(v___f_2579_, 15, v___x_2578_);
lean_closure_set(v___f_2579_, 16, v_x_2553_);
lean_closure_set(v___f_2579_, 17, v_x_2554_);
lean_closure_set(v___f_2579_, 18, v_toBind_2570_);
v___x_2580_ = lean_expr_instantiate_rev(v_type_2566_, v_fvars_2555_);
lean_dec_ref(v_fvars_2555_);
lean_dec_ref(v_type_2566_);
v___x_2581_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2545_, v_inst_2546_, v_inst_2547_, v_pre_2548_, v_post_2549_, v_usedLetOnly_2550_, v_skipConstInApp_2551_, v_skipInstances_2552_, v_x_2553_, v_x_2554_, v___x_2580_, v_a_2557_);
v___x_2582_ = lean_apply_4(v_toBind_2570_, lean_box(0), lean_box(0), v___x_2581_, v___f_2579_);
return v___x_2582_;
}
else
{
lean_object* v_toBind_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___f_2587_; lean_object* v___x_2588_; lean_object* v___f_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; 
lean_dec_ref_known(v___x_2564_, 2);
lean_dec_ref(v___x_2560_);
v_toBind_2583_ = lean_ctor_get(v_inst_2545_, 1);
lean_inc_n(v_toBind_2583_, 2);
v___x_2584_ = lean_box(v_usedLetOnly_2550_);
v___x_2585_ = lean_box(v_skipConstInApp_2551_);
v___x_2586_ = lean_box(v_skipInstances_2552_);
lean_inc(v_a_2557_);
lean_inc(v_x_2554_);
lean_inc(v_post_2549_);
lean_inc(v_pre_2548_);
lean_inc_ref(v_inst_2547_);
lean_inc_n(v_inst_2546_, 2);
lean_inc_ref(v_inst_2545_);
v___f_2587_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3___boxed), 12, 11);
lean_closure_set(v___f_2587_, 0, v_inst_2545_);
lean_closure_set(v___f_2587_, 1, v_inst_2546_);
lean_closure_set(v___f_2587_, 2, v_inst_2547_);
lean_closure_set(v___f_2587_, 3, v_pre_2548_);
lean_closure_set(v___f_2587_, 4, v_post_2549_);
lean_closure_set(v___f_2587_, 5, v___x_2584_);
lean_closure_set(v___f_2587_, 6, v___x_2585_);
lean_closure_set(v___f_2587_, 7, v___x_2586_);
lean_closure_set(v___f_2587_, 8, v_x_2553_);
lean_closure_set(v___f_2587_, 9, v_x_2554_);
lean_closure_set(v___f_2587_, 10, v_a_2557_);
v___x_2588_ = lean_box(v_usedLetOnly_2550_);
lean_inc_ref(v_fvars_2555_);
v___f_2589_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__4___boxed), 6, 5);
lean_closure_set(v___f_2589_, 0, v_fvars_2555_);
lean_closure_set(v___f_2589_, 1, v___x_2588_);
lean_closure_set(v___f_2589_, 2, v_inst_2546_);
lean_closure_set(v___f_2589_, 3, v_toBind_2583_);
lean_closure_set(v___f_2589_, 4, v___f_2587_);
v___x_2590_ = lean_expr_instantiate_rev(v_e_2556_, v_fvars_2555_);
lean_dec_ref(v_fvars_2555_);
lean_dec_ref(v_e_2556_);
v___x_2591_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2545_, v_inst_2546_, v_inst_2547_, v_pre_2548_, v_post_2549_, v_usedLetOnly_2550_, v_skipConstInApp_2551_, v_skipInstances_2552_, v_x_2553_, v_x_2554_, v___x_2590_, v_a_2557_);
v___x_2592_ = lean_apply_4(v_toBind_2583_, lean_box(0), lean_box(0), v___x_2591_, v___f_2589_);
return v___x_2592_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__8(lean_object* v_expr_2593_, lean_object* v_data_2594_, lean_object* v_inst_2595_, lean_object* v_inst_2596_, lean_object* v_inst_2597_, lean_object* v_pre_2598_, lean_object* v_post_2599_, uint8_t v_usedLetOnly_2600_, uint8_t v_skipConstInApp_2601_, uint8_t v_skipInstances_2602_, lean_object* v_x_2603_, lean_object* v_x_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v_a_2607_){
_start:
{
size_t v___x_2608_; size_t v___x_2609_; uint8_t v___x_2610_; 
v___x_2608_ = lean_ptr_addr(v_expr_2593_);
v___x_2609_ = lean_ptr_addr(v_a_2607_);
v___x_2610_ = lean_usize_dec_eq(v___x_2608_, v___x_2609_);
if (v___x_2610_ == 0)
{
lean_object* v___x_2611_; lean_object* v___x_2612_; 
lean_dec_ref(v___y_2606_);
v___x_2611_ = l_Lean_Expr_mdata___override(v_data_2594_, v_a_2607_);
v___x_2612_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2595_, v_inst_2596_, v_inst_2597_, v_pre_2598_, v_post_2599_, v_usedLetOnly_2600_, v_skipConstInApp_2601_, v_skipInstances_2602_, v_x_2603_, v_x_2604_, v___x_2611_, v___y_2605_);
return v___x_2612_;
}
else
{
lean_object* v___x_2613_; 
lean_dec_ref(v_a_2607_);
lean_dec(v_data_2594_);
v___x_2613_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2595_, v_inst_2596_, v_inst_2597_, v_pre_2598_, v_post_2599_, v_usedLetOnly_2600_, v_skipConstInApp_2601_, v_skipInstances_2602_, v_x_2603_, v_x_2604_, v___y_2606_, v___y_2605_);
return v___x_2613_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__8___boxed(lean_object* v_expr_2614_, lean_object* v_data_2615_, lean_object* v_inst_2616_, lean_object* v_inst_2617_, lean_object* v_inst_2618_, lean_object* v_pre_2619_, lean_object* v_post_2620_, lean_object* v_usedLetOnly_2621_, lean_object* v_skipConstInApp_2622_, lean_object* v_skipInstances_2623_, lean_object* v_x_2624_, lean_object* v_x_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v_a_2628_){
_start:
{
uint8_t v_usedLetOnly_boxed_2629_; uint8_t v_skipConstInApp_boxed_2630_; uint8_t v_skipInstances_boxed_2631_; lean_object* v_res_2632_; 
v_usedLetOnly_boxed_2629_ = lean_unbox(v_usedLetOnly_2621_);
v_skipConstInApp_boxed_2630_ = lean_unbox(v_skipConstInApp_2622_);
v_skipInstances_boxed_2631_ = lean_unbox(v_skipInstances_2623_);
v_res_2632_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__8(v_expr_2614_, v_data_2615_, v_inst_2616_, v_inst_2617_, v_inst_2618_, v_pre_2619_, v_post_2620_, v_usedLetOnly_boxed_2629_, v_skipConstInApp_boxed_2630_, v_skipInstances_boxed_2631_, v_x_2624_, v_x_2625_, v___y_2626_, v___y_2627_, v_a_2628_);
lean_dec(v___y_2626_);
lean_dec_ref(v_expr_2614_);
return v_res_2632_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__10(lean_object* v_struct_2633_, lean_object* v_typeName_2634_, lean_object* v_idx_2635_, lean_object* v_inst_2636_, lean_object* v_inst_2637_, lean_object* v_inst_2638_, lean_object* v_pre_2639_, lean_object* v_post_2640_, uint8_t v_usedLetOnly_2641_, uint8_t v_skipConstInApp_2642_, uint8_t v_skipInstances_2643_, lean_object* v_x_2644_, lean_object* v_x_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v_a_2648_){
_start:
{
size_t v___x_2649_; size_t v___x_2650_; uint8_t v___x_2651_; 
v___x_2649_ = lean_ptr_addr(v_struct_2633_);
v___x_2650_ = lean_ptr_addr(v_a_2648_);
v___x_2651_ = lean_usize_dec_eq(v___x_2649_, v___x_2650_);
if (v___x_2651_ == 0)
{
lean_object* v___x_2652_; lean_object* v___x_2653_; 
lean_dec_ref(v___y_2647_);
v___x_2652_ = l_Lean_Expr_proj___override(v_typeName_2634_, v_idx_2635_, v_a_2648_);
v___x_2653_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2636_, v_inst_2637_, v_inst_2638_, v_pre_2639_, v_post_2640_, v_usedLetOnly_2641_, v_skipConstInApp_2642_, v_skipInstances_2643_, v_x_2644_, v_x_2645_, v___x_2652_, v___y_2646_);
return v___x_2653_;
}
else
{
lean_object* v___x_2654_; 
lean_dec_ref(v_a_2648_);
lean_dec(v_idx_2635_);
lean_dec(v_typeName_2634_);
v___x_2654_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2636_, v_inst_2637_, v_inst_2638_, v_pre_2639_, v_post_2640_, v_usedLetOnly_2641_, v_skipConstInApp_2642_, v_skipInstances_2643_, v_x_2644_, v_x_2645_, v___y_2647_, v___y_2646_);
return v___x_2654_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__10___boxed(lean_object* v_struct_2655_, lean_object* v_typeName_2656_, lean_object* v_idx_2657_, lean_object* v_inst_2658_, lean_object* v_inst_2659_, lean_object* v_inst_2660_, lean_object* v_pre_2661_, lean_object* v_post_2662_, lean_object* v_usedLetOnly_2663_, lean_object* v_skipConstInApp_2664_, lean_object* v_skipInstances_2665_, lean_object* v_x_2666_, lean_object* v_x_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v_a_2670_){
_start:
{
uint8_t v_usedLetOnly_boxed_2671_; uint8_t v_skipConstInApp_boxed_2672_; uint8_t v_skipInstances_boxed_2673_; lean_object* v_res_2674_; 
v_usedLetOnly_boxed_2671_ = lean_unbox(v_usedLetOnly_2663_);
v_skipConstInApp_boxed_2672_ = lean_unbox(v_skipConstInApp_2664_);
v_skipInstances_boxed_2673_ = lean_unbox(v_skipInstances_2665_);
v_res_2674_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__10(v_struct_2655_, v_typeName_2656_, v_idx_2657_, v_inst_2658_, v_inst_2659_, v_inst_2660_, v_pre_2661_, v_post_2662_, v_usedLetOnly_boxed_2671_, v_skipConstInApp_boxed_2672_, v_skipInstances_boxed_2673_, v_x_2666_, v_x_2667_, v___y_2668_, v___y_2669_, v_a_2670_);
lean_dec(v___y_2668_);
lean_dec_ref(v_struct_2655_);
return v_res_2674_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11(lean_object* v_toApplicative_2675_, lean_object* v_inst_2676_, lean_object* v_inst_2677_, lean_object* v_inst_2678_, lean_object* v_pre_2679_, lean_object* v_post_2680_, uint8_t v_usedLetOnly_2681_, uint8_t v_skipConstInApp_2682_, uint8_t v_skipInstances_2683_, lean_object* v_x_2684_, lean_object* v_x_2685_, lean_object* v___y_2686_, lean_object* v___f_2687_, lean_object* v_toBind_2688_, lean_object* v_e_2689_, lean_object* v_a_2690_){
_start:
{
lean_object* v___y_2692_; 
switch(lean_obj_tag(v_a_2690_))
{
case 0:
{
lean_object* v_e_2724_; lean_object* v_toPure_2725_; lean_object* v___x_2726_; 
lean_dec_ref(v_e_2689_);
lean_dec(v_toBind_2688_);
lean_dec(v___f_2687_);
lean_dec(v_x_2685_);
lean_dec(v_post_2680_);
lean_dec(v_pre_2679_);
lean_dec_ref(v_inst_2678_);
lean_dec(v_inst_2677_);
lean_dec_ref(v_inst_2676_);
v_e_2724_ = lean_ctor_get(v_a_2690_, 0);
lean_inc_ref(v_e_2724_);
lean_dec_ref_known(v_a_2690_, 1);
v_toPure_2725_ = lean_ctor_get(v_toApplicative_2675_, 1);
lean_inc(v_toPure_2725_);
lean_dec_ref(v_toApplicative_2675_);
v___x_2726_ = lean_apply_2(v_toPure_2725_, lean_box(0), v_e_2724_);
return v___x_2726_;
}
case 1:
{
lean_object* v_e_2727_; lean_object* v___x_2728_; 
lean_dec_ref(v_e_2689_);
lean_dec(v_toBind_2688_);
lean_dec(v___f_2687_);
lean_dec_ref(v_toApplicative_2675_);
v_e_2727_ = lean_ctor_get(v_a_2690_, 0);
lean_inc_ref(v_e_2727_);
lean_dec_ref_known(v_a_2690_, 1);
v___x_2728_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2676_, v_inst_2677_, v_inst_2678_, v_pre_2679_, v_post_2680_, v_usedLetOnly_2681_, v_skipConstInApp_2682_, v_skipInstances_2683_, v_x_2684_, v_x_2685_, v_e_2727_, v___y_2686_);
return v___x_2728_;
}
default: 
{
lean_object* v_e_x3f_2729_; 
lean_dec_ref(v_toApplicative_2675_);
v_e_x3f_2729_ = lean_ctor_get(v_a_2690_, 0);
lean_inc(v_e_x3f_2729_);
lean_dec_ref_known(v_a_2690_, 1);
if (lean_obj_tag(v_e_x3f_2729_) == 0)
{
v___y_2692_ = v_e_2689_;
goto v___jp_2691_;
}
else
{
lean_object* v_val_2730_; 
lean_dec_ref(v_e_2689_);
v_val_2730_ = lean_ctor_get(v_e_x3f_2729_, 0);
lean_inc(v_val_2730_);
lean_dec_ref_known(v_e_x3f_2729_, 1);
v___y_2692_ = v_val_2730_;
goto v___jp_2691_;
}
}
}
v___jp_2691_:
{
switch(lean_obj_tag(v___y_2692_))
{
case 7:
{
lean_object* v___x_2693_; lean_object* v___x_2694_; 
lean_dec(v_toBind_2688_);
lean_dec(v___f_2687_);
v___x_2693_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_2694_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(v_inst_2676_, v_inst_2677_, v_inst_2678_, v_pre_2679_, v_post_2680_, v_usedLetOnly_2681_, v_skipConstInApp_2682_, v_skipInstances_2683_, v_x_2684_, v_x_2685_, v___x_2693_, v___y_2692_, v___y_2686_);
return v___x_2694_;
}
case 6:
{
lean_object* v___x_2695_; lean_object* v___x_2696_; 
lean_dec(v_toBind_2688_);
lean_dec(v___f_2687_);
v___x_2695_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_2696_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(v_inst_2676_, v_inst_2677_, v_inst_2678_, v_pre_2679_, v_post_2680_, v_usedLetOnly_2681_, v_skipConstInApp_2682_, v_skipInstances_2683_, v_x_2684_, v_x_2685_, v___x_2695_, v___y_2692_, v___y_2686_);
return v___x_2696_;
}
case 8:
{
lean_object* v___x_2697_; lean_object* v___x_2698_; 
lean_dec(v_toBind_2688_);
lean_dec(v___f_2687_);
v___x_2697_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_2698_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(v_inst_2676_, v_inst_2677_, v_inst_2678_, v_pre_2679_, v_post_2680_, v_usedLetOnly_2681_, v_skipConstInApp_2682_, v_skipInstances_2683_, v_x_2684_, v_x_2685_, v___x_2697_, v___y_2692_, v___y_2686_);
return v___x_2698_;
}
case 5:
{
lean_object* v_dummy_2699_; lean_object* v_nargs_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_3385__overap_2704_; lean_object* v___x_2705_; 
lean_dec(v_toBind_2688_);
lean_dec(v_x_2685_);
lean_dec(v_post_2680_);
lean_dec(v_pre_2679_);
lean_dec_ref(v_inst_2678_);
lean_dec(v_inst_2677_);
lean_dec_ref(v_inst_2676_);
v_dummy_2699_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_2700_ = l_Lean_Expr_getAppNumArgs(v___y_2692_);
lean_inc(v_nargs_2700_);
v___x_2701_ = lean_mk_array(v_nargs_2700_, v_dummy_2699_);
v___x_2702_ = lean_unsigned_to_nat(1u);
v___x_2703_ = lean_nat_sub(v_nargs_2700_, v___x_2702_);
lean_dec(v_nargs_2700_);
v___x_3385__overap_2704_ = l_Lean_Expr_withAppAux___redArg(v___f_2687_, v___y_2692_, v___x_2701_, v___x_2703_);
lean_inc(v___y_2686_);
v___x_2705_ = lean_apply_1(v___x_3385__overap_2704_, v___y_2686_);
return v___x_2705_;
}
case 10:
{
lean_object* v_data_2706_; lean_object* v_expr_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___f_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; 
lean_dec(v___f_2687_);
v_data_2706_ = lean_ctor_get(v___y_2692_, 0);
lean_inc(v_data_2706_);
v_expr_2707_ = lean_ctor_get(v___y_2692_, 1);
lean_inc_ref_n(v_expr_2707_, 2);
v___x_2708_ = lean_box(v_usedLetOnly_2681_);
v___x_2709_ = lean_box(v_skipConstInApp_2682_);
v___x_2710_ = lean_box(v_skipInstances_2683_);
lean_inc(v___y_2686_);
lean_inc(v_x_2685_);
lean_inc(v_post_2680_);
lean_inc(v_pre_2679_);
lean_inc_ref(v_inst_2678_);
lean_inc(v_inst_2677_);
lean_inc_ref(v_inst_2676_);
v___f_2711_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__8___boxed), 15, 14);
lean_closure_set(v___f_2711_, 0, v_expr_2707_);
lean_closure_set(v___f_2711_, 1, v_data_2706_);
lean_closure_set(v___f_2711_, 2, v_inst_2676_);
lean_closure_set(v___f_2711_, 3, v_inst_2677_);
lean_closure_set(v___f_2711_, 4, v_inst_2678_);
lean_closure_set(v___f_2711_, 5, v_pre_2679_);
lean_closure_set(v___f_2711_, 6, v_post_2680_);
lean_closure_set(v___f_2711_, 7, v___x_2708_);
lean_closure_set(v___f_2711_, 8, v___x_2709_);
lean_closure_set(v___f_2711_, 9, v___x_2710_);
lean_closure_set(v___f_2711_, 10, v_x_2684_);
lean_closure_set(v___f_2711_, 11, v_x_2685_);
lean_closure_set(v___f_2711_, 12, v___y_2686_);
lean_closure_set(v___f_2711_, 13, v___y_2692_);
v___x_2712_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2676_, v_inst_2677_, v_inst_2678_, v_pre_2679_, v_post_2680_, v_usedLetOnly_2681_, v_skipConstInApp_2682_, v_skipInstances_2683_, v_x_2684_, v_x_2685_, v_expr_2707_, v___y_2686_);
v___x_2713_ = lean_apply_4(v_toBind_2688_, lean_box(0), lean_box(0), v___x_2712_, v___f_2711_);
return v___x_2713_;
}
case 11:
{
lean_object* v_typeName_2714_; lean_object* v_idx_2715_; lean_object* v_struct_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___f_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; 
lean_dec(v___f_2687_);
v_typeName_2714_ = lean_ctor_get(v___y_2692_, 0);
lean_inc(v_typeName_2714_);
v_idx_2715_ = lean_ctor_get(v___y_2692_, 1);
lean_inc(v_idx_2715_);
v_struct_2716_ = lean_ctor_get(v___y_2692_, 2);
lean_inc_ref_n(v_struct_2716_, 2);
v___x_2717_ = lean_box(v_usedLetOnly_2681_);
v___x_2718_ = lean_box(v_skipConstInApp_2682_);
v___x_2719_ = lean_box(v_skipInstances_2683_);
lean_inc(v___y_2686_);
lean_inc(v_x_2685_);
lean_inc(v_post_2680_);
lean_inc(v_pre_2679_);
lean_inc_ref(v_inst_2678_);
lean_inc(v_inst_2677_);
lean_inc_ref(v_inst_2676_);
v___f_2720_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__10___boxed), 16, 15);
lean_closure_set(v___f_2720_, 0, v_struct_2716_);
lean_closure_set(v___f_2720_, 1, v_typeName_2714_);
lean_closure_set(v___f_2720_, 2, v_idx_2715_);
lean_closure_set(v___f_2720_, 3, v_inst_2676_);
lean_closure_set(v___f_2720_, 4, v_inst_2677_);
lean_closure_set(v___f_2720_, 5, v_inst_2678_);
lean_closure_set(v___f_2720_, 6, v_pre_2679_);
lean_closure_set(v___f_2720_, 7, v_post_2680_);
lean_closure_set(v___f_2720_, 8, v___x_2717_);
lean_closure_set(v___f_2720_, 9, v___x_2718_);
lean_closure_set(v___f_2720_, 10, v___x_2719_);
lean_closure_set(v___f_2720_, 11, v_x_2684_);
lean_closure_set(v___f_2720_, 12, v_x_2685_);
lean_closure_set(v___f_2720_, 13, v___y_2686_);
lean_closure_set(v___f_2720_, 14, v___y_2692_);
v___x_2721_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2676_, v_inst_2677_, v_inst_2678_, v_pre_2679_, v_post_2680_, v_usedLetOnly_2681_, v_skipConstInApp_2682_, v_skipInstances_2683_, v_x_2684_, v_x_2685_, v_struct_2716_, v___y_2686_);
v___x_2722_ = lean_apply_4(v_toBind_2688_, lean_box(0), lean_box(0), v___x_2721_, v___f_2720_);
return v___x_2722_;
}
default: 
{
lean_object* v___x_2723_; 
lean_dec(v_toBind_2688_);
lean_dec(v___f_2687_);
v___x_2723_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2676_, v_inst_2677_, v_inst_2678_, v_pre_2679_, v_post_2680_, v_usedLetOnly_2681_, v_skipConstInApp_2682_, v_skipInstances_2683_, v_x_2684_, v_x_2685_, v___y_2692_, v___y_2686_);
return v___x_2723_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___boxed(lean_object* v_toApplicative_2731_, lean_object* v_inst_2732_, lean_object* v_inst_2733_, lean_object* v_inst_2734_, lean_object* v_pre_2735_, lean_object* v_post_2736_, lean_object* v_usedLetOnly_2737_, lean_object* v_skipConstInApp_2738_, lean_object* v_skipInstances_2739_, lean_object* v_x_2740_, lean_object* v_x_2741_, lean_object* v___y_2742_, lean_object* v___f_2743_, lean_object* v_toBind_2744_, lean_object* v_e_2745_, lean_object* v_a_2746_){
_start:
{
uint8_t v_usedLetOnly_boxed_2747_; uint8_t v_skipConstInApp_boxed_2748_; uint8_t v_skipInstances_boxed_2749_; lean_object* v_res_2750_; 
v_usedLetOnly_boxed_2747_ = lean_unbox(v_usedLetOnly_2737_);
v_skipConstInApp_boxed_2748_ = lean_unbox(v_skipConstInApp_2738_);
v_skipInstances_boxed_2749_ = lean_unbox(v_skipInstances_2739_);
v_res_2750_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11(v_toApplicative_2731_, v_inst_2732_, v_inst_2733_, v_inst_2734_, v_pre_2735_, v_post_2736_, v_usedLetOnly_boxed_2747_, v_skipConstInApp_boxed_2748_, v_skipInstances_boxed_2749_, v_x_2740_, v_x_2741_, v___y_2742_, v___f_2743_, v_toBind_2744_, v_e_2745_, v_a_2746_);
lean_dec(v___y_2742_);
return v_res_2750_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12(lean_object* v_toApplicative_2751_, lean_object* v_inst_2752_, lean_object* v_inst_2753_, lean_object* v_inst_2754_, lean_object* v_pre_2755_, lean_object* v_post_2756_, uint8_t v_usedLetOnly_2757_, uint8_t v_skipConstInApp_2758_, uint8_t v_skipInstances_2759_, lean_object* v_x_2760_, lean_object* v_x_2761_, lean_object* v___f_2762_, lean_object* v_toBind_2763_, lean_object* v_e_2764_, lean_object* v_____r_2765_, lean_object* v___y_2766_){
_start:
{
lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___f_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; 
v___x_2767_ = lean_box(v_usedLetOnly_2757_);
v___x_2768_ = lean_box(v_skipConstInApp_2758_);
v___x_2769_ = lean_box(v_skipInstances_2759_);
lean_inc_ref(v_e_2764_);
lean_inc(v_toBind_2763_);
lean_inc(v___y_2766_);
lean_inc(v_pre_2755_);
v___f_2770_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___boxed), 16, 15);
lean_closure_set(v___f_2770_, 0, v_toApplicative_2751_);
lean_closure_set(v___f_2770_, 1, v_inst_2752_);
lean_closure_set(v___f_2770_, 2, v_inst_2753_);
lean_closure_set(v___f_2770_, 3, v_inst_2754_);
lean_closure_set(v___f_2770_, 4, v_pre_2755_);
lean_closure_set(v___f_2770_, 5, v_post_2756_);
lean_closure_set(v___f_2770_, 6, v___x_2767_);
lean_closure_set(v___f_2770_, 7, v___x_2768_);
lean_closure_set(v___f_2770_, 8, v___x_2769_);
lean_closure_set(v___f_2770_, 9, v_x_2760_);
lean_closure_set(v___f_2770_, 10, v_x_2761_);
lean_closure_set(v___f_2770_, 11, v___y_2766_);
lean_closure_set(v___f_2770_, 12, v___f_2762_);
lean_closure_set(v___f_2770_, 13, v_toBind_2763_);
lean_closure_set(v___f_2770_, 14, v_e_2764_);
v___x_2771_ = lean_apply_1(v_pre_2755_, v_e_2764_);
v___x_2772_ = lean_apply_4(v_toBind_2763_, lean_box(0), lean_box(0), v___x_2771_, v___f_2770_);
return v___x_2772_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12___boxed(lean_object* v_toApplicative_2773_, lean_object* v_inst_2774_, lean_object* v_inst_2775_, lean_object* v_inst_2776_, lean_object* v_pre_2777_, lean_object* v_post_2778_, lean_object* v_usedLetOnly_2779_, lean_object* v_skipConstInApp_2780_, lean_object* v_skipInstances_2781_, lean_object* v_x_2782_, lean_object* v_x_2783_, lean_object* v___f_2784_, lean_object* v_toBind_2785_, lean_object* v_e_2786_, lean_object* v_____r_2787_, lean_object* v___y_2788_){
_start:
{
uint8_t v_usedLetOnly_boxed_2789_; uint8_t v_skipConstInApp_boxed_2790_; uint8_t v_skipInstances_boxed_2791_; lean_object* v_res_2792_; 
v_usedLetOnly_boxed_2789_ = lean_unbox(v_usedLetOnly_2779_);
v_skipConstInApp_boxed_2790_ = lean_unbox(v_skipConstInApp_2780_);
v_skipInstances_boxed_2791_ = lean_unbox(v_skipInstances_2781_);
v_res_2792_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12(v_toApplicative_2773_, v_inst_2774_, v_inst_2775_, v_inst_2776_, v_pre_2777_, v_post_2778_, v_usedLetOnly_boxed_2789_, v_skipConstInApp_boxed_2790_, v_skipInstances_boxed_2791_, v_x_2782_, v_x_2783_, v___f_2784_, v_toBind_2785_, v_e_2786_, v_____r_2787_, v___y_2788_);
lean_dec(v___y_2788_);
return v_res_2792_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(lean_object* v_inst_2793_, lean_object* v_inst_2794_, lean_object* v_inst_2795_, lean_object* v_pre_2796_, lean_object* v_post_2797_, uint8_t v_usedLetOnly_2798_, uint8_t v_skipConstInApp_2799_, uint8_t v_skipInstances_2800_, lean_object* v_x_2801_, lean_object* v_x_2802_, lean_object* v_e_2803_, lean_object* v_a_2804_){
_start:
{
lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___f_2809_; lean_object* v___f_2810_; lean_object* v___x_2811_; lean_object* v_toApplicative_2812_; lean_object* v_toBind_2813_; lean_object* v___f_2814_; lean_object* v___f_2815_; lean_object* v___f_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___f_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___f_2824_; lean_object* v___f_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; 
v___x_2805_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0));
v___x_2806_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1));
lean_inc_ref_n(v_inst_2793_, 3);
v___x_2807_ = l_Lean_MonadCacheT_instMonad___redArg(v_x_2801_, v___x_2805_, v___x_2806_, v_inst_2793_);
v___x_2808_ = l_Lean_MonadCacheT_instMonadControl___redArg(v_x_2801_, v___x_2805_, v___x_2806_);
lean_inc_ref_n(v_inst_2795_, 3);
lean_inc_ref(v___x_2808_);
v___f_2809_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_2809_, 0, v___x_2808_);
lean_closure_set(v___f_2809_, 1, v_inst_2795_);
v___f_2810_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_2810_, 0, v___x_2808_);
lean_closure_set(v___f_2810_, 1, v_inst_2795_);
v___x_2811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2811_, 0, v___f_2809_);
lean_ctor_set(v___x_2811_, 1, v___f_2810_);
v_toApplicative_2812_ = lean_ctor_get(v_inst_2793_, 0);
lean_inc_ref_n(v_toApplicative_2812_, 6);
v_toBind_2813_ = lean_ctor_get(v_inst_2793_, 1);
lean_inc_n(v_toBind_2813_, 6);
v___f_2814_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2814_, 0, v_toApplicative_2812_);
lean_inc_n(v_x_2802_, 3);
lean_inc_n(v_a_2804_, 3);
lean_inc_ref_n(v_e_2803_, 2);
v___f_2815_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_2815_, 0, v_toApplicative_2812_);
lean_closure_set(v___f_2815_, 1, v___x_2805_);
lean_closure_set(v___f_2815_, 2, v___x_2806_);
lean_closure_set(v___f_2815_, 3, v_e_2803_);
lean_closure_set(v___f_2815_, 4, v_a_2804_);
lean_closure_set(v___f_2815_, 5, v_x_2802_);
lean_closure_set(v___f_2815_, 6, v_toBind_2813_);
v___f_2816_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__3___boxed), 5, 4);
lean_closure_set(v___f_2816_, 0, v_toApplicative_2812_);
lean_closure_set(v___f_2816_, 1, v___x_2805_);
lean_closure_set(v___f_2816_, 2, v___x_2806_);
lean_closure_set(v___f_2816_, 3, v_e_2803_);
v___x_2817_ = lean_box(v_skipInstances_2800_);
v___x_2818_ = lean_box(v_usedLetOnly_2798_);
v___x_2819_ = lean_box(v_skipConstInApp_2799_);
lean_inc_ref(v___x_2807_);
lean_inc(v_post_2797_);
lean_inc(v_pre_2796_);
lean_inc_n(v_inst_2794_, 2);
v___f_2820_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__9___boxed), 17, 14);
lean_closure_set(v___f_2820_, 0, v___x_2817_);
lean_closure_set(v___f_2820_, 1, v_inst_2793_);
lean_closure_set(v___f_2820_, 2, v_inst_2794_);
lean_closure_set(v___f_2820_, 3, v_inst_2795_);
lean_closure_set(v___f_2820_, 4, v_pre_2796_);
lean_closure_set(v___f_2820_, 5, v_post_2797_);
lean_closure_set(v___f_2820_, 6, v___x_2818_);
lean_closure_set(v___f_2820_, 7, v___x_2819_);
lean_closure_set(v___f_2820_, 8, v_x_2801_);
lean_closure_set(v___f_2820_, 9, v_x_2802_);
lean_closure_set(v___f_2820_, 10, v___x_2807_);
lean_closure_set(v___f_2820_, 11, v_toBind_2813_);
lean_closure_set(v___f_2820_, 12, v_toApplicative_2812_);
lean_closure_set(v___f_2820_, 13, v___f_2814_);
v___x_2821_ = lean_box(v_usedLetOnly_2798_);
v___x_2822_ = lean_box(v_skipConstInApp_2799_);
v___x_2823_ = lean_box(v_skipInstances_2800_);
v___f_2824_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12___boxed), 16, 14);
lean_closure_set(v___f_2824_, 0, v_toApplicative_2812_);
lean_closure_set(v___f_2824_, 1, v_inst_2793_);
lean_closure_set(v___f_2824_, 2, v_inst_2794_);
lean_closure_set(v___f_2824_, 3, v_inst_2795_);
lean_closure_set(v___f_2824_, 4, v_pre_2796_);
lean_closure_set(v___f_2824_, 5, v_post_2797_);
lean_closure_set(v___f_2824_, 6, v___x_2821_);
lean_closure_set(v___f_2824_, 7, v___x_2822_);
lean_closure_set(v___f_2824_, 8, v___x_2823_);
lean_closure_set(v___f_2824_, 9, v_x_2801_);
lean_closure_set(v___f_2824_, 10, v_x_2802_);
lean_closure_set(v___f_2824_, 11, v___f_2820_);
lean_closure_set(v___f_2824_, 12, v_toBind_2813_);
lean_closure_set(v___f_2824_, 13, v_e_2803_);
v___f_2825_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14___boxed), 13, 12);
lean_closure_set(v___f_2825_, 0, v_inst_2794_);
lean_closure_set(v___f_2825_, 1, v_x_2801_);
lean_closure_set(v___f_2825_, 2, v___x_2805_);
lean_closure_set(v___f_2825_, 3, v___x_2806_);
lean_closure_set(v___f_2825_, 4, v_inst_2793_);
lean_closure_set(v___f_2825_, 5, v___f_2824_);
lean_closure_set(v___f_2825_, 6, v___x_2811_);
lean_closure_set(v___f_2825_, 7, v___x_2807_);
lean_closure_set(v___f_2825_, 8, v_a_2804_);
lean_closure_set(v___f_2825_, 9, v_toBind_2813_);
lean_closure_set(v___f_2825_, 10, v___f_2815_);
lean_closure_set(v___f_2825_, 11, v_toApplicative_2812_);
v___x_2826_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2826_, 0, lean_box(0));
lean_closure_set(v___x_2826_, 1, lean_box(0));
lean_closure_set(v___x_2826_, 2, v_a_2804_);
v___x_2827_ = lean_apply_2(v_x_2802_, lean_box(0), v___x_2826_);
v___x_2828_ = lean_apply_4(v_toBind_2813_, lean_box(0), lean_box(0), v___x_2827_, v___f_2816_);
v___x_2829_ = lean_apply_4(v_toBind_2813_, lean_box(0), lean_box(0), v___x_2828_, v___f_2825_);
return v___x_2829_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___lam__0(lean_object* v_toApplicative_2830_, lean_object* v_inst_2831_, lean_object* v_inst_2832_, lean_object* v_inst_2833_, lean_object* v_pre_2834_, lean_object* v_post_2835_, uint8_t v_usedLetOnly_2836_, uint8_t v_skipConstInApp_2837_, uint8_t v_skipInstances_2838_, lean_object* v_x_2839_, lean_object* v_x_2840_, lean_object* v_a_2841_, lean_object* v_e_2842_, lean_object* v_a_2843_){
_start:
{
lean_object* v___y_2845_; 
switch(lean_obj_tag(v_a_2843_))
{
case 0:
{
lean_object* v_e_2848_; lean_object* v_toPure_2849_; lean_object* v___x_2850_; 
lean_dec_ref(v_e_2842_);
lean_dec(v_x_2840_);
lean_dec(v_post_2835_);
lean_dec(v_pre_2834_);
lean_dec_ref(v_inst_2833_);
lean_dec(v_inst_2832_);
lean_dec_ref(v_inst_2831_);
v_e_2848_ = lean_ctor_get(v_a_2843_, 0);
lean_inc_ref(v_e_2848_);
lean_dec_ref_known(v_a_2843_, 1);
v_toPure_2849_ = lean_ctor_get(v_toApplicative_2830_, 1);
lean_inc(v_toPure_2849_);
lean_dec_ref(v_toApplicative_2830_);
v___x_2850_ = lean_apply_2(v_toPure_2849_, lean_box(0), v_e_2848_);
return v___x_2850_;
}
case 1:
{
lean_object* v_e_2851_; lean_object* v___x_2852_; 
lean_dec_ref(v_e_2842_);
lean_dec_ref(v_toApplicative_2830_);
v_e_2851_ = lean_ctor_get(v_a_2843_, 0);
lean_inc_ref(v_e_2851_);
lean_dec_ref_known(v_a_2843_, 1);
v___x_2852_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2831_, v_inst_2832_, v_inst_2833_, v_pre_2834_, v_post_2835_, v_usedLetOnly_2836_, v_skipConstInApp_2837_, v_skipInstances_2838_, v_x_2839_, v_x_2840_, v_e_2851_, v_a_2841_);
return v___x_2852_;
}
default: 
{
lean_object* v_e_x3f_2853_; 
lean_dec(v_x_2840_);
lean_dec(v_post_2835_);
lean_dec(v_pre_2834_);
lean_dec_ref(v_inst_2833_);
lean_dec(v_inst_2832_);
lean_dec_ref(v_inst_2831_);
v_e_x3f_2853_ = lean_ctor_get(v_a_2843_, 0);
lean_inc(v_e_x3f_2853_);
lean_dec_ref_known(v_a_2843_, 1);
if (lean_obj_tag(v_e_x3f_2853_) == 0)
{
v___y_2845_ = v_e_2842_;
goto v___jp_2844_;
}
else
{
lean_object* v_val_2854_; 
lean_dec_ref(v_e_2842_);
v_val_2854_ = lean_ctor_get(v_e_x3f_2853_, 0);
lean_inc(v_val_2854_);
lean_dec_ref_known(v_e_x3f_2853_, 1);
v___y_2845_ = v_val_2854_;
goto v___jp_2844_;
}
}
}
v___jp_2844_:
{
lean_object* v_toPure_2846_; lean_object* v___x_2847_; 
v_toPure_2846_ = lean_ctor_get(v_toApplicative_2830_, 1);
lean_inc(v_toPure_2846_);
lean_dec_ref(v_toApplicative_2830_);
v___x_2847_ = lean_apply_2(v_toPure_2846_, lean_box(0), v___y_2845_);
return v___x_2847_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___lam__0___boxed(lean_object* v_toApplicative_2855_, lean_object* v_inst_2856_, lean_object* v_inst_2857_, lean_object* v_inst_2858_, lean_object* v_pre_2859_, lean_object* v_post_2860_, lean_object* v_usedLetOnly_2861_, lean_object* v_skipConstInApp_2862_, lean_object* v_skipInstances_2863_, lean_object* v_x_2864_, lean_object* v_x_2865_, lean_object* v_a_2866_, lean_object* v_e_2867_, lean_object* v_a_2868_){
_start:
{
uint8_t v_usedLetOnly_boxed_2869_; uint8_t v_skipConstInApp_boxed_2870_; uint8_t v_skipInstances_boxed_2871_; lean_object* v_res_2872_; 
v_usedLetOnly_boxed_2869_ = lean_unbox(v_usedLetOnly_2861_);
v_skipConstInApp_boxed_2870_ = lean_unbox(v_skipConstInApp_2862_);
v_skipInstances_boxed_2871_ = lean_unbox(v_skipInstances_2863_);
v_res_2872_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___lam__0(v_toApplicative_2855_, v_inst_2856_, v_inst_2857_, v_inst_2858_, v_pre_2859_, v_post_2860_, v_usedLetOnly_boxed_2869_, v_skipConstInApp_boxed_2870_, v_skipInstances_boxed_2871_, v_x_2864_, v_x_2865_, v_a_2866_, v_e_2867_, v_a_2868_);
lean_dec(v_a_2866_);
return v_res_2872_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(lean_object* v_inst_2873_, lean_object* v_inst_2874_, lean_object* v_inst_2875_, lean_object* v_pre_2876_, lean_object* v_post_2877_, uint8_t v_usedLetOnly_2878_, uint8_t v_skipConstInApp_2879_, uint8_t v_skipInstances_2880_, lean_object* v_x_2881_, lean_object* v_x_2882_, lean_object* v_e_2883_, lean_object* v_a_2884_){
_start:
{
lean_object* v_toApplicative_2885_; lean_object* v_toBind_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___f_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; 
v_toApplicative_2885_ = lean_ctor_get(v_inst_2873_, 0);
lean_inc_ref(v_toApplicative_2885_);
v_toBind_2886_ = lean_ctor_get(v_inst_2873_, 1);
lean_inc(v_toBind_2886_);
v___x_2887_ = lean_box(v_usedLetOnly_2878_);
v___x_2888_ = lean_box(v_skipConstInApp_2879_);
v___x_2889_ = lean_box(v_skipInstances_2880_);
lean_inc_ref(v_e_2883_);
lean_inc(v_a_2884_);
lean_inc(v_post_2877_);
v___f_2890_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___lam__0___boxed), 14, 13);
lean_closure_set(v___f_2890_, 0, v_toApplicative_2885_);
lean_closure_set(v___f_2890_, 1, v_inst_2873_);
lean_closure_set(v___f_2890_, 2, v_inst_2874_);
lean_closure_set(v___f_2890_, 3, v_inst_2875_);
lean_closure_set(v___f_2890_, 4, v_pre_2876_);
lean_closure_set(v___f_2890_, 5, v_post_2877_);
lean_closure_set(v___f_2890_, 6, v___x_2887_);
lean_closure_set(v___f_2890_, 7, v___x_2888_);
lean_closure_set(v___f_2890_, 8, v___x_2889_);
lean_closure_set(v___f_2890_, 9, v_x_2881_);
lean_closure_set(v___f_2890_, 10, v_x_2882_);
lean_closure_set(v___f_2890_, 11, v_a_2884_);
lean_closure_set(v___f_2890_, 12, v_e_2883_);
v___x_2891_ = lean_apply_1(v_post_2877_, v_e_2883_);
v___x_2892_ = lean_apply_4(v_toBind_2886_, lean_box(0), lean_box(0), v___x_2891_, v___f_2890_);
return v___x_2892_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3(lean_object* v_inst_2893_, lean_object* v_inst_2894_, lean_object* v_inst_2895_, lean_object* v_pre_2896_, lean_object* v_post_2897_, uint8_t v_usedLetOnly_2898_, uint8_t v_skipConstInApp_2899_, uint8_t v_skipInstances_2900_, lean_object* v_x_2901_, lean_object* v_x_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_){
_start:
{
lean_object* v___x_2905_; 
v___x_2905_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2893_, v_inst_2894_, v_inst_2895_, v_pre_2896_, v_post_2897_, v_usedLetOnly_2898_, v_skipConstInApp_2899_, v_skipInstances_2900_, v_x_2901_, v_x_2902_, v_a_2904_, v_a_2903_);
return v___x_2905_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___boxed(lean_object* v_inst_2906_, lean_object* v_inst_2907_, lean_object* v_inst_2908_, lean_object* v_pre_2909_, lean_object* v_post_2910_, lean_object* v_usedLetOnly_2911_, lean_object* v_skipConstInApp_2912_, lean_object* v_skipInstances_2913_, lean_object* v_x_2914_, lean_object* v_x_2915_, lean_object* v_e_2916_, lean_object* v_a_2917_){
_start:
{
uint8_t v_usedLetOnly_boxed_2918_; uint8_t v_skipConstInApp_boxed_2919_; uint8_t v_skipInstances_boxed_2920_; lean_object* v_res_2921_; 
v_usedLetOnly_boxed_2918_ = lean_unbox(v_usedLetOnly_2911_);
v_skipConstInApp_boxed_2919_ = lean_unbox(v_skipConstInApp_2912_);
v_skipInstances_boxed_2920_ = lean_unbox(v_skipInstances_2913_);
v_res_2921_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2906_, v_inst_2907_, v_inst_2908_, v_pre_2909_, v_post_2910_, v_usedLetOnly_boxed_2918_, v_skipConstInApp_boxed_2919_, v_skipInstances_boxed_2920_, v_x_2914_, v_x_2915_, v_e_2916_, v_a_2917_);
lean_dec(v_a_2917_);
return v_res_2921_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___boxed(lean_object* v_inst_2922_, lean_object* v_inst_2923_, lean_object* v_inst_2924_, lean_object* v_pre_2925_, lean_object* v_post_2926_, lean_object* v_usedLetOnly_2927_, lean_object* v_skipConstInApp_2928_, lean_object* v_skipInstances_2929_, lean_object* v_x_2930_, lean_object* v_x_2931_, lean_object* v_fvars_2932_, lean_object* v_e_2933_, lean_object* v_a_2934_){
_start:
{
uint8_t v_usedLetOnly_boxed_2935_; uint8_t v_skipConstInApp_boxed_2936_; uint8_t v_skipInstances_boxed_2937_; lean_object* v_res_2938_; 
v_usedLetOnly_boxed_2935_ = lean_unbox(v_usedLetOnly_2927_);
v_skipConstInApp_boxed_2936_ = lean_unbox(v_skipConstInApp_2928_);
v_skipInstances_boxed_2937_ = lean_unbox(v_skipInstances_2929_);
v_res_2938_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(v_inst_2922_, v_inst_2923_, v_inst_2924_, v_pre_2925_, v_post_2926_, v_usedLetOnly_boxed_2935_, v_skipConstInApp_boxed_2936_, v_skipInstances_boxed_2937_, v_x_2930_, v_x_2931_, v_fvars_2932_, v_e_2933_, v_a_2934_);
lean_dec(v_a_2934_);
return v_res_2938_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___boxed(lean_object* v_inst_2939_, lean_object* v_inst_2940_, lean_object* v_inst_2941_, lean_object* v_pre_2942_, lean_object* v_post_2943_, lean_object* v_usedLetOnly_2944_, lean_object* v_skipConstInApp_2945_, lean_object* v_skipInstances_2946_, lean_object* v_x_2947_, lean_object* v_x_2948_, lean_object* v_fvars_2949_, lean_object* v_e_2950_, lean_object* v_a_2951_){
_start:
{
uint8_t v_usedLetOnly_boxed_2952_; uint8_t v_skipConstInApp_boxed_2953_; uint8_t v_skipInstances_boxed_2954_; lean_object* v_res_2955_; 
v_usedLetOnly_boxed_2952_ = lean_unbox(v_usedLetOnly_2944_);
v_skipConstInApp_boxed_2953_ = lean_unbox(v_skipConstInApp_2945_);
v_skipInstances_boxed_2954_ = lean_unbox(v_skipInstances_2946_);
v_res_2955_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(v_inst_2939_, v_inst_2940_, v_inst_2941_, v_pre_2942_, v_post_2943_, v_usedLetOnly_boxed_2952_, v_skipConstInApp_boxed_2953_, v_skipInstances_boxed_2954_, v_x_2947_, v_x_2948_, v_fvars_2949_, v_e_2950_, v_a_2951_);
lean_dec(v_a_2951_);
return v_res_2955_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___boxed(lean_object* v_inst_2956_, lean_object* v_inst_2957_, lean_object* v_inst_2958_, lean_object* v_pre_2959_, lean_object* v_post_2960_, lean_object* v_usedLetOnly_2961_, lean_object* v_skipConstInApp_2962_, lean_object* v_skipInstances_2963_, lean_object* v_x_2964_, lean_object* v_x_2965_, lean_object* v_fvars_2966_, lean_object* v_e_2967_, lean_object* v_a_2968_){
_start:
{
uint8_t v_usedLetOnly_boxed_2969_; uint8_t v_skipConstInApp_boxed_2970_; uint8_t v_skipInstances_boxed_2971_; lean_object* v_res_2972_; 
v_usedLetOnly_boxed_2969_ = lean_unbox(v_usedLetOnly_2961_);
v_skipConstInApp_boxed_2970_ = lean_unbox(v_skipConstInApp_2962_);
v_skipInstances_boxed_2971_ = lean_unbox(v_skipInstances_2963_);
v_res_2972_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(v_inst_2956_, v_inst_2957_, v_inst_2958_, v_pre_2959_, v_post_2960_, v_usedLetOnly_boxed_2969_, v_skipConstInApp_boxed_2970_, v_skipInstances_boxed_2971_, v_x_2964_, v_x_2965_, v_fvars_2966_, v_e_2967_, v_a_2968_);
lean_dec(v_a_2968_);
return v_res_2972_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit(lean_object* v_m_2973_, lean_object* v_inst_2974_, lean_object* v_inst_2975_, lean_object* v_inst_2976_, lean_object* v_pre_2977_, lean_object* v_post_2978_, uint8_t v_usedLetOnly_2979_, uint8_t v_skipConstInApp_2980_, uint8_t v_skipInstances_2981_, lean_object* v_x_2982_, lean_object* v_x_2983_, lean_object* v_e_2984_, lean_object* v_a_2985_){
_start:
{
lean_object* v___x_2986_; 
v___x_2986_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2974_, v_inst_2975_, v_inst_2976_, v_pre_2977_, v_post_2978_, v_usedLetOnly_2979_, v_skipConstInApp_2980_, v_skipInstances_2981_, v_x_2982_, v_x_2983_, v_e_2984_, v_a_2985_);
return v___x_2986_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___boxed(lean_object* v_m_2987_, lean_object* v_inst_2988_, lean_object* v_inst_2989_, lean_object* v_inst_2990_, lean_object* v_pre_2991_, lean_object* v_post_2992_, lean_object* v_usedLetOnly_2993_, lean_object* v_skipConstInApp_2994_, lean_object* v_skipInstances_2995_, lean_object* v_x_2996_, lean_object* v_x_2997_, lean_object* v_e_2998_, lean_object* v_a_2999_){
_start:
{
uint8_t v_usedLetOnly_boxed_3000_; uint8_t v_skipConstInApp_boxed_3001_; uint8_t v_skipInstances_boxed_3002_; lean_object* v_res_3003_; 
v_usedLetOnly_boxed_3000_ = lean_unbox(v_usedLetOnly_2993_);
v_skipConstInApp_boxed_3001_ = lean_unbox(v_skipConstInApp_2994_);
v_skipInstances_boxed_3002_ = lean_unbox(v_skipInstances_2995_);
v_res_3003_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit(v_m_2987_, v_inst_2988_, v_inst_2989_, v_inst_2990_, v_pre_2991_, v_post_2992_, v_usedLetOnly_boxed_3000_, v_skipConstInApp_boxed_3001_, v_skipInstances_boxed_3002_, v_x_2996_, v_x_2997_, v_e_2998_, v_a_2999_);
lean_dec(v_a_2999_);
return v_res_3003_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet(lean_object* v_m_3004_, lean_object* v_inst_3005_, lean_object* v_inst_3006_, lean_object* v_inst_3007_, lean_object* v_pre_3008_, lean_object* v_post_3009_, uint8_t v_usedLetOnly_3010_, uint8_t v_skipConstInApp_3011_, uint8_t v_skipInstances_3012_, lean_object* v_x_3013_, lean_object* v_x_3014_, lean_object* v_fvars_3015_, lean_object* v_e_3016_, lean_object* v_a_3017_){
_start:
{
lean_object* v___x_3018_; 
v___x_3018_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(v_inst_3005_, v_inst_3006_, v_inst_3007_, v_pre_3008_, v_post_3009_, v_usedLetOnly_3010_, v_skipConstInApp_3011_, v_skipInstances_3012_, v_x_3013_, v_x_3014_, v_fvars_3015_, v_e_3016_, v_a_3017_);
return v___x_3018_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___boxed(lean_object* v_m_3019_, lean_object* v_inst_3020_, lean_object* v_inst_3021_, lean_object* v_inst_3022_, lean_object* v_pre_3023_, lean_object* v_post_3024_, lean_object* v_usedLetOnly_3025_, lean_object* v_skipConstInApp_3026_, lean_object* v_skipInstances_3027_, lean_object* v_x_3028_, lean_object* v_x_3029_, lean_object* v_fvars_3030_, lean_object* v_e_3031_, lean_object* v_a_3032_){
_start:
{
uint8_t v_usedLetOnly_boxed_3033_; uint8_t v_skipConstInApp_boxed_3034_; uint8_t v_skipInstances_boxed_3035_; lean_object* v_res_3036_; 
v_usedLetOnly_boxed_3033_ = lean_unbox(v_usedLetOnly_3025_);
v_skipConstInApp_boxed_3034_ = lean_unbox(v_skipConstInApp_3026_);
v_skipInstances_boxed_3035_ = lean_unbox(v_skipInstances_3027_);
v_res_3036_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet(v_m_3019_, v_inst_3020_, v_inst_3021_, v_inst_3022_, v_pre_3023_, v_post_3024_, v_usedLetOnly_boxed_3033_, v_skipConstInApp_boxed_3034_, v_skipInstances_boxed_3035_, v_x_3028_, v_x_3029_, v_fvars_3030_, v_e_3031_, v_a_3032_);
lean_dec(v_a_3032_);
return v_res_3036_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost(lean_object* v_m_3037_, lean_object* v_inst_3038_, lean_object* v_inst_3039_, lean_object* v_inst_3040_, lean_object* v_pre_3041_, lean_object* v_post_3042_, uint8_t v_usedLetOnly_3043_, uint8_t v_skipConstInApp_3044_, uint8_t v_skipInstances_3045_, lean_object* v_x_3046_, lean_object* v_x_3047_, lean_object* v_e_3048_, lean_object* v_a_3049_){
_start:
{
lean_object* v___x_3050_; 
v___x_3050_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_3038_, v_inst_3039_, v_inst_3040_, v_pre_3041_, v_post_3042_, v_usedLetOnly_3043_, v_skipConstInApp_3044_, v_skipInstances_3045_, v_x_3046_, v_x_3047_, v_e_3048_, v_a_3049_);
return v___x_3050_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___boxed(lean_object* v_m_3051_, lean_object* v_inst_3052_, lean_object* v_inst_3053_, lean_object* v_inst_3054_, lean_object* v_pre_3055_, lean_object* v_post_3056_, lean_object* v_usedLetOnly_3057_, lean_object* v_skipConstInApp_3058_, lean_object* v_skipInstances_3059_, lean_object* v_x_3060_, lean_object* v_x_3061_, lean_object* v_e_3062_, lean_object* v_a_3063_){
_start:
{
uint8_t v_usedLetOnly_boxed_3064_; uint8_t v_skipConstInApp_boxed_3065_; uint8_t v_skipInstances_boxed_3066_; lean_object* v_res_3067_; 
v_usedLetOnly_boxed_3064_ = lean_unbox(v_usedLetOnly_3057_);
v_skipConstInApp_boxed_3065_ = lean_unbox(v_skipConstInApp_3058_);
v_skipInstances_boxed_3066_ = lean_unbox(v_skipInstances_3059_);
v_res_3067_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost(v_m_3051_, v_inst_3052_, v_inst_3053_, v_inst_3054_, v_pre_3055_, v_post_3056_, v_usedLetOnly_boxed_3064_, v_skipConstInApp_boxed_3065_, v_skipInstances_boxed_3066_, v_x_3060_, v_x_3061_, v_e_3062_, v_a_3063_);
lean_dec(v_a_3063_);
return v_res_3067_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda(lean_object* v_m_3068_, lean_object* v_inst_3069_, lean_object* v_inst_3070_, lean_object* v_inst_3071_, lean_object* v_pre_3072_, lean_object* v_post_3073_, uint8_t v_usedLetOnly_3074_, uint8_t v_skipConstInApp_3075_, uint8_t v_skipInstances_3076_, lean_object* v_x_3077_, lean_object* v_x_3078_, lean_object* v_fvars_3079_, lean_object* v_e_3080_, lean_object* v_a_3081_){
_start:
{
lean_object* v___x_3082_; 
v___x_3082_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(v_inst_3069_, v_inst_3070_, v_inst_3071_, v_pre_3072_, v_post_3073_, v_usedLetOnly_3074_, v_skipConstInApp_3075_, v_skipInstances_3076_, v_x_3077_, v_x_3078_, v_fvars_3079_, v_e_3080_, v_a_3081_);
return v___x_3082_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___boxed(lean_object* v_m_3083_, lean_object* v_inst_3084_, lean_object* v_inst_3085_, lean_object* v_inst_3086_, lean_object* v_pre_3087_, lean_object* v_post_3088_, lean_object* v_usedLetOnly_3089_, lean_object* v_skipConstInApp_3090_, lean_object* v_skipInstances_3091_, lean_object* v_x_3092_, lean_object* v_x_3093_, lean_object* v_fvars_3094_, lean_object* v_e_3095_, lean_object* v_a_3096_){
_start:
{
uint8_t v_usedLetOnly_boxed_3097_; uint8_t v_skipConstInApp_boxed_3098_; uint8_t v_skipInstances_boxed_3099_; lean_object* v_res_3100_; 
v_usedLetOnly_boxed_3097_ = lean_unbox(v_usedLetOnly_3089_);
v_skipConstInApp_boxed_3098_ = lean_unbox(v_skipConstInApp_3090_);
v_skipInstances_boxed_3099_ = lean_unbox(v_skipInstances_3091_);
v_res_3100_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda(v_m_3083_, v_inst_3084_, v_inst_3085_, v_inst_3086_, v_pre_3087_, v_post_3088_, v_usedLetOnly_boxed_3097_, v_skipConstInApp_boxed_3098_, v_skipInstances_boxed_3099_, v_x_3092_, v_x_3093_, v_fvars_3094_, v_e_3095_, v_a_3096_);
lean_dec(v_a_3096_);
return v_res_3100_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall(lean_object* v_m_3101_, lean_object* v_inst_3102_, lean_object* v_inst_3103_, lean_object* v_inst_3104_, lean_object* v_pre_3105_, lean_object* v_post_3106_, uint8_t v_usedLetOnly_3107_, uint8_t v_skipConstInApp_3108_, uint8_t v_skipInstances_3109_, lean_object* v_x_3110_, lean_object* v_x_3111_, lean_object* v_fvars_3112_, lean_object* v_e_3113_, lean_object* v_a_3114_){
_start:
{
lean_object* v___x_3115_; 
v___x_3115_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(v_inst_3102_, v_inst_3103_, v_inst_3104_, v_pre_3105_, v_post_3106_, v_usedLetOnly_3107_, v_skipConstInApp_3108_, v_skipInstances_3109_, v_x_3110_, v_x_3111_, v_fvars_3112_, v_e_3113_, v_a_3114_);
return v___x_3115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___boxed(lean_object* v_m_3116_, lean_object* v_inst_3117_, lean_object* v_inst_3118_, lean_object* v_inst_3119_, lean_object* v_pre_3120_, lean_object* v_post_3121_, lean_object* v_usedLetOnly_3122_, lean_object* v_skipConstInApp_3123_, lean_object* v_skipInstances_3124_, lean_object* v_x_3125_, lean_object* v_x_3126_, lean_object* v_fvars_3127_, lean_object* v_e_3128_, lean_object* v_a_3129_){
_start:
{
uint8_t v_usedLetOnly_boxed_3130_; uint8_t v_skipConstInApp_boxed_3131_; uint8_t v_skipInstances_boxed_3132_; lean_object* v_res_3133_; 
v_usedLetOnly_boxed_3130_ = lean_unbox(v_usedLetOnly_3122_);
v_skipConstInApp_boxed_3131_ = lean_unbox(v_skipConstInApp_3123_);
v_skipInstances_boxed_3132_ = lean_unbox(v_skipInstances_3124_);
v_res_3133_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall(v_m_3116_, v_inst_3117_, v_inst_3118_, v_inst_3119_, v_pre_3120_, v_post_3121_, v_usedLetOnly_boxed_3130_, v_skipConstInApp_boxed_3131_, v_skipInstances_boxed_3132_, v_x_3125_, v_x_3126_, v_fvars_3127_, v_e_3128_, v_a_3129_);
lean_dec(v_a_3129_);
return v_res_3133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__0(lean_object* v_x_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_){
_start:
{
lean_object* v___x_3140_; lean_object* v___x_3141_; 
v___x_3140_ = lean_apply_1(v_x_3134_, lean_box(0));
v___x_3141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3141_, 0, v___x_3140_);
return v___x_3141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__0___boxed(lean_object* v_x_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_){
_start:
{
lean_object* v_res_3148_; 
v_res_3148_ = l_Lean_Meta_transformWithCache___redArg___lam__0(v_x_3142_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_);
lean_dec(v___y_3146_);
lean_dec_ref(v___y_3145_);
lean_dec(v___y_3144_);
lean_dec_ref(v___y_3143_);
return v_res_3148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__1(lean_object* v_inst_3149_, lean_object* v_00_u03b1_3150_, lean_object* v_x_3151_){
_start:
{
lean_object* v___f_3152_; lean_object* v___x_3153_; 
v___f_3152_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_3152_, 0, v_x_3151_);
v___x_3153_ = lean_apply_2(v_inst_3149_, lean_box(0), v___f_3152_);
return v___x_3153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__4(lean_object* v_toPure_3154_, lean_object* v_x_3155_, lean_object* v_toBind_3156_, lean_object* v_inst_3157_, lean_object* v_inst_3158_, lean_object* v_inst_3159_, lean_object* v_pre_3160_, lean_object* v_post_3161_, uint8_t v_usedLetOnly_3162_, uint8_t v_skipConstInApp_3163_, uint8_t v_skipInstances_3164_, lean_object* v_x_3165_, lean_object* v_input_3166_, lean_object* v_ref_3167_){
_start:
{
lean_object* v___f_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; 
lean_inc(v_toBind_3156_);
lean_inc(v_x_3155_);
lean_inc(v_ref_3167_);
v___f_3168_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__4), 5, 4);
lean_closure_set(v___f_3168_, 0, v_toPure_3154_);
lean_closure_set(v___f_3168_, 1, v_ref_3167_);
lean_closure_set(v___f_3168_, 2, v_x_3155_);
lean_closure_set(v___f_3168_, 3, v_toBind_3156_);
v___x_3169_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_3157_, v_inst_3158_, v_inst_3159_, v_pre_3160_, v_post_3161_, v_usedLetOnly_3162_, v_skipConstInApp_3163_, v_skipInstances_3164_, v_x_3165_, v_x_3155_, v_input_3166_, v_ref_3167_);
lean_dec(v_ref_3167_);
v___x_3170_ = lean_apply_4(v_toBind_3156_, lean_box(0), lean_box(0), v___x_3169_, v___f_3168_);
return v___x_3170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__4___boxed(lean_object* v_toPure_3171_, lean_object* v_x_3172_, lean_object* v_toBind_3173_, lean_object* v_inst_3174_, lean_object* v_inst_3175_, lean_object* v_inst_3176_, lean_object* v_pre_3177_, lean_object* v_post_3178_, lean_object* v_usedLetOnly_3179_, lean_object* v_skipConstInApp_3180_, lean_object* v_skipInstances_3181_, lean_object* v_x_3182_, lean_object* v_input_3183_, lean_object* v_ref_3184_){
_start:
{
uint8_t v_usedLetOnly_boxed_3185_; uint8_t v_skipConstInApp_boxed_3186_; uint8_t v_skipInstances_boxed_3187_; lean_object* v_res_3188_; 
v_usedLetOnly_boxed_3185_ = lean_unbox(v_usedLetOnly_3179_);
v_skipConstInApp_boxed_3186_ = lean_unbox(v_skipConstInApp_3180_);
v_skipInstances_boxed_3187_ = lean_unbox(v_skipInstances_3181_);
v_res_3188_ = l_Lean_Meta_transformWithCache___redArg___lam__4(v_toPure_3171_, v_x_3172_, v_toBind_3173_, v_inst_3174_, v_inst_3175_, v_inst_3176_, v_pre_3177_, v_post_3178_, v_usedLetOnly_boxed_3185_, v_skipConstInApp_boxed_3186_, v_skipInstances_boxed_3187_, v_x_3182_, v_input_3183_, v_ref_3184_);
return v_res_3188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg(lean_object* v_inst_3189_, lean_object* v_inst_3190_, lean_object* v_inst_3191_, lean_object* v_input_3192_, lean_object* v_cache_3193_, lean_object* v_pre_3194_, lean_object* v_post_3195_, uint8_t v_usedLetOnly_3196_, uint8_t v_skipConstInApp_3197_, uint8_t v_skipInstances_3198_){
_start:
{
lean_object* v_x_3199_; lean_object* v_toApplicative_3200_; lean_object* v_toBind_3201_; lean_object* v_toPure_3202_; lean_object* v_x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___f_3209_; lean_object* v___x_3210_; 
v_x_3199_ = lean_box(0);
v_toApplicative_3200_ = lean_ctor_get(v_inst_3189_, 0);
v_toBind_3201_ = lean_ctor_get(v_inst_3189_, 1);
lean_inc_n(v_toBind_3201_, 2);
v_toPure_3202_ = lean_ctor_get(v_toApplicative_3200_, 1);
lean_inc(v_toPure_3202_);
lean_inc_n(v_inst_3190_, 2);
v_x_3203_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__1), 3, 1);
lean_closure_set(v_x_3203_, 0, v_inst_3190_);
v___x_3204_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_3204_, 0, lean_box(0));
lean_closure_set(v___x_3204_, 1, lean_box(0));
lean_closure_set(v___x_3204_, 2, v_cache_3193_);
v___x_3205_ = l_Lean_Meta_transformWithCache___redArg___lam__1(v_inst_3190_, lean_box(0), v___x_3204_);
v___x_3206_ = lean_box(v_usedLetOnly_3196_);
v___x_3207_ = lean_box(v_skipConstInApp_3197_);
v___x_3208_ = lean_box(v_skipInstances_3198_);
v___f_3209_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__4___boxed), 14, 13);
lean_closure_set(v___f_3209_, 0, v_toPure_3202_);
lean_closure_set(v___f_3209_, 1, v_x_3203_);
lean_closure_set(v___f_3209_, 2, v_toBind_3201_);
lean_closure_set(v___f_3209_, 3, v_inst_3189_);
lean_closure_set(v___f_3209_, 4, v_inst_3190_);
lean_closure_set(v___f_3209_, 5, v_inst_3191_);
lean_closure_set(v___f_3209_, 6, v_pre_3194_);
lean_closure_set(v___f_3209_, 7, v_post_3195_);
lean_closure_set(v___f_3209_, 8, v___x_3206_);
lean_closure_set(v___f_3209_, 9, v___x_3207_);
lean_closure_set(v___f_3209_, 10, v___x_3208_);
lean_closure_set(v___f_3209_, 11, v_x_3199_);
lean_closure_set(v___f_3209_, 12, v_input_3192_);
v___x_3210_ = lean_apply_4(v_toBind_3201_, lean_box(0), lean_box(0), v___x_3205_, v___f_3209_);
return v___x_3210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___boxed(lean_object* v_inst_3211_, lean_object* v_inst_3212_, lean_object* v_inst_3213_, lean_object* v_input_3214_, lean_object* v_cache_3215_, lean_object* v_pre_3216_, lean_object* v_post_3217_, lean_object* v_usedLetOnly_3218_, lean_object* v_skipConstInApp_3219_, lean_object* v_skipInstances_3220_){
_start:
{
uint8_t v_usedLetOnly_boxed_3221_; uint8_t v_skipConstInApp_boxed_3222_; uint8_t v_skipInstances_boxed_3223_; lean_object* v_res_3224_; 
v_usedLetOnly_boxed_3221_ = lean_unbox(v_usedLetOnly_3218_);
v_skipConstInApp_boxed_3222_ = lean_unbox(v_skipConstInApp_3219_);
v_skipInstances_boxed_3223_ = lean_unbox(v_skipInstances_3220_);
v_res_3224_ = l_Lean_Meta_transformWithCache___redArg(v_inst_3211_, v_inst_3212_, v_inst_3213_, v_input_3214_, v_cache_3215_, v_pre_3216_, v_post_3217_, v_usedLetOnly_boxed_3221_, v_skipConstInApp_boxed_3222_, v_skipInstances_boxed_3223_);
return v_res_3224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache(lean_object* v_m_3225_, lean_object* v_inst_3226_, lean_object* v_inst_3227_, lean_object* v_inst_3228_, lean_object* v_input_3229_, lean_object* v_cache_3230_, lean_object* v_pre_3231_, lean_object* v_post_3232_, uint8_t v_usedLetOnly_3233_, uint8_t v_skipConstInApp_3234_, uint8_t v_skipInstances_3235_){
_start:
{
lean_object* v_x_3236_; lean_object* v_toApplicative_3237_; lean_object* v_toBind_3238_; lean_object* v_toPure_3239_; lean_object* v_x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___f_3246_; lean_object* v___x_3247_; 
v_x_3236_ = lean_box(0);
v_toApplicative_3237_ = lean_ctor_get(v_inst_3226_, 0);
v_toBind_3238_ = lean_ctor_get(v_inst_3226_, 1);
lean_inc_n(v_toBind_3238_, 2);
v_toPure_3239_ = lean_ctor_get(v_toApplicative_3237_, 1);
lean_inc(v_toPure_3239_);
lean_inc_n(v_inst_3227_, 2);
v_x_3240_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__1), 3, 1);
lean_closure_set(v_x_3240_, 0, v_inst_3227_);
v___x_3241_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_3241_, 0, lean_box(0));
lean_closure_set(v___x_3241_, 1, lean_box(0));
lean_closure_set(v___x_3241_, 2, v_cache_3230_);
v___x_3242_ = l_Lean_Meta_transformWithCache___redArg___lam__1(v_inst_3227_, lean_box(0), v___x_3241_);
v___x_3243_ = lean_box(v_usedLetOnly_3233_);
v___x_3244_ = lean_box(v_skipConstInApp_3234_);
v___x_3245_ = lean_box(v_skipInstances_3235_);
v___f_3246_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__4___boxed), 14, 13);
lean_closure_set(v___f_3246_, 0, v_toPure_3239_);
lean_closure_set(v___f_3246_, 1, v_x_3240_);
lean_closure_set(v___f_3246_, 2, v_toBind_3238_);
lean_closure_set(v___f_3246_, 3, v_inst_3226_);
lean_closure_set(v___f_3246_, 4, v_inst_3227_);
lean_closure_set(v___f_3246_, 5, v_inst_3228_);
lean_closure_set(v___f_3246_, 6, v_pre_3231_);
lean_closure_set(v___f_3246_, 7, v_post_3232_);
lean_closure_set(v___f_3246_, 8, v___x_3243_);
lean_closure_set(v___f_3246_, 9, v___x_3244_);
lean_closure_set(v___f_3246_, 10, v___x_3245_);
lean_closure_set(v___f_3246_, 11, v_x_3236_);
lean_closure_set(v___f_3246_, 12, v_input_3229_);
v___x_3247_ = lean_apply_4(v_toBind_3238_, lean_box(0), lean_box(0), v___x_3242_, v___f_3246_);
return v___x_3247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___boxed(lean_object* v_m_3248_, lean_object* v_inst_3249_, lean_object* v_inst_3250_, lean_object* v_inst_3251_, lean_object* v_input_3252_, lean_object* v_cache_3253_, lean_object* v_pre_3254_, lean_object* v_post_3255_, lean_object* v_usedLetOnly_3256_, lean_object* v_skipConstInApp_3257_, lean_object* v_skipInstances_3258_){
_start:
{
uint8_t v_usedLetOnly_boxed_3259_; uint8_t v_skipConstInApp_boxed_3260_; uint8_t v_skipInstances_boxed_3261_; lean_object* v_res_3262_; 
v_usedLetOnly_boxed_3259_ = lean_unbox(v_usedLetOnly_3256_);
v_skipConstInApp_boxed_3260_ = lean_unbox(v_skipConstInApp_3257_);
v_skipInstances_boxed_3261_ = lean_unbox(v_skipInstances_3258_);
v_res_3262_ = l_Lean_Meta_transformWithCache(v_m_3248_, v_inst_3249_, v_inst_3250_, v_inst_3251_, v_input_3252_, v_cache_3253_, v_pre_3254_, v_post_3255_, v_usedLetOnly_boxed_3259_, v_skipConstInApp_boxed_3260_, v_skipInstances_boxed_3261_);
return v_res_3262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___redArg___lam__5(lean_object* v_toPure_3263_, lean_object* v_x_3264_, lean_object* v_toBind_3265_, lean_object* v_inst_3266_, lean_object* v_inst_3267_, lean_object* v_inst_3268_, lean_object* v_pre_3269_, lean_object* v_post_3270_, uint8_t v_usedLetOnly_3271_, uint8_t v_skipConstInApp_3272_, uint8_t v___x_3273_, lean_object* v_x_3274_, lean_object* v_input_3275_, lean_object* v_ref_3276_){
_start:
{
lean_object* v___f_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; 
lean_inc(v_toBind_3265_);
lean_inc(v_x_3264_);
lean_inc(v_ref_3276_);
v___f_3277_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__4), 5, 4);
lean_closure_set(v___f_3277_, 0, v_toPure_3263_);
lean_closure_set(v___f_3277_, 1, v_ref_3276_);
lean_closure_set(v___f_3277_, 2, v_x_3264_);
lean_closure_set(v___f_3277_, 3, v_toBind_3265_);
v___x_3278_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_3266_, v_inst_3267_, v_inst_3268_, v_pre_3269_, v_post_3270_, v_usedLetOnly_3271_, v_skipConstInApp_3272_, v___x_3273_, v_x_3274_, v_x_3264_, v_input_3275_, v_ref_3276_);
lean_dec(v_ref_3276_);
v___x_3279_ = lean_apply_4(v_toBind_3265_, lean_box(0), lean_box(0), v___x_3278_, v___f_3277_);
return v___x_3279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___redArg___lam__5___boxed(lean_object* v_toPure_3280_, lean_object* v_x_3281_, lean_object* v_toBind_3282_, lean_object* v_inst_3283_, lean_object* v_inst_3284_, lean_object* v_inst_3285_, lean_object* v_pre_3286_, lean_object* v_post_3287_, lean_object* v_usedLetOnly_3288_, lean_object* v_skipConstInApp_3289_, lean_object* v___x_3290_, lean_object* v_x_3291_, lean_object* v_input_3292_, lean_object* v_ref_3293_){
_start:
{
uint8_t v_usedLetOnly_boxed_3294_; uint8_t v_skipConstInApp_boxed_3295_; uint8_t v___x_115__boxed_3296_; lean_object* v_res_3297_; 
v_usedLetOnly_boxed_3294_ = lean_unbox(v_usedLetOnly_3288_);
v_skipConstInApp_boxed_3295_ = lean_unbox(v_skipConstInApp_3289_);
v___x_115__boxed_3296_ = lean_unbox(v___x_3290_);
v_res_3297_ = l_Lean_Meta_transform___redArg___lam__5(v_toPure_3280_, v_x_3281_, v_toBind_3282_, v_inst_3283_, v_inst_3284_, v_inst_3285_, v_pre_3286_, v_post_3287_, v_usedLetOnly_boxed_3294_, v_skipConstInApp_boxed_3295_, v___x_115__boxed_3296_, v_x_3291_, v_input_3292_, v_ref_3293_);
return v_res_3297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___redArg(lean_object* v_inst_3298_, lean_object* v_inst_3299_, lean_object* v_inst_3300_, lean_object* v_input_3301_, lean_object* v_pre_3302_, lean_object* v_post_3303_, uint8_t v_usedLetOnly_3304_, uint8_t v_skipConstInApp_3305_){
_start:
{
lean_object* v_toApplicative_3306_; lean_object* v_toBind_3307_; lean_object* v_x_3308_; lean_object* v_toPure_3309_; lean_object* v_x_3310_; uint8_t v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___f_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___f_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; 
v_toApplicative_3306_ = lean_ctor_get(v_inst_3298_, 0);
v_toBind_3307_ = lean_ctor_get(v_inst_3298_, 1);
lean_inc_n(v_toBind_3307_, 3);
v_x_3308_ = lean_box(0);
v_toPure_3309_ = lean_ctor_get(v_toApplicative_3306_, 1);
lean_inc_n(v_toPure_3309_, 2);
lean_inc_n(v_inst_3299_, 2);
v_x_3310_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__1), 3, 1);
lean_closure_set(v_x_3310_, 0, v_inst_3299_);
v___x_3311_ = 0;
v___x_3312_ = lean_obj_once(&l_Lean_Core_transform___redArg___closed__2, &l_Lean_Core_transform___redArg___closed__2_once, _init_l_Lean_Core_transform___redArg___closed__2);
v___x_3313_ = l_Lean_Meta_transformWithCache___redArg___lam__1(v_inst_3299_, lean_box(0), v___x_3312_);
v___f_3314_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__2), 2, 1);
lean_closure_set(v___f_3314_, 0, v_toPure_3309_);
v___x_3315_ = lean_box(v_usedLetOnly_3304_);
v___x_3316_ = lean_box(v_skipConstInApp_3305_);
v___x_3317_ = lean_box(v___x_3311_);
v___f_3318_ = lean_alloc_closure((void*)(l_Lean_Meta_transform___redArg___lam__5___boxed), 14, 13);
lean_closure_set(v___f_3318_, 0, v_toPure_3309_);
lean_closure_set(v___f_3318_, 1, v_x_3310_);
lean_closure_set(v___f_3318_, 2, v_toBind_3307_);
lean_closure_set(v___f_3318_, 3, v_inst_3298_);
lean_closure_set(v___f_3318_, 4, v_inst_3299_);
lean_closure_set(v___f_3318_, 5, v_inst_3300_);
lean_closure_set(v___f_3318_, 6, v_pre_3302_);
lean_closure_set(v___f_3318_, 7, v_post_3303_);
lean_closure_set(v___f_3318_, 8, v___x_3315_);
lean_closure_set(v___f_3318_, 9, v___x_3316_);
lean_closure_set(v___f_3318_, 10, v___x_3317_);
lean_closure_set(v___f_3318_, 11, v_x_3308_);
lean_closure_set(v___f_3318_, 12, v_input_3301_);
v___x_3319_ = lean_apply_4(v_toBind_3307_, lean_box(0), lean_box(0), v___x_3313_, v___f_3318_);
v___x_3320_ = lean_apply_4(v_toBind_3307_, lean_box(0), lean_box(0), v___x_3319_, v___f_3314_);
return v___x_3320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___redArg___boxed(lean_object* v_inst_3321_, lean_object* v_inst_3322_, lean_object* v_inst_3323_, lean_object* v_input_3324_, lean_object* v_pre_3325_, lean_object* v_post_3326_, lean_object* v_usedLetOnly_3327_, lean_object* v_skipConstInApp_3328_){
_start:
{
uint8_t v_usedLetOnly_boxed_3329_; uint8_t v_skipConstInApp_boxed_3330_; lean_object* v_res_3331_; 
v_usedLetOnly_boxed_3329_ = lean_unbox(v_usedLetOnly_3327_);
v_skipConstInApp_boxed_3330_ = lean_unbox(v_skipConstInApp_3328_);
v_res_3331_ = l_Lean_Meta_transform___redArg(v_inst_3321_, v_inst_3322_, v_inst_3323_, v_input_3324_, v_pre_3325_, v_post_3326_, v_usedLetOnly_boxed_3329_, v_skipConstInApp_boxed_3330_);
return v_res_3331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform(lean_object* v_m_3332_, lean_object* v_inst_3333_, lean_object* v_inst_3334_, lean_object* v_inst_3335_, lean_object* v_input_3336_, lean_object* v_pre_3337_, lean_object* v_post_3338_, uint8_t v_usedLetOnly_3339_, uint8_t v_skipConstInApp_3340_){
_start:
{
lean_object* v___x_3341_; 
v___x_3341_ = l_Lean_Meta_transform___redArg(v_inst_3333_, v_inst_3334_, v_inst_3335_, v_input_3336_, v_pre_3337_, v_post_3338_, v_usedLetOnly_3339_, v_skipConstInApp_3340_);
return v___x_3341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___boxed(lean_object* v_m_3342_, lean_object* v_inst_3343_, lean_object* v_inst_3344_, lean_object* v_inst_3345_, lean_object* v_input_3346_, lean_object* v_pre_3347_, lean_object* v_post_3348_, lean_object* v_usedLetOnly_3349_, lean_object* v_skipConstInApp_3350_){
_start:
{
uint8_t v_usedLetOnly_boxed_3351_; uint8_t v_skipConstInApp_boxed_3352_; lean_object* v_res_3353_; 
v_usedLetOnly_boxed_3351_ = lean_unbox(v_usedLetOnly_3349_);
v_skipConstInApp_boxed_3352_ = lean_unbox(v_skipConstInApp_3350_);
v_res_3353_ = l_Lean_Meta_transform(v_m_3342_, v_inst_3343_, v_inst_3344_, v_inst_3345_, v_input_3346_, v_pre_3347_, v_post_3348_, v_usedLetOnly_boxed_3351_, v_skipConstInApp_boxed_3352_);
return v_res_3353_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(lean_object* v_e_3354_, lean_object* v___y_3355_){
_start:
{
uint8_t v___x_3357_; 
v___x_3357_ = l_Lean_Expr_hasMVar(v_e_3354_);
if (v___x_3357_ == 0)
{
lean_object* v___x_3358_; 
v___x_3358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3358_, 0, v_e_3354_);
return v___x_3358_;
}
else
{
lean_object* v___x_3359_; lean_object* v_mctx_3360_; lean_object* v___x_3361_; lean_object* v_fst_3362_; lean_object* v_snd_3363_; lean_object* v___x_3364_; lean_object* v_cache_3365_; lean_object* v_zetaDeltaFVarIds_3366_; lean_object* v_postponed_3367_; lean_object* v_diag_3368_; lean_object* v___x_3370_; uint8_t v_isShared_3371_; uint8_t v_isSharedCheck_3377_; 
v___x_3359_ = lean_st_ref_get(v___y_3355_);
v_mctx_3360_ = lean_ctor_get(v___x_3359_, 0);
lean_inc_ref(v_mctx_3360_);
lean_dec(v___x_3359_);
v___x_3361_ = l_Lean_instantiateMVarsCore(v_mctx_3360_, v_e_3354_);
v_fst_3362_ = lean_ctor_get(v___x_3361_, 0);
lean_inc(v_fst_3362_);
v_snd_3363_ = lean_ctor_get(v___x_3361_, 1);
lean_inc(v_snd_3363_);
lean_dec_ref(v___x_3361_);
v___x_3364_ = lean_st_ref_take(v___y_3355_);
v_cache_3365_ = lean_ctor_get(v___x_3364_, 1);
v_zetaDeltaFVarIds_3366_ = lean_ctor_get(v___x_3364_, 2);
v_postponed_3367_ = lean_ctor_get(v___x_3364_, 3);
v_diag_3368_ = lean_ctor_get(v___x_3364_, 4);
v_isSharedCheck_3377_ = !lean_is_exclusive(v___x_3364_);
if (v_isSharedCheck_3377_ == 0)
{
lean_object* v_unused_3378_; 
v_unused_3378_ = lean_ctor_get(v___x_3364_, 0);
lean_dec(v_unused_3378_);
v___x_3370_ = v___x_3364_;
v_isShared_3371_ = v_isSharedCheck_3377_;
goto v_resetjp_3369_;
}
else
{
lean_inc(v_diag_3368_);
lean_inc(v_postponed_3367_);
lean_inc(v_zetaDeltaFVarIds_3366_);
lean_inc(v_cache_3365_);
lean_dec(v___x_3364_);
v___x_3370_ = lean_box(0);
v_isShared_3371_ = v_isSharedCheck_3377_;
goto v_resetjp_3369_;
}
v_resetjp_3369_:
{
lean_object* v___x_3373_; 
if (v_isShared_3371_ == 0)
{
lean_ctor_set(v___x_3370_, 0, v_snd_3363_);
v___x_3373_ = v___x_3370_;
goto v_reusejp_3372_;
}
else
{
lean_object* v_reuseFailAlloc_3376_; 
v_reuseFailAlloc_3376_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3376_, 0, v_snd_3363_);
lean_ctor_set(v_reuseFailAlloc_3376_, 1, v_cache_3365_);
lean_ctor_set(v_reuseFailAlloc_3376_, 2, v_zetaDeltaFVarIds_3366_);
lean_ctor_set(v_reuseFailAlloc_3376_, 3, v_postponed_3367_);
lean_ctor_set(v_reuseFailAlloc_3376_, 4, v_diag_3368_);
v___x_3373_ = v_reuseFailAlloc_3376_;
goto v_reusejp_3372_;
}
v_reusejp_3372_:
{
lean_object* v___x_3374_; lean_object* v___x_3375_; 
v___x_3374_ = lean_st_ref_put(v___y_3355_, v___x_3373_);
v___x_3375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3375_, 0, v_fst_3362_);
return v___x_3375_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg___boxed(lean_object* v_e_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_){
_start:
{
lean_object* v_res_3382_; 
v_res_3382_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(v_e_3379_, v___y_3380_);
lean_dec(v___y_3380_);
return v_res_3382_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0(lean_object* v_e_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_){
_start:
{
lean_object* v___x_3389_; 
v___x_3389_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(v_e_3383_, v___y_3385_);
return v___x_3389_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___boxed(lean_object* v_e_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_){
_start:
{
lean_object* v_res_3396_; 
v_res_3396_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0(v_e_3390_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_);
lean_dec(v___y_3394_);
lean_dec_ref(v___y_3393_);
lean_dec(v___y_3392_);
lean_dec_ref(v___y_3391_);
return v_res_3396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__0(uint8_t v_zetaHave_3397_, lean_object* v___x_3398_, uint8_t v_zetaDelta_3399_, lean_object* v_fvarId_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_){
_start:
{
lean_object* v___x_3406_; 
v___x_3406_ = l_Lean_FVarId_findDecl_x3f___redArg(v_fvarId_3400_, v___y_3401_);
if (lean_obj_tag(v___x_3406_) == 0)
{
lean_object* v_a_3407_; lean_object* v___x_3409_; uint8_t v_isShared_3410_; uint8_t v_isSharedCheck_3435_; 
v_a_3407_ = lean_ctor_get(v___x_3406_, 0);
v_isSharedCheck_3435_ = !lean_is_exclusive(v___x_3406_);
if (v_isSharedCheck_3435_ == 0)
{
v___x_3409_ = v___x_3406_;
v_isShared_3410_ = v_isSharedCheck_3435_;
goto v_resetjp_3408_;
}
else
{
lean_inc(v_a_3407_);
lean_dec(v___x_3406_);
v___x_3409_ = lean_box(0);
v_isShared_3410_ = v_isSharedCheck_3435_;
goto v_resetjp_3408_;
}
v_resetjp_3408_:
{
if (lean_obj_tag(v_a_3407_) == 1)
{
lean_object* v_val_3411_; lean_object* v___x_3413_; uint8_t v_isShared_3414_; uint8_t v_isSharedCheck_3430_; 
v_val_3411_ = lean_ctor_get(v_a_3407_, 0);
v_isSharedCheck_3430_ = !lean_is_exclusive(v_a_3407_);
if (v_isSharedCheck_3430_ == 0)
{
v___x_3413_ = v_a_3407_;
v_isShared_3414_ = v_isSharedCheck_3430_;
goto v_resetjp_3412_;
}
else
{
lean_inc(v_val_3411_);
lean_dec(v_a_3407_);
v___x_3413_ = lean_box(0);
v_isShared_3414_ = v_isSharedCheck_3430_;
goto v_resetjp_3412_;
}
v_resetjp_3412_:
{
uint8_t v___y_3416_; 
if (v_zetaDelta_3399_ == 0)
{
lean_object* v___x_3424_; uint8_t v___x_3425_; 
v___x_3424_ = l_Lean_LocalDecl_index(v_val_3411_);
v___x_3425_ = lean_nat_dec_lt(v___x_3424_, v___x_3398_);
lean_dec(v___x_3424_);
if (v___x_3425_ == 0)
{
lean_del_object(v___x_3413_);
goto v___jp_3421_;
}
else
{
lean_object* v___x_3426_; lean_object* v___x_3428_; 
lean_dec(v_val_3411_);
lean_del_object(v___x_3409_);
v___x_3426_ = lean_box(0);
if (v_isShared_3414_ == 0)
{
lean_ctor_set_tag(v___x_3413_, 0);
lean_ctor_set(v___x_3413_, 0, v___x_3426_);
v___x_3428_ = v___x_3413_;
goto v_reusejp_3427_;
}
else
{
lean_object* v_reuseFailAlloc_3429_; 
v_reuseFailAlloc_3429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3429_, 0, v___x_3426_);
v___x_3428_ = v_reuseFailAlloc_3429_;
goto v_reusejp_3427_;
}
v_reusejp_3427_:
{
return v___x_3428_;
}
}
}
else
{
lean_del_object(v___x_3413_);
goto v___jp_3421_;
}
v___jp_3415_:
{
lean_object* v___x_3417_; lean_object* v___x_3419_; 
v___x_3417_ = l_Lean_LocalDecl_value_x3f(v_val_3411_, v___y_3416_);
lean_dec(v_val_3411_);
if (v_isShared_3410_ == 0)
{
lean_ctor_set(v___x_3409_, 0, v___x_3417_);
v___x_3419_ = v___x_3409_;
goto v_reusejp_3418_;
}
else
{
lean_object* v_reuseFailAlloc_3420_; 
v_reuseFailAlloc_3420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3420_, 0, v___x_3417_);
v___x_3419_ = v_reuseFailAlloc_3420_;
goto v_reusejp_3418_;
}
v_reusejp_3418_:
{
return v___x_3419_;
}
}
v___jp_3421_:
{
if (v_zetaHave_3397_ == 0)
{
v___y_3416_ = v_zetaHave_3397_;
goto v___jp_3415_;
}
else
{
lean_object* v___x_3422_; uint8_t v___x_3423_; 
v___x_3422_ = l_Lean_LocalDecl_index(v_val_3411_);
v___x_3423_ = lean_nat_dec_le(v___x_3398_, v___x_3422_);
lean_dec(v___x_3422_);
v___y_3416_ = v___x_3423_;
goto v___jp_3415_;
}
}
}
}
else
{
lean_object* v___x_3431_; lean_object* v___x_3433_; 
lean_dec(v_a_3407_);
v___x_3431_ = lean_box(0);
if (v_isShared_3410_ == 0)
{
lean_ctor_set(v___x_3409_, 0, v___x_3431_);
v___x_3433_ = v___x_3409_;
goto v_reusejp_3432_;
}
else
{
lean_object* v_reuseFailAlloc_3434_; 
v_reuseFailAlloc_3434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3434_, 0, v___x_3431_);
v___x_3433_ = v_reuseFailAlloc_3434_;
goto v_reusejp_3432_;
}
v_reusejp_3432_:
{
return v___x_3433_;
}
}
}
}
else
{
lean_object* v_a_3436_; lean_object* v___x_3438_; uint8_t v_isShared_3439_; uint8_t v_isSharedCheck_3443_; 
v_a_3436_ = lean_ctor_get(v___x_3406_, 0);
v_isSharedCheck_3443_ = !lean_is_exclusive(v___x_3406_);
if (v_isSharedCheck_3443_ == 0)
{
v___x_3438_ = v___x_3406_;
v_isShared_3439_ = v_isSharedCheck_3443_;
goto v_resetjp_3437_;
}
else
{
lean_inc(v_a_3436_);
lean_dec(v___x_3406_);
v___x_3438_ = lean_box(0);
v_isShared_3439_ = v_isSharedCheck_3443_;
goto v_resetjp_3437_;
}
v_resetjp_3437_:
{
lean_object* v___x_3441_; 
if (v_isShared_3439_ == 0)
{
v___x_3441_ = v___x_3438_;
goto v_reusejp_3440_;
}
else
{
lean_object* v_reuseFailAlloc_3442_; 
v_reuseFailAlloc_3442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3442_, 0, v_a_3436_);
v___x_3441_ = v_reuseFailAlloc_3442_;
goto v_reusejp_3440_;
}
v_reusejp_3440_:
{
return v___x_3441_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__0___boxed(lean_object* v_zetaHave_3444_, lean_object* v___x_3445_, lean_object* v_zetaDelta_3446_, lean_object* v_fvarId_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_){
_start:
{
uint8_t v_zetaHave_boxed_3453_; uint8_t v_zetaDelta_boxed_3454_; lean_object* v_res_3455_; 
v_zetaHave_boxed_3453_ = lean_unbox(v_zetaHave_3444_);
v_zetaDelta_boxed_3454_ = lean_unbox(v_zetaDelta_3446_);
v_res_3455_ = l_Lean_Meta_zetaReduce___lam__0(v_zetaHave_boxed_3453_, v___x_3445_, v_zetaDelta_boxed_3454_, v_fvarId_3447_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_);
lean_dec(v___y_3451_);
lean_dec_ref(v___y_3450_);
lean_dec(v___y_3449_);
lean_dec_ref(v___y_3448_);
lean_dec(v___x_3445_);
return v_res_3455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__1(lean_object* v_e_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_){
_start:
{
lean_object* v___x_3462_; lean_object* v___x_3463_; 
v___x_3462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3462_, 0, v_e_3456_);
v___x_3463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3463_, 0, v___x_3462_);
return v___x_3463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__1___boxed(lean_object* v_e_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_){
_start:
{
lean_object* v_res_3470_; 
v_res_3470_ = l_Lean_Meta_zetaReduce___lam__1(v_e_3464_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_);
lean_dec(v___y_3468_);
lean_dec_ref(v___y_3467_);
lean_dec(v___y_3466_);
lean_dec_ref(v___y_3465_);
return v_res_3470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__2(lean_object* v___f_3471_, lean_object* v_e_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_){
_start:
{
if (lean_obj_tag(v_e_3472_) == 1)
{
lean_object* v_fvarId_3478_; lean_object* v___x_3479_; 
v_fvarId_3478_ = lean_ctor_get(v_e_3472_, 0);
lean_inc(v___y_3476_);
lean_inc_ref(v___y_3475_);
lean_inc(v___y_3474_);
lean_inc_ref(v___y_3473_);
lean_inc(v_fvarId_3478_);
v___x_3479_ = lean_apply_6(v___f_3471_, v_fvarId_3478_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_, lean_box(0));
if (lean_obj_tag(v___x_3479_) == 0)
{
lean_object* v_a_3480_; lean_object* v___x_3482_; uint8_t v_isShared_3483_; uint8_t v_isSharedCheck_3505_; 
v_a_3480_ = lean_ctor_get(v___x_3479_, 0);
v_isSharedCheck_3505_ = !lean_is_exclusive(v___x_3479_);
if (v_isSharedCheck_3505_ == 0)
{
v___x_3482_ = v___x_3479_;
v_isShared_3483_ = v_isSharedCheck_3505_;
goto v_resetjp_3481_;
}
else
{
lean_inc(v_a_3480_);
lean_dec(v___x_3479_);
v___x_3482_ = lean_box(0);
v_isShared_3483_ = v_isSharedCheck_3505_;
goto v_resetjp_3481_;
}
v_resetjp_3481_:
{
if (lean_obj_tag(v_a_3480_) == 1)
{
lean_object* v_val_3484_; lean_object* v___x_3486_; uint8_t v_isShared_3487_; uint8_t v_isSharedCheck_3500_; 
lean_del_object(v___x_3482_);
lean_dec_ref_known(v_e_3472_, 1);
v_val_3484_ = lean_ctor_get(v_a_3480_, 0);
v_isSharedCheck_3500_ = !lean_is_exclusive(v_a_3480_);
if (v_isSharedCheck_3500_ == 0)
{
v___x_3486_ = v_a_3480_;
v_isShared_3487_ = v_isSharedCheck_3500_;
goto v_resetjp_3485_;
}
else
{
lean_inc(v_val_3484_);
lean_dec(v_a_3480_);
v___x_3486_ = lean_box(0);
v_isShared_3487_ = v_isSharedCheck_3500_;
goto v_resetjp_3485_;
}
v_resetjp_3485_:
{
lean_object* v___x_3488_; lean_object* v_a_3489_; lean_object* v___x_3491_; uint8_t v_isShared_3492_; uint8_t v_isSharedCheck_3499_; 
v___x_3488_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(v_val_3484_, v___y_3474_);
v_a_3489_ = lean_ctor_get(v___x_3488_, 0);
v_isSharedCheck_3499_ = !lean_is_exclusive(v___x_3488_);
if (v_isSharedCheck_3499_ == 0)
{
v___x_3491_ = v___x_3488_;
v_isShared_3492_ = v_isSharedCheck_3499_;
goto v_resetjp_3490_;
}
else
{
lean_inc(v_a_3489_);
lean_dec(v___x_3488_);
v___x_3491_ = lean_box(0);
v_isShared_3492_ = v_isSharedCheck_3499_;
goto v_resetjp_3490_;
}
v_resetjp_3490_:
{
lean_object* v___x_3494_; 
if (v_isShared_3487_ == 0)
{
lean_ctor_set(v___x_3486_, 0, v_a_3489_);
v___x_3494_ = v___x_3486_;
goto v_reusejp_3493_;
}
else
{
lean_object* v_reuseFailAlloc_3498_; 
v_reuseFailAlloc_3498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3498_, 0, v_a_3489_);
v___x_3494_ = v_reuseFailAlloc_3498_;
goto v_reusejp_3493_;
}
v_reusejp_3493_:
{
lean_object* v___x_3496_; 
if (v_isShared_3492_ == 0)
{
lean_ctor_set(v___x_3491_, 0, v___x_3494_);
v___x_3496_ = v___x_3491_;
goto v_reusejp_3495_;
}
else
{
lean_object* v_reuseFailAlloc_3497_; 
v_reuseFailAlloc_3497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3497_, 0, v___x_3494_);
v___x_3496_ = v_reuseFailAlloc_3497_;
goto v_reusejp_3495_;
}
v_reusejp_3495_:
{
return v___x_3496_;
}
}
}
}
}
else
{
lean_object* v___x_3501_; lean_object* v___x_3503_; 
lean_dec(v_a_3480_);
v___x_3501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3501_, 0, v_e_3472_);
if (v_isShared_3483_ == 0)
{
lean_ctor_set(v___x_3482_, 0, v___x_3501_);
v___x_3503_ = v___x_3482_;
goto v_reusejp_3502_;
}
else
{
lean_object* v_reuseFailAlloc_3504_; 
v_reuseFailAlloc_3504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3504_, 0, v___x_3501_);
v___x_3503_ = v_reuseFailAlloc_3504_;
goto v_reusejp_3502_;
}
v_reusejp_3502_:
{
return v___x_3503_;
}
}
}
}
else
{
lean_object* v_a_3506_; lean_object* v___x_3508_; uint8_t v_isShared_3509_; uint8_t v_isSharedCheck_3513_; 
lean_dec_ref_known(v_e_3472_, 1);
v_a_3506_ = lean_ctor_get(v___x_3479_, 0);
v_isSharedCheck_3513_ = !lean_is_exclusive(v___x_3479_);
if (v_isSharedCheck_3513_ == 0)
{
v___x_3508_ = v___x_3479_;
v_isShared_3509_ = v_isSharedCheck_3513_;
goto v_resetjp_3507_;
}
else
{
lean_inc(v_a_3506_);
lean_dec(v___x_3479_);
v___x_3508_ = lean_box(0);
v_isShared_3509_ = v_isSharedCheck_3513_;
goto v_resetjp_3507_;
}
v_resetjp_3507_:
{
lean_object* v___x_3511_; 
if (v_isShared_3509_ == 0)
{
v___x_3511_ = v___x_3508_;
goto v_reusejp_3510_;
}
else
{
lean_object* v_reuseFailAlloc_3512_; 
v_reuseFailAlloc_3512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3512_, 0, v_a_3506_);
v___x_3511_ = v_reuseFailAlloc_3512_;
goto v_reusejp_3510_;
}
v_reusejp_3510_:
{
return v___x_3511_;
}
}
}
}
else
{
lean_object* v___x_3514_; lean_object* v___x_3515_; 
lean_dec_ref(v_e_3472_);
lean_dec_ref(v___f_3471_);
v___x_3514_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_3515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3515_, 0, v___x_3514_);
return v___x_3515_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__2___boxed(lean_object* v___f_3516_, lean_object* v_e_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_){
_start:
{
lean_object* v_res_3523_; 
v_res_3523_ = l_Lean_Meta_zetaReduce___lam__2(v___f_3516_, v_e_3517_, v___y_3518_, v___y_3519_, v___y_3520_, v___y_3521_);
lean_dec(v___y_3521_);
lean_dec_ref(v___y_3520_);
lean_dec(v___y_3519_);
lean_dec_ref(v___y_3518_);
return v_res_3523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__4(lean_object* v___f_3524_, lean_object* v_e_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_){
_start:
{
lean_object* v___x_3531_; 
v___x_3531_ = l_Lean_Expr_getAppFn(v_e_3525_);
if (lean_obj_tag(v___x_3531_) == 1)
{
lean_object* v_fvarId_3532_; lean_object* v___x_3533_; 
v_fvarId_3532_ = lean_ctor_get(v___x_3531_, 0);
lean_inc(v_fvarId_3532_);
lean_dec_ref_known(v___x_3531_, 1);
lean_inc(v___y_3529_);
lean_inc_ref(v___y_3528_);
lean_inc(v___y_3527_);
lean_inc_ref(v___y_3526_);
v___x_3533_ = lean_apply_6(v___f_3524_, v_fvarId_3532_, v___y_3526_, v___y_3527_, v___y_3528_, v___y_3529_, lean_box(0));
if (lean_obj_tag(v___x_3533_) == 0)
{
lean_object* v_a_3534_; lean_object* v___x_3536_; uint8_t v_isShared_3537_; uint8_t v_isSharedCheck_3566_; 
v_a_3534_ = lean_ctor_get(v___x_3533_, 0);
v_isSharedCheck_3566_ = !lean_is_exclusive(v___x_3533_);
if (v_isSharedCheck_3566_ == 0)
{
v___x_3536_ = v___x_3533_;
v_isShared_3537_ = v_isSharedCheck_3566_;
goto v_resetjp_3535_;
}
else
{
lean_inc(v_a_3534_);
lean_dec(v___x_3533_);
v___x_3536_ = lean_box(0);
v_isShared_3537_ = v_isSharedCheck_3566_;
goto v_resetjp_3535_;
}
v_resetjp_3535_:
{
if (lean_obj_tag(v_a_3534_) == 1)
{
lean_object* v_val_3538_; lean_object* v___x_3540_; uint8_t v_isShared_3541_; uint8_t v_isSharedCheck_3561_; 
lean_del_object(v___x_3536_);
v_val_3538_ = lean_ctor_get(v_a_3534_, 0);
v_isSharedCheck_3561_ = !lean_is_exclusive(v_a_3534_);
if (v_isSharedCheck_3561_ == 0)
{
v___x_3540_ = v_a_3534_;
v_isShared_3541_ = v_isSharedCheck_3561_;
goto v_resetjp_3539_;
}
else
{
lean_inc(v_val_3538_);
lean_dec(v_a_3534_);
v___x_3540_ = lean_box(0);
v_isShared_3541_ = v_isSharedCheck_3561_;
goto v_resetjp_3539_;
}
v_resetjp_3539_:
{
lean_object* v___x_3542_; lean_object* v_a_3543_; lean_object* v___x_3545_; uint8_t v_isShared_3546_; uint8_t v_isSharedCheck_3560_; 
v___x_3542_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(v_val_3538_, v___y_3527_);
v_a_3543_ = lean_ctor_get(v___x_3542_, 0);
v_isSharedCheck_3560_ = !lean_is_exclusive(v___x_3542_);
if (v_isSharedCheck_3560_ == 0)
{
v___x_3545_ = v___x_3542_;
v_isShared_3546_ = v_isSharedCheck_3560_;
goto v_resetjp_3544_;
}
else
{
lean_inc(v_a_3543_);
lean_dec(v___x_3542_);
v___x_3545_ = lean_box(0);
v_isShared_3546_ = v_isSharedCheck_3560_;
goto v_resetjp_3544_;
}
v_resetjp_3544_:
{
lean_object* v_dummy_3547_; lean_object* v_nargs_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3555_; 
v_dummy_3547_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_3548_ = l_Lean_Expr_getAppNumArgs(v_e_3525_);
lean_inc(v_nargs_3548_);
v___x_3549_ = lean_mk_array(v_nargs_3548_, v_dummy_3547_);
v___x_3550_ = lean_unsigned_to_nat(1u);
v___x_3551_ = lean_nat_sub(v_nargs_3548_, v___x_3550_);
lean_dec(v_nargs_3548_);
v___x_3552_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3525_, v___x_3549_, v___x_3551_);
v___x_3553_ = l_Lean_Expr_beta(v_a_3543_, v___x_3552_);
if (v_isShared_3541_ == 0)
{
lean_ctor_set(v___x_3540_, 0, v___x_3553_);
v___x_3555_ = v___x_3540_;
goto v_reusejp_3554_;
}
else
{
lean_object* v_reuseFailAlloc_3559_; 
v_reuseFailAlloc_3559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3559_, 0, v___x_3553_);
v___x_3555_ = v_reuseFailAlloc_3559_;
goto v_reusejp_3554_;
}
v_reusejp_3554_:
{
lean_object* v___x_3557_; 
if (v_isShared_3546_ == 0)
{
lean_ctor_set(v___x_3545_, 0, v___x_3555_);
v___x_3557_ = v___x_3545_;
goto v_reusejp_3556_;
}
else
{
lean_object* v_reuseFailAlloc_3558_; 
v_reuseFailAlloc_3558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3558_, 0, v___x_3555_);
v___x_3557_ = v_reuseFailAlloc_3558_;
goto v_reusejp_3556_;
}
v_reusejp_3556_:
{
return v___x_3557_;
}
}
}
}
}
else
{
lean_object* v___x_3562_; lean_object* v___x_3564_; 
lean_dec(v_a_3534_);
lean_dec_ref(v_e_3525_);
v___x_3562_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
if (v_isShared_3537_ == 0)
{
lean_ctor_set(v___x_3536_, 0, v___x_3562_);
v___x_3564_ = v___x_3536_;
goto v_reusejp_3563_;
}
else
{
lean_object* v_reuseFailAlloc_3565_; 
v_reuseFailAlloc_3565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3565_, 0, v___x_3562_);
v___x_3564_ = v_reuseFailAlloc_3565_;
goto v_reusejp_3563_;
}
v_reusejp_3563_:
{
return v___x_3564_;
}
}
}
}
else
{
lean_object* v_a_3567_; lean_object* v___x_3569_; uint8_t v_isShared_3570_; uint8_t v_isSharedCheck_3574_; 
lean_dec_ref(v_e_3525_);
v_a_3567_ = lean_ctor_get(v___x_3533_, 0);
v_isSharedCheck_3574_ = !lean_is_exclusive(v___x_3533_);
if (v_isSharedCheck_3574_ == 0)
{
v___x_3569_ = v___x_3533_;
v_isShared_3570_ = v_isSharedCheck_3574_;
goto v_resetjp_3568_;
}
else
{
lean_inc(v_a_3567_);
lean_dec(v___x_3533_);
v___x_3569_ = lean_box(0);
v_isShared_3570_ = v_isSharedCheck_3574_;
goto v_resetjp_3568_;
}
v_resetjp_3568_:
{
lean_object* v___x_3572_; 
if (v_isShared_3570_ == 0)
{
v___x_3572_ = v___x_3569_;
goto v_reusejp_3571_;
}
else
{
lean_object* v_reuseFailAlloc_3573_; 
v_reuseFailAlloc_3573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3573_, 0, v_a_3567_);
v___x_3572_ = v_reuseFailAlloc_3573_;
goto v_reusejp_3571_;
}
v_reusejp_3571_:
{
return v___x_3572_;
}
}
}
}
else
{
lean_object* v___x_3575_; lean_object* v___x_3576_; 
lean_dec_ref(v___x_3531_);
lean_dec_ref(v_e_3525_);
lean_dec_ref(v___f_3524_);
v___x_3575_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_3576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3576_, 0, v___x_3575_);
return v___x_3576_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__4___boxed(lean_object* v___f_3577_, lean_object* v_e_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_){
_start:
{
lean_object* v_res_3584_; 
v_res_3584_ = l_Lean_Meta_zetaReduce___lam__4(v___f_3577_, v_e_3578_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_);
lean_dec(v___y_3582_);
lean_dec_ref(v___y_3581_);
lean_dec(v___y_3580_);
lean_dec_ref(v___y_3579_);
return v_res_3584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0(lean_object* v_00_u03b1_3585_, lean_object* v_x_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_){
_start:
{
lean_object* v___x_3592_; lean_object* v___x_3593_; 
v___x_3592_ = lean_apply_1(v_x_3586_, lean_box(0));
v___x_3593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3593_, 0, v___x_3592_);
return v___x_3593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0___boxed(lean_object* v_00_u03b1_3594_, lean_object* v_x_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_){
_start:
{
lean_object* v_res_3601_; 
v_res_3601_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0(v_00_u03b1_3594_, v_x_3595_, v___y_3596_, v___y_3597_, v___y_3598_, v___y_3599_);
lean_dec(v___y_3599_);
lean_dec_ref(v___y_3598_);
lean_dec(v___y_3597_);
lean_dec_ref(v___y_3596_);
return v_res_3601_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__2(lean_object* v___x_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_){
_start:
{
lean_object* v___x_3608_; 
v___x_3608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3608_, 0, v___x_3602_);
return v___x_3608_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__2___boxed(lean_object* v___x_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_){
_start:
{
lean_object* v_res_3615_; 
v_res_3615_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__2(v___x_3609_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_);
lean_dec(v___y_3613_);
lean_dec_ref(v___y_3612_);
lean_dec(v___y_3611_);
lean_dec_ref(v___y_3610_);
return v_res_3615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0(lean_object* v_k_3616_, lean_object* v___y_3617_, lean_object* v_b_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_){
_start:
{
lean_object* v___x_3624_; 
lean_inc(v___y_3622_);
lean_inc_ref(v___y_3621_);
lean_inc(v___y_3620_);
lean_inc_ref(v___y_3619_);
lean_inc(v___y_3617_);
v___x_3624_ = lean_apply_7(v_k_3616_, v_b_3618_, v___y_3617_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_, lean_box(0));
return v___x_3624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0___boxed(lean_object* v_k_3625_, lean_object* v___y_3626_, lean_object* v_b_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_){
_start:
{
lean_object* v_res_3633_; 
v_res_3633_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0(v_k_3625_, v___y_3626_, v_b_3627_, v___y_3628_, v___y_3629_, v___y_3630_, v___y_3631_);
lean_dec(v___y_3631_);
lean_dec_ref(v___y_3630_);
lean_dec(v___y_3629_);
lean_dec_ref(v___y_3628_);
lean_dec(v___y_3626_);
return v_res_3633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(lean_object* v_name_3634_, uint8_t v_bi_3635_, lean_object* v_type_3636_, lean_object* v_k_3637_, uint8_t v_kind_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_){
_start:
{
lean_object* v___f_3645_; lean_object* v___x_3646_; 
lean_inc(v___y_3639_);
v___f_3645_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3645_, 0, v_k_3637_);
lean_closure_set(v___f_3645_, 1, v___y_3639_);
v___x_3646_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3634_, v_bi_3635_, v_type_3636_, v___f_3645_, v_kind_3638_, v___y_3640_, v___y_3641_, v___y_3642_, v___y_3643_);
if (lean_obj_tag(v___x_3646_) == 0)
{
return v___x_3646_;
}
else
{
lean_object* v_a_3647_; lean_object* v___x_3649_; uint8_t v_isShared_3650_; uint8_t v_isSharedCheck_3654_; 
v_a_3647_ = lean_ctor_get(v___x_3646_, 0);
v_isSharedCheck_3654_ = !lean_is_exclusive(v___x_3646_);
if (v_isSharedCheck_3654_ == 0)
{
v___x_3649_ = v___x_3646_;
v_isShared_3650_ = v_isSharedCheck_3654_;
goto v_resetjp_3648_;
}
else
{
lean_inc(v_a_3647_);
lean_dec(v___x_3646_);
v___x_3649_ = lean_box(0);
v_isShared_3650_ = v_isSharedCheck_3654_;
goto v_resetjp_3648_;
}
v_resetjp_3648_:
{
lean_object* v___x_3652_; 
if (v_isShared_3650_ == 0)
{
v___x_3652_ = v___x_3649_;
goto v_reusejp_3651_;
}
else
{
lean_object* v_reuseFailAlloc_3653_; 
v_reuseFailAlloc_3653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3653_, 0, v_a_3647_);
v___x_3652_ = v_reuseFailAlloc_3653_;
goto v_reusejp_3651_;
}
v_reusejp_3651_:
{
return v___x_3652_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___boxed(lean_object* v_name_3655_, lean_object* v_bi_3656_, lean_object* v_type_3657_, lean_object* v_k_3658_, lean_object* v_kind_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_){
_start:
{
uint8_t v_bi_boxed_3666_; uint8_t v_kind_boxed_3667_; lean_object* v_res_3668_; 
v_bi_boxed_3666_ = lean_unbox(v_bi_3656_);
v_kind_boxed_3667_ = lean_unbox(v_kind_3659_);
v_res_3668_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_name_3655_, v_bi_boxed_3666_, v_type_3657_, v_k_3658_, v_kind_boxed_3667_, v___y_3660_, v___y_3661_, v___y_3662_, v___y_3663_, v___y_3664_);
lean_dec(v___y_3664_);
lean_dec_ref(v___y_3663_);
lean_dec(v___y_3662_);
lean_dec_ref(v___y_3661_);
lean_dec(v___y_3660_);
return v_res_3668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg(lean_object* v_name_3669_, lean_object* v_type_3670_, lean_object* v_val_3671_, lean_object* v_k_3672_, uint8_t v_nondep_3673_, uint8_t v_kind_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_){
_start:
{
lean_object* v___f_3681_; lean_object* v___x_3682_; 
lean_inc(v___y_3675_);
v___f_3681_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3681_, 0, v_k_3672_);
lean_closure_set(v___f_3681_, 1, v___y_3675_);
v___x_3682_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_3669_, v_type_3670_, v_val_3671_, v___f_3681_, v_nondep_3673_, v_kind_3674_, v___y_3676_, v___y_3677_, v___y_3678_, v___y_3679_);
if (lean_obj_tag(v___x_3682_) == 0)
{
return v___x_3682_;
}
else
{
lean_object* v_a_3683_; lean_object* v___x_3685_; uint8_t v_isShared_3686_; uint8_t v_isSharedCheck_3690_; 
v_a_3683_ = lean_ctor_get(v___x_3682_, 0);
v_isSharedCheck_3690_ = !lean_is_exclusive(v___x_3682_);
if (v_isSharedCheck_3690_ == 0)
{
v___x_3685_ = v___x_3682_;
v_isShared_3686_ = v_isSharedCheck_3690_;
goto v_resetjp_3684_;
}
else
{
lean_inc(v_a_3683_);
lean_dec(v___x_3682_);
v___x_3685_ = lean_box(0);
v_isShared_3686_ = v_isSharedCheck_3690_;
goto v_resetjp_3684_;
}
v_resetjp_3684_:
{
lean_object* v___x_3688_; 
if (v_isShared_3686_ == 0)
{
v___x_3688_ = v___x_3685_;
goto v_reusejp_3687_;
}
else
{
lean_object* v_reuseFailAlloc_3689_; 
v_reuseFailAlloc_3689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3689_, 0, v_a_3683_);
v___x_3688_ = v_reuseFailAlloc_3689_;
goto v_reusejp_3687_;
}
v_reusejp_3687_:
{
return v___x_3688_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg___boxed(lean_object* v_name_3691_, lean_object* v_type_3692_, lean_object* v_val_3693_, lean_object* v_k_3694_, lean_object* v_nondep_3695_, lean_object* v_kind_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_){
_start:
{
uint8_t v_nondep_boxed_3703_; uint8_t v_kind_boxed_3704_; lean_object* v_res_3705_; 
v_nondep_boxed_3703_ = lean_unbox(v_nondep_3695_);
v_kind_boxed_3704_ = lean_unbox(v_kind_3696_);
v_res_3705_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg(v_name_3691_, v_type_3692_, v_val_3693_, v_k_3694_, v_nondep_boxed_3703_, v_kind_boxed_3704_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_, v___y_3701_);
lean_dec(v___y_3701_);
lean_dec_ref(v___y_3700_);
lean_dec(v___y_3699_);
lean_dec_ref(v___y_3698_);
lean_dec(v___y_3697_);
return v_res_3705_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0(lean_object* v_00_u03b1_3706_, lean_object* v_x_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_){
_start:
{
lean_object* v___x_3713_; lean_object* v___x_3714_; 
v___x_3713_ = lean_apply_1(v_x_3707_, lean_box(0));
v___x_3714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3714_, 0, v___x_3713_);
return v___x_3714_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0___boxed(lean_object* v_00_u03b1_3715_, lean_object* v_x_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_){
_start:
{
lean_object* v_res_3722_; 
v_res_3722_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0(v_00_u03b1_3715_, v_x_3716_, v___y_3717_, v___y_3718_, v___y_3719_, v___y_3720_);
lean_dec(v___y_3720_);
lean_dec_ref(v___y_3719_);
lean_dec(v___y_3718_);
lean_dec_ref(v___y_3717_);
return v_res_3722_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg(lean_object* v_ref_3723_){
_start:
{
lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; 
v___x_3725_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5);
v___x_3726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3726_, 0, v_ref_3723_);
lean_ctor_set(v___x_3726_, 1, v___x_3725_);
v___x_3727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3727_, 0, v___x_3726_);
return v___x_3727_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg___boxed(lean_object* v_ref_3728_, lean_object* v___y_3729_){
_start:
{
lean_object* v_res_3730_; 
v_res_3730_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg(v_ref_3728_);
return v_res_3730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg(lean_object* v_x_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_){
_start:
{
lean_object* v___y_3739_; lean_object* v_toCold_3748_; lean_object* v_currRecDepth_3749_; lean_object* v_ref_3750_; uint16_t v_optionFlags_3751_; uint8_t v_suppressElabErrors_3752_; uint8_t v_isRecordingDeps_3753_; lean_object* v_maxRecDepth_3759_; lean_object* v___x_3760_; uint8_t v___x_3761_; 
v_toCold_3748_ = lean_ctor_get(v___y_3735_, 0);
v_currRecDepth_3749_ = lean_ctor_get(v___y_3735_, 1);
v_ref_3750_ = lean_ctor_get(v___y_3735_, 2);
v_optionFlags_3751_ = lean_ctor_get_uint16(v___y_3735_, sizeof(void*)*3);
v_suppressElabErrors_3752_ = lean_ctor_get_uint8(v___y_3735_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3753_ = lean_ctor_get_uint8(v___y_3735_, sizeof(void*)*3 + 3);
v_maxRecDepth_3759_ = lean_ctor_get(v_toCold_3748_, 3);
v___x_3760_ = lean_unsigned_to_nat(0u);
v___x_3761_ = lean_nat_dec_eq(v_maxRecDepth_3759_, v___x_3760_);
if (v___x_3761_ == 0)
{
uint8_t v___x_3762_; 
v___x_3762_ = lean_nat_dec_eq(v_currRecDepth_3749_, v_maxRecDepth_3759_);
if (v___x_3762_ == 0)
{
goto v___jp_3754_;
}
else
{
lean_object* v___x_3763_; 
lean_dec_ref(v_x_3731_);
lean_inc(v_ref_3750_);
v___x_3763_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg(v_ref_3750_);
v___y_3739_ = v___x_3763_;
goto v___jp_3738_;
}
}
else
{
goto v___jp_3754_;
}
v___jp_3738_:
{
if (lean_obj_tag(v___y_3739_) == 0)
{
return v___y_3739_;
}
else
{
lean_object* v_a_3740_; lean_object* v___x_3742_; uint8_t v_isShared_3743_; uint8_t v_isSharedCheck_3747_; 
v_a_3740_ = lean_ctor_get(v___y_3739_, 0);
v_isSharedCheck_3747_ = !lean_is_exclusive(v___y_3739_);
if (v_isSharedCheck_3747_ == 0)
{
v___x_3742_ = v___y_3739_;
v_isShared_3743_ = v_isSharedCheck_3747_;
goto v_resetjp_3741_;
}
else
{
lean_inc(v_a_3740_);
lean_dec(v___y_3739_);
v___x_3742_ = lean_box(0);
v_isShared_3743_ = v_isSharedCheck_3747_;
goto v_resetjp_3741_;
}
v_resetjp_3741_:
{
lean_object* v___x_3745_; 
if (v_isShared_3743_ == 0)
{
v___x_3745_ = v___x_3742_;
goto v_reusejp_3744_;
}
else
{
lean_object* v_reuseFailAlloc_3746_; 
v_reuseFailAlloc_3746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3746_, 0, v_a_3740_);
v___x_3745_ = v_reuseFailAlloc_3746_;
goto v_reusejp_3744_;
}
v_reusejp_3744_:
{
return v___x_3745_;
}
}
}
}
v___jp_3754_:
{
lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; 
v___x_3755_ = lean_unsigned_to_nat(1u);
v___x_3756_ = lean_nat_add(v_currRecDepth_3749_, v___x_3755_);
lean_inc(v_ref_3750_);
lean_inc_ref(v_toCold_3748_);
v___x_3757_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3757_, 0, v_toCold_3748_);
lean_ctor_set(v___x_3757_, 1, v___x_3756_);
lean_ctor_set(v___x_3757_, 2, v_ref_3750_);
lean_ctor_set_uint16(v___x_3757_, sizeof(void*)*3, v_optionFlags_3751_);
lean_ctor_set_uint8(v___x_3757_, sizeof(void*)*3 + 2, v_suppressElabErrors_3752_);
lean_ctor_set_uint8(v___x_3757_, sizeof(void*)*3 + 3, v_isRecordingDeps_3753_);
lean_inc(v___y_3736_);
lean_inc(v___y_3734_);
lean_inc_ref(v___y_3733_);
lean_inc(v___y_3732_);
v___x_3758_ = lean_apply_6(v_x_3731_, v___y_3732_, v___y_3733_, v___y_3734_, v___x_3757_, v___y_3736_, lean_box(0));
v___y_3739_ = v___x_3758_;
goto v___jp_3738_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg___boxed(lean_object* v_x_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_){
_start:
{
lean_object* v_res_3771_; 
v_res_3771_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg(v_x_3764_, v___y_3765_, v___y_3766_, v___y_3767_, v___y_3768_, v___y_3769_);
lean_dec(v___y_3769_);
lean_dec_ref(v___y_3768_);
lean_dec(v___y_3767_);
lean_dec_ref(v___y_3766_);
lean_dec(v___y_3765_);
return v_res_3771_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___lam__0___boxed(lean_object* v_fvars_3772_, lean_object* v_pre_3773_, lean_object* v_post_3774_, lean_object* v_usedLetOnly_3775_, lean_object* v_skipConstInApp_3776_, lean_object* v_skipInstances_3777_, lean_object* v_body_3778_, lean_object* v_x_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_){
_start:
{
uint8_t v_usedLetOnly_boxed_3786_; uint8_t v_skipConstInApp_boxed_3787_; uint8_t v_skipInstances_boxed_3788_; lean_object* v_res_3789_; 
v_usedLetOnly_boxed_3786_ = lean_unbox(v_usedLetOnly_3775_);
v_skipConstInApp_boxed_3787_ = lean_unbox(v_skipConstInApp_3776_);
v_skipInstances_boxed_3788_ = lean_unbox(v_skipInstances_3777_);
v_res_3789_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___lam__0(v_fvars_3772_, v_pre_3773_, v_post_3774_, v_usedLetOnly_boxed_3786_, v_skipConstInApp_boxed_3787_, v_skipInstances_boxed_3788_, v_body_3778_, v_x_3779_, v___y_3780_, v___y_3781_, v___y_3782_, v___y_3783_, v___y_3784_);
lean_dec(v___y_3784_);
lean_dec_ref(v___y_3783_);
lean_dec(v___y_3782_);
lean_dec_ref(v___y_3781_);
lean_dec(v___y_3780_);
return v_res_3789_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___lam__0(lean_object* v_fvars_3790_, lean_object* v_pre_3791_, lean_object* v_post_3792_, uint8_t v_usedLetOnly_3793_, uint8_t v_skipConstInApp_3794_, uint8_t v_skipInstances_3795_, lean_object* v_body_3796_, lean_object* v_x_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_){
_start:
{
lean_object* v___x_3804_; lean_object* v___x_3805_; 
v___x_3804_ = lean_array_push(v_fvars_3790_, v_x_3797_);
v___x_3805_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6(v_pre_3791_, v_post_3792_, v_usedLetOnly_3793_, v_skipConstInApp_3794_, v_skipInstances_3795_, v___x_3804_, v_body_3796_, v___y_3798_, v___y_3799_, v___y_3800_, v___y_3801_, v___y_3802_);
return v___x_3805_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___lam__0___boxed(lean_object* v_fvars_3806_, lean_object* v_pre_3807_, lean_object* v_post_3808_, lean_object* v_usedLetOnly_3809_, lean_object* v_skipConstInApp_3810_, lean_object* v_skipInstances_3811_, lean_object* v_body_3812_, lean_object* v_x_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_){
_start:
{
uint8_t v_usedLetOnly_boxed_3820_; uint8_t v_skipConstInApp_boxed_3821_; uint8_t v_skipInstances_boxed_3822_; lean_object* v_res_3823_; 
v_usedLetOnly_boxed_3820_ = lean_unbox(v_usedLetOnly_3809_);
v_skipConstInApp_boxed_3821_ = lean_unbox(v_skipConstInApp_3810_);
v_skipInstances_boxed_3822_ = lean_unbox(v_skipInstances_3811_);
v_res_3823_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___lam__0(v_fvars_3806_, v_pre_3807_, v_post_3808_, v_usedLetOnly_boxed_3820_, v_skipConstInApp_boxed_3821_, v_skipInstances_boxed_3822_, v_body_3812_, v_x_3813_, v___y_3814_, v___y_3815_, v___y_3816_, v___y_3817_, v___y_3818_);
lean_dec(v___y_3818_);
lean_dec_ref(v___y_3817_);
lean_dec(v___y_3816_);
lean_dec_ref(v___y_3815_);
lean_dec(v___y_3814_);
return v_res_3823_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(lean_object* v_pre_3824_, lean_object* v_post_3825_, uint8_t v_usedLetOnly_3826_, uint8_t v_skipConstInApp_3827_, uint8_t v_skipInstances_3828_, lean_object* v_e_3829_, lean_object* v_a_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_){
_start:
{
lean_object* v___x_3836_; 
lean_inc_ref(v_post_3825_);
lean_inc(v___y_3834_);
lean_inc_ref(v___y_3833_);
lean_inc(v___y_3832_);
lean_inc_ref(v___y_3831_);
lean_inc_ref(v_e_3829_);
v___x_3836_ = lean_apply_6(v_post_3825_, v_e_3829_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_, lean_box(0));
if (lean_obj_tag(v___x_3836_) == 0)
{
lean_object* v_a_3837_; lean_object* v___x_3839_; uint8_t v_isShared_3840_; uint8_t v_isSharedCheck_3855_; 
v_a_3837_ = lean_ctor_get(v___x_3836_, 0);
v_isSharedCheck_3855_ = !lean_is_exclusive(v___x_3836_);
if (v_isSharedCheck_3855_ == 0)
{
v___x_3839_ = v___x_3836_;
v_isShared_3840_ = v_isSharedCheck_3855_;
goto v_resetjp_3838_;
}
else
{
lean_inc(v_a_3837_);
lean_dec(v___x_3836_);
v___x_3839_ = lean_box(0);
v_isShared_3840_ = v_isSharedCheck_3855_;
goto v_resetjp_3838_;
}
v_resetjp_3838_:
{
switch(lean_obj_tag(v_a_3837_))
{
case 0:
{
lean_object* v_e_3841_; lean_object* v___x_3843_; 
lean_dec_ref(v_e_3829_);
lean_dec_ref(v_post_3825_);
lean_dec_ref(v_pre_3824_);
v_e_3841_ = lean_ctor_get(v_a_3837_, 0);
lean_inc_ref(v_e_3841_);
lean_dec_ref_known(v_a_3837_, 1);
if (v_isShared_3840_ == 0)
{
lean_ctor_set(v___x_3839_, 0, v_e_3841_);
v___x_3843_ = v___x_3839_;
goto v_reusejp_3842_;
}
else
{
lean_object* v_reuseFailAlloc_3844_; 
v_reuseFailAlloc_3844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3844_, 0, v_e_3841_);
v___x_3843_ = v_reuseFailAlloc_3844_;
goto v_reusejp_3842_;
}
v_reusejp_3842_:
{
return v___x_3843_;
}
}
case 1:
{
lean_object* v_e_3845_; lean_object* v___x_3846_; 
lean_del_object(v___x_3839_);
lean_dec_ref(v_e_3829_);
v_e_3845_ = lean_ctor_get(v_a_3837_, 0);
lean_inc_ref(v_e_3845_);
lean_dec_ref_known(v_a_3837_, 1);
v___x_3846_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3824_, v_post_3825_, v_usedLetOnly_3826_, v_skipConstInApp_3827_, v_skipInstances_3828_, v_e_3845_, v_a_3830_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_);
return v___x_3846_;
}
default: 
{
lean_object* v_e_x3f_3847_; 
lean_dec_ref(v_post_3825_);
lean_dec_ref(v_pre_3824_);
v_e_x3f_3847_ = lean_ctor_get(v_a_3837_, 0);
lean_inc(v_e_x3f_3847_);
lean_dec_ref_known(v_a_3837_, 1);
if (lean_obj_tag(v_e_x3f_3847_) == 0)
{
lean_object* v___x_3849_; 
if (v_isShared_3840_ == 0)
{
lean_ctor_set(v___x_3839_, 0, v_e_3829_);
v___x_3849_ = v___x_3839_;
goto v_reusejp_3848_;
}
else
{
lean_object* v_reuseFailAlloc_3850_; 
v_reuseFailAlloc_3850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3850_, 0, v_e_3829_);
v___x_3849_ = v_reuseFailAlloc_3850_;
goto v_reusejp_3848_;
}
v_reusejp_3848_:
{
return v___x_3849_;
}
}
else
{
lean_object* v_val_3851_; lean_object* v___x_3853_; 
lean_dec_ref(v_e_3829_);
v_val_3851_ = lean_ctor_get(v_e_x3f_3847_, 0);
lean_inc(v_val_3851_);
lean_dec_ref_known(v_e_x3f_3847_, 1);
if (v_isShared_3840_ == 0)
{
lean_ctor_set(v___x_3839_, 0, v_val_3851_);
v___x_3853_ = v___x_3839_;
goto v_reusejp_3852_;
}
else
{
lean_object* v_reuseFailAlloc_3854_; 
v_reuseFailAlloc_3854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3854_, 0, v_val_3851_);
v___x_3853_ = v_reuseFailAlloc_3854_;
goto v_reusejp_3852_;
}
v_reusejp_3852_:
{
return v___x_3853_;
}
}
}
}
}
}
else
{
lean_object* v_a_3856_; lean_object* v___x_3858_; uint8_t v_isShared_3859_; uint8_t v_isSharedCheck_3863_; 
lean_dec_ref(v_e_3829_);
lean_dec_ref(v_post_3825_);
lean_dec_ref(v_pre_3824_);
v_a_3856_ = lean_ctor_get(v___x_3836_, 0);
v_isSharedCheck_3863_ = !lean_is_exclusive(v___x_3836_);
if (v_isSharedCheck_3863_ == 0)
{
v___x_3858_ = v___x_3836_;
v_isShared_3859_ = v_isSharedCheck_3863_;
goto v_resetjp_3857_;
}
else
{
lean_inc(v_a_3856_);
lean_dec(v___x_3836_);
v___x_3858_ = lean_box(0);
v_isShared_3859_ = v_isSharedCheck_3863_;
goto v_resetjp_3857_;
}
v_resetjp_3857_:
{
lean_object* v___x_3861_; 
if (v_isShared_3859_ == 0)
{
v___x_3861_ = v___x_3858_;
goto v_reusejp_3860_;
}
else
{
lean_object* v_reuseFailAlloc_3862_; 
v_reuseFailAlloc_3862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3862_, 0, v_a_3856_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6(lean_object* v_pre_3864_, lean_object* v_post_3865_, uint8_t v_usedLetOnly_3866_, uint8_t v_skipConstInApp_3867_, uint8_t v_skipInstances_3868_, lean_object* v_fvars_3869_, lean_object* v_e_3870_, lean_object* v_a_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_){
_start:
{
if (lean_obj_tag(v_e_3870_) == 6)
{
lean_object* v_binderName_3877_; lean_object* v_binderType_3878_; lean_object* v_body_3879_; uint8_t v_binderInfo_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___f_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; 
v_binderName_3877_ = lean_ctor_get(v_e_3870_, 0);
lean_inc(v_binderName_3877_);
v_binderType_3878_ = lean_ctor_get(v_e_3870_, 1);
lean_inc_ref(v_binderType_3878_);
v_body_3879_ = lean_ctor_get(v_e_3870_, 2);
lean_inc_ref(v_body_3879_);
v_binderInfo_3880_ = lean_ctor_get_uint8(v_e_3870_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_3870_, 3);
v___x_3881_ = lean_box(v_usedLetOnly_3866_);
v___x_3882_ = lean_box(v_skipConstInApp_3867_);
v___x_3883_ = lean_box(v_skipInstances_3868_);
lean_inc_ref(v_post_3865_);
lean_inc_ref(v_pre_3864_);
lean_inc_ref(v_fvars_3869_);
v___f_3884_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___lam__0___boxed), 14, 7);
lean_closure_set(v___f_3884_, 0, v_fvars_3869_);
lean_closure_set(v___f_3884_, 1, v_pre_3864_);
lean_closure_set(v___f_3884_, 2, v_post_3865_);
lean_closure_set(v___f_3884_, 3, v___x_3881_);
lean_closure_set(v___f_3884_, 4, v___x_3882_);
lean_closure_set(v___f_3884_, 5, v___x_3883_);
lean_closure_set(v___f_3884_, 6, v_body_3879_);
v___x_3885_ = lean_expr_instantiate_rev(v_binderType_3878_, v_fvars_3869_);
lean_dec_ref(v_fvars_3869_);
lean_dec_ref(v_binderType_3878_);
v___x_3886_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3864_, v_post_3865_, v_usedLetOnly_3866_, v_skipConstInApp_3867_, v_skipInstances_3868_, v___x_3885_, v_a_3871_, v___y_3872_, v___y_3873_, v___y_3874_, v___y_3875_);
if (lean_obj_tag(v___x_3886_) == 0)
{
lean_object* v_a_3887_; uint8_t v___x_3888_; lean_object* v___x_3889_; 
v_a_3887_ = lean_ctor_get(v___x_3886_, 0);
lean_inc(v_a_3887_);
lean_dec_ref_known(v___x_3886_, 1);
v___x_3888_ = 0;
v___x_3889_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_binderName_3877_, v_binderInfo_3880_, v_a_3887_, v___f_3884_, v___x_3888_, v_a_3871_, v___y_3872_, v___y_3873_, v___y_3874_, v___y_3875_);
return v___x_3889_;
}
else
{
lean_dec_ref(v___f_3884_);
lean_dec(v_binderName_3877_);
return v___x_3886_;
}
}
else
{
lean_object* v___x_3890_; lean_object* v___x_3891_; 
v___x_3890_ = lean_expr_instantiate_rev(v_e_3870_, v_fvars_3869_);
lean_dec_ref(v_e_3870_);
lean_inc_ref(v_post_3865_);
lean_inc_ref(v_pre_3864_);
v___x_3891_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3864_, v_post_3865_, v_usedLetOnly_3866_, v_skipConstInApp_3867_, v_skipInstances_3868_, v___x_3890_, v_a_3871_, v___y_3872_, v___y_3873_, v___y_3874_, v___y_3875_);
if (lean_obj_tag(v___x_3891_) == 0)
{
lean_object* v_a_3892_; uint8_t v___x_3893_; uint8_t v___x_3894_; uint8_t v___x_3895_; lean_object* v___x_3896_; 
v_a_3892_ = lean_ctor_get(v___x_3891_, 0);
lean_inc(v_a_3892_);
lean_dec_ref_known(v___x_3891_, 1);
v___x_3893_ = 0;
v___x_3894_ = 1;
v___x_3895_ = 1;
v___x_3896_ = l_Lean_Meta_mkLambdaFVars(v_fvars_3869_, v_a_3892_, v___x_3893_, v_usedLetOnly_3866_, v___x_3893_, v___x_3894_, v___x_3895_, v___y_3872_, v___y_3873_, v___y_3874_, v___y_3875_);
lean_dec_ref(v_fvars_3869_);
if (lean_obj_tag(v___x_3896_) == 0)
{
lean_object* v_a_3897_; lean_object* v___x_3898_; 
v_a_3897_ = lean_ctor_get(v___x_3896_, 0);
lean_inc(v_a_3897_);
lean_dec_ref_known(v___x_3896_, 1);
v___x_3898_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_3864_, v_post_3865_, v_usedLetOnly_3866_, v_skipConstInApp_3867_, v_skipInstances_3868_, v_a_3897_, v_a_3871_, v___y_3872_, v___y_3873_, v___y_3874_, v___y_3875_);
return v___x_3898_;
}
else
{
lean_dec_ref(v_post_3865_);
lean_dec_ref(v_pre_3864_);
return v___x_3896_;
}
}
else
{
lean_dec_ref(v_fvars_3869_);
lean_dec_ref(v_post_3865_);
lean_dec_ref(v_pre_3864_);
return v___x_3891_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___lam__0(lean_object* v_fvars_3899_, lean_object* v_pre_3900_, lean_object* v_post_3901_, uint8_t v_usedLetOnly_3902_, uint8_t v_skipConstInApp_3903_, uint8_t v_skipInstances_3904_, lean_object* v_body_3905_, lean_object* v_x_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_){
_start:
{
lean_object* v___x_3913_; lean_object* v___x_3914_; 
v___x_3913_ = lean_array_push(v_fvars_3899_, v_x_3906_);
v___x_3914_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7(v_pre_3900_, v_post_3901_, v_usedLetOnly_3902_, v_skipConstInApp_3903_, v_skipInstances_3904_, v___x_3913_, v_body_3905_, v___y_3907_, v___y_3908_, v___y_3909_, v___y_3910_, v___y_3911_);
return v___x_3914_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___lam__0___boxed(lean_object* v_fvars_3915_, lean_object* v_pre_3916_, lean_object* v_post_3917_, lean_object* v_usedLetOnly_3918_, lean_object* v_skipConstInApp_3919_, lean_object* v_skipInstances_3920_, lean_object* v_body_3921_, lean_object* v_x_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_){
_start:
{
uint8_t v_usedLetOnly_boxed_3929_; uint8_t v_skipConstInApp_boxed_3930_; uint8_t v_skipInstances_boxed_3931_; lean_object* v_res_3932_; 
v_usedLetOnly_boxed_3929_ = lean_unbox(v_usedLetOnly_3918_);
v_skipConstInApp_boxed_3930_ = lean_unbox(v_skipConstInApp_3919_);
v_skipInstances_boxed_3931_ = lean_unbox(v_skipInstances_3920_);
v_res_3932_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___lam__0(v_fvars_3915_, v_pre_3916_, v_post_3917_, v_usedLetOnly_boxed_3929_, v_skipConstInApp_boxed_3930_, v_skipInstances_boxed_3931_, v_body_3921_, v_x_3922_, v___y_3923_, v___y_3924_, v___y_3925_, v___y_3926_, v___y_3927_);
lean_dec(v___y_3927_);
lean_dec_ref(v___y_3926_);
lean_dec(v___y_3925_);
lean_dec_ref(v___y_3924_);
lean_dec(v___y_3923_);
return v_res_3932_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7(lean_object* v_pre_3933_, lean_object* v_post_3934_, uint8_t v_usedLetOnly_3935_, uint8_t v_skipConstInApp_3936_, uint8_t v_skipInstances_3937_, lean_object* v_fvars_3938_, lean_object* v_e_3939_, lean_object* v_a_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_){
_start:
{
if (lean_obj_tag(v_e_3939_) == 8)
{
lean_object* v_declName_3946_; lean_object* v_type_3947_; lean_object* v_value_3948_; lean_object* v_body_3949_; uint8_t v_nondep_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___f_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; 
v_declName_3946_ = lean_ctor_get(v_e_3939_, 0);
lean_inc(v_declName_3946_);
v_type_3947_ = lean_ctor_get(v_e_3939_, 1);
lean_inc_ref(v_type_3947_);
v_value_3948_ = lean_ctor_get(v_e_3939_, 2);
lean_inc_ref(v_value_3948_);
v_body_3949_ = lean_ctor_get(v_e_3939_, 3);
lean_inc_ref(v_body_3949_);
v_nondep_3950_ = lean_ctor_get_uint8(v_e_3939_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_3939_, 4);
v___x_3951_ = lean_box(v_usedLetOnly_3935_);
v___x_3952_ = lean_box(v_skipConstInApp_3936_);
v___x_3953_ = lean_box(v_skipInstances_3937_);
lean_inc_ref_n(v_post_3934_, 2);
lean_inc_ref_n(v_pre_3933_, 2);
lean_inc_ref(v_fvars_3938_);
v___f_3954_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___lam__0___boxed), 14, 7);
lean_closure_set(v___f_3954_, 0, v_fvars_3938_);
lean_closure_set(v___f_3954_, 1, v_pre_3933_);
lean_closure_set(v___f_3954_, 2, v_post_3934_);
lean_closure_set(v___f_3954_, 3, v___x_3951_);
lean_closure_set(v___f_3954_, 4, v___x_3952_);
lean_closure_set(v___f_3954_, 5, v___x_3953_);
lean_closure_set(v___f_3954_, 6, v_body_3949_);
v___x_3955_ = lean_expr_instantiate_rev(v_type_3947_, v_fvars_3938_);
lean_dec_ref(v_type_3947_);
v___x_3956_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3933_, v_post_3934_, v_usedLetOnly_3935_, v_skipConstInApp_3936_, v_skipInstances_3937_, v___x_3955_, v_a_3940_, v___y_3941_, v___y_3942_, v___y_3943_, v___y_3944_);
if (lean_obj_tag(v___x_3956_) == 0)
{
lean_object* v_a_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; 
v_a_3957_ = lean_ctor_get(v___x_3956_, 0);
lean_inc(v_a_3957_);
lean_dec_ref_known(v___x_3956_, 1);
v___x_3958_ = lean_expr_instantiate_rev(v_value_3948_, v_fvars_3938_);
lean_dec_ref(v_fvars_3938_);
lean_dec_ref(v_value_3948_);
v___x_3959_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3933_, v_post_3934_, v_usedLetOnly_3935_, v_skipConstInApp_3936_, v_skipInstances_3937_, v___x_3958_, v_a_3940_, v___y_3941_, v___y_3942_, v___y_3943_, v___y_3944_);
if (lean_obj_tag(v___x_3959_) == 0)
{
lean_object* v_a_3960_; uint8_t v___x_3961_; lean_object* v___x_3962_; 
v_a_3960_ = lean_ctor_get(v___x_3959_, 0);
lean_inc(v_a_3960_);
lean_dec_ref_known(v___x_3959_, 1);
v___x_3961_ = 0;
v___x_3962_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg(v_declName_3946_, v_a_3957_, v_a_3960_, v___f_3954_, v_nondep_3950_, v___x_3961_, v_a_3940_, v___y_3941_, v___y_3942_, v___y_3943_, v___y_3944_);
return v___x_3962_;
}
else
{
lean_dec(v_a_3957_);
lean_dec_ref(v___f_3954_);
lean_dec(v_declName_3946_);
return v___x_3959_;
}
}
else
{
lean_dec_ref(v___f_3954_);
lean_dec_ref(v_value_3948_);
lean_dec(v_declName_3946_);
lean_dec_ref(v_fvars_3938_);
lean_dec_ref(v_post_3934_);
lean_dec_ref(v_pre_3933_);
return v___x_3956_;
}
}
else
{
lean_object* v___x_3963_; lean_object* v___x_3964_; 
v___x_3963_ = lean_expr_instantiate_rev(v_e_3939_, v_fvars_3938_);
lean_dec_ref(v_e_3939_);
lean_inc_ref(v_post_3934_);
lean_inc_ref(v_pre_3933_);
v___x_3964_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3933_, v_post_3934_, v_usedLetOnly_3935_, v_skipConstInApp_3936_, v_skipInstances_3937_, v___x_3963_, v_a_3940_, v___y_3941_, v___y_3942_, v___y_3943_, v___y_3944_);
if (lean_obj_tag(v___x_3964_) == 0)
{
lean_object* v_a_3965_; uint8_t v___x_3966_; uint8_t v___x_3967_; lean_object* v___x_3968_; 
v_a_3965_ = lean_ctor_get(v___x_3964_, 0);
lean_inc(v_a_3965_);
lean_dec_ref_known(v___x_3964_, 1);
v___x_3966_ = 0;
v___x_3967_ = 1;
v___x_3968_ = l_Lean_Meta_mkLetFVars(v_fvars_3938_, v_a_3965_, v_usedLetOnly_3935_, v___x_3966_, v___x_3967_, v___y_3941_, v___y_3942_, v___y_3943_, v___y_3944_);
lean_dec_ref(v_fvars_3938_);
if (lean_obj_tag(v___x_3968_) == 0)
{
lean_object* v_a_3969_; lean_object* v___x_3970_; 
v_a_3969_ = lean_ctor_get(v___x_3968_, 0);
lean_inc(v_a_3969_);
lean_dec_ref_known(v___x_3968_, 1);
v___x_3970_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_3933_, v_post_3934_, v_usedLetOnly_3935_, v_skipConstInApp_3936_, v_skipInstances_3937_, v_a_3969_, v_a_3940_, v___y_3941_, v___y_3942_, v___y_3943_, v___y_3944_);
return v___x_3970_;
}
else
{
lean_dec_ref(v_post_3934_);
lean_dec_ref(v_pre_3933_);
return v___x_3968_;
}
}
else
{
lean_dec_ref(v_fvars_3938_);
lean_dec_ref(v_post_3934_);
lean_dec_ref(v_pre_3933_);
return v___x_3964_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__2(lean_object* v_pre_3971_, lean_object* v_post_3972_, uint8_t v_usedLetOnly_3973_, uint8_t v_skipConstInApp_3974_, uint8_t v_skipInstances_3975_, size_t v_sz_3976_, size_t v_i_3977_, lean_object* v_bs_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_){
_start:
{
uint8_t v___x_3985_; 
v___x_3985_ = lean_usize_dec_lt(v_i_3977_, v_sz_3976_);
if (v___x_3985_ == 0)
{
lean_object* v___x_3986_; 
lean_dec_ref(v_post_3972_);
lean_dec_ref(v_pre_3971_);
v___x_3986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3986_, 0, v_bs_3978_);
return v___x_3986_;
}
else
{
lean_object* v_v_3987_; lean_object* v___x_3988_; lean_object* v_bs_x27_3989_; lean_object* v___x_3990_; 
v_v_3987_ = lean_array_uget(v_bs_3978_, v_i_3977_);
v___x_3988_ = lean_unsigned_to_nat(0u);
v_bs_x27_3989_ = lean_array_uset(v_bs_3978_, v_i_3977_, v___x_3988_);
lean_inc_ref(v_post_3972_);
lean_inc_ref(v_pre_3971_);
v___x_3990_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3971_, v_post_3972_, v_usedLetOnly_3973_, v_skipConstInApp_3974_, v_skipInstances_3975_, v_v_3987_, v___y_3979_, v___y_3980_, v___y_3981_, v___y_3982_, v___y_3983_);
if (lean_obj_tag(v___x_3990_) == 0)
{
lean_object* v_a_3991_; size_t v___x_3992_; size_t v___x_3993_; lean_object* v___x_3994_; 
v_a_3991_ = lean_ctor_get(v___x_3990_, 0);
lean_inc(v_a_3991_);
lean_dec_ref_known(v___x_3990_, 1);
v___x_3992_ = ((size_t)1ULL);
v___x_3993_ = lean_usize_add(v_i_3977_, v___x_3992_);
v___x_3994_ = lean_array_uset(v_bs_x27_3989_, v_i_3977_, v_a_3991_);
v_i_3977_ = v___x_3993_;
v_bs_3978_ = v___x_3994_;
goto _start;
}
else
{
lean_object* v_a_3996_; lean_object* v___x_3998_; uint8_t v_isShared_3999_; uint8_t v_isSharedCheck_4003_; 
lean_dec_ref(v_bs_x27_3989_);
lean_dec_ref(v_post_3972_);
lean_dec_ref(v_pre_3971_);
v_a_3996_ = lean_ctor_get(v___x_3990_, 0);
v_isSharedCheck_4003_ = !lean_is_exclusive(v___x_3990_);
if (v_isSharedCheck_4003_ == 0)
{
v___x_3998_ = v___x_3990_;
v_isShared_3999_ = v_isSharedCheck_4003_;
goto v_resetjp_3997_;
}
else
{
lean_inc(v_a_3996_);
lean_dec(v___x_3990_);
v___x_3998_ = lean_box(0);
v_isShared_3999_ = v_isSharedCheck_4003_;
goto v_resetjp_3997_;
}
v_resetjp_3997_:
{
lean_object* v___x_4001_; 
if (v_isShared_3999_ == 0)
{
v___x_4001_ = v___x_3998_;
goto v_reusejp_4000_;
}
else
{
lean_object* v_reuseFailAlloc_4002_; 
v_reuseFailAlloc_4002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4002_, 0, v_a_3996_);
v___x_4001_ = v_reuseFailAlloc_4002_;
goto v_reusejp_4000_;
}
v_reusejp_4000_:
{
return v___x_4001_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0(lean_object* v_pre_4004_, lean_object* v_post_4005_, uint8_t v_usedLetOnly_4006_, uint8_t v_skipConstInApp_4007_, uint8_t v_skipInstances_4008_, lean_object* v___x_4009_, lean_object* v___y_4010_, lean_object* v_b_4011_, lean_object* v_a_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_){
_start:
{
lean_object* v___x_4018_; 
v___x_4018_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4004_, v_post_4005_, v_usedLetOnly_4006_, v_skipConstInApp_4007_, v_skipInstances_4008_, v___x_4009_, v___y_4010_, v___y_4013_, v___y_4014_, v___y_4015_, v___y_4016_);
if (lean_obj_tag(v___x_4018_) == 0)
{
lean_object* v_a_4019_; lean_object* v___x_4021_; uint8_t v_isShared_4022_; uint8_t v_isSharedCheck_4028_; 
v_a_4019_ = lean_ctor_get(v___x_4018_, 0);
v_isSharedCheck_4028_ = !lean_is_exclusive(v___x_4018_);
if (v_isSharedCheck_4028_ == 0)
{
v___x_4021_ = v___x_4018_;
v_isShared_4022_ = v_isSharedCheck_4028_;
goto v_resetjp_4020_;
}
else
{
lean_inc(v_a_4019_);
lean_dec(v___x_4018_);
v___x_4021_ = lean_box(0);
v_isShared_4022_ = v_isSharedCheck_4028_;
goto v_resetjp_4020_;
}
v_resetjp_4020_:
{
lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4026_; 
v___x_4023_ = lean_array_fset(v_b_4011_, v_a_4012_, v_a_4019_);
v___x_4024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4024_, 0, v___x_4023_);
if (v_isShared_4022_ == 0)
{
lean_ctor_set(v___x_4021_, 0, v___x_4024_);
v___x_4026_ = v___x_4021_;
goto v_reusejp_4025_;
}
else
{
lean_object* v_reuseFailAlloc_4027_; 
v_reuseFailAlloc_4027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4027_, 0, v___x_4024_);
v___x_4026_ = v_reuseFailAlloc_4027_;
goto v_reusejp_4025_;
}
v_reusejp_4025_:
{
return v___x_4026_;
}
}
}
else
{
lean_object* v_a_4029_; lean_object* v___x_4031_; uint8_t v_isShared_4032_; uint8_t v_isSharedCheck_4036_; 
lean_dec_ref(v_b_4011_);
v_a_4029_ = lean_ctor_get(v___x_4018_, 0);
v_isSharedCheck_4036_ = !lean_is_exclusive(v___x_4018_);
if (v_isSharedCheck_4036_ == 0)
{
v___x_4031_ = v___x_4018_;
v_isShared_4032_ = v_isSharedCheck_4036_;
goto v_resetjp_4030_;
}
else
{
lean_inc(v_a_4029_);
lean_dec(v___x_4018_);
v___x_4031_ = lean_box(0);
v_isShared_4032_ = v_isSharedCheck_4036_;
goto v_resetjp_4030_;
}
v_resetjp_4030_:
{
lean_object* v___x_4034_; 
if (v_isShared_4032_ == 0)
{
v___x_4034_ = v___x_4031_;
goto v_reusejp_4033_;
}
else
{
lean_object* v_reuseFailAlloc_4035_; 
v_reuseFailAlloc_4035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4035_, 0, v_a_4029_);
v___x_4034_ = v_reuseFailAlloc_4035_;
goto v_reusejp_4033_;
}
v_reusejp_4033_:
{
return v___x_4034_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed(lean_object* v_pre_4037_, lean_object* v_post_4038_, lean_object* v_usedLetOnly_4039_, lean_object* v_skipConstInApp_4040_, lean_object* v_skipInstances_4041_, lean_object* v___x_4042_, lean_object* v___y_4043_, lean_object* v_b_4044_, lean_object* v_a_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_){
_start:
{
uint8_t v_usedLetOnly_boxed_4051_; uint8_t v_skipConstInApp_boxed_4052_; uint8_t v_skipInstances_boxed_4053_; lean_object* v_res_4054_; 
v_usedLetOnly_boxed_4051_ = lean_unbox(v_usedLetOnly_4039_);
v_skipConstInApp_boxed_4052_ = lean_unbox(v_skipConstInApp_4040_);
v_skipInstances_boxed_4053_ = lean_unbox(v_skipInstances_4041_);
v_res_4054_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0(v_pre_4037_, v_post_4038_, v_usedLetOnly_boxed_4051_, v_skipConstInApp_boxed_4052_, v_skipInstances_boxed_4053_, v___x_4042_, v___y_4043_, v_b_4044_, v_a_4045_, v___y_4046_, v___y_4047_, v___y_4048_, v___y_4049_);
lean_dec(v___y_4049_);
lean_dec_ref(v___y_4048_);
lean_dec(v___y_4047_);
lean_dec_ref(v___y_4046_);
lean_dec(v_a_4045_);
lean_dec(v___y_4043_);
return v_res_4054_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg(lean_object* v_upperBound_4055_, lean_object* v___x_4056_, lean_object* v_pre_4057_, lean_object* v_post_4058_, uint8_t v_usedLetOnly_4059_, uint8_t v_skipConstInApp_4060_, uint8_t v_skipInstances_4061_, lean_object* v_a_4062_, lean_object* v_b_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_){
_start:
{
lean_object* v___y_4071_; uint8_t v___x_4094_; 
v___x_4094_ = lean_nat_dec_lt(v_a_4062_, v_upperBound_4055_);
if (v___x_4094_ == 0)
{
lean_object* v___x_4095_; 
lean_dec(v_a_4062_);
lean_dec_ref(v_post_4058_);
lean_dec_ref(v_pre_4057_);
v___x_4095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4095_, 0, v_b_4063_);
return v___x_4095_;
}
else
{
lean_object* v___x_4096_; lean_object* v___x_4097_; uint8_t v___x_4098_; 
v___x_4096_ = lean_array_fget_borrowed(v_b_4063_, v_a_4062_);
v___x_4097_ = lean_array_get_size(v___x_4056_);
v___x_4098_ = lean_nat_dec_lt(v_a_4062_, v___x_4097_);
if (v___x_4098_ == 0)
{
lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___f_4102_; 
lean_inc(v___x_4096_);
v___x_4099_ = lean_box(v_usedLetOnly_4059_);
v___x_4100_ = lean_box(v_skipConstInApp_4060_);
v___x_4101_ = lean_box(v_skipInstances_4061_);
lean_inc(v_a_4062_);
lean_inc(v___y_4064_);
lean_inc_ref(v_post_4058_);
lean_inc_ref(v_pre_4057_);
v___f_4102_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_4102_, 0, v_pre_4057_);
lean_closure_set(v___f_4102_, 1, v_post_4058_);
lean_closure_set(v___f_4102_, 2, v___x_4099_);
lean_closure_set(v___f_4102_, 3, v___x_4100_);
lean_closure_set(v___f_4102_, 4, v___x_4101_);
lean_closure_set(v___f_4102_, 5, v___x_4096_);
lean_closure_set(v___f_4102_, 6, v___y_4064_);
lean_closure_set(v___f_4102_, 7, v_b_4063_);
lean_closure_set(v___f_4102_, 8, v_a_4062_);
v___y_4071_ = v___f_4102_;
goto v___jp_4070_;
}
else
{
lean_object* v___x_4103_; uint8_t v_isInstance_4104_; 
v___x_4103_ = lean_array_fget_borrowed(v___x_4056_, v_a_4062_);
v_isInstance_4104_ = lean_ctor_get_uint8(v___x_4103_, sizeof(void*)*1 + 4);
if (v_isInstance_4104_ == 0)
{
lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___f_4108_; 
lean_inc(v___x_4096_);
v___x_4105_ = lean_box(v_usedLetOnly_4059_);
v___x_4106_ = lean_box(v_skipConstInApp_4060_);
v___x_4107_ = lean_box(v_skipInstances_4061_);
lean_inc(v_a_4062_);
lean_inc(v___y_4064_);
lean_inc_ref(v_post_4058_);
lean_inc_ref(v_pre_4057_);
v___f_4108_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_4108_, 0, v_pre_4057_);
lean_closure_set(v___f_4108_, 1, v_post_4058_);
lean_closure_set(v___f_4108_, 2, v___x_4105_);
lean_closure_set(v___f_4108_, 3, v___x_4106_);
lean_closure_set(v___f_4108_, 4, v___x_4107_);
lean_closure_set(v___f_4108_, 5, v___x_4096_);
lean_closure_set(v___f_4108_, 6, v___y_4064_);
lean_closure_set(v___f_4108_, 7, v_b_4063_);
lean_closure_set(v___f_4108_, 8, v_a_4062_);
v___y_4071_ = v___f_4108_;
goto v___jp_4070_;
}
else
{
lean_object* v___x_4109_; lean_object* v___f_4110_; 
v___x_4109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4109_, 0, v_b_4063_);
v___f_4110_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_4110_, 0, v___x_4109_);
v___y_4071_ = v___f_4110_;
goto v___jp_4070_;
}
}
}
v___jp_4070_:
{
lean_object* v___x_4072_; 
lean_inc(v___y_4068_);
lean_inc_ref(v___y_4067_);
lean_inc(v___y_4066_);
lean_inc_ref(v___y_4065_);
v___x_4072_ = lean_apply_5(v___y_4071_, v___y_4065_, v___y_4066_, v___y_4067_, v___y_4068_, lean_box(0));
if (lean_obj_tag(v___x_4072_) == 0)
{
lean_object* v_a_4073_; lean_object* v___x_4075_; uint8_t v_isShared_4076_; uint8_t v_isSharedCheck_4085_; 
v_a_4073_ = lean_ctor_get(v___x_4072_, 0);
v_isSharedCheck_4085_ = !lean_is_exclusive(v___x_4072_);
if (v_isSharedCheck_4085_ == 0)
{
v___x_4075_ = v___x_4072_;
v_isShared_4076_ = v_isSharedCheck_4085_;
goto v_resetjp_4074_;
}
else
{
lean_inc(v_a_4073_);
lean_dec(v___x_4072_);
v___x_4075_ = lean_box(0);
v_isShared_4076_ = v_isSharedCheck_4085_;
goto v_resetjp_4074_;
}
v_resetjp_4074_:
{
if (lean_obj_tag(v_a_4073_) == 0)
{
lean_object* v_a_4077_; lean_object* v___x_4079_; 
lean_dec(v_a_4062_);
lean_dec_ref(v_post_4058_);
lean_dec_ref(v_pre_4057_);
v_a_4077_ = lean_ctor_get(v_a_4073_, 0);
lean_inc(v_a_4077_);
lean_dec_ref_known(v_a_4073_, 1);
if (v_isShared_4076_ == 0)
{
lean_ctor_set(v___x_4075_, 0, v_a_4077_);
v___x_4079_ = v___x_4075_;
goto v_reusejp_4078_;
}
else
{
lean_object* v_reuseFailAlloc_4080_; 
v_reuseFailAlloc_4080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4080_, 0, v_a_4077_);
v___x_4079_ = v_reuseFailAlloc_4080_;
goto v_reusejp_4078_;
}
v_reusejp_4078_:
{
return v___x_4079_;
}
}
else
{
lean_object* v_a_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; 
lean_del_object(v___x_4075_);
v_a_4081_ = lean_ctor_get(v_a_4073_, 0);
lean_inc(v_a_4081_);
lean_dec_ref_known(v_a_4073_, 1);
v___x_4082_ = lean_unsigned_to_nat(1u);
v___x_4083_ = lean_nat_add(v_a_4062_, v___x_4082_);
lean_dec(v_a_4062_);
v_a_4062_ = v___x_4083_;
v_b_4063_ = v_a_4081_;
goto _start;
}
}
}
else
{
lean_object* v_a_4086_; lean_object* v___x_4088_; uint8_t v_isShared_4089_; uint8_t v_isSharedCheck_4093_; 
lean_dec(v_a_4062_);
lean_dec_ref(v_post_4058_);
lean_dec_ref(v_pre_4057_);
v_a_4086_ = lean_ctor_get(v___x_4072_, 0);
v_isSharedCheck_4093_ = !lean_is_exclusive(v___x_4072_);
if (v_isSharedCheck_4093_ == 0)
{
v___x_4088_ = v___x_4072_;
v_isShared_4089_ = v_isSharedCheck_4093_;
goto v_resetjp_4087_;
}
else
{
lean_inc(v_a_4086_);
lean_dec(v___x_4072_);
v___x_4088_ = lean_box(0);
v_isShared_4089_ = v_isSharedCheck_4093_;
goto v_resetjp_4087_;
}
v_resetjp_4087_:
{
lean_object* v___x_4091_; 
if (v_isShared_4089_ == 0)
{
v___x_4091_ = v___x_4088_;
goto v_reusejp_4090_;
}
else
{
lean_object* v_reuseFailAlloc_4092_; 
v_reuseFailAlloc_4092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4092_, 0, v_a_4086_);
v___x_4091_ = v_reuseFailAlloc_4092_;
goto v_reusejp_4090_;
}
v_reusejp_4090_:
{
return v___x_4091_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__8(uint8_t v_skipInstances_4111_, lean_object* v_pre_4112_, lean_object* v_post_4113_, uint8_t v_usedLetOnly_4114_, uint8_t v_skipConstInApp_4115_, lean_object* v_x_4116_, lean_object* v_x_4117_, lean_object* v_x_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_){
_start:
{
lean_object* v_f_4126_; lean_object* v___y_4127_; lean_object* v___y_4128_; lean_object* v___y_4129_; lean_object* v___y_4130_; lean_object* v___y_4131_; 
if (lean_obj_tag(v_x_4116_) == 5)
{
lean_object* v_fn_4174_; lean_object* v_arg_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; 
v_fn_4174_ = lean_ctor_get(v_x_4116_, 0);
lean_inc_ref(v_fn_4174_);
v_arg_4175_ = lean_ctor_get(v_x_4116_, 1);
lean_inc_ref(v_arg_4175_);
lean_dec_ref_known(v_x_4116_, 2);
v___x_4176_ = lean_array_set(v_x_4117_, v_x_4118_, v_arg_4175_);
v___x_4177_ = lean_unsigned_to_nat(1u);
v___x_4178_ = lean_nat_sub(v_x_4118_, v___x_4177_);
lean_dec(v_x_4118_);
v_x_4116_ = v_fn_4174_;
v_x_4117_ = v___x_4176_;
v_x_4118_ = v___x_4178_;
goto _start;
}
else
{
lean_dec(v_x_4118_);
if (v_skipConstInApp_4115_ == 0)
{
goto v___jp_4171_;
}
else
{
uint8_t v___x_4180_; 
v___x_4180_ = l_Lean_Expr_isConst(v_x_4116_);
if (v___x_4180_ == 0)
{
goto v___jp_4171_;
}
else
{
v_f_4126_ = v_x_4116_;
v___y_4127_ = v___y_4119_;
v___y_4128_ = v___y_4120_;
v___y_4129_ = v___y_4121_;
v___y_4130_ = v___y_4122_;
v___y_4131_ = v___y_4123_;
goto v___jp_4125_;
}
}
}
v___jp_4125_:
{
if (v_skipInstances_4111_ == 0)
{
size_t v_sz_4132_; size_t v___x_4133_; lean_object* v___x_4134_; 
v_sz_4132_ = lean_array_size(v_x_4117_);
v___x_4133_ = ((size_t)0ULL);
lean_inc_ref(v_post_4113_);
lean_inc_ref(v_pre_4112_);
v___x_4134_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__2(v_pre_4112_, v_post_4113_, v_usedLetOnly_4114_, v_skipConstInApp_4115_, v_skipInstances_4111_, v_sz_4132_, v___x_4133_, v_x_4117_, v___y_4127_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_);
if (lean_obj_tag(v___x_4134_) == 0)
{
lean_object* v_a_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; 
v_a_4135_ = lean_ctor_get(v___x_4134_, 0);
lean_inc(v_a_4135_);
lean_dec_ref_known(v___x_4134_, 1);
v___x_4136_ = l_Lean_mkAppN(v_f_4126_, v_a_4135_);
lean_dec(v_a_4135_);
v___x_4137_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4112_, v_post_4113_, v_usedLetOnly_4114_, v_skipConstInApp_4115_, v_skipInstances_4111_, v___x_4136_, v___y_4127_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_);
return v___x_4137_;
}
else
{
lean_object* v_a_4138_; lean_object* v___x_4140_; uint8_t v_isShared_4141_; uint8_t v_isSharedCheck_4145_; 
lean_dec_ref(v_f_4126_);
lean_dec_ref(v_post_4113_);
lean_dec_ref(v_pre_4112_);
v_a_4138_ = lean_ctor_get(v___x_4134_, 0);
v_isSharedCheck_4145_ = !lean_is_exclusive(v___x_4134_);
if (v_isSharedCheck_4145_ == 0)
{
v___x_4140_ = v___x_4134_;
v_isShared_4141_ = v_isSharedCheck_4145_;
goto v_resetjp_4139_;
}
else
{
lean_inc(v_a_4138_);
lean_dec(v___x_4134_);
v___x_4140_ = lean_box(0);
v_isShared_4141_ = v_isSharedCheck_4145_;
goto v_resetjp_4139_;
}
v_resetjp_4139_:
{
lean_object* v___x_4143_; 
if (v_isShared_4141_ == 0)
{
v___x_4143_ = v___x_4140_;
goto v_reusejp_4142_;
}
else
{
lean_object* v_reuseFailAlloc_4144_; 
v_reuseFailAlloc_4144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4144_, 0, v_a_4138_);
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
lean_object* v___x_4146_; lean_object* v___x_4147_; 
v___x_4146_ = lean_array_get_size(v_x_4117_);
lean_inc_ref(v_f_4126_);
v___x_4147_ = l_Lean_Meta_getFunInfoNArgs(v_f_4126_, v___x_4146_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_);
if (lean_obj_tag(v___x_4147_) == 0)
{
lean_object* v_a_4148_; lean_object* v_paramInfo_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; 
v_a_4148_ = lean_ctor_get(v___x_4147_, 0);
lean_inc(v_a_4148_);
lean_dec_ref_known(v___x_4147_, 1);
v_paramInfo_4149_ = lean_ctor_get(v_a_4148_, 0);
lean_inc_ref(v_paramInfo_4149_);
lean_dec(v_a_4148_);
v___x_4150_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_4113_);
lean_inc_ref(v_pre_4112_);
v___x_4151_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg(v___x_4146_, v_paramInfo_4149_, v_pre_4112_, v_post_4113_, v_usedLetOnly_4114_, v_skipConstInApp_4115_, v_skipInstances_4111_, v___x_4150_, v_x_4117_, v___y_4127_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_);
lean_dec_ref(v_paramInfo_4149_);
if (lean_obj_tag(v___x_4151_) == 0)
{
lean_object* v_a_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; 
v_a_4152_ = lean_ctor_get(v___x_4151_, 0);
lean_inc(v_a_4152_);
lean_dec_ref_known(v___x_4151_, 1);
v___x_4153_ = l_Lean_mkAppN(v_f_4126_, v_a_4152_);
lean_dec(v_a_4152_);
v___x_4154_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4112_, v_post_4113_, v_usedLetOnly_4114_, v_skipConstInApp_4115_, v_skipInstances_4111_, v___x_4153_, v___y_4127_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_);
return v___x_4154_;
}
else
{
lean_object* v_a_4155_; lean_object* v___x_4157_; uint8_t v_isShared_4158_; uint8_t v_isSharedCheck_4162_; 
lean_dec_ref(v_f_4126_);
lean_dec_ref(v_post_4113_);
lean_dec_ref(v_pre_4112_);
v_a_4155_ = lean_ctor_get(v___x_4151_, 0);
v_isSharedCheck_4162_ = !lean_is_exclusive(v___x_4151_);
if (v_isSharedCheck_4162_ == 0)
{
v___x_4157_ = v___x_4151_;
v_isShared_4158_ = v_isSharedCheck_4162_;
goto v_resetjp_4156_;
}
else
{
lean_inc(v_a_4155_);
lean_dec(v___x_4151_);
v___x_4157_ = lean_box(0);
v_isShared_4158_ = v_isSharedCheck_4162_;
goto v_resetjp_4156_;
}
v_resetjp_4156_:
{
lean_object* v___x_4160_; 
if (v_isShared_4158_ == 0)
{
v___x_4160_ = v___x_4157_;
goto v_reusejp_4159_;
}
else
{
lean_object* v_reuseFailAlloc_4161_; 
v_reuseFailAlloc_4161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4161_, 0, v_a_4155_);
v___x_4160_ = v_reuseFailAlloc_4161_;
goto v_reusejp_4159_;
}
v_reusejp_4159_:
{
return v___x_4160_;
}
}
}
}
else
{
lean_object* v_a_4163_; lean_object* v___x_4165_; uint8_t v_isShared_4166_; uint8_t v_isSharedCheck_4170_; 
lean_dec_ref(v_f_4126_);
lean_dec_ref(v_x_4117_);
lean_dec_ref(v_post_4113_);
lean_dec_ref(v_pre_4112_);
v_a_4163_ = lean_ctor_get(v___x_4147_, 0);
v_isSharedCheck_4170_ = !lean_is_exclusive(v___x_4147_);
if (v_isSharedCheck_4170_ == 0)
{
v___x_4165_ = v___x_4147_;
v_isShared_4166_ = v_isSharedCheck_4170_;
goto v_resetjp_4164_;
}
else
{
lean_inc(v_a_4163_);
lean_dec(v___x_4147_);
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
}
v___jp_4171_:
{
lean_object* v___x_4172_; 
lean_inc_ref(v_post_4113_);
lean_inc_ref(v_pre_4112_);
v___x_4172_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4112_, v_post_4113_, v_usedLetOnly_4114_, v_skipConstInApp_4115_, v_skipInstances_4111_, v_x_4116_, v___y_4119_, v___y_4120_, v___y_4121_, v___y_4122_, v___y_4123_);
if (lean_obj_tag(v___x_4172_) == 0)
{
lean_object* v_a_4173_; 
v_a_4173_ = lean_ctor_get(v___x_4172_, 0);
lean_inc(v_a_4173_);
lean_dec_ref_known(v___x_4172_, 1);
v_f_4126_ = v_a_4173_;
v___y_4127_ = v___y_4119_;
v___y_4128_ = v___y_4120_;
v___y_4129_ = v___y_4121_;
v___y_4130_ = v___y_4122_;
v___y_4131_ = v___y_4123_;
goto v___jp_4125_;
}
else
{
lean_dec_ref(v_x_4117_);
lean_dec_ref(v_post_4113_);
lean_dec_ref(v_pre_4112_);
return v___x_4172_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1(lean_object* v___x_4181_, lean_object* v_pre_4182_, lean_object* v_e_4183_, lean_object* v_post_4184_, uint8_t v_usedLetOnly_4185_, uint8_t v_skipConstInApp_4186_, uint8_t v_skipInstances_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_){
_start:
{
lean_object* v___x_4194_; 
v___x_4194_ = l_Lean_Core_checkSystem(v___x_4181_, v___y_4191_, v___y_4192_);
if (lean_obj_tag(v___x_4194_) == 0)
{
lean_object* v___x_4195_; 
lean_dec_ref_known(v___x_4194_, 1);
lean_inc_ref(v_pre_4182_);
lean_inc(v___y_4192_);
lean_inc_ref(v___y_4191_);
lean_inc(v___y_4190_);
lean_inc_ref(v___y_4189_);
lean_inc_ref(v_e_4183_);
v___x_4195_ = lean_apply_6(v_pre_4182_, v_e_4183_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_, lean_box(0));
if (lean_obj_tag(v___x_4195_) == 0)
{
lean_object* v_a_4196_; lean_object* v___x_4198_; uint8_t v_isShared_4199_; uint8_t v_isSharedCheck_4244_; 
v_a_4196_ = lean_ctor_get(v___x_4195_, 0);
v_isSharedCheck_4244_ = !lean_is_exclusive(v___x_4195_);
if (v_isSharedCheck_4244_ == 0)
{
v___x_4198_ = v___x_4195_;
v_isShared_4199_ = v_isSharedCheck_4244_;
goto v_resetjp_4197_;
}
else
{
lean_inc(v_a_4196_);
lean_dec(v___x_4195_);
v___x_4198_ = lean_box(0);
v_isShared_4199_ = v_isSharedCheck_4244_;
goto v_resetjp_4197_;
}
v_resetjp_4197_:
{
lean_object* v___y_4201_; 
switch(lean_obj_tag(v_a_4196_))
{
case 0:
{
lean_object* v_e_4236_; lean_object* v___x_4238_; 
lean_dec_ref(v_post_4184_);
lean_dec_ref(v_e_4183_);
lean_dec_ref(v_pre_4182_);
v_e_4236_ = lean_ctor_get(v_a_4196_, 0);
lean_inc_ref(v_e_4236_);
lean_dec_ref_known(v_a_4196_, 1);
if (v_isShared_4199_ == 0)
{
lean_ctor_set(v___x_4198_, 0, v_e_4236_);
v___x_4238_ = v___x_4198_;
goto v_reusejp_4237_;
}
else
{
lean_object* v_reuseFailAlloc_4239_; 
v_reuseFailAlloc_4239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4239_, 0, v_e_4236_);
v___x_4238_ = v_reuseFailAlloc_4239_;
goto v_reusejp_4237_;
}
v_reusejp_4237_:
{
return v___x_4238_;
}
}
case 1:
{
lean_object* v_e_4240_; lean_object* v___x_4241_; 
lean_del_object(v___x_4198_);
lean_dec_ref(v_e_4183_);
v_e_4240_ = lean_ctor_get(v_a_4196_, 0);
lean_inc_ref(v_e_4240_);
lean_dec_ref_known(v_a_4196_, 1);
v___x_4241_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4182_, v_post_4184_, v_usedLetOnly_4185_, v_skipConstInApp_4186_, v_skipInstances_4187_, v_e_4240_, v___y_4188_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_);
return v___x_4241_;
}
default: 
{
lean_object* v_e_x3f_4242_; 
lean_del_object(v___x_4198_);
v_e_x3f_4242_ = lean_ctor_get(v_a_4196_, 0);
lean_inc(v_e_x3f_4242_);
lean_dec_ref_known(v_a_4196_, 1);
if (lean_obj_tag(v_e_x3f_4242_) == 0)
{
v___y_4201_ = v_e_4183_;
goto v___jp_4200_;
}
else
{
lean_object* v_val_4243_; 
lean_dec_ref(v_e_4183_);
v_val_4243_ = lean_ctor_get(v_e_x3f_4242_, 0);
lean_inc(v_val_4243_);
lean_dec_ref_known(v_e_x3f_4242_, 1);
v___y_4201_ = v_val_4243_;
goto v___jp_4200_;
}
}
}
v___jp_4200_:
{
switch(lean_obj_tag(v___y_4201_))
{
case 7:
{
lean_object* v___x_4202_; lean_object* v___x_4203_; 
v___x_4202_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_4203_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5(v_pre_4182_, v_post_4184_, v_usedLetOnly_4185_, v_skipConstInApp_4186_, v_skipInstances_4187_, v___x_4202_, v___y_4201_, v___y_4188_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_);
return v___x_4203_;
}
case 6:
{
lean_object* v___x_4204_; lean_object* v___x_4205_; 
v___x_4204_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_4205_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6(v_pre_4182_, v_post_4184_, v_usedLetOnly_4185_, v_skipConstInApp_4186_, v_skipInstances_4187_, v___x_4204_, v___y_4201_, v___y_4188_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_);
return v___x_4205_;
}
case 8:
{
lean_object* v___x_4206_; lean_object* v___x_4207_; 
v___x_4206_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_4207_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7(v_pre_4182_, v_post_4184_, v_usedLetOnly_4185_, v_skipConstInApp_4186_, v_skipInstances_4187_, v___x_4206_, v___y_4201_, v___y_4188_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_);
return v___x_4207_;
}
case 5:
{
lean_object* v_dummy_4208_; lean_object* v_nargs_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; 
v_dummy_4208_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_4209_ = l_Lean_Expr_getAppNumArgs(v___y_4201_);
lean_inc(v_nargs_4209_);
v___x_4210_ = lean_mk_array(v_nargs_4209_, v_dummy_4208_);
v___x_4211_ = lean_unsigned_to_nat(1u);
v___x_4212_ = lean_nat_sub(v_nargs_4209_, v___x_4211_);
lean_dec(v_nargs_4209_);
v___x_4213_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__8(v_skipInstances_4187_, v_pre_4182_, v_post_4184_, v_usedLetOnly_4185_, v_skipConstInApp_4186_, v___y_4201_, v___x_4210_, v___x_4212_, v___y_4188_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_);
return v___x_4213_;
}
case 10:
{
lean_object* v_data_4214_; lean_object* v_expr_4215_; lean_object* v___x_4216_; 
v_data_4214_ = lean_ctor_get(v___y_4201_, 0);
v_expr_4215_ = lean_ctor_get(v___y_4201_, 1);
lean_inc_ref(v_expr_4215_);
lean_inc_ref(v_post_4184_);
lean_inc_ref(v_pre_4182_);
v___x_4216_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4182_, v_post_4184_, v_usedLetOnly_4185_, v_skipConstInApp_4186_, v_skipInstances_4187_, v_expr_4215_, v___y_4188_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_);
if (lean_obj_tag(v___x_4216_) == 0)
{
lean_object* v_a_4217_; size_t v___x_4218_; size_t v___x_4219_; uint8_t v___x_4220_; 
v_a_4217_ = lean_ctor_get(v___x_4216_, 0);
lean_inc(v_a_4217_);
lean_dec_ref_known(v___x_4216_, 1);
v___x_4218_ = lean_ptr_addr(v_expr_4215_);
v___x_4219_ = lean_ptr_addr(v_a_4217_);
v___x_4220_ = lean_usize_dec_eq(v___x_4218_, v___x_4219_);
if (v___x_4220_ == 0)
{
lean_object* v___x_4221_; lean_object* v___x_4222_; 
lean_inc(v_data_4214_);
lean_dec_ref_known(v___y_4201_, 2);
v___x_4221_ = l_Lean_Expr_mdata___override(v_data_4214_, v_a_4217_);
v___x_4222_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4182_, v_post_4184_, v_usedLetOnly_4185_, v_skipConstInApp_4186_, v_skipInstances_4187_, v___x_4221_, v___y_4188_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_);
return v___x_4222_;
}
else
{
lean_object* v___x_4223_; 
lean_dec(v_a_4217_);
v___x_4223_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4182_, v_post_4184_, v_usedLetOnly_4185_, v_skipConstInApp_4186_, v_skipInstances_4187_, v___y_4201_, v___y_4188_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_);
return v___x_4223_;
}
}
else
{
lean_dec_ref_known(v___y_4201_, 2);
lean_dec_ref(v_post_4184_);
lean_dec_ref(v_pre_4182_);
return v___x_4216_;
}
}
case 11:
{
lean_object* v_typeName_4224_; lean_object* v_idx_4225_; lean_object* v_struct_4226_; lean_object* v___x_4227_; 
v_typeName_4224_ = lean_ctor_get(v___y_4201_, 0);
v_idx_4225_ = lean_ctor_get(v___y_4201_, 1);
v_struct_4226_ = lean_ctor_get(v___y_4201_, 2);
lean_inc_ref(v_struct_4226_);
lean_inc_ref(v_post_4184_);
lean_inc_ref(v_pre_4182_);
v___x_4227_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4182_, v_post_4184_, v_usedLetOnly_4185_, v_skipConstInApp_4186_, v_skipInstances_4187_, v_struct_4226_, v___y_4188_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_);
if (lean_obj_tag(v___x_4227_) == 0)
{
lean_object* v_a_4228_; size_t v___x_4229_; size_t v___x_4230_; uint8_t v___x_4231_; 
v_a_4228_ = lean_ctor_get(v___x_4227_, 0);
lean_inc(v_a_4228_);
lean_dec_ref_known(v___x_4227_, 1);
v___x_4229_ = lean_ptr_addr(v_struct_4226_);
v___x_4230_ = lean_ptr_addr(v_a_4228_);
v___x_4231_ = lean_usize_dec_eq(v___x_4229_, v___x_4230_);
if (v___x_4231_ == 0)
{
lean_object* v___x_4232_; lean_object* v___x_4233_; 
lean_inc(v_idx_4225_);
lean_inc(v_typeName_4224_);
lean_dec_ref_known(v___y_4201_, 3);
v___x_4232_ = l_Lean_Expr_proj___override(v_typeName_4224_, v_idx_4225_, v_a_4228_);
v___x_4233_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4182_, v_post_4184_, v_usedLetOnly_4185_, v_skipConstInApp_4186_, v_skipInstances_4187_, v___x_4232_, v___y_4188_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_);
return v___x_4233_;
}
else
{
lean_object* v___x_4234_; 
lean_dec(v_a_4228_);
v___x_4234_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4182_, v_post_4184_, v_usedLetOnly_4185_, v_skipConstInApp_4186_, v_skipInstances_4187_, v___y_4201_, v___y_4188_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_);
return v___x_4234_;
}
}
else
{
lean_dec_ref_known(v___y_4201_, 3);
lean_dec_ref(v_post_4184_);
lean_dec_ref(v_pre_4182_);
return v___x_4227_;
}
}
default: 
{
lean_object* v___x_4235_; 
v___x_4235_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4182_, v_post_4184_, v_usedLetOnly_4185_, v_skipConstInApp_4186_, v_skipInstances_4187_, v___y_4201_, v___y_4188_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_);
return v___x_4235_;
}
}
}
}
}
else
{
lean_object* v_a_4245_; lean_object* v___x_4247_; uint8_t v_isShared_4248_; uint8_t v_isSharedCheck_4252_; 
lean_dec_ref(v_post_4184_);
lean_dec_ref(v_e_4183_);
lean_dec_ref(v_pre_4182_);
v_a_4245_ = lean_ctor_get(v___x_4195_, 0);
v_isSharedCheck_4252_ = !lean_is_exclusive(v___x_4195_);
if (v_isSharedCheck_4252_ == 0)
{
v___x_4247_ = v___x_4195_;
v_isShared_4248_ = v_isSharedCheck_4252_;
goto v_resetjp_4246_;
}
else
{
lean_inc(v_a_4245_);
lean_dec(v___x_4195_);
v___x_4247_ = lean_box(0);
v_isShared_4248_ = v_isSharedCheck_4252_;
goto v_resetjp_4246_;
}
v_resetjp_4246_:
{
lean_object* v___x_4250_; 
if (v_isShared_4248_ == 0)
{
v___x_4250_ = v___x_4247_;
goto v_reusejp_4249_;
}
else
{
lean_object* v_reuseFailAlloc_4251_; 
v_reuseFailAlloc_4251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4251_, 0, v_a_4245_);
v___x_4250_ = v_reuseFailAlloc_4251_;
goto v_reusejp_4249_;
}
v_reusejp_4249_:
{
return v___x_4250_;
}
}
}
}
else
{
lean_object* v_a_4253_; lean_object* v___x_4255_; uint8_t v_isShared_4256_; uint8_t v_isSharedCheck_4260_; 
lean_dec_ref(v_post_4184_);
lean_dec_ref(v_e_4183_);
lean_dec_ref(v_pre_4182_);
v_a_4253_ = lean_ctor_get(v___x_4194_, 0);
v_isSharedCheck_4260_ = !lean_is_exclusive(v___x_4194_);
if (v_isSharedCheck_4260_ == 0)
{
v___x_4255_ = v___x_4194_;
v_isShared_4256_ = v_isSharedCheck_4260_;
goto v_resetjp_4254_;
}
else
{
lean_inc(v_a_4253_);
lean_dec(v___x_4194_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1___boxed(lean_object* v___x_4261_, lean_object* v_pre_4262_, lean_object* v_e_4263_, lean_object* v_post_4264_, lean_object* v_usedLetOnly_4265_, lean_object* v_skipConstInApp_4266_, lean_object* v_skipInstances_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_){
_start:
{
uint8_t v_usedLetOnly_boxed_4274_; uint8_t v_skipConstInApp_boxed_4275_; uint8_t v_skipInstances_boxed_4276_; lean_object* v_res_4277_; 
v_usedLetOnly_boxed_4274_ = lean_unbox(v_usedLetOnly_4265_);
v_skipConstInApp_boxed_4275_ = lean_unbox(v_skipConstInApp_4266_);
v_skipInstances_boxed_4276_ = lean_unbox(v_skipInstances_4267_);
v_res_4277_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1(v___x_4261_, v_pre_4262_, v_e_4263_, v_post_4264_, v_usedLetOnly_boxed_4274_, v_skipConstInApp_boxed_4275_, v_skipInstances_boxed_4276_, v___y_4268_, v___y_4269_, v___y_4270_, v___y_4271_, v___y_4272_);
lean_dec(v___y_4272_);
lean_dec_ref(v___y_4271_);
lean_dec(v___y_4270_);
lean_dec_ref(v___y_4269_);
lean_dec(v___y_4268_);
return v_res_4277_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(lean_object* v_pre_4278_, lean_object* v_post_4279_, uint8_t v_usedLetOnly_4280_, uint8_t v_skipConstInApp_4281_, uint8_t v_skipInstances_4282_, lean_object* v_e_4283_, lean_object* v_a_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_){
_start:
{
lean_object* v___x_4290_; lean_object* v___x_4291_; 
lean_inc(v_a_4284_);
v___x_4290_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_4290_, 0, lean_box(0));
lean_closure_set(v___x_4290_, 1, lean_box(0));
lean_closure_set(v___x_4290_, 2, v_a_4284_);
v___x_4291_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0(lean_box(0), v___x_4290_, v___y_4285_, v___y_4286_, v___y_4287_, v___y_4288_);
if (lean_obj_tag(v___x_4291_) == 0)
{
lean_object* v_a_4292_; lean_object* v___x_4294_; uint8_t v_isShared_4295_; uint8_t v_isSharedCheck_4326_; 
v_a_4292_ = lean_ctor_get(v___x_4291_, 0);
v_isSharedCheck_4326_ = !lean_is_exclusive(v___x_4291_);
if (v_isSharedCheck_4326_ == 0)
{
v___x_4294_ = v___x_4291_;
v_isShared_4295_ = v_isSharedCheck_4326_;
goto v_resetjp_4293_;
}
else
{
lean_inc(v_a_4292_);
lean_dec(v___x_4291_);
v___x_4294_ = lean_box(0);
v_isShared_4295_ = v_isSharedCheck_4326_;
goto v_resetjp_4293_;
}
v_resetjp_4293_:
{
lean_object* v___x_4296_; 
v___x_4296_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg(v_a_4292_, v_e_4283_);
lean_dec(v_a_4292_);
if (lean_obj_tag(v___x_4296_) == 0)
{
lean_object* v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; lean_object* v___f_4301_; lean_object* v___x_4302_; 
lean_del_object(v___x_4294_);
v___x_4297_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__19___closed__0));
v___x_4298_ = lean_box(v_usedLetOnly_4280_);
v___x_4299_ = lean_box(v_skipConstInApp_4281_);
v___x_4300_ = lean_box(v_skipInstances_4282_);
lean_inc_ref(v_e_4283_);
v___f_4301_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1___boxed), 13, 7);
lean_closure_set(v___f_4301_, 0, v___x_4297_);
lean_closure_set(v___f_4301_, 1, v_pre_4278_);
lean_closure_set(v___f_4301_, 2, v_e_4283_);
lean_closure_set(v___f_4301_, 3, v_post_4279_);
lean_closure_set(v___f_4301_, 4, v___x_4298_);
lean_closure_set(v___f_4301_, 5, v___x_4299_);
lean_closure_set(v___f_4301_, 6, v___x_4300_);
v___x_4302_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg(v___f_4301_, v_a_4284_, v___y_4285_, v___y_4286_, v___y_4287_, v___y_4288_);
if (lean_obj_tag(v___x_4302_) == 0)
{
lean_object* v_a_4303_; lean_object* v___f_4304_; lean_object* v___x_4305_; 
v_a_4303_ = lean_ctor_get(v___x_4302_, 0);
lean_inc_n(v_a_4303_, 2);
lean_dec_ref_known(v___x_4302_, 1);
lean_inc(v_a_4284_);
v___f_4304_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_4304_, 0, v_a_4284_);
lean_closure_set(v___f_4304_, 1, v_e_4283_);
lean_closure_set(v___f_4304_, 2, v_a_4303_);
v___x_4305_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0(lean_box(0), v___f_4304_, v___y_4285_, v___y_4286_, v___y_4287_, v___y_4288_);
if (lean_obj_tag(v___x_4305_) == 0)
{
lean_object* v___x_4307_; uint8_t v_isShared_4308_; uint8_t v_isSharedCheck_4312_; 
v_isSharedCheck_4312_ = !lean_is_exclusive(v___x_4305_);
if (v_isSharedCheck_4312_ == 0)
{
lean_object* v_unused_4313_; 
v_unused_4313_ = lean_ctor_get(v___x_4305_, 0);
lean_dec(v_unused_4313_);
v___x_4307_ = v___x_4305_;
v_isShared_4308_ = v_isSharedCheck_4312_;
goto v_resetjp_4306_;
}
else
{
lean_dec(v___x_4305_);
v___x_4307_ = lean_box(0);
v_isShared_4308_ = v_isSharedCheck_4312_;
goto v_resetjp_4306_;
}
v_resetjp_4306_:
{
lean_object* v___x_4310_; 
if (v_isShared_4308_ == 0)
{
lean_ctor_set(v___x_4307_, 0, v_a_4303_);
v___x_4310_ = v___x_4307_;
goto v_reusejp_4309_;
}
else
{
lean_object* v_reuseFailAlloc_4311_; 
v_reuseFailAlloc_4311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4311_, 0, v_a_4303_);
v___x_4310_ = v_reuseFailAlloc_4311_;
goto v_reusejp_4309_;
}
v_reusejp_4309_:
{
return v___x_4310_;
}
}
}
else
{
lean_object* v_a_4314_; lean_object* v___x_4316_; uint8_t v_isShared_4317_; uint8_t v_isSharedCheck_4321_; 
lean_dec(v_a_4303_);
v_a_4314_ = lean_ctor_get(v___x_4305_, 0);
v_isSharedCheck_4321_ = !lean_is_exclusive(v___x_4305_);
if (v_isSharedCheck_4321_ == 0)
{
v___x_4316_ = v___x_4305_;
v_isShared_4317_ = v_isSharedCheck_4321_;
goto v_resetjp_4315_;
}
else
{
lean_inc(v_a_4314_);
lean_dec(v___x_4305_);
v___x_4316_ = lean_box(0);
v_isShared_4317_ = v_isSharedCheck_4321_;
goto v_resetjp_4315_;
}
v_resetjp_4315_:
{
lean_object* v___x_4319_; 
if (v_isShared_4317_ == 0)
{
v___x_4319_ = v___x_4316_;
goto v_reusejp_4318_;
}
else
{
lean_object* v_reuseFailAlloc_4320_; 
v_reuseFailAlloc_4320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4320_, 0, v_a_4314_);
v___x_4319_ = v_reuseFailAlloc_4320_;
goto v_reusejp_4318_;
}
v_reusejp_4318_:
{
return v___x_4319_;
}
}
}
}
else
{
lean_dec_ref(v_e_4283_);
return v___x_4302_;
}
}
else
{
lean_object* v_val_4322_; lean_object* v___x_4324_; 
lean_dec_ref(v_e_4283_);
lean_dec_ref(v_post_4279_);
lean_dec_ref(v_pre_4278_);
v_val_4322_ = lean_ctor_get(v___x_4296_, 0);
lean_inc(v_val_4322_);
lean_dec_ref_known(v___x_4296_, 1);
if (v_isShared_4295_ == 0)
{
lean_ctor_set(v___x_4294_, 0, v_val_4322_);
v___x_4324_ = v___x_4294_;
goto v_reusejp_4323_;
}
else
{
lean_object* v_reuseFailAlloc_4325_; 
v_reuseFailAlloc_4325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4325_, 0, v_val_4322_);
v___x_4324_ = v_reuseFailAlloc_4325_;
goto v_reusejp_4323_;
}
v_reusejp_4323_:
{
return v___x_4324_;
}
}
}
}
else
{
lean_object* v_a_4327_; lean_object* v___x_4329_; uint8_t v_isShared_4330_; uint8_t v_isSharedCheck_4334_; 
lean_dec_ref(v_e_4283_);
lean_dec_ref(v_post_4279_);
lean_dec_ref(v_pre_4278_);
v_a_4327_ = lean_ctor_get(v___x_4291_, 0);
v_isSharedCheck_4334_ = !lean_is_exclusive(v___x_4291_);
if (v_isSharedCheck_4334_ == 0)
{
v___x_4329_ = v___x_4291_;
v_isShared_4330_ = v_isSharedCheck_4334_;
goto v_resetjp_4328_;
}
else
{
lean_inc(v_a_4327_);
lean_dec(v___x_4291_);
v___x_4329_ = lean_box(0);
v_isShared_4330_ = v_isSharedCheck_4334_;
goto v_resetjp_4328_;
}
v_resetjp_4328_:
{
lean_object* v___x_4332_; 
if (v_isShared_4330_ == 0)
{
v___x_4332_ = v___x_4329_;
goto v_reusejp_4331_;
}
else
{
lean_object* v_reuseFailAlloc_4333_; 
v_reuseFailAlloc_4333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4333_, 0, v_a_4327_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5(lean_object* v_pre_4335_, lean_object* v_post_4336_, uint8_t v_usedLetOnly_4337_, uint8_t v_skipConstInApp_4338_, uint8_t v_skipInstances_4339_, lean_object* v_fvars_4340_, lean_object* v_e_4341_, lean_object* v_a_4342_, lean_object* v___y_4343_, lean_object* v___y_4344_, lean_object* v___y_4345_, lean_object* v___y_4346_){
_start:
{
if (lean_obj_tag(v_e_4341_) == 7)
{
lean_object* v_binderName_4348_; lean_object* v_binderType_4349_; lean_object* v_body_4350_; uint8_t v_binderInfo_4351_; lean_object* v___x_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; lean_object* v___f_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; 
v_binderName_4348_ = lean_ctor_get(v_e_4341_, 0);
lean_inc(v_binderName_4348_);
v_binderType_4349_ = lean_ctor_get(v_e_4341_, 1);
lean_inc_ref(v_binderType_4349_);
v_body_4350_ = lean_ctor_get(v_e_4341_, 2);
lean_inc_ref(v_body_4350_);
v_binderInfo_4351_ = lean_ctor_get_uint8(v_e_4341_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_4341_, 3);
v___x_4352_ = lean_box(v_usedLetOnly_4337_);
v___x_4353_ = lean_box(v_skipConstInApp_4338_);
v___x_4354_ = lean_box(v_skipInstances_4339_);
lean_inc_ref(v_post_4336_);
lean_inc_ref(v_pre_4335_);
lean_inc_ref(v_fvars_4340_);
v___f_4355_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___lam__0___boxed), 14, 7);
lean_closure_set(v___f_4355_, 0, v_fvars_4340_);
lean_closure_set(v___f_4355_, 1, v_pre_4335_);
lean_closure_set(v___f_4355_, 2, v_post_4336_);
lean_closure_set(v___f_4355_, 3, v___x_4352_);
lean_closure_set(v___f_4355_, 4, v___x_4353_);
lean_closure_set(v___f_4355_, 5, v___x_4354_);
lean_closure_set(v___f_4355_, 6, v_body_4350_);
v___x_4356_ = lean_expr_instantiate_rev(v_binderType_4349_, v_fvars_4340_);
lean_dec_ref(v_fvars_4340_);
lean_dec_ref(v_binderType_4349_);
v___x_4357_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4335_, v_post_4336_, v_usedLetOnly_4337_, v_skipConstInApp_4338_, v_skipInstances_4339_, v___x_4356_, v_a_4342_, v___y_4343_, v___y_4344_, v___y_4345_, v___y_4346_);
if (lean_obj_tag(v___x_4357_) == 0)
{
lean_object* v_a_4358_; uint8_t v___x_4359_; lean_object* v___x_4360_; 
v_a_4358_ = lean_ctor_get(v___x_4357_, 0);
lean_inc(v_a_4358_);
lean_dec_ref_known(v___x_4357_, 1);
v___x_4359_ = 0;
v___x_4360_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_binderName_4348_, v_binderInfo_4351_, v_a_4358_, v___f_4355_, v___x_4359_, v_a_4342_, v___y_4343_, v___y_4344_, v___y_4345_, v___y_4346_);
return v___x_4360_;
}
else
{
lean_dec_ref(v___f_4355_);
lean_dec(v_binderName_4348_);
return v___x_4357_;
}
}
else
{
lean_object* v___x_4361_; lean_object* v___x_4362_; 
v___x_4361_ = lean_expr_instantiate_rev(v_e_4341_, v_fvars_4340_);
lean_dec_ref(v_e_4341_);
lean_inc_ref(v_post_4336_);
lean_inc_ref(v_pre_4335_);
v___x_4362_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4335_, v_post_4336_, v_usedLetOnly_4337_, v_skipConstInApp_4338_, v_skipInstances_4339_, v___x_4361_, v_a_4342_, v___y_4343_, v___y_4344_, v___y_4345_, v___y_4346_);
if (lean_obj_tag(v___x_4362_) == 0)
{
lean_object* v_a_4363_; uint8_t v___x_4364_; uint8_t v___x_4365_; uint8_t v___x_4366_; lean_object* v___x_4367_; 
v_a_4363_ = lean_ctor_get(v___x_4362_, 0);
lean_inc(v_a_4363_);
lean_dec_ref_known(v___x_4362_, 1);
v___x_4364_ = 0;
v___x_4365_ = 1;
v___x_4366_ = 1;
v___x_4367_ = l_Lean_Meta_mkForallFVars(v_fvars_4340_, v_a_4363_, v___x_4364_, v_usedLetOnly_4337_, v___x_4365_, v___x_4366_, v___y_4343_, v___y_4344_, v___y_4345_, v___y_4346_);
lean_dec_ref(v_fvars_4340_);
if (lean_obj_tag(v___x_4367_) == 0)
{
lean_object* v_a_4368_; lean_object* v___x_4369_; 
v_a_4368_ = lean_ctor_get(v___x_4367_, 0);
lean_inc(v_a_4368_);
lean_dec_ref_known(v___x_4367_, 1);
v___x_4369_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4335_, v_post_4336_, v_usedLetOnly_4337_, v_skipConstInApp_4338_, v_skipInstances_4339_, v_a_4368_, v_a_4342_, v___y_4343_, v___y_4344_, v___y_4345_, v___y_4346_);
return v___x_4369_;
}
else
{
lean_dec_ref(v_post_4336_);
lean_dec_ref(v_pre_4335_);
return v___x_4367_;
}
}
else
{
lean_dec_ref(v_fvars_4340_);
lean_dec_ref(v_post_4336_);
lean_dec_ref(v_pre_4335_);
return v___x_4362_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___lam__0(lean_object* v_fvars_4370_, lean_object* v_pre_4371_, lean_object* v_post_4372_, uint8_t v_usedLetOnly_4373_, uint8_t v_skipConstInApp_4374_, uint8_t v_skipInstances_4375_, lean_object* v_body_4376_, lean_object* v_x_4377_, lean_object* v___y_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_){
_start:
{
lean_object* v___x_4384_; lean_object* v___x_4385_; 
v___x_4384_ = lean_array_push(v_fvars_4370_, v_x_4377_);
v___x_4385_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5(v_pre_4371_, v_post_4372_, v_usedLetOnly_4373_, v_skipConstInApp_4374_, v_skipInstances_4375_, v___x_4384_, v_body_4376_, v___y_4378_, v___y_4379_, v___y_4380_, v___y_4381_, v___y_4382_);
return v___x_4385_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3___boxed(lean_object* v_pre_4386_, lean_object* v_post_4387_, lean_object* v_usedLetOnly_4388_, lean_object* v_skipConstInApp_4389_, lean_object* v_skipInstances_4390_, lean_object* v_e_4391_, lean_object* v_a_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_, lean_object* v___y_4397_){
_start:
{
uint8_t v_usedLetOnly_boxed_4398_; uint8_t v_skipConstInApp_boxed_4399_; uint8_t v_skipInstances_boxed_4400_; lean_object* v_res_4401_; 
v_usedLetOnly_boxed_4398_ = lean_unbox(v_usedLetOnly_4388_);
v_skipConstInApp_boxed_4399_ = lean_unbox(v_skipConstInApp_4389_);
v_skipInstances_boxed_4400_ = lean_unbox(v_skipInstances_4390_);
v_res_4401_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4386_, v_post_4387_, v_usedLetOnly_boxed_4398_, v_skipConstInApp_boxed_4399_, v_skipInstances_boxed_4400_, v_e_4391_, v_a_4392_, v___y_4393_, v___y_4394_, v___y_4395_, v___y_4396_);
lean_dec(v___y_4396_);
lean_dec_ref(v___y_4395_);
lean_dec(v___y_4394_);
lean_dec_ref(v___y_4393_);
lean_dec(v_a_4392_);
return v_res_4401_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__2___boxed(lean_object* v_pre_4402_, lean_object* v_post_4403_, lean_object* v_usedLetOnly_4404_, lean_object* v_skipConstInApp_4405_, lean_object* v_skipInstances_4406_, lean_object* v_sz_4407_, lean_object* v_i_4408_, lean_object* v_bs_4409_, lean_object* v___y_4410_, lean_object* v___y_4411_, lean_object* v___y_4412_, lean_object* v___y_4413_, lean_object* v___y_4414_, lean_object* v___y_4415_){
_start:
{
uint8_t v_usedLetOnly_boxed_4416_; uint8_t v_skipConstInApp_boxed_4417_; uint8_t v_skipInstances_boxed_4418_; size_t v_sz_boxed_4419_; size_t v_i_boxed_4420_; lean_object* v_res_4421_; 
v_usedLetOnly_boxed_4416_ = lean_unbox(v_usedLetOnly_4404_);
v_skipConstInApp_boxed_4417_ = lean_unbox(v_skipConstInApp_4405_);
v_skipInstances_boxed_4418_ = lean_unbox(v_skipInstances_4406_);
v_sz_boxed_4419_ = lean_unbox_usize(v_sz_4407_);
lean_dec(v_sz_4407_);
v_i_boxed_4420_ = lean_unbox_usize(v_i_4408_);
lean_dec(v_i_4408_);
v_res_4421_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__2(v_pre_4402_, v_post_4403_, v_usedLetOnly_boxed_4416_, v_skipConstInApp_boxed_4417_, v_skipInstances_boxed_4418_, v_sz_boxed_4419_, v_i_boxed_4420_, v_bs_4409_, v___y_4410_, v___y_4411_, v___y_4412_, v___y_4413_, v___y_4414_);
lean_dec(v___y_4414_);
lean_dec_ref(v___y_4413_);
lean_dec(v___y_4412_);
lean_dec_ref(v___y_4411_);
lean_dec(v___y_4410_);
return v_res_4421_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___boxed(lean_object* v_pre_4422_, lean_object* v_post_4423_, lean_object* v_usedLetOnly_4424_, lean_object* v_skipConstInApp_4425_, lean_object* v_skipInstances_4426_, lean_object* v_e_4427_, lean_object* v_a_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_){
_start:
{
uint8_t v_usedLetOnly_boxed_4434_; uint8_t v_skipConstInApp_boxed_4435_; uint8_t v_skipInstances_boxed_4436_; lean_object* v_res_4437_; 
v_usedLetOnly_boxed_4434_ = lean_unbox(v_usedLetOnly_4424_);
v_skipConstInApp_boxed_4435_ = lean_unbox(v_skipConstInApp_4425_);
v_skipInstances_boxed_4436_ = lean_unbox(v_skipInstances_4426_);
v_res_4437_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4422_, v_post_4423_, v_usedLetOnly_boxed_4434_, v_skipConstInApp_boxed_4435_, v_skipInstances_boxed_4436_, v_e_4427_, v_a_4428_, v___y_4429_, v___y_4430_, v___y_4431_, v___y_4432_);
lean_dec(v___y_4432_);
lean_dec_ref(v___y_4431_);
lean_dec(v___y_4430_);
lean_dec_ref(v___y_4429_);
lean_dec(v_a_4428_);
return v_res_4437_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___boxed(lean_object* v_pre_4438_, lean_object* v_post_4439_, lean_object* v_usedLetOnly_4440_, lean_object* v_skipConstInApp_4441_, lean_object* v_skipInstances_4442_, lean_object* v_fvars_4443_, lean_object* v_e_4444_, lean_object* v_a_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_){
_start:
{
uint8_t v_usedLetOnly_boxed_4451_; uint8_t v_skipConstInApp_boxed_4452_; uint8_t v_skipInstances_boxed_4453_; lean_object* v_res_4454_; 
v_usedLetOnly_boxed_4451_ = lean_unbox(v_usedLetOnly_4440_);
v_skipConstInApp_boxed_4452_ = lean_unbox(v_skipConstInApp_4441_);
v_skipInstances_boxed_4453_ = lean_unbox(v_skipInstances_4442_);
v_res_4454_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5(v_pre_4438_, v_post_4439_, v_usedLetOnly_boxed_4451_, v_skipConstInApp_boxed_4452_, v_skipInstances_boxed_4453_, v_fvars_4443_, v_e_4444_, v_a_4445_, v___y_4446_, v___y_4447_, v___y_4448_, v___y_4449_);
lean_dec(v___y_4449_);
lean_dec_ref(v___y_4448_);
lean_dec(v___y_4447_);
lean_dec_ref(v___y_4446_);
lean_dec(v_a_4445_);
return v_res_4454_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___boxed(lean_object* v_pre_4455_, lean_object* v_post_4456_, lean_object* v_usedLetOnly_4457_, lean_object* v_skipConstInApp_4458_, lean_object* v_skipInstances_4459_, lean_object* v_fvars_4460_, lean_object* v_e_4461_, lean_object* v_a_4462_, lean_object* v___y_4463_, lean_object* v___y_4464_, lean_object* v___y_4465_, lean_object* v___y_4466_, lean_object* v___y_4467_){
_start:
{
uint8_t v_usedLetOnly_boxed_4468_; uint8_t v_skipConstInApp_boxed_4469_; uint8_t v_skipInstances_boxed_4470_; lean_object* v_res_4471_; 
v_usedLetOnly_boxed_4468_ = lean_unbox(v_usedLetOnly_4457_);
v_skipConstInApp_boxed_4469_ = lean_unbox(v_skipConstInApp_4458_);
v_skipInstances_boxed_4470_ = lean_unbox(v_skipInstances_4459_);
v_res_4471_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6(v_pre_4455_, v_post_4456_, v_usedLetOnly_boxed_4468_, v_skipConstInApp_boxed_4469_, v_skipInstances_boxed_4470_, v_fvars_4460_, v_e_4461_, v_a_4462_, v___y_4463_, v___y_4464_, v___y_4465_, v___y_4466_);
lean_dec(v___y_4466_);
lean_dec_ref(v___y_4465_);
lean_dec(v___y_4464_);
lean_dec_ref(v___y_4463_);
lean_dec(v_a_4462_);
return v_res_4471_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___boxed(lean_object* v_pre_4472_, lean_object* v_post_4473_, lean_object* v_usedLetOnly_4474_, lean_object* v_skipConstInApp_4475_, lean_object* v_skipInstances_4476_, lean_object* v_fvars_4477_, lean_object* v_e_4478_, lean_object* v_a_4479_, lean_object* v___y_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_, lean_object* v___y_4483_, lean_object* v___y_4484_){
_start:
{
uint8_t v_usedLetOnly_boxed_4485_; uint8_t v_skipConstInApp_boxed_4486_; uint8_t v_skipInstances_boxed_4487_; lean_object* v_res_4488_; 
v_usedLetOnly_boxed_4485_ = lean_unbox(v_usedLetOnly_4474_);
v_skipConstInApp_boxed_4486_ = lean_unbox(v_skipConstInApp_4475_);
v_skipInstances_boxed_4487_ = lean_unbox(v_skipInstances_4476_);
v_res_4488_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7(v_pre_4472_, v_post_4473_, v_usedLetOnly_boxed_4485_, v_skipConstInApp_boxed_4486_, v_skipInstances_boxed_4487_, v_fvars_4477_, v_e_4478_, v_a_4479_, v___y_4480_, v___y_4481_, v___y_4482_, v___y_4483_);
lean_dec(v___y_4483_);
lean_dec_ref(v___y_4482_);
lean_dec(v___y_4481_);
lean_dec_ref(v___y_4480_);
lean_dec(v_a_4479_);
return v_res_4488_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_upperBound_4489_, lean_object* v___x_4490_, lean_object* v_pre_4491_, lean_object* v_post_4492_, lean_object* v_usedLetOnly_4493_, lean_object* v_skipConstInApp_4494_, lean_object* v_skipInstances_4495_, lean_object* v_a_4496_, lean_object* v_b_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_, lean_object* v___y_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_, lean_object* v___y_4503_){
_start:
{
uint8_t v_usedLetOnly_boxed_4504_; uint8_t v_skipConstInApp_boxed_4505_; uint8_t v_skipInstances_boxed_4506_; lean_object* v_res_4507_; 
v_usedLetOnly_boxed_4504_ = lean_unbox(v_usedLetOnly_4493_);
v_skipConstInApp_boxed_4505_ = lean_unbox(v_skipConstInApp_4494_);
v_skipInstances_boxed_4506_ = lean_unbox(v_skipInstances_4495_);
v_res_4507_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg(v_upperBound_4489_, v___x_4490_, v_pre_4491_, v_post_4492_, v_usedLetOnly_boxed_4504_, v_skipConstInApp_boxed_4505_, v_skipInstances_boxed_4506_, v_a_4496_, v_b_4497_, v___y_4498_, v___y_4499_, v___y_4500_, v___y_4501_, v___y_4502_);
lean_dec(v___y_4502_);
lean_dec_ref(v___y_4501_);
lean_dec(v___y_4500_);
lean_dec_ref(v___y_4499_);
lean_dec(v___y_4498_);
lean_dec_ref(v___x_4490_);
lean_dec(v_upperBound_4489_);
return v_res_4507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__8___boxed(lean_object* v_skipInstances_4508_, lean_object* v_pre_4509_, lean_object* v_post_4510_, lean_object* v_usedLetOnly_4511_, lean_object* v_skipConstInApp_4512_, lean_object* v_x_4513_, lean_object* v_x_4514_, lean_object* v_x_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_){
_start:
{
uint8_t v_skipInstances_boxed_4522_; uint8_t v_usedLetOnly_boxed_4523_; uint8_t v_skipConstInApp_boxed_4524_; lean_object* v_res_4525_; 
v_skipInstances_boxed_4522_ = lean_unbox(v_skipInstances_4508_);
v_usedLetOnly_boxed_4523_ = lean_unbox(v_usedLetOnly_4511_);
v_skipConstInApp_boxed_4524_ = lean_unbox(v_skipConstInApp_4512_);
v_res_4525_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__8(v_skipInstances_boxed_4522_, v_pre_4509_, v_post_4510_, v_usedLetOnly_boxed_4523_, v_skipConstInApp_boxed_4524_, v_x_4513_, v_x_4514_, v_x_4515_, v___y_4516_, v___y_4517_, v___y_4518_, v___y_4519_, v___y_4520_);
lean_dec(v___y_4520_);
lean_dec_ref(v___y_4519_);
lean_dec(v___y_4518_);
lean_dec_ref(v___y_4517_);
lean_dec(v___y_4516_);
return v_res_4525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(lean_object* v_input_4526_, lean_object* v_pre_4527_, lean_object* v_post_4528_, uint8_t v_usedLetOnly_4529_, uint8_t v_skipConstInApp_4530_, lean_object* v___y_4531_, lean_object* v___y_4532_, lean_object* v___y_4533_, lean_object* v___y_4534_){
_start:
{
uint8_t v___x_4536_; lean_object* v___x_4537_; lean_object* v___x_4538_; lean_object* v_a_4539_; lean_object* v___x_4540_; 
v___x_4536_ = 0;
v___x_4537_ = lean_obj_once(&l_Lean_Core_transform___redArg___closed__2, &l_Lean_Core_transform___redArg___closed__2_once, _init_l_Lean_Core_transform___redArg___closed__2);
v___x_4538_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0(lean_box(0), v___x_4537_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_);
v_a_4539_ = lean_ctor_get(v___x_4538_, 0);
lean_inc(v_a_4539_);
lean_dec_ref(v___x_4538_);
v___x_4540_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4527_, v_post_4528_, v_usedLetOnly_4529_, v_skipConstInApp_4530_, v___x_4536_, v_input_4526_, v_a_4539_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_);
if (lean_obj_tag(v___x_4540_) == 0)
{
lean_object* v_a_4541_; lean_object* v___x_4542_; lean_object* v___x_4543_; lean_object* v___x_4545_; uint8_t v_isShared_4546_; uint8_t v_isSharedCheck_4550_; 
v_a_4541_ = lean_ctor_get(v___x_4540_, 0);
lean_inc(v_a_4541_);
lean_dec_ref_known(v___x_4540_, 1);
v___x_4542_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_4542_, 0, lean_box(0));
lean_closure_set(v___x_4542_, 1, lean_box(0));
lean_closure_set(v___x_4542_, 2, v_a_4539_);
v___x_4543_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0(lean_box(0), v___x_4542_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_);
v_isSharedCheck_4550_ = !lean_is_exclusive(v___x_4543_);
if (v_isSharedCheck_4550_ == 0)
{
lean_object* v_unused_4551_; 
v_unused_4551_ = lean_ctor_get(v___x_4543_, 0);
lean_dec(v_unused_4551_);
v___x_4545_ = v___x_4543_;
v_isShared_4546_ = v_isSharedCheck_4550_;
goto v_resetjp_4544_;
}
else
{
lean_dec(v___x_4543_);
v___x_4545_ = lean_box(0);
v_isShared_4546_ = v_isSharedCheck_4550_;
goto v_resetjp_4544_;
}
v_resetjp_4544_:
{
lean_object* v___x_4548_; 
if (v_isShared_4546_ == 0)
{
lean_ctor_set(v___x_4545_, 0, v_a_4541_);
v___x_4548_ = v___x_4545_;
goto v_reusejp_4547_;
}
else
{
lean_object* v_reuseFailAlloc_4549_; 
v_reuseFailAlloc_4549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4549_, 0, v_a_4541_);
v___x_4548_ = v_reuseFailAlloc_4549_;
goto v_reusejp_4547_;
}
v_reusejp_4547_:
{
return v___x_4548_;
}
}
}
else
{
lean_dec(v_a_4539_);
return v___x_4540_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___boxed(lean_object* v_input_4552_, lean_object* v_pre_4553_, lean_object* v_post_4554_, lean_object* v_usedLetOnly_4555_, lean_object* v_skipConstInApp_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_, lean_object* v___y_4559_, lean_object* v___y_4560_, lean_object* v___y_4561_){
_start:
{
uint8_t v_usedLetOnly_boxed_4562_; uint8_t v_skipConstInApp_boxed_4563_; lean_object* v_res_4564_; 
v_usedLetOnly_boxed_4562_ = lean_unbox(v_usedLetOnly_4555_);
v_skipConstInApp_boxed_4563_ = lean_unbox(v_skipConstInApp_4556_);
v_res_4564_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(v_input_4552_, v_pre_4553_, v_post_4554_, v_usedLetOnly_boxed_4562_, v_skipConstInApp_boxed_4563_, v___y_4557_, v___y_4558_, v___y_4559_, v___y_4560_);
lean_dec(v___y_4560_);
lean_dec_ref(v___y_4559_);
lean_dec(v___y_4558_);
lean_dec_ref(v___y_4557_);
return v_res_4564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce(lean_object* v_e_4566_, uint8_t v_zetaDelta_4567_, uint8_t v_zetaHave_4568_, uint8_t v_beta_4569_, lean_object* v_a_4570_, lean_object* v_a_4571_, lean_object* v_a_4572_, lean_object* v_a_4573_){
_start:
{
lean_object* v_lctx_4575_; lean_object* v___x_4576_; lean_object* v___x_4577_; lean_object* v___x_4578_; lean_object* v___f_4579_; uint8_t v___x_4580_; 
v_lctx_4575_ = lean_ctor_get(v_a_4570_, 2);
lean_inc_ref(v_lctx_4575_);
v___x_4576_ = lean_local_ctx_num_indices(v_lctx_4575_);
v___x_4577_ = lean_box(v_zetaHave_4568_);
v___x_4578_ = lean_box(v_zetaDelta_4567_);
v___f_4579_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaReduce___lam__0___boxed), 9, 3);
lean_closure_set(v___f_4579_, 0, v___x_4577_);
lean_closure_set(v___f_4579_, 1, v___x_4576_);
lean_closure_set(v___f_4579_, 2, v___x_4578_);
v___x_4580_ = 1;
if (v_beta_4569_ == 0)
{
lean_object* v___f_4581_; lean_object* v___f_4582_; lean_object* v___x_4583_; 
v___f_4581_ = ((lean_object*)(l_Lean_Meta_zetaReduce___closed__0));
v___f_4582_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaReduce___lam__2___boxed), 7, 1);
lean_closure_set(v___f_4582_, 0, v___f_4579_);
v___x_4583_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(v_e_4566_, v___f_4582_, v___f_4581_, v___x_4580_, v_beta_4569_, v_a_4570_, v_a_4571_, v_a_4572_, v_a_4573_);
return v___x_4583_;
}
else
{
lean_object* v___f_4584_; lean_object* v___f_4585_; uint8_t v___x_4586_; lean_object* v___x_4587_; 
v___f_4584_ = ((lean_object*)(l_Lean_Meta_zetaReduce___closed__0));
v___f_4585_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaReduce___lam__4___boxed), 7, 1);
lean_closure_set(v___f_4585_, 0, v___f_4579_);
v___x_4586_ = 0;
v___x_4587_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(v_e_4566_, v___f_4585_, v___f_4584_, v___x_4580_, v___x_4586_, v_a_4570_, v_a_4571_, v_a_4572_, v_a_4573_);
return v___x_4587_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___boxed(lean_object* v_e_4588_, lean_object* v_zetaDelta_4589_, lean_object* v_zetaHave_4590_, lean_object* v_beta_4591_, lean_object* v_a_4592_, lean_object* v_a_4593_, lean_object* v_a_4594_, lean_object* v_a_4595_, lean_object* v_a_4596_){
_start:
{
uint8_t v_zetaDelta_boxed_4597_; uint8_t v_zetaHave_boxed_4598_; uint8_t v_beta_boxed_4599_; lean_object* v_res_4600_; 
v_zetaDelta_boxed_4597_ = lean_unbox(v_zetaDelta_4589_);
v_zetaHave_boxed_4598_ = lean_unbox(v_zetaHave_4590_);
v_beta_boxed_4599_ = lean_unbox(v_beta_4591_);
v_res_4600_ = l_Lean_Meta_zetaReduce(v_e_4588_, v_zetaDelta_boxed_4597_, v_zetaHave_boxed_4598_, v_beta_boxed_4599_, v_a_4592_, v_a_4593_, v_a_4594_, v_a_4595_);
lean_dec(v_a_4595_);
lean_dec_ref(v_a_4594_);
lean_dec(v_a_4593_);
lean_dec_ref(v_a_4592_);
return v_res_4600_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4(lean_object* v_upperBound_4601_, lean_object* v___x_4602_, lean_object* v_pre_4603_, lean_object* v_post_4604_, uint8_t v_usedLetOnly_4605_, uint8_t v_skipConstInApp_4606_, uint8_t v_skipInstances_4607_, lean_object* v___x_4608_, lean_object* v_inst_4609_, lean_object* v_R_4610_, lean_object* v_a_4611_, lean_object* v_b_4612_, lean_object* v_c_4613_, lean_object* v___y_4614_, lean_object* v___y_4615_, lean_object* v___y_4616_, lean_object* v___y_4617_, lean_object* v___y_4618_){
_start:
{
lean_object* v___x_4620_; 
v___x_4620_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg(v_upperBound_4601_, v___x_4602_, v_pre_4603_, v_post_4604_, v_usedLetOnly_4605_, v_skipConstInApp_4606_, v_skipInstances_4607_, v_a_4611_, v_b_4612_, v___y_4614_, v___y_4615_, v___y_4616_, v___y_4617_, v___y_4618_);
return v___x_4620_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___boxed(lean_object** _args){
lean_object* v_upperBound_4621_ = _args[0];
lean_object* v___x_4622_ = _args[1];
lean_object* v_pre_4623_ = _args[2];
lean_object* v_post_4624_ = _args[3];
lean_object* v_usedLetOnly_4625_ = _args[4];
lean_object* v_skipConstInApp_4626_ = _args[5];
lean_object* v_skipInstances_4627_ = _args[6];
lean_object* v___x_4628_ = _args[7];
lean_object* v_inst_4629_ = _args[8];
lean_object* v_R_4630_ = _args[9];
lean_object* v_a_4631_ = _args[10];
lean_object* v_b_4632_ = _args[11];
lean_object* v_c_4633_ = _args[12];
lean_object* v___y_4634_ = _args[13];
lean_object* v___y_4635_ = _args[14];
lean_object* v___y_4636_ = _args[15];
lean_object* v___y_4637_ = _args[16];
lean_object* v___y_4638_ = _args[17];
lean_object* v___y_4639_ = _args[18];
_start:
{
uint8_t v_usedLetOnly_boxed_4640_; uint8_t v_skipConstInApp_boxed_4641_; uint8_t v_skipInstances_boxed_4642_; lean_object* v_res_4643_; 
v_usedLetOnly_boxed_4640_ = lean_unbox(v_usedLetOnly_4625_);
v_skipConstInApp_boxed_4641_ = lean_unbox(v_skipConstInApp_4626_);
v_skipInstances_boxed_4642_ = lean_unbox(v_skipInstances_4627_);
v_res_4643_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4(v_upperBound_4621_, v___x_4622_, v_pre_4623_, v_post_4624_, v_usedLetOnly_boxed_4640_, v_skipConstInApp_boxed_4641_, v_skipInstances_boxed_4642_, v___x_4628_, v_inst_4629_, v_R_4630_, v_a_4631_, v_b_4632_, v_c_4633_, v___y_4634_, v___y_4635_, v___y_4636_, v___y_4637_, v___y_4638_);
lean_dec(v___y_4638_);
lean_dec_ref(v___y_4637_);
lean_dec(v___y_4636_);
lean_dec_ref(v___y_4635_);
lean_dec(v___y_4634_);
lean_dec(v___x_4628_);
lean_dec_ref(v___x_4622_);
lean_dec(v_upperBound_4621_);
return v_res_4643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6(lean_object* v_00_u03b1_4644_, lean_object* v_name_4645_, uint8_t v_bi_4646_, lean_object* v_type_4647_, lean_object* v_k_4648_, uint8_t v_kind_4649_, lean_object* v___y_4650_, lean_object* v___y_4651_, lean_object* v___y_4652_, lean_object* v___y_4653_, lean_object* v___y_4654_){
_start:
{
lean_object* v___x_4656_; 
v___x_4656_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_name_4645_, v_bi_4646_, v_type_4647_, v_k_4648_, v_kind_4649_, v___y_4650_, v___y_4651_, v___y_4652_, v___y_4653_, v___y_4654_);
return v___x_4656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___boxed(lean_object* v_00_u03b1_4657_, lean_object* v_name_4658_, lean_object* v_bi_4659_, lean_object* v_type_4660_, lean_object* v_k_4661_, lean_object* v_kind_4662_, lean_object* v___y_4663_, lean_object* v___y_4664_, lean_object* v___y_4665_, lean_object* v___y_4666_, lean_object* v___y_4667_, lean_object* v___y_4668_){
_start:
{
uint8_t v_bi_boxed_4669_; uint8_t v_kind_boxed_4670_; lean_object* v_res_4671_; 
v_bi_boxed_4669_ = lean_unbox(v_bi_4659_);
v_kind_boxed_4670_ = lean_unbox(v_kind_4662_);
v_res_4671_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6(v_00_u03b1_4657_, v_name_4658_, v_bi_boxed_4669_, v_type_4660_, v_k_4661_, v_kind_boxed_4670_, v___y_4663_, v___y_4664_, v___y_4665_, v___y_4666_, v___y_4667_);
lean_dec(v___y_4667_);
lean_dec_ref(v___y_4666_);
lean_dec(v___y_4665_);
lean_dec_ref(v___y_4664_);
lean_dec(v___y_4663_);
return v_res_4671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9(lean_object* v_00_u03b1_4672_, lean_object* v_name_4673_, lean_object* v_type_4674_, lean_object* v_val_4675_, lean_object* v_k_4676_, uint8_t v_nondep_4677_, uint8_t v_kind_4678_, lean_object* v___y_4679_, lean_object* v___y_4680_, lean_object* v___y_4681_, lean_object* v___y_4682_, lean_object* v___y_4683_){
_start:
{
lean_object* v___x_4685_; 
v___x_4685_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg(v_name_4673_, v_type_4674_, v_val_4675_, v_k_4676_, v_nondep_4677_, v_kind_4678_, v___y_4679_, v___y_4680_, v___y_4681_, v___y_4682_, v___y_4683_);
return v___x_4685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___boxed(lean_object* v_00_u03b1_4686_, lean_object* v_name_4687_, lean_object* v_type_4688_, lean_object* v_val_4689_, lean_object* v_k_4690_, lean_object* v_nondep_4691_, lean_object* v_kind_4692_, lean_object* v___y_4693_, lean_object* v___y_4694_, lean_object* v___y_4695_, lean_object* v___y_4696_, lean_object* v___y_4697_, lean_object* v___y_4698_){
_start:
{
uint8_t v_nondep_boxed_4699_; uint8_t v_kind_boxed_4700_; lean_object* v_res_4701_; 
v_nondep_boxed_4699_ = lean_unbox(v_nondep_4691_);
v_kind_boxed_4700_ = lean_unbox(v_kind_4692_);
v_res_4701_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9(v_00_u03b1_4686_, v_name_4687_, v_type_4688_, v_val_4689_, v_k_4690_, v_nondep_boxed_4699_, v_kind_boxed_4700_, v___y_4693_, v___y_4694_, v___y_4695_, v___y_4696_, v___y_4697_);
lean_dec(v___y_4697_);
lean_dec_ref(v___y_4696_);
lean_dec(v___y_4695_);
lean_dec_ref(v___y_4694_);
lean_dec(v___y_4693_);
return v_res_4701_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12(lean_object* v_00_u03b1_4702_, lean_object* v_ref_4703_, lean_object* v___y_4704_, lean_object* v___y_4705_, lean_object* v___y_4706_, lean_object* v___y_4707_){
_start:
{
lean_object* v___x_4709_; 
v___x_4709_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg(v_ref_4703_);
return v___x_4709_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___boxed(lean_object* v_00_u03b1_4710_, lean_object* v_ref_4711_, lean_object* v___y_4712_, lean_object* v___y_4713_, lean_object* v___y_4714_, lean_object* v___y_4715_, lean_object* v___y_4716_){
_start:
{
lean_object* v_res_4717_; 
v_res_4717_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12(v_00_u03b1_4710_, v_ref_4711_, v___y_4712_, v___y_4713_, v___y_4714_, v___y_4715_);
lean_dec(v___y_4715_);
lean_dec_ref(v___y_4714_);
lean_dec(v___y_4713_);
lean_dec_ref(v___y_4712_);
return v_res_4717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9(lean_object* v_00_u03b1_4718_, lean_object* v_x_4719_, lean_object* v___y_4720_, lean_object* v___y_4721_, lean_object* v___y_4722_, lean_object* v___y_4723_, lean_object* v___y_4724_){
_start:
{
lean_object* v___x_4726_; 
v___x_4726_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg(v_x_4719_, v___y_4720_, v___y_4721_, v___y_4722_, v___y_4723_, v___y_4724_);
return v___x_4726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___boxed(lean_object* v_00_u03b1_4727_, lean_object* v_x_4728_, lean_object* v___y_4729_, lean_object* v___y_4730_, lean_object* v___y_4731_, lean_object* v___y_4732_, lean_object* v___y_4733_, lean_object* v___y_4734_){
_start:
{
lean_object* v_res_4735_; 
v_res_4735_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9(v_00_u03b1_4727_, v_x_4728_, v___y_4729_, v___y_4730_, v___y_4731_, v___y_4732_, v___y_4733_);
lean_dec(v___y_4733_);
lean_dec_ref(v___y_4732_);
lean_dec(v___y_4731_);
lean_dec_ref(v___y_4730_);
lean_dec(v___y_4729_);
return v_res_4735_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0_spec__0(lean_object* v_a_4736_, lean_object* v_as_4737_, size_t v_i_4738_, size_t v_stop_4739_){
_start:
{
uint8_t v___x_4740_; 
v___x_4740_ = lean_usize_dec_eq(v_i_4738_, v_stop_4739_);
if (v___x_4740_ == 0)
{
lean_object* v___x_4741_; uint8_t v___x_4742_; 
v___x_4741_ = lean_array_uget_borrowed(v_as_4737_, v_i_4738_);
v___x_4742_ = l_Lean_instBEqFVarId_beq(v_a_4736_, v___x_4741_);
if (v___x_4742_ == 0)
{
size_t v___x_4743_; size_t v___x_4744_; 
v___x_4743_ = ((size_t)1ULL);
v___x_4744_ = lean_usize_add(v_i_4738_, v___x_4743_);
v_i_4738_ = v___x_4744_;
goto _start;
}
else
{
return v___x_4742_;
}
}
else
{
uint8_t v___x_4746_; 
v___x_4746_ = 0;
return v___x_4746_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0_spec__0___boxed(lean_object* v_a_4747_, lean_object* v_as_4748_, lean_object* v_i_4749_, lean_object* v_stop_4750_){
_start:
{
size_t v_i_boxed_4751_; size_t v_stop_boxed_4752_; uint8_t v_res_4753_; lean_object* v_r_4754_; 
v_i_boxed_4751_ = lean_unbox_usize(v_i_4749_);
lean_dec(v_i_4749_);
v_stop_boxed_4752_ = lean_unbox_usize(v_stop_4750_);
lean_dec(v_stop_4750_);
v_res_4753_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0_spec__0(v_a_4747_, v_as_4748_, v_i_boxed_4751_, v_stop_boxed_4752_);
lean_dec_ref(v_as_4748_);
lean_dec(v_a_4747_);
v_r_4754_ = lean_box(v_res_4753_);
return v_r_4754_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0(lean_object* v_as_4755_, lean_object* v_a_4756_){
_start:
{
lean_object* v___x_4757_; lean_object* v___x_4758_; uint8_t v___x_4759_; 
v___x_4757_ = lean_unsigned_to_nat(0u);
v___x_4758_ = lean_array_get_size(v_as_4755_);
v___x_4759_ = lean_nat_dec_lt(v___x_4757_, v___x_4758_);
if (v___x_4759_ == 0)
{
return v___x_4759_;
}
else
{
if (v___x_4759_ == 0)
{
return v___x_4759_;
}
else
{
size_t v___x_4760_; size_t v___x_4761_; uint8_t v___x_4762_; 
v___x_4760_ = ((size_t)0ULL);
v___x_4761_ = lean_usize_of_nat(v___x_4758_);
v___x_4762_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0_spec__0(v_a_4756_, v_as_4755_, v___x_4760_, v___x_4761_);
return v___x_4762_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0___boxed(lean_object* v_as_4763_, lean_object* v_a_4764_){
_start:
{
uint8_t v_res_4765_; lean_object* v_r_4766_; 
v_res_4765_ = l_Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0(v_as_4763_, v_a_4764_);
lean_dec(v_a_4764_);
lean_dec_ref(v_as_4763_);
v_r_4766_ = lean_box(v_res_4765_);
return v_r_4766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaFVars___lam__1(lean_object* v_fvars_4767_, lean_object* v_e_4768_, lean_object* v___y_4769_, lean_object* v___y_4770_, lean_object* v___y_4771_, lean_object* v___y_4772_){
_start:
{
lean_object* v___x_4777_; 
v___x_4777_ = l_Lean_Expr_getAppFn(v_e_4768_);
if (lean_obj_tag(v___x_4777_) == 1)
{
lean_object* v_fvarId_4778_; uint8_t v___x_4779_; 
v_fvarId_4778_ = lean_ctor_get(v___x_4777_, 0);
lean_inc(v_fvarId_4778_);
lean_dec_ref_known(v___x_4777_, 1);
v___x_4779_ = l_Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0(v_fvars_4767_, v_fvarId_4778_);
if (v___x_4779_ == 0)
{
lean_dec(v_fvarId_4778_);
lean_dec_ref(v_e_4768_);
goto v___jp_4774_;
}
else
{
uint8_t v___x_4780_; lean_object* v___x_4781_; 
v___x_4780_ = 0;
v___x_4781_ = l_Lean_FVarId_getValue_x3f___redArg(v_fvarId_4778_, v___x_4780_, v___y_4769_, v___y_4771_, v___y_4772_);
if (lean_obj_tag(v___x_4781_) == 0)
{
lean_object* v_a_4782_; 
v_a_4782_ = lean_ctor_get(v___x_4781_, 0);
lean_inc(v_a_4782_);
lean_dec_ref_known(v___x_4781_, 1);
if (lean_obj_tag(v_a_4782_) == 1)
{
lean_object* v_val_4783_; lean_object* v___x_4785_; uint8_t v_isShared_4786_; uint8_t v_isSharedCheck_4806_; 
v_val_4783_ = lean_ctor_get(v_a_4782_, 0);
v_isSharedCheck_4806_ = !lean_is_exclusive(v_a_4782_);
if (v_isSharedCheck_4806_ == 0)
{
v___x_4785_ = v_a_4782_;
v_isShared_4786_ = v_isSharedCheck_4806_;
goto v_resetjp_4784_;
}
else
{
lean_inc(v_val_4783_);
lean_dec(v_a_4782_);
v___x_4785_ = lean_box(0);
v_isShared_4786_ = v_isSharedCheck_4806_;
goto v_resetjp_4784_;
}
v_resetjp_4784_:
{
lean_object* v___x_4787_; lean_object* v_a_4788_; lean_object* v___x_4790_; uint8_t v_isShared_4791_; uint8_t v_isSharedCheck_4805_; 
v___x_4787_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(v_val_4783_, v___y_4770_);
v_a_4788_ = lean_ctor_get(v___x_4787_, 0);
v_isSharedCheck_4805_ = !lean_is_exclusive(v___x_4787_);
if (v_isSharedCheck_4805_ == 0)
{
v___x_4790_ = v___x_4787_;
v_isShared_4791_ = v_isSharedCheck_4805_;
goto v_resetjp_4789_;
}
else
{
lean_inc(v_a_4788_);
lean_dec(v___x_4787_);
v___x_4790_ = lean_box(0);
v_isShared_4791_ = v_isSharedCheck_4805_;
goto v_resetjp_4789_;
}
v_resetjp_4789_:
{
lean_object* v_dummy_4792_; lean_object* v_nargs_4793_; lean_object* v___x_4794_; lean_object* v___x_4795_; lean_object* v___x_4796_; lean_object* v___x_4797_; lean_object* v___x_4798_; lean_object* v___x_4800_; 
v_dummy_4792_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_4793_ = l_Lean_Expr_getAppNumArgs(v_e_4768_);
lean_inc(v_nargs_4793_);
v___x_4794_ = lean_mk_array(v_nargs_4793_, v_dummy_4792_);
v___x_4795_ = lean_unsigned_to_nat(1u);
v___x_4796_ = lean_nat_sub(v_nargs_4793_, v___x_4795_);
lean_dec(v_nargs_4793_);
v___x_4797_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_4768_, v___x_4794_, v___x_4796_);
v___x_4798_ = l_Lean_Expr_beta(v_a_4788_, v___x_4797_);
if (v_isShared_4786_ == 0)
{
lean_ctor_set(v___x_4785_, 0, v___x_4798_);
v___x_4800_ = v___x_4785_;
goto v_reusejp_4799_;
}
else
{
lean_object* v_reuseFailAlloc_4804_; 
v_reuseFailAlloc_4804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4804_, 0, v___x_4798_);
v___x_4800_ = v_reuseFailAlloc_4804_;
goto v_reusejp_4799_;
}
v_reusejp_4799_:
{
lean_object* v___x_4802_; 
if (v_isShared_4791_ == 0)
{
lean_ctor_set(v___x_4790_, 0, v___x_4800_);
v___x_4802_ = v___x_4790_;
goto v_reusejp_4801_;
}
else
{
lean_object* v_reuseFailAlloc_4803_; 
v_reuseFailAlloc_4803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4803_, 0, v___x_4800_);
v___x_4802_ = v_reuseFailAlloc_4803_;
goto v_reusejp_4801_;
}
v_reusejp_4801_:
{
return v___x_4802_;
}
}
}
}
}
else
{
lean_dec(v_a_4782_);
lean_dec_ref(v_e_4768_);
goto v___jp_4774_;
}
}
else
{
lean_object* v_a_4807_; lean_object* v___x_4809_; uint8_t v_isShared_4810_; uint8_t v_isSharedCheck_4814_; 
lean_dec_ref(v_e_4768_);
v_a_4807_ = lean_ctor_get(v___x_4781_, 0);
v_isSharedCheck_4814_ = !lean_is_exclusive(v___x_4781_);
if (v_isSharedCheck_4814_ == 0)
{
v___x_4809_ = v___x_4781_;
v_isShared_4810_ = v_isSharedCheck_4814_;
goto v_resetjp_4808_;
}
else
{
lean_inc(v_a_4807_);
lean_dec(v___x_4781_);
v___x_4809_ = lean_box(0);
v_isShared_4810_ = v_isSharedCheck_4814_;
goto v_resetjp_4808_;
}
v_resetjp_4808_:
{
lean_object* v___x_4812_; 
if (v_isShared_4810_ == 0)
{
v___x_4812_ = v___x_4809_;
goto v_reusejp_4811_;
}
else
{
lean_object* v_reuseFailAlloc_4813_; 
v_reuseFailAlloc_4813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4813_, 0, v_a_4807_);
v___x_4812_ = v_reuseFailAlloc_4813_;
goto v_reusejp_4811_;
}
v_reusejp_4811_:
{
return v___x_4812_;
}
}
}
}
}
else
{
lean_object* v___x_4815_; lean_object* v___x_4816_; 
lean_dec_ref(v___x_4777_);
lean_dec_ref(v_e_4768_);
v___x_4815_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_4816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4816_, 0, v___x_4815_);
return v___x_4816_;
}
v___jp_4774_:
{
lean_object* v___x_4775_; lean_object* v___x_4776_; 
v___x_4775_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_4776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4776_, 0, v___x_4775_);
return v___x_4776_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaFVars___lam__1___boxed(lean_object* v_fvars_4817_, lean_object* v_e_4818_, lean_object* v___y_4819_, lean_object* v___y_4820_, lean_object* v___y_4821_, lean_object* v___y_4822_, lean_object* v___y_4823_){
_start:
{
lean_object* v_res_4824_; 
v_res_4824_ = l_Lean_Meta_zetaDeltaFVars___lam__1(v_fvars_4817_, v_e_4818_, v___y_4819_, v___y_4820_, v___y_4821_, v___y_4822_);
lean_dec(v___y_4822_);
lean_dec_ref(v___y_4821_);
lean_dec(v___y_4820_);
lean_dec_ref(v___y_4819_);
lean_dec_ref(v_fvars_4817_);
return v_res_4824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaFVars(lean_object* v_e_4825_, lean_object* v_fvars_4826_, lean_object* v_a_4827_, lean_object* v_a_4828_, lean_object* v_a_4829_, lean_object* v_a_4830_){
_start:
{
lean_object* v___f_4832_; lean_object* v_pre_4833_; uint8_t v___x_4834_; lean_object* v___x_4835_; 
v___f_4832_ = ((lean_object*)(l_Lean_Meta_zetaReduce___closed__0));
v_pre_4833_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaDeltaFVars___lam__1___boxed), 7, 1);
lean_closure_set(v_pre_4833_, 0, v_fvars_4826_);
v___x_4834_ = 0;
v___x_4835_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(v_e_4825_, v_pre_4833_, v___f_4832_, v___x_4834_, v___x_4834_, v_a_4827_, v_a_4828_, v_a_4829_, v_a_4830_);
return v___x_4835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaFVars___boxed(lean_object* v_e_4836_, lean_object* v_fvars_4837_, lean_object* v_a_4838_, lean_object* v_a_4839_, lean_object* v_a_4840_, lean_object* v_a_4841_, lean_object* v_a_4842_){
_start:
{
lean_object* v_res_4843_; 
v_res_4843_ = l_Lean_Meta_zetaDeltaFVars(v_e_4836_, v_fvars_4837_, v_a_4838_, v_a_4839_, v_a_4840_, v_a_4841_);
lean_dec(v_a_4841_);
lean_dec_ref(v_a_4840_);
lean_dec(v_a_4839_);
lean_dec_ref(v_a_4838_);
return v_res_4843_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_4844_; 
v___x_4844_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_4844_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_4845_; lean_object* v___x_4846_; 
v___x_4845_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__0, &l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__0);
v___x_4846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4846_, 0, v___x_4845_);
return v___x_4846_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_4847_; lean_object* v___x_4848_; 
v___x_4847_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__1, &l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__1);
v___x_4848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4848_, 0, v___x_4847_);
lean_ctor_set(v___x_4848_, 1, v___x_4847_);
return v___x_4848_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(lean_object* v_env_4849_, lean_object* v___y_4850_){
_start:
{
lean_object* v___x_4852_; lean_object* v_nextMacroScope_4853_; lean_object* v_ngen_4854_; lean_object* v_auxDeclNGen_4855_; lean_object* v_traceState_4856_; lean_object* v_recordedDeps_4857_; lean_object* v_messages_4858_; lean_object* v_infoState_4859_; lean_object* v_snapshotTasks_4860_; lean_object* v___x_4862_; uint8_t v_isShared_4863_; uint8_t v_isSharedCheck_4871_; 
v___x_4852_ = lean_st_ref_take(v___y_4850_);
v_nextMacroScope_4853_ = lean_ctor_get(v___x_4852_, 1);
v_ngen_4854_ = lean_ctor_get(v___x_4852_, 2);
v_auxDeclNGen_4855_ = lean_ctor_get(v___x_4852_, 3);
v_traceState_4856_ = lean_ctor_get(v___x_4852_, 4);
v_recordedDeps_4857_ = lean_ctor_get(v___x_4852_, 6);
v_messages_4858_ = lean_ctor_get(v___x_4852_, 7);
v_infoState_4859_ = lean_ctor_get(v___x_4852_, 8);
v_snapshotTasks_4860_ = lean_ctor_get(v___x_4852_, 9);
v_isSharedCheck_4871_ = !lean_is_exclusive(v___x_4852_);
if (v_isSharedCheck_4871_ == 0)
{
lean_object* v_unused_4872_; lean_object* v_unused_4873_; 
v_unused_4872_ = lean_ctor_get(v___x_4852_, 5);
lean_dec(v_unused_4872_);
v_unused_4873_ = lean_ctor_get(v___x_4852_, 0);
lean_dec(v_unused_4873_);
v___x_4862_ = v___x_4852_;
v_isShared_4863_ = v_isSharedCheck_4871_;
goto v_resetjp_4861_;
}
else
{
lean_inc(v_snapshotTasks_4860_);
lean_inc(v_infoState_4859_);
lean_inc(v_messages_4858_);
lean_inc(v_recordedDeps_4857_);
lean_inc(v_traceState_4856_);
lean_inc(v_auxDeclNGen_4855_);
lean_inc(v_ngen_4854_);
lean_inc(v_nextMacroScope_4853_);
lean_dec(v___x_4852_);
v___x_4862_ = lean_box(0);
v_isShared_4863_ = v_isSharedCheck_4871_;
goto v_resetjp_4861_;
}
v_resetjp_4861_:
{
lean_object* v___x_4864_; lean_object* v___x_4865_; lean_object* v___x_4867_; 
v___x_4864_ = lean_box(0);
v___x_4865_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2, &l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2);
if (v_isShared_4863_ == 0)
{
lean_ctor_set(v___x_4862_, 5, v___x_4865_);
lean_ctor_set(v___x_4862_, 0, v_env_4849_);
v___x_4867_ = v___x_4862_;
goto v_reusejp_4866_;
}
else
{
lean_object* v_reuseFailAlloc_4870_; 
v_reuseFailAlloc_4870_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4870_, 0, v_env_4849_);
lean_ctor_set(v_reuseFailAlloc_4870_, 1, v_nextMacroScope_4853_);
lean_ctor_set(v_reuseFailAlloc_4870_, 2, v_ngen_4854_);
lean_ctor_set(v_reuseFailAlloc_4870_, 3, v_auxDeclNGen_4855_);
lean_ctor_set(v_reuseFailAlloc_4870_, 4, v_traceState_4856_);
lean_ctor_set(v_reuseFailAlloc_4870_, 5, v___x_4865_);
lean_ctor_set(v_reuseFailAlloc_4870_, 6, v_recordedDeps_4857_);
lean_ctor_set(v_reuseFailAlloc_4870_, 7, v_messages_4858_);
lean_ctor_set(v_reuseFailAlloc_4870_, 8, v_infoState_4859_);
lean_ctor_set(v_reuseFailAlloc_4870_, 9, v_snapshotTasks_4860_);
v___x_4867_ = v_reuseFailAlloc_4870_;
goto v_reusejp_4866_;
}
v_reusejp_4866_:
{
lean_object* v___x_4868_; lean_object* v___x_4869_; 
v___x_4868_ = lean_st_ref_put(v___y_4850_, v___x_4867_);
v___x_4869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4869_, 0, v___x_4864_);
return v___x_4869_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___boxed(lean_object* v_env_4874_, lean_object* v___y_4875_, lean_object* v___y_4876_){
_start:
{
lean_object* v_res_4877_; 
v_res_4877_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_4874_, v___y_4875_);
lean_dec(v___y_4875_);
return v_res_4877_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0(lean_object* v_env_4878_, lean_object* v___y_4879_, lean_object* v___y_4880_){
_start:
{
lean_object* v___x_4882_; 
v___x_4882_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_4878_, v___y_4880_);
return v___x_4882_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___boxed(lean_object* v_env_4883_, lean_object* v___y_4884_, lean_object* v___y_4885_, lean_object* v___y_4886_){
_start:
{
lean_object* v_res_4887_; 
v_res_4887_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0(v_env_4883_, v___y_4884_, v___y_4885_);
lean_dec(v___y_4885_);
lean_dec_ref(v___y_4884_);
return v_res_4887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___lam__1(lean_object* v_env_4888_, lean_object* v___x_4889_, uint8_t v___x_4890_, lean_object* v_e_4891_, lean_object* v___y_4892_, lean_object* v___y_4893_){
_start:
{
if (lean_obj_tag(v_e_4891_) == 4)
{
lean_object* v_declName_4895_; lean_object* v_us_4896_; uint8_t v___x_4897_; uint8_t v___x_4898_; 
v_declName_4895_ = lean_ctor_get(v_e_4891_, 0);
v_us_4896_ = lean_ctor_get(v_e_4891_, 1);
v___x_4897_ = 1;
lean_inc(v_declName_4895_);
v___x_4898_ = l_Lean_Environment_contains(v_env_4888_, v_declName_4895_, v___x_4897_);
if (v___x_4898_ == 0)
{
lean_object* v___x_4899_; 
lean_inc(v_declName_4895_);
v___x_4899_ = l_Lean_Environment_find_x3f(v___x_4889_, v_declName_4895_, v___x_4890_);
if (lean_obj_tag(v___x_4899_) == 1)
{
lean_object* v_val_4900_; lean_object* v___x_4902_; uint8_t v_isShared_4903_; uint8_t v_isSharedCheck_4929_; 
v_val_4900_ = lean_ctor_get(v___x_4899_, 0);
v_isSharedCheck_4929_ = !lean_is_exclusive(v___x_4899_);
if (v_isSharedCheck_4929_ == 0)
{
v___x_4902_ = v___x_4899_;
v_isShared_4903_ = v_isSharedCheck_4929_;
goto v_resetjp_4901_;
}
else
{
lean_inc(v_val_4900_);
lean_dec(v___x_4899_);
v___x_4902_ = lean_box(0);
v_isShared_4903_ = v_isSharedCheck_4929_;
goto v_resetjp_4901_;
}
v_resetjp_4901_:
{
uint8_t v___x_4904_; 
v___x_4904_ = l_Lean_ConstantInfo_hasValue(v_val_4900_, v___x_4897_);
if (v___x_4904_ == 0)
{
lean_object* v___x_4906_; 
lean_dec(v_val_4900_);
if (v_isShared_4903_ == 0)
{
lean_ctor_set_tag(v___x_4902_, 0);
lean_ctor_set(v___x_4902_, 0, v_e_4891_);
v___x_4906_ = v___x_4902_;
goto v_reusejp_4905_;
}
else
{
lean_object* v_reuseFailAlloc_4908_; 
v_reuseFailAlloc_4908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4908_, 0, v_e_4891_);
v___x_4906_ = v_reuseFailAlloc_4908_;
goto v_reusejp_4905_;
}
v_reusejp_4905_:
{
lean_object* v___x_4907_; 
v___x_4907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4907_, 0, v___x_4906_);
return v___x_4907_;
}
}
else
{
lean_object* v___x_4909_; 
lean_inc(v_us_4896_);
lean_dec_ref_known(v_e_4891_, 2);
v___x_4909_ = l_Lean_Core_instantiateValueLevelParams(v_val_4900_, v_us_4896_, v___x_4897_, v___y_4892_, v___y_4893_);
lean_dec(v_val_4900_);
if (lean_obj_tag(v___x_4909_) == 0)
{
lean_object* v_a_4910_; lean_object* v___x_4912_; uint8_t v_isShared_4913_; uint8_t v_isSharedCheck_4920_; 
v_a_4910_ = lean_ctor_get(v___x_4909_, 0);
v_isSharedCheck_4920_ = !lean_is_exclusive(v___x_4909_);
if (v_isSharedCheck_4920_ == 0)
{
v___x_4912_ = v___x_4909_;
v_isShared_4913_ = v_isSharedCheck_4920_;
goto v_resetjp_4911_;
}
else
{
lean_inc(v_a_4910_);
lean_dec(v___x_4909_);
v___x_4912_ = lean_box(0);
v_isShared_4913_ = v_isSharedCheck_4920_;
goto v_resetjp_4911_;
}
v_resetjp_4911_:
{
lean_object* v___x_4915_; 
if (v_isShared_4903_ == 0)
{
lean_ctor_set(v___x_4902_, 0, v_a_4910_);
v___x_4915_ = v___x_4902_;
goto v_reusejp_4914_;
}
else
{
lean_object* v_reuseFailAlloc_4919_; 
v_reuseFailAlloc_4919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4919_, 0, v_a_4910_);
v___x_4915_ = v_reuseFailAlloc_4919_;
goto v_reusejp_4914_;
}
v_reusejp_4914_:
{
lean_object* v___x_4917_; 
if (v_isShared_4913_ == 0)
{
lean_ctor_set(v___x_4912_, 0, v___x_4915_);
v___x_4917_ = v___x_4912_;
goto v_reusejp_4916_;
}
else
{
lean_object* v_reuseFailAlloc_4918_; 
v_reuseFailAlloc_4918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4918_, 0, v___x_4915_);
v___x_4917_ = v_reuseFailAlloc_4918_;
goto v_reusejp_4916_;
}
v_reusejp_4916_:
{
return v___x_4917_;
}
}
}
}
else
{
lean_object* v_a_4921_; lean_object* v___x_4923_; uint8_t v_isShared_4924_; uint8_t v_isSharedCheck_4928_; 
lean_del_object(v___x_4902_);
v_a_4921_ = lean_ctor_get(v___x_4909_, 0);
v_isSharedCheck_4928_ = !lean_is_exclusive(v___x_4909_);
if (v_isSharedCheck_4928_ == 0)
{
v___x_4923_ = v___x_4909_;
v_isShared_4924_ = v_isSharedCheck_4928_;
goto v_resetjp_4922_;
}
else
{
lean_inc(v_a_4921_);
lean_dec(v___x_4909_);
v___x_4923_ = lean_box(0);
v_isShared_4924_ = v_isSharedCheck_4928_;
goto v_resetjp_4922_;
}
v_resetjp_4922_:
{
lean_object* v___x_4926_; 
if (v_isShared_4924_ == 0)
{
v___x_4926_ = v___x_4923_;
goto v_reusejp_4925_;
}
else
{
lean_object* v_reuseFailAlloc_4927_; 
v_reuseFailAlloc_4927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4927_, 0, v_a_4921_);
v___x_4926_ = v_reuseFailAlloc_4927_;
goto v_reusejp_4925_;
}
v_reusejp_4925_:
{
return v___x_4926_;
}
}
}
}
}
}
else
{
lean_object* v___x_4930_; lean_object* v___x_4931_; 
lean_dec(v___x_4899_);
v___x_4930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4930_, 0, v_e_4891_);
v___x_4931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4931_, 0, v___x_4930_);
return v___x_4931_;
}
}
else
{
lean_object* v___x_4932_; lean_object* v___x_4933_; 
lean_dec_ref(v___x_4889_);
v___x_4932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4932_, 0, v_e_4891_);
v___x_4933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4933_, 0, v___x_4932_);
return v___x_4933_;
}
}
else
{
lean_object* v___x_4934_; lean_object* v___x_4935_; 
lean_dec_ref(v_e_4891_);
lean_dec_ref(v___x_4889_);
lean_dec_ref(v_env_4888_);
v___x_4934_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_4935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4935_, 0, v___x_4934_);
return v___x_4935_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___lam__1___boxed(lean_object* v_env_4936_, lean_object* v___x_4937_, lean_object* v___x_4938_, lean_object* v_e_4939_, lean_object* v___y_4940_, lean_object* v___y_4941_, lean_object* v___y_4942_){
_start:
{
uint8_t v___x_1999__boxed_4943_; lean_object* v_res_4944_; 
v___x_1999__boxed_4943_ = lean_unbox(v___x_4938_);
v_res_4944_ = l_Lean_Meta_unfoldDeclsFrom___lam__1(v_env_4936_, v___x_4937_, v___x_1999__boxed_4943_, v_e_4939_, v___y_4940_, v___y_4941_);
lean_dec(v___y_4941_);
lean_dec_ref(v___y_4940_);
return v_res_4944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___lam__0(lean_object* v_biggerEnv_4945_, lean_object* v_e_4946_, lean_object* v___f_4947_, lean_object* v___y_4948_, lean_object* v___y_4949_){
_start:
{
lean_object* v___x_4951_; lean_object* v_env_4952_; uint8_t v___x_4953_; lean_object* v___x_4954_; lean_object* v___x_4955_; lean_object* v___f_4956_; lean_object* v___x_4957_; lean_object* v___x_4958_; 
v___x_4951_ = lean_st_ref_get(v___y_4949_);
v_env_4952_ = lean_ctor_get(v___x_4951_, 0);
lean_inc_ref(v_env_4952_);
lean_dec(v___x_4951_);
v___x_4953_ = 0;
v___x_4954_ = l_Lean_Environment_setExporting(v_biggerEnv_4945_, v___x_4953_);
v___x_4955_ = lean_box(v___x_4953_);
lean_inc_ref(v___x_4954_);
v___f_4956_ = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDeclsFrom___lam__1___boxed), 7, 3);
lean_closure_set(v___f_4956_, 0, v_env_4952_);
lean_closure_set(v___f_4956_, 1, v___x_4954_);
lean_closure_set(v___f_4956_, 2, v___x_4955_);
v___x_4957_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v___x_4954_, v___y_4949_);
lean_dec_ref(v___x_4957_);
v___x_4958_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_4946_, v___f_4956_, v___f_4947_, v___y_4948_, v___y_4949_);
return v___x_4958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___lam__0___boxed(lean_object* v_biggerEnv_4959_, lean_object* v_e_4960_, lean_object* v___f_4961_, lean_object* v___y_4962_, lean_object* v___y_4963_, lean_object* v___y_4964_){
_start:
{
lean_object* v_res_4965_; 
v_res_4965_ = l_Lean_Meta_unfoldDeclsFrom___lam__0(v_biggerEnv_4959_, v_e_4960_, v___f_4961_, v___y_4962_, v___y_4963_);
lean_dec(v___y_4963_);
lean_dec_ref(v___y_4962_);
return v_res_4965_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg(lean_object* v_env_4966_, lean_object* v_x_4967_, lean_object* v___y_4968_, lean_object* v___y_4969_){
_start:
{
lean_object* v___x_4971_; lean_object* v_env_4972_; lean_object* v_a_4974_; lean_object* v___x_4984_; lean_object* v___x_4985_; 
v___x_4971_ = lean_st_ref_get(v___y_4969_);
v_env_4972_ = lean_ctor_get(v___x_4971_, 0);
lean_inc_ref(v_env_4972_);
lean_dec(v___x_4971_);
v___x_4984_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_4966_, v___y_4969_);
lean_dec_ref(v___x_4984_);
lean_inc(v___y_4969_);
lean_inc_ref(v___y_4968_);
v___x_4985_ = lean_apply_3(v_x_4967_, v___y_4968_, v___y_4969_, lean_box(0));
if (lean_obj_tag(v___x_4985_) == 0)
{
lean_object* v_a_4986_; lean_object* v___x_4987_; lean_object* v___x_4989_; uint8_t v_isShared_4990_; uint8_t v_isSharedCheck_4994_; 
v_a_4986_ = lean_ctor_get(v___x_4985_, 0);
lean_inc(v_a_4986_);
lean_dec_ref_known(v___x_4985_, 1);
v___x_4987_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_4972_, v___y_4969_);
v_isSharedCheck_4994_ = !lean_is_exclusive(v___x_4987_);
if (v_isSharedCheck_4994_ == 0)
{
lean_object* v_unused_4995_; 
v_unused_4995_ = lean_ctor_get(v___x_4987_, 0);
lean_dec(v_unused_4995_);
v___x_4989_ = v___x_4987_;
v_isShared_4990_ = v_isSharedCheck_4994_;
goto v_resetjp_4988_;
}
else
{
lean_dec(v___x_4987_);
v___x_4989_ = lean_box(0);
v_isShared_4990_ = v_isSharedCheck_4994_;
goto v_resetjp_4988_;
}
v_resetjp_4988_:
{
lean_object* v___x_4992_; 
if (v_isShared_4990_ == 0)
{
lean_ctor_set(v___x_4989_, 0, v_a_4986_);
v___x_4992_ = v___x_4989_;
goto v_reusejp_4991_;
}
else
{
lean_object* v_reuseFailAlloc_4993_; 
v_reuseFailAlloc_4993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4993_, 0, v_a_4986_);
v___x_4992_ = v_reuseFailAlloc_4993_;
goto v_reusejp_4991_;
}
v_reusejp_4991_:
{
return v___x_4992_;
}
}
}
else
{
lean_object* v_a_4996_; 
v_a_4996_ = lean_ctor_get(v___x_4985_, 0);
lean_inc(v_a_4996_);
lean_dec_ref_known(v___x_4985_, 1);
v_a_4974_ = v_a_4996_;
goto v___jp_4973_;
}
v___jp_4973_:
{
lean_object* v___x_4975_; lean_object* v___x_4977_; uint8_t v_isShared_4978_; uint8_t v_isSharedCheck_4982_; 
v___x_4975_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_4972_, v___y_4969_);
v_isSharedCheck_4982_ = !lean_is_exclusive(v___x_4975_);
if (v_isSharedCheck_4982_ == 0)
{
lean_object* v_unused_4983_; 
v_unused_4983_ = lean_ctor_get(v___x_4975_, 0);
lean_dec(v_unused_4983_);
v___x_4977_ = v___x_4975_;
v_isShared_4978_ = v_isSharedCheck_4982_;
goto v_resetjp_4976_;
}
else
{
lean_dec(v___x_4975_);
v___x_4977_ = lean_box(0);
v_isShared_4978_ = v_isSharedCheck_4982_;
goto v_resetjp_4976_;
}
v_resetjp_4976_:
{
lean_object* v___x_4980_; 
if (v_isShared_4978_ == 0)
{
lean_ctor_set_tag(v___x_4977_, 1);
lean_ctor_set(v___x_4977_, 0, v_a_4974_);
v___x_4980_ = v___x_4977_;
goto v_reusejp_4979_;
}
else
{
lean_object* v_reuseFailAlloc_4981_; 
v_reuseFailAlloc_4981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4981_, 0, v_a_4974_);
v___x_4980_ = v_reuseFailAlloc_4981_;
goto v_reusejp_4979_;
}
v_reusejp_4979_:
{
return v___x_4980_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg___boxed(lean_object* v_env_4997_, lean_object* v_x_4998_, lean_object* v___y_4999_, lean_object* v___y_5000_, lean_object* v___y_5001_){
_start:
{
lean_object* v_res_5002_; 
v_res_5002_ = l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg(v_env_4997_, v_x_4998_, v___y_4999_, v___y_5000_);
lean_dec(v___y_5000_);
lean_dec_ref(v___y_4999_);
return v_res_5002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom(lean_object* v_biggerEnv_5003_, lean_object* v_e_5004_, lean_object* v_a_5005_, lean_object* v_a_5006_){
_start:
{
lean_object* v___f_5008_; lean_object* v___f_5009_; lean_object* v___x_5010_; lean_object* v_env_5011_; lean_object* v___x_5012_; lean_object* v___x_5013_; 
v___f_5008_ = ((lean_object*)(l_Lean_Core_betaReduce___closed__1));
v___f_5009_ = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDeclsFrom___lam__0___boxed), 6, 3);
lean_closure_set(v___f_5009_, 0, v_biggerEnv_5003_);
lean_closure_set(v___f_5009_, 1, v_e_5004_);
lean_closure_set(v___f_5009_, 2, v___f_5008_);
v___x_5010_ = lean_st_ref_get(v_a_5006_);
v_env_5011_ = lean_ctor_get(v___x_5010_, 0);
lean_inc_ref(v_env_5011_);
lean_dec(v___x_5010_);
v___x_5012_ = l_Lean_Environment_unlockAsync(v_env_5011_);
v___x_5013_ = l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg(v___x_5012_, v___f_5009_, v_a_5005_, v_a_5006_);
return v___x_5013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___boxed(lean_object* v_biggerEnv_5014_, lean_object* v_e_5015_, lean_object* v_a_5016_, lean_object* v_a_5017_, lean_object* v_a_5018_){
_start:
{
lean_object* v_res_5019_; 
v_res_5019_ = l_Lean_Meta_unfoldDeclsFrom(v_biggerEnv_5014_, v_e_5015_, v_a_5016_, v_a_5017_);
lean_dec(v_a_5017_);
lean_dec_ref(v_a_5016_);
return v_res_5019_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1(lean_object* v_00_u03b1_5020_, lean_object* v_env_5021_, lean_object* v_x_5022_, lean_object* v___y_5023_, lean_object* v___y_5024_){
_start:
{
lean_object* v___x_5026_; 
v___x_5026_ = l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg(v_env_5021_, v_x_5022_, v___y_5023_, v___y_5024_);
return v___x_5026_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___boxed(lean_object* v_00_u03b1_5027_, lean_object* v_env_5028_, lean_object* v_x_5029_, lean_object* v___y_5030_, lean_object* v___y_5031_, lean_object* v___y_5032_){
_start:
{
lean_object* v_res_5033_; 
v_res_5033_ = l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1(v_00_u03b1_5027_, v_env_5028_, v_x_5029_, v___y_5030_, v___y_5031_);
lean_dec(v___y_5031_);
lean_dec_ref(v___y_5030_);
return v_res_5033_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0(lean_object* v_af_5034_, lean_object* v_axs_5035_, lean_object* v_numSectionVars_5036_, lean_object* v_as_5037_, size_t v_i_5038_, size_t v_stop_5039_){
_start:
{
uint8_t v___x_5040_; 
v___x_5040_ = lean_usize_dec_eq(v_i_5038_, v_stop_5039_);
if (v___x_5040_ == 0)
{
uint8_t v___x_5041_; uint8_t v___y_5043_; lean_object* v___x_5047_; lean_object* v___x_5048_; uint8_t v___x_5049_; 
v___x_5041_ = 1;
v___x_5047_ = lean_array_uget_borrowed(v_as_5037_, v_i_5038_);
v___x_5048_ = l_Lean_Expr_constName_x21(v_af_5034_);
v___x_5049_ = lean_name_eq(v___x_5048_, v___x_5047_);
lean_dec(v___x_5048_);
if (v___x_5049_ == 0)
{
v___y_5043_ = v___x_5049_;
goto v___jp_5042_;
}
else
{
lean_object* v___x_5050_; uint8_t v___x_5051_; 
v___x_5050_ = lean_array_get_size(v_axs_5035_);
v___x_5051_ = lean_nat_dec_le(v___x_5050_, v_numSectionVars_5036_);
v___y_5043_ = v___x_5051_;
goto v___jp_5042_;
}
v___jp_5042_:
{
if (v___y_5043_ == 0)
{
size_t v___x_5044_; size_t v___x_5045_; 
v___x_5044_ = ((size_t)1ULL);
v___x_5045_ = lean_usize_add(v_i_5038_, v___x_5044_);
v_i_5038_ = v___x_5045_;
goto _start;
}
else
{
return v___x_5041_;
}
}
}
else
{
uint8_t v___x_5052_; 
v___x_5052_ = 0;
return v___x_5052_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0___boxed(lean_object* v_af_5053_, lean_object* v_axs_5054_, lean_object* v_numSectionVars_5055_, lean_object* v_as_5056_, lean_object* v_i_5057_, lean_object* v_stop_5058_){
_start:
{
size_t v_i_boxed_5059_; size_t v_stop_boxed_5060_; uint8_t v_res_5061_; lean_object* v_r_5062_; 
v_i_boxed_5059_ = lean_unbox_usize(v_i_5057_);
lean_dec(v_i_5057_);
v_stop_boxed_5060_ = lean_unbox_usize(v_stop_5058_);
lean_dec(v_stop_5058_);
v_res_5061_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0(v_af_5053_, v_axs_5054_, v_numSectionVars_5055_, v_as_5056_, v_i_boxed_5059_, v_stop_boxed_5060_);
lean_dec_ref(v_as_5056_);
lean_dec(v_numSectionVars_5055_);
lean_dec_ref(v_axs_5054_);
lean_dec_ref(v_af_5053_);
v_r_5062_ = lean_box(v_res_5061_);
return v_r_5062_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1_spec__1(lean_object* v_fnNames_5063_, lean_object* v_numSectionVars_5064_, lean_object* v_x_5065_, lean_object* v_x_5066_, lean_object* v_x_5067_){
_start:
{
if (lean_obj_tag(v_x_5065_) == 5)
{
lean_object* v_fn_5068_; lean_object* v_arg_5069_; lean_object* v___x_5070_; lean_object* v___x_5071_; lean_object* v___x_5072_; 
v_fn_5068_ = lean_ctor_get(v_x_5065_, 0);
lean_inc_ref(v_fn_5068_);
v_arg_5069_ = lean_ctor_get(v_x_5065_, 1);
lean_inc_ref(v_arg_5069_);
lean_dec_ref_known(v_x_5065_, 2);
v___x_5070_ = lean_array_set(v_x_5066_, v_x_5067_, v_arg_5069_);
v___x_5071_ = lean_unsigned_to_nat(1u);
v___x_5072_ = lean_nat_sub(v_x_5067_, v___x_5071_);
lean_dec(v_x_5067_);
v_x_5065_ = v_fn_5068_;
v_x_5066_ = v___x_5070_;
v_x_5067_ = v___x_5072_;
goto _start;
}
else
{
uint8_t v___x_5074_; 
lean_dec(v_x_5067_);
v___x_5074_ = l_Lean_Expr_isConst(v_x_5065_);
if (v___x_5074_ == 0)
{
lean_dec_ref(v_x_5066_);
lean_dec_ref(v_x_5065_);
return v___x_5074_;
}
else
{
lean_object* v___x_5075_; lean_object* v___x_5076_; uint8_t v___x_5077_; 
v___x_5075_ = lean_unsigned_to_nat(0u);
v___x_5076_ = lean_array_get_size(v_fnNames_5063_);
v___x_5077_ = lean_nat_dec_lt(v___x_5075_, v___x_5076_);
if (v___x_5077_ == 0)
{
lean_dec_ref(v_x_5066_);
lean_dec_ref(v_x_5065_);
return v___x_5077_;
}
else
{
if (v___x_5077_ == 0)
{
lean_dec_ref(v_x_5066_);
lean_dec_ref(v_x_5065_);
return v___x_5077_;
}
else
{
size_t v___x_5078_; size_t v___x_5079_; uint8_t v___x_5080_; 
v___x_5078_ = ((size_t)0ULL);
v___x_5079_ = lean_usize_of_nat(v___x_5076_);
v___x_5080_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0(v_x_5065_, v_x_5066_, v_numSectionVars_5064_, v_fnNames_5063_, v___x_5078_, v___x_5079_);
lean_dec_ref(v_x_5066_);
lean_dec_ref(v_x_5065_);
return v___x_5080_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1_spec__1___boxed(lean_object* v_fnNames_5081_, lean_object* v_numSectionVars_5082_, lean_object* v_x_5083_, lean_object* v_x_5084_, lean_object* v_x_5085_){
_start:
{
uint8_t v_res_5086_; lean_object* v_r_5087_; 
v_res_5086_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1_spec__1(v_fnNames_5081_, v_numSectionVars_5082_, v_x_5083_, v_x_5084_, v_x_5085_);
lean_dec(v_numSectionVars_5082_);
lean_dec_ref(v_fnNames_5081_);
v_r_5087_ = lean_box(v_res_5086_);
return v_r_5087_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1(lean_object* v_numSectionVars_5088_, lean_object* v_fnNames_5089_, lean_object* v_x_5090_, lean_object* v_x_5091_, lean_object* v_x_5092_){
_start:
{
if (lean_obj_tag(v_x_5090_) == 5)
{
lean_object* v_fn_5093_; lean_object* v_arg_5094_; lean_object* v___x_5095_; lean_object* v___x_5096_; lean_object* v___x_5097_; uint8_t v___x_5098_; 
v_fn_5093_ = lean_ctor_get(v_x_5090_, 0);
lean_inc_ref(v_fn_5093_);
v_arg_5094_ = lean_ctor_get(v_x_5090_, 1);
lean_inc_ref(v_arg_5094_);
lean_dec_ref_known(v_x_5090_, 2);
v___x_5095_ = lean_array_set(v_x_5091_, v_x_5092_, v_arg_5094_);
v___x_5096_ = lean_unsigned_to_nat(1u);
v___x_5097_ = lean_nat_sub(v_x_5092_, v___x_5096_);
v___x_5098_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1_spec__1(v_fnNames_5089_, v_numSectionVars_5088_, v_fn_5093_, v___x_5095_, v___x_5097_);
return v___x_5098_;
}
else
{
uint8_t v___x_5099_; 
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
v___x_5101_ = lean_array_get_size(v_fnNames_5089_);
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
v___x_5105_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0(v_x_5090_, v_x_5091_, v_numSectionVars_5088_, v_fnNames_5089_, v___x_5103_, v___x_5104_);
lean_dec_ref(v_x_5091_);
lean_dec_ref(v_x_5090_);
return v___x_5105_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1___boxed(lean_object* v_numSectionVars_5106_, lean_object* v_fnNames_5107_, lean_object* v_x_5108_, lean_object* v_x_5109_, lean_object* v_x_5110_){
_start:
{
uint8_t v_res_5111_; lean_object* v_r_5112_; 
v_res_5111_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1(v_numSectionVars_5106_, v_fnNames_5107_, v_x_5108_, v_x_5109_, v_x_5110_);
lean_dec(v_x_5110_);
lean_dec_ref(v_fnNames_5107_);
lean_dec(v_numSectionVars_5106_);
v_r_5112_ = lean_box(v_res_5111_);
return v_r_5112_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg(lean_object* v_fnNames_5113_, lean_object* v_numSectionVars_5114_, lean_object* v_a_5115_){
_start:
{
lean_object* v_dummy_5116_; lean_object* v_nargs_5117_; lean_object* v___x_5118_; lean_object* v___x_5119_; lean_object* v___x_5120_; uint8_t v___x_5121_; 
v_dummy_5116_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_5117_ = l_Lean_Expr_getAppNumArgs(v_a_5115_);
lean_inc(v_nargs_5117_);
v___x_5118_ = lean_mk_array(v_nargs_5117_, v_dummy_5116_);
v___x_5119_ = lean_unsigned_to_nat(1u);
v___x_5120_ = lean_nat_sub(v_nargs_5117_, v___x_5119_);
lean_dec(v_nargs_5117_);
v___x_5121_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1(v_numSectionVars_5114_, v_fnNames_5113_, v_a_5115_, v___x_5118_, v___x_5120_);
lean_dec(v___x_5120_);
return v___x_5121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg___boxed(lean_object* v_fnNames_5122_, lean_object* v_numSectionVars_5123_, lean_object* v_a_5124_){
_start:
{
uint8_t v_res_5125_; lean_object* v_r_5126_; 
v_res_5125_ = l___private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg(v_fnNames_5122_, v_numSectionVars_5123_, v_a_5124_);
lean_dec(v_numSectionVars_5123_);
lean_dec_ref(v_fnNames_5122_);
v_r_5126_ = lean_box(v_res_5125_);
return v_r_5126_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__0(lean_object* v_fnNames_5127_, lean_object* v_numSectionVars_5128_, lean_object* v_as_5129_, size_t v_i_5130_, size_t v_stop_5131_){
_start:
{
uint8_t v___x_5132_; 
v___x_5132_ = lean_usize_dec_eq(v_i_5130_, v_stop_5131_);
if (v___x_5132_ == 0)
{
lean_object* v___x_5133_; uint8_t v___x_5134_; 
v___x_5133_ = lean_array_uget_borrowed(v_as_5129_, v_i_5130_);
lean_inc(v___x_5133_);
v___x_5134_ = l___private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg(v_fnNames_5127_, v_numSectionVars_5128_, v___x_5133_);
if (v___x_5134_ == 0)
{
size_t v___x_5135_; size_t v___x_5136_; 
v___x_5135_ = ((size_t)1ULL);
v___x_5136_ = lean_usize_add(v_i_5130_, v___x_5135_);
v_i_5130_ = v___x_5136_;
goto _start;
}
else
{
return v___x_5134_;
}
}
else
{
uint8_t v___x_5138_; 
v___x_5138_ = 0;
return v___x_5138_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__0___boxed(lean_object* v_fnNames_5139_, lean_object* v_numSectionVars_5140_, lean_object* v_as_5141_, lean_object* v_i_5142_, lean_object* v_stop_5143_){
_start:
{
size_t v_i_boxed_5144_; size_t v_stop_boxed_5145_; uint8_t v_res_5146_; lean_object* v_r_5147_; 
v_i_boxed_5144_ = lean_unbox_usize(v_i_5142_);
lean_dec(v_i_5142_);
v_stop_boxed_5145_ = lean_unbox_usize(v_stop_5143_);
lean_dec(v_stop_5143_);
v_res_5146_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__0(v_fnNames_5139_, v_numSectionVars_5140_, v_as_5141_, v_i_boxed_5144_, v_stop_boxed_5145_);
lean_dec_ref(v_as_5141_);
lean_dec(v_numSectionVars_5140_);
lean_dec_ref(v_fnNames_5139_);
v_r_5147_ = lean_box(v_res_5146_);
return v_r_5147_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__1(lean_object* v_fnNames_5148_, lean_object* v_numSectionVars_5149_, lean_object* v___x_5150_, lean_object* v_x_5151_, lean_object* v_x_5152_, lean_object* v___y_5153_, lean_object* v___y_5154_){
_start:
{
if (lean_obj_tag(v_x_5151_) == 5)
{
lean_object* v_fn_5159_; lean_object* v_arg_5160_; lean_object* v___x_5161_; 
v_fn_5159_ = lean_ctor_get(v_x_5151_, 0);
lean_inc_ref(v_fn_5159_);
v_arg_5160_ = lean_ctor_get(v_x_5151_, 1);
lean_inc_ref(v_arg_5160_);
lean_dec_ref_known(v_x_5151_, 2);
v___x_5161_ = lean_array_push(v_x_5152_, v_arg_5160_);
v_x_5151_ = v_fn_5159_;
v_x_5152_ = v___x_5161_;
goto _start;
}
else
{
uint8_t v___x_5163_; 
v___x_5163_ = l_Lean_Expr_isConst(v_x_5151_);
if (v___x_5163_ == 0)
{
lean_dec_ref(v_x_5152_);
lean_dec_ref(v_x_5151_);
lean_dec_ref(v___x_5150_);
goto v___jp_5156_;
}
else
{
lean_object* v___x_5164_; lean_object* v___x_5165_; uint8_t v___x_5166_; 
v___x_5164_ = lean_unsigned_to_nat(0u);
v___x_5165_ = lean_array_get_size(v_x_5152_);
v___x_5166_ = lean_nat_dec_lt(v___x_5164_, v___x_5165_);
if (v___x_5166_ == 0)
{
lean_dec_ref(v_x_5152_);
lean_dec_ref(v_x_5151_);
lean_dec_ref(v___x_5150_);
goto v___jp_5156_;
}
else
{
if (v___x_5166_ == 0)
{
lean_dec_ref(v_x_5152_);
lean_dec_ref(v_x_5151_);
lean_dec_ref(v___x_5150_);
goto v___jp_5156_;
}
else
{
size_t v___x_5167_; size_t v___x_5168_; uint8_t v___x_5169_; 
v___x_5167_ = ((size_t)0ULL);
v___x_5168_ = lean_usize_of_nat(v___x_5165_);
v___x_5169_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__0(v_fnNames_5148_, v_numSectionVars_5149_, v_x_5152_, v___x_5167_, v___x_5168_);
if (v___x_5169_ == 0)
{
lean_dec_ref(v_x_5152_);
lean_dec_ref(v_x_5151_);
lean_dec_ref(v___x_5150_);
goto v___jp_5156_;
}
else
{
lean_object* v___x_5170_; uint8_t v___x_5171_; lean_object* v___x_5172_; 
v___x_5170_ = l_Lean_Expr_constName_x21(v_x_5151_);
v___x_5171_ = 0;
v___x_5172_ = l_Lean_Environment_find_x3f(v___x_5150_, v___x_5170_, v___x_5171_);
if (lean_obj_tag(v___x_5172_) == 1)
{
lean_object* v_val_5173_; 
v_val_5173_ = lean_ctor_get(v___x_5172_, 0);
lean_inc(v_val_5173_);
lean_dec_ref_known(v___x_5172_, 1);
if (lean_obj_tag(v_val_5173_) == 2)
{
lean_object* v___x_5174_; lean_object* v___x_5175_; lean_object* v___x_5177_; uint8_t v_isShared_5178_; uint8_t v_isSharedCheck_5199_; 
v___x_5174_ = l_Lean_Expr_constLevels_x21(v_x_5151_);
lean_dec_ref(v_x_5151_);
v___x_5175_ = l_Lean_Core_instantiateValueLevelParams(v_val_5173_, v___x_5174_, v___x_5166_, v___y_5153_, v___y_5154_);
v_isSharedCheck_5199_ = !lean_is_exclusive(v_val_5173_);
if (v_isSharedCheck_5199_ == 0)
{
lean_object* v_unused_5200_; 
v_unused_5200_ = lean_ctor_get(v_val_5173_, 0);
lean_dec(v_unused_5200_);
v___x_5177_ = v_val_5173_;
v_isShared_5178_ = v_isSharedCheck_5199_;
goto v_resetjp_5176_;
}
else
{
lean_dec(v_val_5173_);
v___x_5177_ = lean_box(0);
v_isShared_5178_ = v_isSharedCheck_5199_;
goto v_resetjp_5176_;
}
v_resetjp_5176_:
{
if (lean_obj_tag(v___x_5175_) == 0)
{
lean_object* v_a_5179_; lean_object* v___x_5181_; uint8_t v_isShared_5182_; uint8_t v_isSharedCheck_5190_; 
v_a_5179_ = lean_ctor_get(v___x_5175_, 0);
v_isSharedCheck_5190_ = !lean_is_exclusive(v___x_5175_);
if (v_isSharedCheck_5190_ == 0)
{
v___x_5181_ = v___x_5175_;
v_isShared_5182_ = v_isSharedCheck_5190_;
goto v_resetjp_5180_;
}
else
{
lean_inc(v_a_5179_);
lean_dec(v___x_5175_);
v___x_5181_ = lean_box(0);
v_isShared_5182_ = v_isSharedCheck_5190_;
goto v_resetjp_5180_;
}
v_resetjp_5180_:
{
lean_object* v___x_5183_; lean_object* v___x_5185_; 
v___x_5183_ = l_Lean_Expr_betaRev(v_a_5179_, v_x_5152_, v___x_5171_, v___x_5171_);
lean_dec_ref(v_x_5152_);
if (v_isShared_5178_ == 0)
{
lean_ctor_set_tag(v___x_5177_, 1);
lean_ctor_set(v___x_5177_, 0, v___x_5183_);
v___x_5185_ = v___x_5177_;
goto v_reusejp_5184_;
}
else
{
lean_object* v_reuseFailAlloc_5189_; 
v_reuseFailAlloc_5189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5189_, 0, v___x_5183_);
v___x_5185_ = v_reuseFailAlloc_5189_;
goto v_reusejp_5184_;
}
v_reusejp_5184_:
{
lean_object* v___x_5187_; 
if (v_isShared_5182_ == 0)
{
lean_ctor_set(v___x_5181_, 0, v___x_5185_);
v___x_5187_ = v___x_5181_;
goto v_reusejp_5186_;
}
else
{
lean_object* v_reuseFailAlloc_5188_; 
v_reuseFailAlloc_5188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5188_, 0, v___x_5185_);
v___x_5187_ = v_reuseFailAlloc_5188_;
goto v_reusejp_5186_;
}
v_reusejp_5186_:
{
return v___x_5187_;
}
}
}
}
else
{
lean_object* v_a_5191_; lean_object* v___x_5193_; uint8_t v_isShared_5194_; uint8_t v_isSharedCheck_5198_; 
lean_del_object(v___x_5177_);
lean_dec_ref(v_x_5152_);
v_a_5191_ = lean_ctor_get(v___x_5175_, 0);
v_isSharedCheck_5198_ = !lean_is_exclusive(v___x_5175_);
if (v_isSharedCheck_5198_ == 0)
{
v___x_5193_ = v___x_5175_;
v_isShared_5194_ = v_isSharedCheck_5198_;
goto v_resetjp_5192_;
}
else
{
lean_inc(v_a_5191_);
lean_dec(v___x_5175_);
v___x_5193_ = lean_box(0);
v_isShared_5194_ = v_isSharedCheck_5198_;
goto v_resetjp_5192_;
}
v_resetjp_5192_:
{
lean_object* v___x_5196_; 
if (v_isShared_5194_ == 0)
{
v___x_5196_ = v___x_5193_;
goto v_reusejp_5195_;
}
else
{
lean_object* v_reuseFailAlloc_5197_; 
v_reuseFailAlloc_5197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5197_, 0, v_a_5191_);
v___x_5196_ = v_reuseFailAlloc_5197_;
goto v_reusejp_5195_;
}
v_reusejp_5195_:
{
return v___x_5196_;
}
}
}
}
}
else
{
lean_dec(v_val_5173_);
lean_dec_ref(v_x_5152_);
lean_dec_ref(v_x_5151_);
goto v___jp_5156_;
}
}
else
{
lean_dec(v___x_5172_);
lean_dec_ref(v_x_5152_);
lean_dec_ref(v_x_5151_);
goto v___jp_5156_;
}
}
}
}
}
}
v___jp_5156_:
{
lean_object* v___x_5157_; lean_object* v___x_5158_; 
v___x_5157_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_5158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5158_, 0, v___x_5157_);
return v___x_5158_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__1___boxed(lean_object* v_fnNames_5201_, lean_object* v_numSectionVars_5202_, lean_object* v___x_5203_, lean_object* v_x_5204_, lean_object* v_x_5205_, lean_object* v___y_5206_, lean_object* v___y_5207_, lean_object* v___y_5208_){
_start:
{
lean_object* v_res_5209_; 
v_res_5209_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__1(v_fnNames_5201_, v_numSectionVars_5202_, v___x_5203_, v_x_5204_, v_x_5205_, v___y_5206_, v___y_5207_);
lean_dec(v___y_5207_);
lean_dec_ref(v___y_5206_);
lean_dec(v_numSectionVars_5202_);
lean_dec_ref(v_fnNames_5201_);
return v_res_5209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___lam__1(lean_object* v_fnNames_5210_, lean_object* v_numSectionVars_5211_, lean_object* v_env_5212_, lean_object* v_e_5213_, lean_object* v___y_5214_, lean_object* v___y_5215_){
_start:
{
lean_object* v___x_5217_; lean_object* v___x_5218_; lean_object* v___x_5219_; 
v___x_5217_ = l_Lean_Expr_getAppNumArgs(v_e_5213_);
v___x_5218_ = lean_mk_empty_array_with_capacity(v___x_5217_);
lean_dec(v___x_5217_);
v___x_5219_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__1(v_fnNames_5210_, v_numSectionVars_5211_, v_env_5212_, v_e_5213_, v___x_5218_, v___y_5214_, v___y_5215_);
return v___x_5219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___lam__1___boxed(lean_object* v_fnNames_5220_, lean_object* v_numSectionVars_5221_, lean_object* v_env_5222_, lean_object* v_e_5223_, lean_object* v___y_5224_, lean_object* v___y_5225_, lean_object* v___y_5226_){
_start:
{
lean_object* v_res_5227_; 
v_res_5227_ = l_Lean_Meta_unfoldIfArgIsAppOf___lam__1(v_fnNames_5220_, v_numSectionVars_5221_, v_env_5222_, v_e_5223_, v___y_5224_, v___y_5225_);
lean_dec(v___y_5225_);
lean_dec_ref(v___y_5224_);
lean_dec(v_numSectionVars_5221_);
lean_dec_ref(v_fnNames_5220_);
return v_res_5227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___lam__0(lean_object* v_fnNames_5228_, lean_object* v_numSectionVars_5229_, lean_object* v_e_5230_, lean_object* v___f_5231_, lean_object* v___y_5232_, lean_object* v___y_5233_){
_start:
{
lean_object* v___x_5235_; lean_object* v_env_5236_; lean_object* v___f_5237_; lean_object* v___x_5238_; 
v___x_5235_ = lean_st_ref_get(v___y_5233_);
v_env_5236_ = lean_ctor_get(v___x_5235_, 0);
lean_inc_ref(v_env_5236_);
lean_dec(v___x_5235_);
v___f_5237_ = lean_alloc_closure((void*)(l_Lean_Meta_unfoldIfArgIsAppOf___lam__1___boxed), 7, 3);
lean_closure_set(v___f_5237_, 0, v_fnNames_5228_);
lean_closure_set(v___f_5237_, 1, v_numSectionVars_5229_);
lean_closure_set(v___f_5237_, 2, v_env_5236_);
v___x_5238_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_5230_, v___f_5237_, v___f_5231_, v___y_5232_, v___y_5233_);
return v___x_5238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___lam__0___boxed(lean_object* v_fnNames_5239_, lean_object* v_numSectionVars_5240_, lean_object* v_e_5241_, lean_object* v___f_5242_, lean_object* v___y_5243_, lean_object* v___y_5244_, lean_object* v___y_5245_){
_start:
{
lean_object* v_res_5246_; 
v_res_5246_ = l_Lean_Meta_unfoldIfArgIsAppOf___lam__0(v_fnNames_5239_, v_numSectionVars_5240_, v_e_5241_, v___f_5242_, v___y_5243_, v___y_5244_);
lean_dec(v___y_5244_);
lean_dec_ref(v___y_5243_);
return v_res_5246_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0(lean_object* v___y_5247_, uint8_t v_isExporting_5248_, lean_object* v___x_5249_, lean_object* v_a_x3f_5250_){
_start:
{
lean_object* v___x_5252_; lean_object* v_env_5253_; lean_object* v_nextMacroScope_5254_; lean_object* v_ngen_5255_; lean_object* v_auxDeclNGen_5256_; lean_object* v_traceState_5257_; lean_object* v_recordedDeps_5258_; lean_object* v_messages_5259_; lean_object* v_infoState_5260_; lean_object* v_snapshotTasks_5261_; lean_object* v___x_5263_; uint8_t v_isShared_5264_; uint8_t v_isSharedCheck_5272_; 
v___x_5252_ = lean_st_ref_take(v___y_5247_);
v_env_5253_ = lean_ctor_get(v___x_5252_, 0);
v_nextMacroScope_5254_ = lean_ctor_get(v___x_5252_, 1);
v_ngen_5255_ = lean_ctor_get(v___x_5252_, 2);
v_auxDeclNGen_5256_ = lean_ctor_get(v___x_5252_, 3);
v_traceState_5257_ = lean_ctor_get(v___x_5252_, 4);
v_recordedDeps_5258_ = lean_ctor_get(v___x_5252_, 6);
v_messages_5259_ = lean_ctor_get(v___x_5252_, 7);
v_infoState_5260_ = lean_ctor_get(v___x_5252_, 8);
v_snapshotTasks_5261_ = lean_ctor_get(v___x_5252_, 9);
v_isSharedCheck_5272_ = !lean_is_exclusive(v___x_5252_);
if (v_isSharedCheck_5272_ == 0)
{
lean_object* v_unused_5273_; 
v_unused_5273_ = lean_ctor_get(v___x_5252_, 5);
lean_dec(v_unused_5273_);
v___x_5263_ = v___x_5252_;
v_isShared_5264_ = v_isSharedCheck_5272_;
goto v_resetjp_5262_;
}
else
{
lean_inc(v_snapshotTasks_5261_);
lean_inc(v_infoState_5260_);
lean_inc(v_messages_5259_);
lean_inc(v_recordedDeps_5258_);
lean_inc(v_traceState_5257_);
lean_inc(v_auxDeclNGen_5256_);
lean_inc(v_ngen_5255_);
lean_inc(v_nextMacroScope_5254_);
lean_inc(v_env_5253_);
lean_dec(v___x_5252_);
v___x_5263_ = lean_box(0);
v_isShared_5264_ = v_isSharedCheck_5272_;
goto v_resetjp_5262_;
}
v_resetjp_5262_:
{
lean_object* v___x_5265_; lean_object* v___x_5266_; lean_object* v___x_5268_; 
v___x_5265_ = lean_box(0);
v___x_5266_ = l_Lean_Environment_setExporting(v_env_5253_, v_isExporting_5248_);
if (v_isShared_5264_ == 0)
{
lean_ctor_set(v___x_5263_, 5, v___x_5249_);
lean_ctor_set(v___x_5263_, 0, v___x_5266_);
v___x_5268_ = v___x_5263_;
goto v_reusejp_5267_;
}
else
{
lean_object* v_reuseFailAlloc_5271_; 
v_reuseFailAlloc_5271_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5271_, 0, v___x_5266_);
lean_ctor_set(v_reuseFailAlloc_5271_, 1, v_nextMacroScope_5254_);
lean_ctor_set(v_reuseFailAlloc_5271_, 2, v_ngen_5255_);
lean_ctor_set(v_reuseFailAlloc_5271_, 3, v_auxDeclNGen_5256_);
lean_ctor_set(v_reuseFailAlloc_5271_, 4, v_traceState_5257_);
lean_ctor_set(v_reuseFailAlloc_5271_, 5, v___x_5249_);
lean_ctor_set(v_reuseFailAlloc_5271_, 6, v_recordedDeps_5258_);
lean_ctor_set(v_reuseFailAlloc_5271_, 7, v_messages_5259_);
lean_ctor_set(v_reuseFailAlloc_5271_, 8, v_infoState_5260_);
lean_ctor_set(v_reuseFailAlloc_5271_, 9, v_snapshotTasks_5261_);
v___x_5268_ = v_reuseFailAlloc_5271_;
goto v_reusejp_5267_;
}
v_reusejp_5267_:
{
lean_object* v___x_5269_; lean_object* v___x_5270_; 
v___x_5269_ = lean_st_ref_put(v___y_5247_, v___x_5268_);
v___x_5270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5270_, 0, v___x_5265_);
return v___x_5270_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0___boxed(lean_object* v___y_5274_, lean_object* v_isExporting_5275_, lean_object* v___x_5276_, lean_object* v_a_x3f_5277_, lean_object* v___y_5278_){
_start:
{
uint8_t v_isExporting_boxed_5279_; lean_object* v_res_5280_; 
v_isExporting_boxed_5279_ = lean_unbox(v_isExporting_5275_);
v_res_5280_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0(v___y_5274_, v_isExporting_boxed_5279_, v___x_5276_, v_a_x3f_5277_);
lean_dec(v_a_x3f_5277_);
lean_dec(v___y_5274_);
return v_res_5280_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg(lean_object* v_x_5281_, uint8_t v_isExporting_5282_, lean_object* v___y_5283_, lean_object* v___y_5284_){
_start:
{
lean_object* v___x_5286_; lean_object* v_env_5287_; lean_object* v___x_5288_; uint8_t v_isModule_5289_; 
v___x_5286_ = lean_st_ref_get(v___y_5284_);
v_env_5287_ = lean_ctor_get(v___x_5286_, 0);
lean_inc_ref(v_env_5287_);
lean_dec(v___x_5286_);
v___x_5288_ = l_Lean_Environment_header(v_env_5287_);
v_isModule_5289_ = lean_ctor_get_uint8(v___x_5288_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_5288_);
if (v_isModule_5289_ == 0)
{
lean_object* v___x_5290_; 
lean_dec_ref(v_env_5287_);
lean_inc(v___y_5284_);
lean_inc_ref(v___y_5283_);
v___x_5290_ = lean_apply_3(v_x_5281_, v___y_5283_, v___y_5284_, lean_box(0));
return v___x_5290_;
}
else
{
uint8_t v_isExporting_5291_; 
v_isExporting_5291_ = lean_ctor_get_uint8(v_env_5287_, sizeof(void*)*8);
lean_dec_ref(v_env_5287_);
if (v_isExporting_5282_ == 0)
{
if (v_isExporting_5291_ == 0)
{
lean_object* v___x_5343_; 
lean_inc(v___y_5284_);
lean_inc_ref(v___y_5283_);
v___x_5343_ = lean_apply_3(v_x_5281_, v___y_5283_, v___y_5284_, lean_box(0));
return v___x_5343_;
}
else
{
goto v___jp_5292_;
}
}
else
{
if (v_isExporting_5291_ == 0)
{
goto v___jp_5292_;
}
else
{
lean_object* v___x_5344_; 
lean_inc(v___y_5284_);
lean_inc_ref(v___y_5283_);
v___x_5344_ = lean_apply_3(v_x_5281_, v___y_5283_, v___y_5284_, lean_box(0));
return v___x_5344_;
}
}
v___jp_5292_:
{
lean_object* v___x_5293_; lean_object* v_env_5294_; lean_object* v_nextMacroScope_5295_; lean_object* v_ngen_5296_; lean_object* v_auxDeclNGen_5297_; lean_object* v_traceState_5298_; lean_object* v_recordedDeps_5299_; lean_object* v_messages_5300_; lean_object* v_infoState_5301_; lean_object* v_snapshotTasks_5302_; lean_object* v___x_5304_; uint8_t v_isShared_5305_; uint8_t v_isSharedCheck_5341_; 
v___x_5293_ = lean_st_ref_take(v___y_5284_);
v_env_5294_ = lean_ctor_get(v___x_5293_, 0);
v_nextMacroScope_5295_ = lean_ctor_get(v___x_5293_, 1);
v_ngen_5296_ = lean_ctor_get(v___x_5293_, 2);
v_auxDeclNGen_5297_ = lean_ctor_get(v___x_5293_, 3);
v_traceState_5298_ = lean_ctor_get(v___x_5293_, 4);
v_recordedDeps_5299_ = lean_ctor_get(v___x_5293_, 6);
v_messages_5300_ = lean_ctor_get(v___x_5293_, 7);
v_infoState_5301_ = lean_ctor_get(v___x_5293_, 8);
v_snapshotTasks_5302_ = lean_ctor_get(v___x_5293_, 9);
v_isSharedCheck_5341_ = !lean_is_exclusive(v___x_5293_);
if (v_isSharedCheck_5341_ == 0)
{
lean_object* v_unused_5342_; 
v_unused_5342_ = lean_ctor_get(v___x_5293_, 5);
lean_dec(v_unused_5342_);
v___x_5304_ = v___x_5293_;
v_isShared_5305_ = v_isSharedCheck_5341_;
goto v_resetjp_5303_;
}
else
{
lean_inc(v_snapshotTasks_5302_);
lean_inc(v_infoState_5301_);
lean_inc(v_messages_5300_);
lean_inc(v_recordedDeps_5299_);
lean_inc(v_traceState_5298_);
lean_inc(v_auxDeclNGen_5297_);
lean_inc(v_ngen_5296_);
lean_inc(v_nextMacroScope_5295_);
lean_inc(v_env_5294_);
lean_dec(v___x_5293_);
v___x_5304_ = lean_box(0);
v_isShared_5305_ = v_isSharedCheck_5341_;
goto v_resetjp_5303_;
}
v_resetjp_5303_:
{
lean_object* v___x_5306_; lean_object* v___x_5307_; lean_object* v___x_5309_; 
v___x_5306_ = l_Lean_Environment_setExporting(v_env_5294_, v_isExporting_5282_);
v___x_5307_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2, &l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2);
if (v_isShared_5305_ == 0)
{
lean_ctor_set(v___x_5304_, 5, v___x_5307_);
lean_ctor_set(v___x_5304_, 0, v___x_5306_);
v___x_5309_ = v___x_5304_;
goto v_reusejp_5308_;
}
else
{
lean_object* v_reuseFailAlloc_5340_; 
v_reuseFailAlloc_5340_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5340_, 0, v___x_5306_);
lean_ctor_set(v_reuseFailAlloc_5340_, 1, v_nextMacroScope_5295_);
lean_ctor_set(v_reuseFailAlloc_5340_, 2, v_ngen_5296_);
lean_ctor_set(v_reuseFailAlloc_5340_, 3, v_auxDeclNGen_5297_);
lean_ctor_set(v_reuseFailAlloc_5340_, 4, v_traceState_5298_);
lean_ctor_set(v_reuseFailAlloc_5340_, 5, v___x_5307_);
lean_ctor_set(v_reuseFailAlloc_5340_, 6, v_recordedDeps_5299_);
lean_ctor_set(v_reuseFailAlloc_5340_, 7, v_messages_5300_);
lean_ctor_set(v_reuseFailAlloc_5340_, 8, v_infoState_5301_);
lean_ctor_set(v_reuseFailAlloc_5340_, 9, v_snapshotTasks_5302_);
v___x_5309_ = v_reuseFailAlloc_5340_;
goto v_reusejp_5308_;
}
v_reusejp_5308_:
{
lean_object* v___x_5310_; lean_object* v_r_5311_; 
v___x_5310_ = lean_st_ref_put(v___y_5284_, v___x_5309_);
lean_inc(v___y_5284_);
lean_inc_ref(v___y_5283_);
v_r_5311_ = lean_apply_3(v_x_5281_, v___y_5283_, v___y_5284_, lean_box(0));
if (lean_obj_tag(v_r_5311_) == 0)
{
lean_object* v_a_5312_; lean_object* v___x_5314_; uint8_t v_isShared_5315_; uint8_t v_isSharedCheck_5328_; 
v_a_5312_ = lean_ctor_get(v_r_5311_, 0);
v_isSharedCheck_5328_ = !lean_is_exclusive(v_r_5311_);
if (v_isSharedCheck_5328_ == 0)
{
v___x_5314_ = v_r_5311_;
v_isShared_5315_ = v_isSharedCheck_5328_;
goto v_resetjp_5313_;
}
else
{
lean_inc(v_a_5312_);
lean_dec(v_r_5311_);
v___x_5314_ = lean_box(0);
v_isShared_5315_ = v_isSharedCheck_5328_;
goto v_resetjp_5313_;
}
v_resetjp_5313_:
{
lean_object* v___x_5317_; 
lean_inc(v_a_5312_);
if (v_isShared_5315_ == 0)
{
lean_ctor_set_tag(v___x_5314_, 1);
v___x_5317_ = v___x_5314_;
goto v_reusejp_5316_;
}
else
{
lean_object* v_reuseFailAlloc_5327_; 
v_reuseFailAlloc_5327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5327_, 0, v_a_5312_);
v___x_5317_ = v_reuseFailAlloc_5327_;
goto v_reusejp_5316_;
}
v_reusejp_5316_:
{
lean_object* v___x_5318_; lean_object* v___x_5320_; uint8_t v_isShared_5321_; uint8_t v_isSharedCheck_5325_; 
v___x_5318_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0(v___y_5284_, v_isExporting_5291_, v___x_5307_, v___x_5317_);
lean_dec_ref(v___x_5317_);
v_isSharedCheck_5325_ = !lean_is_exclusive(v___x_5318_);
if (v_isSharedCheck_5325_ == 0)
{
lean_object* v_unused_5326_; 
v_unused_5326_ = lean_ctor_get(v___x_5318_, 0);
lean_dec(v_unused_5326_);
v___x_5320_ = v___x_5318_;
v_isShared_5321_ = v_isSharedCheck_5325_;
goto v_resetjp_5319_;
}
else
{
lean_dec(v___x_5318_);
v___x_5320_ = lean_box(0);
v_isShared_5321_ = v_isSharedCheck_5325_;
goto v_resetjp_5319_;
}
v_resetjp_5319_:
{
lean_object* v___x_5323_; 
if (v_isShared_5321_ == 0)
{
lean_ctor_set(v___x_5320_, 0, v_a_5312_);
v___x_5323_ = v___x_5320_;
goto v_reusejp_5322_;
}
else
{
lean_object* v_reuseFailAlloc_5324_; 
v_reuseFailAlloc_5324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5324_, 0, v_a_5312_);
v___x_5323_ = v_reuseFailAlloc_5324_;
goto v_reusejp_5322_;
}
v_reusejp_5322_:
{
return v___x_5323_;
}
}
}
}
}
else
{
lean_object* v_a_5329_; lean_object* v___x_5330_; lean_object* v___x_5331_; lean_object* v___x_5333_; uint8_t v_isShared_5334_; uint8_t v_isSharedCheck_5338_; 
v_a_5329_ = lean_ctor_get(v_r_5311_, 0);
lean_inc(v_a_5329_);
lean_dec_ref_known(v_r_5311_, 1);
v___x_5330_ = lean_box(0);
v___x_5331_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0(v___y_5284_, v_isExporting_5291_, v___x_5307_, v___x_5330_);
v_isSharedCheck_5338_ = !lean_is_exclusive(v___x_5331_);
if (v_isSharedCheck_5338_ == 0)
{
lean_object* v_unused_5339_; 
v_unused_5339_ = lean_ctor_get(v___x_5331_, 0);
lean_dec(v_unused_5339_);
v___x_5333_ = v___x_5331_;
v_isShared_5334_ = v_isSharedCheck_5338_;
goto v_resetjp_5332_;
}
else
{
lean_dec(v___x_5331_);
v___x_5333_ = lean_box(0);
v_isShared_5334_ = v_isSharedCheck_5338_;
goto v_resetjp_5332_;
}
v_resetjp_5332_:
{
lean_object* v___x_5336_; 
if (v_isShared_5334_ == 0)
{
lean_ctor_set_tag(v___x_5333_, 1);
lean_ctor_set(v___x_5333_, 0, v_a_5329_);
v___x_5336_ = v___x_5333_;
goto v_reusejp_5335_;
}
else
{
lean_object* v_reuseFailAlloc_5337_; 
v_reuseFailAlloc_5337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5337_, 0, v_a_5329_);
v___x_5336_ = v_reuseFailAlloc_5337_;
goto v_reusejp_5335_;
}
v_reusejp_5335_:
{
return v___x_5336_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___boxed(lean_object* v_x_5345_, lean_object* v_isExporting_5346_, lean_object* v___y_5347_, lean_object* v___y_5348_, lean_object* v___y_5349_){
_start:
{
uint8_t v_isExporting_boxed_5350_; lean_object* v_res_5351_; 
v_isExporting_boxed_5350_ = lean_unbox(v_isExporting_5346_);
v_res_5351_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg(v_x_5345_, v_isExporting_boxed_5350_, v___y_5347_, v___y_5348_);
lean_dec(v___y_5348_);
lean_dec_ref(v___y_5347_);
return v_res_5351_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg(lean_object* v_x_5352_, uint8_t v_when_5353_, lean_object* v___y_5354_, lean_object* v___y_5355_){
_start:
{
if (v_when_5353_ == 0)
{
lean_object* v___x_5357_; 
lean_inc(v___y_5355_);
lean_inc_ref(v___y_5354_);
v___x_5357_ = lean_apply_3(v_x_5352_, v___y_5354_, v___y_5355_, lean_box(0));
return v___x_5357_;
}
else
{
uint8_t v___x_5358_; lean_object* v___x_5359_; 
v___x_5358_ = 0;
v___x_5359_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg(v_x_5352_, v___x_5358_, v___y_5354_, v___y_5355_);
return v___x_5359_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg___boxed(lean_object* v_x_5360_, lean_object* v_when_5361_, lean_object* v___y_5362_, lean_object* v___y_5363_, lean_object* v___y_5364_){
_start:
{
uint8_t v_when_boxed_5365_; lean_object* v_res_5366_; 
v_when_boxed_5365_ = lean_unbox(v_when_5361_);
v_res_5366_ = l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg(v_x_5360_, v_when_boxed_5365_, v___y_5362_, v___y_5363_);
lean_dec(v___y_5363_);
lean_dec_ref(v___y_5362_);
return v_res_5366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf(lean_object* v_fnNames_5367_, lean_object* v_numSectionVars_5368_, lean_object* v_e_5369_, lean_object* v_a_5370_, lean_object* v_a_5371_){
_start:
{
lean_object* v___f_5373_; lean_object* v___f_5374_; uint8_t v___x_5375_; lean_object* v___x_5376_; 
v___f_5373_ = ((lean_object*)(l_Lean_Core_betaReduce___closed__1));
v___f_5374_ = lean_alloc_closure((void*)(l_Lean_Meta_unfoldIfArgIsAppOf___lam__0___boxed), 7, 4);
lean_closure_set(v___f_5374_, 0, v_fnNames_5367_);
lean_closure_set(v___f_5374_, 1, v_numSectionVars_5368_);
lean_closure_set(v___f_5374_, 2, v_e_5369_);
lean_closure_set(v___f_5374_, 3, v___f_5373_);
v___x_5375_ = 1;
v___x_5376_ = l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg(v___f_5374_, v___x_5375_, v_a_5370_, v_a_5371_);
return v___x_5376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___boxed(lean_object* v_fnNames_5377_, lean_object* v_numSectionVars_5378_, lean_object* v_e_5379_, lean_object* v_a_5380_, lean_object* v_a_5381_, lean_object* v_a_5382_){
_start:
{
lean_object* v_res_5383_; 
v_res_5383_ = l_Lean_Meta_unfoldIfArgIsAppOf(v_fnNames_5377_, v_numSectionVars_5378_, v_e_5379_, v_a_5380_, v_a_5381_);
lean_dec(v_a_5381_);
lean_dec_ref(v_a_5380_);
return v_res_5383_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2(lean_object* v_00_u03b1_5384_, lean_object* v_x_5385_, uint8_t v_isExporting_5386_, lean_object* v___y_5387_, lean_object* v___y_5388_){
_start:
{
lean_object* v___x_5390_; 
v___x_5390_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg(v_x_5385_, v_isExporting_5386_, v___y_5387_, v___y_5388_);
return v___x_5390_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___boxed(lean_object* v_00_u03b1_5391_, lean_object* v_x_5392_, lean_object* v_isExporting_5393_, lean_object* v___y_5394_, lean_object* v___y_5395_, lean_object* v___y_5396_){
_start:
{
uint8_t v_isExporting_boxed_5397_; lean_object* v_res_5398_; 
v_isExporting_boxed_5397_ = lean_unbox(v_isExporting_5393_);
v_res_5398_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2(v_00_u03b1_5391_, v_x_5392_, v_isExporting_boxed_5397_, v___y_5394_, v___y_5395_);
lean_dec(v___y_5395_);
lean_dec_ref(v___y_5394_);
return v_res_5398_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2(lean_object* v_00_u03b1_5399_, lean_object* v_x_5400_, uint8_t v_when_5401_, lean_object* v___y_5402_, lean_object* v___y_5403_){
_start:
{
lean_object* v___x_5405_; 
v___x_5405_ = l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg(v_x_5400_, v_when_5401_, v___y_5402_, v___y_5403_);
return v___x_5405_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___boxed(lean_object* v_00_u03b1_5406_, lean_object* v_x_5407_, lean_object* v_when_5408_, lean_object* v___y_5409_, lean_object* v___y_5410_, lean_object* v___y_5411_){
_start:
{
uint8_t v_when_boxed_5412_; lean_object* v_res_5413_; 
v_when_boxed_5412_ = lean_unbox(v_when_5408_);
v_res_5413_ = l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2(v_00_u03b1_5406_, v_x_5407_, v_when_boxed_5412_, v___y_5409_, v___y_5410_);
lean_dec(v___y_5410_);
lean_dec_ref(v___y_5409_);
return v_res_5413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___lam__0(lean_object* v_x_5414_, lean_object* v___y_5415_, lean_object* v___y_5416_){
_start:
{
lean_object* v___x_5418_; lean_object* v___x_5419_; 
v___x_5418_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_5419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5419_, 0, v___x_5418_);
return v___x_5419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___lam__0___boxed(lean_object* v_x_5420_, lean_object* v___y_5421_, lean_object* v___y_5422_, lean_object* v___y_5423_){
_start:
{
lean_object* v_res_5424_; 
v_res_5424_ = l_Lean_Meta_eraseInaccessibleAnnotations___lam__0(v_x_5420_, v___y_5421_, v___y_5422_);
lean_dec(v___y_5422_);
lean_dec_ref(v___y_5421_);
lean_dec_ref(v_x_5420_);
return v_res_5424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___lam__1(lean_object* v_e_5425_, lean_object* v___y_5426_, lean_object* v___y_5427_){
_start:
{
lean_object* v___y_5430_; lean_object* v___x_5433_; 
v___x_5433_ = l_Lean_inaccessible_x3f(v_e_5425_);
if (lean_obj_tag(v___x_5433_) == 1)
{
lean_object* v_val_5434_; 
lean_dec_ref(v_e_5425_);
v_val_5434_ = lean_ctor_get(v___x_5433_, 0);
lean_inc(v_val_5434_);
lean_dec_ref_known(v___x_5433_, 1);
v___y_5430_ = v_val_5434_;
goto v___jp_5429_;
}
else
{
lean_dec(v___x_5433_);
v___y_5430_ = v_e_5425_;
goto v___jp_5429_;
}
v___jp_5429_:
{
lean_object* v___x_5431_; lean_object* v___x_5432_; 
v___x_5431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5431_, 0, v___y_5430_);
v___x_5432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5432_, 0, v___x_5431_);
return v___x_5432_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___lam__1___boxed(lean_object* v_e_5435_, lean_object* v___y_5436_, lean_object* v___y_5437_, lean_object* v___y_5438_){
_start:
{
lean_object* v_res_5439_; 
v_res_5439_ = l_Lean_Meta_eraseInaccessibleAnnotations___lam__1(v_e_5435_, v___y_5436_, v___y_5437_);
lean_dec(v___y_5437_);
lean_dec_ref(v___y_5436_);
return v_res_5439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations(lean_object* v_e_5442_, lean_object* v_a_5443_, lean_object* v_a_5444_){
_start:
{
lean_object* v___f_5446_; lean_object* v___f_5447_; lean_object* v___x_5448_; 
v___f_5446_ = ((lean_object*)(l_Lean_Meta_eraseInaccessibleAnnotations___closed__0));
v___f_5447_ = ((lean_object*)(l_Lean_Meta_eraseInaccessibleAnnotations___closed__1));
v___x_5448_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_5442_, v___f_5446_, v___f_5447_, v_a_5443_, v_a_5444_);
return v___x_5448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___boxed(lean_object* v_e_5449_, lean_object* v_a_5450_, lean_object* v_a_5451_, lean_object* v_a_5452_){
_start:
{
lean_object* v_res_5453_; 
v_res_5453_ = l_Lean_Meta_eraseInaccessibleAnnotations(v_e_5449_, v_a_5450_, v_a_5451_);
lean_dec(v_a_5451_);
lean_dec_ref(v_a_5450_);
return v_res_5453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_erasePatternRefAnnotations___lam__1(lean_object* v_e_5454_, lean_object* v___y_5455_, lean_object* v___y_5456_){
_start:
{
lean_object* v___y_5459_; lean_object* v___x_5462_; 
v___x_5462_ = l_Lean_patternWithRef_x3f(v_e_5454_);
if (lean_obj_tag(v___x_5462_) == 1)
{
lean_object* v_val_5463_; lean_object* v_snd_5464_; 
lean_dec_ref(v_e_5454_);
v_val_5463_ = lean_ctor_get(v___x_5462_, 0);
lean_inc(v_val_5463_);
lean_dec_ref_known(v___x_5462_, 1);
v_snd_5464_ = lean_ctor_get(v_val_5463_, 1);
lean_inc(v_snd_5464_);
lean_dec(v_val_5463_);
v___y_5459_ = v_snd_5464_;
goto v___jp_5458_;
}
else
{
lean_dec(v___x_5462_);
v___y_5459_ = v_e_5454_;
goto v___jp_5458_;
}
v___jp_5458_:
{
lean_object* v___x_5460_; lean_object* v___x_5461_; 
v___x_5460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5460_, 0, v___y_5459_);
v___x_5461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5461_, 0, v___x_5460_);
return v___x_5461_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_erasePatternRefAnnotations___lam__1___boxed(lean_object* v_e_5465_, lean_object* v___y_5466_, lean_object* v___y_5467_, lean_object* v___y_5468_){
_start:
{
lean_object* v_res_5469_; 
v_res_5469_ = l_Lean_Meta_erasePatternRefAnnotations___lam__1(v_e_5465_, v___y_5466_, v___y_5467_);
lean_dec(v___y_5467_);
lean_dec_ref(v___y_5466_);
return v_res_5469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_erasePatternRefAnnotations(lean_object* v_e_5471_, lean_object* v_a_5472_, lean_object* v_a_5473_){
_start:
{
lean_object* v___f_5475_; lean_object* v___f_5476_; lean_object* v___x_5477_; 
v___f_5475_ = ((lean_object*)(l_Lean_Meta_eraseInaccessibleAnnotations___closed__0));
v___f_5476_ = ((lean_object*)(l_Lean_Meta_erasePatternRefAnnotations___closed__0));
v___x_5477_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_5471_, v___f_5475_, v___f_5476_, v_a_5472_, v_a_5473_);
return v___x_5477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_erasePatternRefAnnotations___boxed(lean_object* v_e_5478_, lean_object* v_a_5479_, lean_object* v_a_5480_, lean_object* v_a_5481_){
_start:
{
lean_object* v_res_5482_; 
v_res_5482_ = l_Lean_Meta_erasePatternRefAnnotations(v_e_5478_, v_a_5479_, v_a_5480_);
lean_dec(v_a_5480_);
lean_dec_ref(v_a_5479_);
return v_res_5482_;
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
