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
lean_object* lean_obj_tag_nat(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_TransformStep_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TransformStep_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_TransformStep_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_TransformStep_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lean_TransformStep_ctorIdx___impl(v_x_3_);
lean_dec_ref(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_TransformStep_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
if (lean_obj_tag(v_t_5_) == 2)
{
lean_object* v_e_x3f_7_; lean_object* v___x_8_; 
v_e_x3f_7_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_e_x3f_7_);
lean_dec_ref_known(v_t_5_, 1);
v___x_8_ = lean_apply_1(v_k_6_, v_e_x3f_7_);
return v___x_8_;
}
else
{
lean_object* v_e_9_; lean_object* v___x_10_; 
v_e_9_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_e_9_);
lean_dec_ref(v_t_5_);
v___x_10_ = lean_apply_1(v_k_6_, v_e_9_);
return v___x_10_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TransformStep_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, lean_object* v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = l_Lean_TransformStep_ctorElim___redArg(v_t_13_, v_k_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_TransformStep_ctorElim___boxed(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Lean_TransformStep_ctorElim(v_motive_17_, v_ctorIdx_18_, v_t_19_, v_h_20_, v_k_21_);
lean_dec(v_ctorIdx_18_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_TransformStep_done_elim___redArg(lean_object* v_t_23_, lean_object* v_done_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = l_Lean_TransformStep_ctorElim___redArg(v_t_23_, v_done_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_TransformStep_done_elim(lean_object* v_motive_26_, lean_object* v_t_27_, lean_object* v_h_28_, lean_object* v_done_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = l_Lean_TransformStep_ctorElim___redArg(v_t_27_, v_done_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_TransformStep_visit_elim___redArg(lean_object* v_t_31_, lean_object* v_visit_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l_Lean_TransformStep_ctorElim___redArg(v_t_31_, v_visit_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_TransformStep_visit_elim(lean_object* v_motive_34_, lean_object* v_t_35_, lean_object* v_h_36_, lean_object* v_visit_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = l_Lean_TransformStep_ctorElim___redArg(v_t_35_, v_visit_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_TransformStep_continue_elim___redArg(lean_object* v_t_39_, lean_object* v_continue_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l_Lean_TransformStep_ctorElim___redArg(v_t_39_, v_continue_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_TransformStep_continue_elim(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_continue_45_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = l_Lean_TransformStep_ctorElim___redArg(v_t_43_, v_continue_45_);
return v___x_46_;
}
}
static lean_object* _init_l_Lean_instInhabitedTransformStep_default___closed__2(void){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_50_ = lean_box(0);
v___x_51_ = ((lean_object*)(l_Lean_instInhabitedTransformStep_default___closed__1));
v___x_52_ = l_Lean_Expr_const___override(v___x_51_, v___x_50_);
return v___x_52_;
}
}
static lean_object* _init_l_Lean_instInhabitedTransformStep_default___closed__3(void){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_53_ = lean_obj_once(&l_Lean_instInhabitedTransformStep_default___closed__2, &l_Lean_instInhabitedTransformStep_default___closed__2_once, _init_l_Lean_instInhabitedTransformStep_default___closed__2);
v___x_54_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_54_, 0, v___x_53_);
return v___x_54_;
}
}
static lean_object* _init_l_Lean_instInhabitedTransformStep_default(void){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = lean_obj_once(&l_Lean_instInhabitedTransformStep_default___closed__3, &l_Lean_instInhabitedTransformStep_default___closed__3_once, _init_l_Lean_instInhabitedTransformStep_default___closed__3);
return v___x_55_;
}
}
static lean_object* _init_l_Lean_instInhabitedTransformStep(void){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = l_Lean_instInhabitedTransformStep_default;
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_instReprTransformStep_repr_spec__0(lean_object* v_x_63_, lean_object* v_x_64_){
_start:
{
if (lean_obj_tag(v_x_63_) == 0)
{
lean_object* v___x_65_; 
v___x_65_ = ((lean_object*)(l_Option_repr___at___00Lean_instReprTransformStep_repr_spec__0___closed__1));
return v___x_65_;
}
else
{
lean_object* v_val_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v_val_66_ = lean_ctor_get(v_x_63_, 0);
lean_inc(v_val_66_);
lean_dec_ref_known(v_x_63_, 1);
v___x_67_ = ((lean_object*)(l_Option_repr___at___00Lean_instReprTransformStep_repr_spec__0___closed__3));
v___x_68_ = lean_unsigned_to_nat(1024u);
v___x_69_ = l_Lean_instReprExpr_repr(v_val_66_, v___x_68_);
v___x_70_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_70_, 0, v___x_67_);
lean_ctor_set(v___x_70_, 1, v___x_69_);
v___x_71_ = l_Repr_addAppParen(v___x_70_, v_x_64_);
return v___x_71_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_instReprTransformStep_repr_spec__0___boxed(lean_object* v_x_72_, lean_object* v_x_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l_Option_repr___at___00Lean_instReprTransformStep_repr_spec__0(v_x_72_, v_x_73_);
lean_dec(v_x_73_);
return v_res_74_;
}
}
static lean_object* _init_l_Lean_instReprTransformStep_repr___closed__3(void){
_start:
{
lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_81_ = lean_unsigned_to_nat(2u);
v___x_82_ = lean_nat_to_int(v___x_81_);
return v___x_82_;
}
}
static lean_object* _init_l_Lean_instReprTransformStep_repr___closed__4(void){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_83_ = lean_unsigned_to_nat(1u);
v___x_84_ = lean_nat_to_int(v___x_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprTransformStep_repr(lean_object* v_x_97_, lean_object* v_prec_98_){
_start:
{
switch(lean_obj_tag(v_x_97_))
{
case 0:
{
lean_object* v_e_99_; lean_object* v___y_101_; lean_object* v___x_110_; uint8_t v___x_111_; 
v_e_99_ = lean_ctor_get(v_x_97_, 0);
lean_inc_ref(v_e_99_);
lean_dec_ref_known(v_x_97_, 1);
v___x_110_ = lean_unsigned_to_nat(1024u);
v___x_111_ = lean_nat_dec_le(v___x_110_, v_prec_98_);
if (v___x_111_ == 0)
{
lean_object* v___x_112_; 
v___x_112_ = lean_obj_once(&l_Lean_instReprTransformStep_repr___closed__3, &l_Lean_instReprTransformStep_repr___closed__3_once, _init_l_Lean_instReprTransformStep_repr___closed__3);
v___y_101_ = v___x_112_;
goto v___jp_100_;
}
else
{
lean_object* v___x_113_; 
v___x_113_ = lean_obj_once(&l_Lean_instReprTransformStep_repr___closed__4, &l_Lean_instReprTransformStep_repr___closed__4_once, _init_l_Lean_instReprTransformStep_repr___closed__4);
v___y_101_ = v___x_113_;
goto v___jp_100_;
}
v___jp_100_:
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; uint8_t v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_102_ = ((lean_object*)(l_Lean_instReprTransformStep_repr___closed__2));
v___x_103_ = lean_unsigned_to_nat(1024u);
v___x_104_ = l_Lean_instReprExpr_repr(v_e_99_, v___x_103_);
v___x_105_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_105_, 0, v___x_102_);
lean_ctor_set(v___x_105_, 1, v___x_104_);
lean_inc(v___y_101_);
v___x_106_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_106_, 0, v___y_101_);
lean_ctor_set(v___x_106_, 1, v___x_105_);
v___x_107_ = 0;
v___x_108_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_108_, 0, v___x_106_);
lean_ctor_set_uint8(v___x_108_, sizeof(void*)*1, v___x_107_);
v___x_109_ = l_Repr_addAppParen(v___x_108_, v_prec_98_);
return v___x_109_;
}
}
case 1:
{
lean_object* v_e_114_; lean_object* v___y_116_; lean_object* v___x_125_; uint8_t v___x_126_; 
v_e_114_ = lean_ctor_get(v_x_97_, 0);
lean_inc_ref(v_e_114_);
lean_dec_ref_known(v_x_97_, 1);
v___x_125_ = lean_unsigned_to_nat(1024u);
v___x_126_ = lean_nat_dec_le(v___x_125_, v_prec_98_);
if (v___x_126_ == 0)
{
lean_object* v___x_127_; 
v___x_127_ = lean_obj_once(&l_Lean_instReprTransformStep_repr___closed__3, &l_Lean_instReprTransformStep_repr___closed__3_once, _init_l_Lean_instReprTransformStep_repr___closed__3);
v___y_116_ = v___x_127_;
goto v___jp_115_;
}
else
{
lean_object* v___x_128_; 
v___x_128_ = lean_obj_once(&l_Lean_instReprTransformStep_repr___closed__4, &l_Lean_instReprTransformStep_repr___closed__4_once, _init_l_Lean_instReprTransformStep_repr___closed__4);
v___y_116_ = v___x_128_;
goto v___jp_115_;
}
v___jp_115_:
{
lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; uint8_t v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_117_ = ((lean_object*)(l_Lean_instReprTransformStep_repr___closed__7));
v___x_118_ = lean_unsigned_to_nat(1024u);
v___x_119_ = l_Lean_instReprExpr_repr(v_e_114_, v___x_118_);
v___x_120_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_120_, 0, v___x_117_);
lean_ctor_set(v___x_120_, 1, v___x_119_);
lean_inc(v___y_116_);
v___x_121_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_121_, 0, v___y_116_);
lean_ctor_set(v___x_121_, 1, v___x_120_);
v___x_122_ = 0;
v___x_123_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_123_, 0, v___x_121_);
lean_ctor_set_uint8(v___x_123_, sizeof(void*)*1, v___x_122_);
v___x_124_ = l_Repr_addAppParen(v___x_123_, v_prec_98_);
return v___x_124_;
}
}
default: 
{
lean_object* v_e_x3f_129_; lean_object* v___y_131_; lean_object* v___x_140_; uint8_t v___x_141_; 
v_e_x3f_129_ = lean_ctor_get(v_x_97_, 0);
lean_inc(v_e_x3f_129_);
lean_dec_ref_known(v_x_97_, 1);
v___x_140_ = lean_unsigned_to_nat(1024u);
v___x_141_ = lean_nat_dec_le(v___x_140_, v_prec_98_);
if (v___x_141_ == 0)
{
lean_object* v___x_142_; 
v___x_142_ = lean_obj_once(&l_Lean_instReprTransformStep_repr___closed__3, &l_Lean_instReprTransformStep_repr___closed__3_once, _init_l_Lean_instReprTransformStep_repr___closed__3);
v___y_131_ = v___x_142_;
goto v___jp_130_;
}
else
{
lean_object* v___x_143_; 
v___x_143_ = lean_obj_once(&l_Lean_instReprTransformStep_repr___closed__4, &l_Lean_instReprTransformStep_repr___closed__4_once, _init_l_Lean_instReprTransformStep_repr___closed__4);
v___y_131_ = v___x_143_;
goto v___jp_130_;
}
v___jp_130_:
{
lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; uint8_t v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_132_ = ((lean_object*)(l_Lean_instReprTransformStep_repr___closed__10));
v___x_133_ = lean_unsigned_to_nat(1024u);
v___x_134_ = l_Option_repr___at___00Lean_instReprTransformStep_repr_spec__0(v_e_x3f_129_, v___x_133_);
v___x_135_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_135_, 0, v___x_132_);
lean_ctor_set(v___x_135_, 1, v___x_134_);
lean_inc(v___y_131_);
v___x_136_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_136_, 0, v___y_131_);
lean_ctor_set(v___x_136_, 1, v___x_135_);
v___x_137_ = 0;
v___x_138_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_138_, 0, v___x_136_);
lean_ctor_set_uint8(v___x_138_, sizeof(void*)*1, v___x_137_);
v___x_139_ = l_Repr_addAppParen(v___x_138_, v_prec_98_);
return v___x_139_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprTransformStep_repr___boxed(lean_object* v_x_144_, lean_object* v_prec_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l_Lean_instReprTransformStep_repr(v_x_144_, v_prec_145_);
lean_dec(v_prec_145_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__0(lean_object* v_toApplicative_149_, lean_object* v_a_150_, lean_object* v_a_151_){
_start:
{
lean_object* v_toPure_152_; lean_object* v___x_153_; 
v_toPure_152_ = lean_ctor_get(v_toApplicative_149_, 1);
lean_inc(v_toPure_152_);
lean_dec_ref(v_toApplicative_149_);
v___x_153_ = lean_apply_2(v_toPure_152_, lean_box(0), v_a_150_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__1(lean_object* v___x_154_, lean_object* v___x_155_, lean_object* v_e_156_, lean_object* v_a_157_, lean_object* v_s_158_){
_start:
{
lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_159_ = lean_box(0);
v___x_160_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_154_, v___x_155_, v_s_158_, v_e_156_, v_a_157_);
v___x_161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_161_, 0, v___x_159_);
lean_ctor_set(v___x_161_, 1, v___x_160_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__2(lean_object* v_toApplicative_162_, lean_object* v___x_163_, lean_object* v___x_164_, lean_object* v_e_165_, lean_object* v_a_166_, lean_object* v_x_167_, lean_object* v_toBind_168_, lean_object* v_a_169_){
_start:
{
lean_object* v___f_170_; lean_object* v___f_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
lean_inc_ref(v_a_169_);
v___f_170_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__0), 3, 2);
lean_closure_set(v___f_170_, 0, v_toApplicative_162_);
lean_closure_set(v___f_170_, 1, v_a_169_);
v___f_171_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__1), 5, 4);
lean_closure_set(v___f_171_, 0, v___x_163_);
lean_closure_set(v___f_171_, 1, v___x_164_);
lean_closure_set(v___f_171_, 2, v_e_165_);
lean_closure_set(v___f_171_, 3, v_a_169_);
lean_inc(v_a_166_);
v___x_172_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_172_, 0, lean_box(0));
lean_closure_set(v___x_172_, 1, lean_box(0));
lean_closure_set(v___x_172_, 2, lean_box(0));
lean_closure_set(v___x_172_, 3, v_a_166_);
lean_closure_set(v___x_172_, 4, v___f_171_);
v___x_173_ = lean_apply_2(v_x_167_, lean_box(0), v___x_172_);
v___x_174_ = lean_apply_4(v_toBind_168_, lean_box(0), lean_box(0), v___x_173_, v___f_170_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__2___boxed(lean_object* v_toApplicative_175_, lean_object* v___x_176_, lean_object* v___x_177_, lean_object* v_e_178_, lean_object* v_a_179_, lean_object* v_x_180_, lean_object* v_toBind_181_, lean_object* v_a_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__2(v_toApplicative_175_, v___x_176_, v___x_177_, v_e_178_, v_a_179_, v_x_180_, v_toBind_181_, v_a_182_);
lean_dec(v_a_179_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__3(lean_object* v_toApplicative_184_, lean_object* v___x_185_, lean_object* v___x_186_, lean_object* v_e_187_, lean_object* v_a_188_){
_start:
{
lean_object* v_toPure_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v_toPure_189_ = lean_ctor_get(v_toApplicative_184_, 1);
lean_inc(v_toPure_189_);
lean_dec_ref(v_toApplicative_184_);
v___x_190_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___x_185_, v___x_186_, v_a_188_, v_e_187_);
v___x_191_ = lean_apply_2(v_toPure_189_, lean_box(0), v___x_190_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__3___boxed(lean_object* v_toApplicative_192_, lean_object* v___x_193_, lean_object* v___x_194_, lean_object* v_e_195_, lean_object* v_a_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__3(v_toApplicative_192_, v___x_193_, v___x_194_, v_e_195_, v_a_196_);
lean_dec_ref(v_a_196_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__19(lean_object* v_inst_201_, lean_object* v_x_202_, lean_object* v___x_203_, lean_object* v___x_204_, lean_object* v_inst_205_, lean_object* v___f_206_, lean_object* v___x_207_, lean_object* v___x_208_, lean_object* v_a_209_, lean_object* v_toBind_210_, lean_object* v___f_211_, lean_object* v_toApplicative_212_, lean_object* v_a_213_){
_start:
{
if (lean_obj_tag(v_a_213_) == 0)
{
lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_2533__overap_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
lean_dec_ref(v_toApplicative_212_);
v___x_214_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__19___closed__1));
v___x_215_ = lean_apply_2(v_inst_201_, lean_box(0), v___x_214_);
lean_inc_ref(v___x_204_);
lean_inc_ref(v___x_203_);
v___x_216_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonadLift___aux__1___boxed), 10, 9);
lean_closure_set(v___x_216_, 0, lean_box(0));
lean_closure_set(v___x_216_, 1, lean_box(0));
lean_closure_set(v___x_216_, 2, lean_box(0));
lean_closure_set(v___x_216_, 3, lean_box(0));
lean_closure_set(v___x_216_, 4, v_x_202_);
lean_closure_set(v___x_216_, 5, v___x_203_);
lean_closure_set(v___x_216_, 6, v___x_204_);
lean_closure_set(v___x_216_, 7, lean_box(0));
lean_closure_set(v___x_216_, 8, v___x_215_);
v___x_217_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonad___aux__13___boxed), 13, 12);
lean_closure_set(v___x_217_, 0, lean_box(0));
lean_closure_set(v___x_217_, 1, lean_box(0));
lean_closure_set(v___x_217_, 2, lean_box(0));
lean_closure_set(v___x_217_, 3, lean_box(0));
lean_closure_set(v___x_217_, 4, v_x_202_);
lean_closure_set(v___x_217_, 5, v___x_203_);
lean_closure_set(v___x_217_, 6, v___x_204_);
lean_closure_set(v___x_217_, 7, v_inst_205_);
lean_closure_set(v___x_217_, 8, lean_box(0));
lean_closure_set(v___x_217_, 9, lean_box(0));
lean_closure_set(v___x_217_, 10, v___x_216_);
lean_closure_set(v___x_217_, 11, v___f_206_);
v___x_2533__overap_218_ = l_Lean_Core_withIncRecDepth___redArg(v___x_207_, v___x_208_, v___x_217_);
lean_inc(v_a_209_);
v___x_219_ = lean_apply_1(v___x_2533__overap_218_, v_a_209_);
v___x_220_ = lean_apply_4(v_toBind_210_, lean_box(0), lean_box(0), v___x_219_, v___f_211_);
return v___x_220_;
}
else
{
lean_object* v_val_221_; lean_object* v_toPure_222_; lean_object* v___x_223_; 
lean_dec(v___f_211_);
lean_dec(v_toBind_210_);
lean_dec_ref(v___x_208_);
lean_dec_ref(v___x_207_);
lean_dec(v___f_206_);
lean_dec_ref(v_inst_205_);
lean_dec_ref(v___x_204_);
lean_dec_ref(v___x_203_);
lean_dec(v_inst_201_);
v_val_221_ = lean_ctor_get(v_a_213_, 0);
lean_inc(v_val_221_);
lean_dec_ref_known(v_a_213_, 1);
v_toPure_222_ = lean_ctor_get(v_toApplicative_212_, 1);
lean_inc(v_toPure_222_);
lean_dec_ref(v_toApplicative_212_);
v___x_223_ = lean_apply_2(v_toPure_222_, lean_box(0), v_val_221_);
return v___x_223_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__19___boxed(lean_object* v_inst_224_, lean_object* v_x_225_, lean_object* v___x_226_, lean_object* v___x_227_, lean_object* v_inst_228_, lean_object* v___f_229_, lean_object* v___x_230_, lean_object* v___x_231_, lean_object* v_a_232_, lean_object* v_toBind_233_, lean_object* v___f_234_, lean_object* v_toApplicative_235_, lean_object* v_a_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__19(v_inst_224_, v_x_225_, v___x_226_, v___x_227_, v_inst_228_, v___f_229_, v___x_230_, v___x_231_, v_a_232_, v_toBind_233_, v___f_234_, v_toApplicative_235_, v_a_236_);
lean_dec(v_a_232_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__4(lean_object* v_a_240_, lean_object* v_inst_241_, lean_object* v_inst_242_, lean_object* v_inst_243_, lean_object* v_pre_244_, lean_object* v_post_245_, lean_object* v_x_246_, lean_object* v_x_247_, lean_object* v___y_248_, lean_object* v_a_249_){
_start:
{
lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_250_ = l_Lean_mkAppN(v_a_240_, v_a_249_);
v___x_251_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_241_, v_inst_242_, v_inst_243_, v_pre_244_, v_post_245_, v_x_246_, v_x_247_, v___x_250_, v___y_248_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__4___boxed(lean_object* v_a_252_, lean_object* v_inst_253_, lean_object* v_inst_254_, lean_object* v_inst_255_, lean_object* v_pre_256_, lean_object* v_post_257_, lean_object* v_x_258_, lean_object* v_x_259_, lean_object* v___y_260_, lean_object* v_a_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__4(v_a_252_, v_inst_253_, v_inst_254_, v_inst_255_, v_pre_256_, v_post_257_, v_x_258_, v_x_259_, v___y_260_, v_a_261_);
lean_dec_ref(v_a_261_);
lean_dec(v___y_260_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___boxed(lean_object* v_inst_263_, lean_object* v_inst_264_, lean_object* v_inst_265_, lean_object* v_pre_266_, lean_object* v_post_267_, lean_object* v_x_268_, lean_object* v_x_269_, lean_object* v_e_270_, lean_object* v_a_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_263_, v_inst_264_, v_inst_265_, v_pre_266_, v_post_267_, v_x_268_, v_x_269_, v_e_270_, v_a_271_);
lean_dec(v_a_271_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__5(lean_object* v_inst_273_, lean_object* v_inst_274_, lean_object* v_inst_275_, lean_object* v_pre_276_, lean_object* v_post_277_, lean_object* v_x_278_, lean_object* v_x_279_, lean_object* v___y_280_, lean_object* v_args_281_, lean_object* v___x_282_, lean_object* v_toBind_283_, lean_object* v_a_284_){
_start:
{
lean_object* v___f_285_; lean_object* v___x_286_; size_t v_sz_287_; size_t v___x_288_; lean_object* v___x_2263__overap_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
lean_inc_n(v___y_280_, 2);
lean_inc(v_x_279_);
lean_inc(v_post_277_);
lean_inc(v_pre_276_);
lean_inc_ref(v_inst_275_);
lean_inc(v_inst_274_);
lean_inc_ref(v_inst_273_);
v___f_285_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__4___boxed), 10, 9);
lean_closure_set(v___f_285_, 0, v_a_284_);
lean_closure_set(v___f_285_, 1, v_inst_273_);
lean_closure_set(v___f_285_, 2, v_inst_274_);
lean_closure_set(v___f_285_, 3, v_inst_275_);
lean_closure_set(v___f_285_, 4, v_pre_276_);
lean_closure_set(v___f_285_, 5, v_post_277_);
lean_closure_set(v___f_285_, 6, v_x_278_);
lean_closure_set(v___f_285_, 7, v_x_279_);
lean_closure_set(v___f_285_, 8, v___y_280_);
v___x_286_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___boxed), 9, 7);
lean_closure_set(v___x_286_, 0, v_inst_273_);
lean_closure_set(v___x_286_, 1, v_inst_274_);
lean_closure_set(v___x_286_, 2, v_inst_275_);
lean_closure_set(v___x_286_, 3, v_pre_276_);
lean_closure_set(v___x_286_, 4, v_post_277_);
lean_closure_set(v___x_286_, 5, v_x_278_);
lean_closure_set(v___x_286_, 6, v_x_279_);
v_sz_287_ = lean_array_size(v_args_281_);
v___x_288_ = ((size_t)0ULL);
v___x_2263__overap_289_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_282_, v___x_286_, v_sz_287_, v___x_288_, v_args_281_);
v___x_290_ = lean_apply_1(v___x_2263__overap_289_, v___y_280_);
v___x_291_ = lean_apply_4(v_toBind_283_, lean_box(0), lean_box(0), v___x_290_, v___f_285_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__5___boxed(lean_object* v_inst_292_, lean_object* v_inst_293_, lean_object* v_inst_294_, lean_object* v_pre_295_, lean_object* v_post_296_, lean_object* v_x_297_, lean_object* v_x_298_, lean_object* v___y_299_, lean_object* v_args_300_, lean_object* v___x_301_, lean_object* v_toBind_302_, lean_object* v_a_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__5(v_inst_292_, v_inst_293_, v_inst_294_, v_pre_295_, v_post_296_, v_x_297_, v_x_298_, v___y_299_, v_args_300_, v___x_301_, v_toBind_302_, v_a_303_);
lean_dec(v___y_299_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__6(lean_object* v_inst_305_, lean_object* v_inst_306_, lean_object* v_inst_307_, lean_object* v_pre_308_, lean_object* v_post_309_, lean_object* v_x_310_, lean_object* v_x_311_, lean_object* v___x_312_, lean_object* v_toBind_313_, lean_object* v_f_314_, lean_object* v_args_315_, lean_object* v___y_316_){
_start:
{
lean_object* v___f_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
lean_inc(v_toBind_313_);
lean_inc(v___y_316_);
lean_inc(v_x_311_);
lean_inc(v_post_309_);
lean_inc(v_pre_308_);
lean_inc_ref(v_inst_307_);
lean_inc(v_inst_306_);
lean_inc_ref(v_inst_305_);
v___f_317_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__5___boxed), 12, 11);
lean_closure_set(v___f_317_, 0, v_inst_305_);
lean_closure_set(v___f_317_, 1, v_inst_306_);
lean_closure_set(v___f_317_, 2, v_inst_307_);
lean_closure_set(v___f_317_, 3, v_pre_308_);
lean_closure_set(v___f_317_, 4, v_post_309_);
lean_closure_set(v___f_317_, 5, v_x_310_);
lean_closure_set(v___f_317_, 6, v_x_311_);
lean_closure_set(v___f_317_, 7, v___y_316_);
lean_closure_set(v___f_317_, 8, v_args_315_);
lean_closure_set(v___f_317_, 9, v___x_312_);
lean_closure_set(v___f_317_, 10, v_toBind_313_);
v___x_318_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_305_, v_inst_306_, v_inst_307_, v_pre_308_, v_post_309_, v_x_310_, v_x_311_, v_f_314_, v___y_316_);
v___x_319_ = lean_apply_4(v_toBind_313_, lean_box(0), lean_box(0), v___x_318_, v___f_317_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__6___boxed(lean_object* v_inst_320_, lean_object* v_inst_321_, lean_object* v_inst_322_, lean_object* v_pre_323_, lean_object* v_post_324_, lean_object* v_x_325_, lean_object* v_x_326_, lean_object* v___x_327_, lean_object* v_toBind_328_, lean_object* v_f_329_, lean_object* v_args_330_, lean_object* v___y_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__6(v_inst_320_, v_inst_321_, v_inst_322_, v_pre_323_, v_post_324_, v_x_325_, v_x_326_, v___x_327_, v_toBind_328_, v_f_329_, v_args_330_, v___y_331_);
lean_dec(v___y_331_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__7___boxed(lean_object* v_inst_333_, lean_object* v_inst_334_, lean_object* v_inst_335_, lean_object* v_pre_336_, lean_object* v_post_337_, lean_object* v_x_338_, lean_object* v_x_339_, lean_object* v___y_340_, lean_object* v_a_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__7(v_inst_333_, v_inst_334_, v_inst_335_, v_pre_336_, v_post_337_, v_x_338_, v_x_339_, v___y_340_, v_a_341_);
lean_dec(v___y_340_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__8(lean_object* v_binderType_343_, lean_object* v_a_344_, lean_object* v_binderName_345_, uint8_t v_binderInfo_346_, lean_object* v_inst_347_, lean_object* v_inst_348_, lean_object* v_inst_349_, lean_object* v_pre_350_, lean_object* v_post_351_, lean_object* v_x_352_, lean_object* v_x_353_, lean_object* v___y_354_, lean_object* v_body_355_, lean_object* v___y_356_, lean_object* v_a_357_){
_start:
{
size_t v___x_358_; size_t v___x_359_; uint8_t v___x_360_; 
v___x_358_ = lean_ptr_addr(v_binderType_343_);
v___x_359_ = lean_ptr_addr(v_a_344_);
v___x_360_ = lean_usize_dec_eq(v___x_358_, v___x_359_);
if (v___x_360_ == 0)
{
lean_object* v___x_361_; lean_object* v___x_362_; 
lean_dec_ref(v___y_356_);
v___x_361_ = l_Lean_Expr_forallE___override(v_binderName_345_, v_a_344_, v_a_357_, v_binderInfo_346_);
v___x_362_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_347_, v_inst_348_, v_inst_349_, v_pre_350_, v_post_351_, v_x_352_, v_x_353_, v___x_361_, v___y_354_);
return v___x_362_;
}
else
{
size_t v___x_363_; size_t v___x_364_; uint8_t v___x_365_; 
v___x_363_ = lean_ptr_addr(v_body_355_);
v___x_364_ = lean_ptr_addr(v_a_357_);
v___x_365_ = lean_usize_dec_eq(v___x_363_, v___x_364_);
if (v___x_365_ == 0)
{
lean_object* v___x_366_; lean_object* v___x_367_; 
lean_dec_ref(v___y_356_);
v___x_366_ = l_Lean_Expr_forallE___override(v_binderName_345_, v_a_344_, v_a_357_, v_binderInfo_346_);
v___x_367_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_347_, v_inst_348_, v_inst_349_, v_pre_350_, v_post_351_, v_x_352_, v_x_353_, v___x_366_, v___y_354_);
return v___x_367_;
}
else
{
uint8_t v___x_368_; 
v___x_368_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_346_, v_binderInfo_346_);
if (v___x_368_ == 0)
{
lean_object* v___x_369_; lean_object* v___x_370_; 
lean_dec_ref(v___y_356_);
v___x_369_ = l_Lean_Expr_forallE___override(v_binderName_345_, v_a_344_, v_a_357_, v_binderInfo_346_);
v___x_370_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_347_, v_inst_348_, v_inst_349_, v_pre_350_, v_post_351_, v_x_352_, v_x_353_, v___x_369_, v___y_354_);
return v___x_370_;
}
else
{
lean_object* v___x_371_; 
lean_dec_ref(v_a_357_);
lean_dec(v_binderName_345_);
lean_dec_ref(v_a_344_);
v___x_371_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_347_, v_inst_348_, v_inst_349_, v_pre_350_, v_post_351_, v_x_352_, v_x_353_, v___y_356_, v___y_354_);
return v___x_371_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__8___boxed(lean_object* v_binderType_372_, lean_object* v_a_373_, lean_object* v_binderName_374_, lean_object* v_binderInfo_375_, lean_object* v_inst_376_, lean_object* v_inst_377_, lean_object* v_inst_378_, lean_object* v_pre_379_, lean_object* v_post_380_, lean_object* v_x_381_, lean_object* v_x_382_, lean_object* v___y_383_, lean_object* v_body_384_, lean_object* v___y_385_, lean_object* v_a_386_){
_start:
{
uint8_t v_binderInfo_2857__boxed_387_; lean_object* v_res_388_; 
v_binderInfo_2857__boxed_387_ = lean_unbox(v_binderInfo_375_);
v_res_388_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__8(v_binderType_372_, v_a_373_, v_binderName_374_, v_binderInfo_2857__boxed_387_, v_inst_376_, v_inst_377_, v_inst_378_, v_pre_379_, v_post_380_, v_x_381_, v_x_382_, v___y_383_, v_body_384_, v___y_385_, v_a_386_);
lean_dec_ref(v_body_384_);
lean_dec(v___y_383_);
lean_dec_ref(v_binderType_372_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__9(lean_object* v_binderType_389_, lean_object* v_binderName_390_, uint8_t v_binderInfo_391_, lean_object* v_inst_392_, lean_object* v_inst_393_, lean_object* v_inst_394_, lean_object* v_pre_395_, lean_object* v_post_396_, lean_object* v_x_397_, lean_object* v_x_398_, lean_object* v___y_399_, lean_object* v_body_400_, lean_object* v___y_401_, lean_object* v_toBind_402_, lean_object* v_a_403_){
_start:
{
lean_object* v___x_404_; lean_object* v___f_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_404_ = lean_box(v_binderInfo_391_);
lean_inc_ref(v_body_400_);
lean_inc(v___y_399_);
lean_inc(v_x_398_);
lean_inc(v_post_396_);
lean_inc(v_pre_395_);
lean_inc_ref(v_inst_394_);
lean_inc(v_inst_393_);
lean_inc_ref(v_inst_392_);
v___f_405_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__8___boxed), 15, 14);
lean_closure_set(v___f_405_, 0, v_binderType_389_);
lean_closure_set(v___f_405_, 1, v_a_403_);
lean_closure_set(v___f_405_, 2, v_binderName_390_);
lean_closure_set(v___f_405_, 3, v___x_404_);
lean_closure_set(v___f_405_, 4, v_inst_392_);
lean_closure_set(v___f_405_, 5, v_inst_393_);
lean_closure_set(v___f_405_, 6, v_inst_394_);
lean_closure_set(v___f_405_, 7, v_pre_395_);
lean_closure_set(v___f_405_, 8, v_post_396_);
lean_closure_set(v___f_405_, 9, v_x_397_);
lean_closure_set(v___f_405_, 10, v_x_398_);
lean_closure_set(v___f_405_, 11, v___y_399_);
lean_closure_set(v___f_405_, 12, v_body_400_);
lean_closure_set(v___f_405_, 13, v___y_401_);
v___x_406_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_392_, v_inst_393_, v_inst_394_, v_pre_395_, v_post_396_, v_x_397_, v_x_398_, v_body_400_, v___y_399_);
v___x_407_ = lean_apply_4(v_toBind_402_, lean_box(0), lean_box(0), v___x_406_, v___f_405_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__9___boxed(lean_object* v_binderType_408_, lean_object* v_binderName_409_, lean_object* v_binderInfo_410_, lean_object* v_inst_411_, lean_object* v_inst_412_, lean_object* v_inst_413_, lean_object* v_pre_414_, lean_object* v_post_415_, lean_object* v_x_416_, lean_object* v_x_417_, lean_object* v___y_418_, lean_object* v_body_419_, lean_object* v___y_420_, lean_object* v_toBind_421_, lean_object* v_a_422_){
_start:
{
uint8_t v_binderInfo_2718__boxed_423_; lean_object* v_res_424_; 
v_binderInfo_2718__boxed_423_ = lean_unbox(v_binderInfo_410_);
v_res_424_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__9(v_binderType_408_, v_binderName_409_, v_binderInfo_2718__boxed_423_, v_inst_411_, v_inst_412_, v_inst_413_, v_pre_414_, v_post_415_, v_x_416_, v_x_417_, v___y_418_, v_body_419_, v___y_420_, v_toBind_421_, v_a_422_);
lean_dec(v___y_418_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__10(lean_object* v_binderType_425_, lean_object* v_a_426_, lean_object* v_binderName_427_, uint8_t v_binderInfo_428_, lean_object* v_inst_429_, lean_object* v_inst_430_, lean_object* v_inst_431_, lean_object* v_pre_432_, lean_object* v_post_433_, lean_object* v_x_434_, lean_object* v_x_435_, lean_object* v___y_436_, lean_object* v_body_437_, lean_object* v___y_438_, lean_object* v_a_439_){
_start:
{
size_t v___x_440_; size_t v___x_441_; uint8_t v___x_442_; 
v___x_440_ = lean_ptr_addr(v_binderType_425_);
v___x_441_ = lean_ptr_addr(v_a_426_);
v___x_442_ = lean_usize_dec_eq(v___x_440_, v___x_441_);
if (v___x_442_ == 0)
{
lean_object* v___x_443_; lean_object* v___x_444_; 
lean_dec_ref(v___y_438_);
v___x_443_ = l_Lean_Expr_lam___override(v_binderName_427_, v_a_426_, v_a_439_, v_binderInfo_428_);
v___x_444_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_429_, v_inst_430_, v_inst_431_, v_pre_432_, v_post_433_, v_x_434_, v_x_435_, v___x_443_, v___y_436_);
return v___x_444_;
}
else
{
size_t v___x_445_; size_t v___x_446_; uint8_t v___x_447_; 
v___x_445_ = lean_ptr_addr(v_body_437_);
v___x_446_ = lean_ptr_addr(v_a_439_);
v___x_447_ = lean_usize_dec_eq(v___x_445_, v___x_446_);
if (v___x_447_ == 0)
{
lean_object* v___x_448_; lean_object* v___x_449_; 
lean_dec_ref(v___y_438_);
v___x_448_ = l_Lean_Expr_lam___override(v_binderName_427_, v_a_426_, v_a_439_, v_binderInfo_428_);
v___x_449_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_429_, v_inst_430_, v_inst_431_, v_pre_432_, v_post_433_, v_x_434_, v_x_435_, v___x_448_, v___y_436_);
return v___x_449_;
}
else
{
uint8_t v___x_450_; 
v___x_450_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_428_, v_binderInfo_428_);
if (v___x_450_ == 0)
{
lean_object* v___x_451_; lean_object* v___x_452_; 
lean_dec_ref(v___y_438_);
v___x_451_ = l_Lean_Expr_lam___override(v_binderName_427_, v_a_426_, v_a_439_, v_binderInfo_428_);
v___x_452_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_429_, v_inst_430_, v_inst_431_, v_pre_432_, v_post_433_, v_x_434_, v_x_435_, v___x_451_, v___y_436_);
return v___x_452_;
}
else
{
lean_object* v___x_453_; 
lean_dec_ref(v_a_439_);
lean_dec(v_binderName_427_);
lean_dec_ref(v_a_426_);
v___x_453_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_429_, v_inst_430_, v_inst_431_, v_pre_432_, v_post_433_, v_x_434_, v_x_435_, v___y_438_, v___y_436_);
return v___x_453_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__10___boxed(lean_object* v_binderType_454_, lean_object* v_a_455_, lean_object* v_binderName_456_, lean_object* v_binderInfo_457_, lean_object* v_inst_458_, lean_object* v_inst_459_, lean_object* v_inst_460_, lean_object* v_pre_461_, lean_object* v_post_462_, lean_object* v_x_463_, lean_object* v_x_464_, lean_object* v___y_465_, lean_object* v_body_466_, lean_object* v___y_467_, lean_object* v_a_468_){
_start:
{
uint8_t v_binderInfo_2832__boxed_469_; lean_object* v_res_470_; 
v_binderInfo_2832__boxed_469_ = lean_unbox(v_binderInfo_457_);
v_res_470_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__10(v_binderType_454_, v_a_455_, v_binderName_456_, v_binderInfo_2832__boxed_469_, v_inst_458_, v_inst_459_, v_inst_460_, v_pre_461_, v_post_462_, v_x_463_, v_x_464_, v___y_465_, v_body_466_, v___y_467_, v_a_468_);
lean_dec_ref(v_body_466_);
lean_dec(v___y_465_);
lean_dec_ref(v_binderType_454_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__11(lean_object* v_binderType_471_, lean_object* v_binderName_472_, uint8_t v_binderInfo_473_, lean_object* v_inst_474_, lean_object* v_inst_475_, lean_object* v_inst_476_, lean_object* v_pre_477_, lean_object* v_post_478_, lean_object* v_x_479_, lean_object* v_x_480_, lean_object* v___y_481_, lean_object* v_body_482_, lean_object* v___y_483_, lean_object* v_toBind_484_, lean_object* v_a_485_){
_start:
{
lean_object* v___x_486_; lean_object* v___f_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_486_ = lean_box(v_binderInfo_473_);
lean_inc_ref(v_body_482_);
lean_inc(v___y_481_);
lean_inc(v_x_480_);
lean_inc(v_post_478_);
lean_inc(v_pre_477_);
lean_inc_ref(v_inst_476_);
lean_inc(v_inst_475_);
lean_inc_ref(v_inst_474_);
v___f_487_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__10___boxed), 15, 14);
lean_closure_set(v___f_487_, 0, v_binderType_471_);
lean_closure_set(v___f_487_, 1, v_a_485_);
lean_closure_set(v___f_487_, 2, v_binderName_472_);
lean_closure_set(v___f_487_, 3, v___x_486_);
lean_closure_set(v___f_487_, 4, v_inst_474_);
lean_closure_set(v___f_487_, 5, v_inst_475_);
lean_closure_set(v___f_487_, 6, v_inst_476_);
lean_closure_set(v___f_487_, 7, v_pre_477_);
lean_closure_set(v___f_487_, 8, v_post_478_);
lean_closure_set(v___f_487_, 9, v_x_479_);
lean_closure_set(v___f_487_, 10, v_x_480_);
lean_closure_set(v___f_487_, 11, v___y_481_);
lean_closure_set(v___f_487_, 12, v_body_482_);
lean_closure_set(v___f_487_, 13, v___y_483_);
v___x_488_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_474_, v_inst_475_, v_inst_476_, v_pre_477_, v_post_478_, v_x_479_, v_x_480_, v_body_482_, v___y_481_);
v___x_489_ = lean_apply_4(v_toBind_484_, lean_box(0), lean_box(0), v___x_488_, v___f_487_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__11___boxed(lean_object* v_binderType_490_, lean_object* v_binderName_491_, lean_object* v_binderInfo_492_, lean_object* v_inst_493_, lean_object* v_inst_494_, lean_object* v_inst_495_, lean_object* v_pre_496_, lean_object* v_post_497_, lean_object* v_x_498_, lean_object* v_x_499_, lean_object* v___y_500_, lean_object* v_body_501_, lean_object* v___y_502_, lean_object* v_toBind_503_, lean_object* v_a_504_){
_start:
{
uint8_t v_binderInfo_2664__boxed_505_; lean_object* v_res_506_; 
v_binderInfo_2664__boxed_505_ = lean_unbox(v_binderInfo_492_);
v_res_506_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__11(v_binderType_490_, v_binderName_491_, v_binderInfo_2664__boxed_505_, v_inst_493_, v_inst_494_, v_inst_495_, v_pre_496_, v_post_497_, v_x_498_, v_x_499_, v___y_500_, v_body_501_, v___y_502_, v_toBind_503_, v_a_504_);
lean_dec(v___y_500_);
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__12(lean_object* v_type_507_, lean_object* v_a_508_, lean_object* v_declName_509_, lean_object* v_a_510_, uint8_t v_nondep_511_, lean_object* v_inst_512_, lean_object* v_inst_513_, lean_object* v_inst_514_, lean_object* v_pre_515_, lean_object* v_post_516_, lean_object* v_x_517_, lean_object* v_x_518_, lean_object* v___y_519_, lean_object* v_value_520_, lean_object* v_body_521_, lean_object* v___y_522_, lean_object* v_a_523_){
_start:
{
size_t v___x_524_; size_t v___x_525_; uint8_t v___x_526_; 
v___x_524_ = lean_ptr_addr(v_type_507_);
v___x_525_ = lean_ptr_addr(v_a_508_);
v___x_526_ = lean_usize_dec_eq(v___x_524_, v___x_525_);
if (v___x_526_ == 0)
{
lean_object* v___x_527_; lean_object* v___x_528_; 
lean_dec_ref(v___y_522_);
v___x_527_ = l_Lean_Expr_letE___override(v_declName_509_, v_a_508_, v_a_510_, v_a_523_, v_nondep_511_);
v___x_528_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_512_, v_inst_513_, v_inst_514_, v_pre_515_, v_post_516_, v_x_517_, v_x_518_, v___x_527_, v___y_519_);
return v___x_528_;
}
else
{
size_t v___x_529_; size_t v___x_530_; uint8_t v___x_531_; 
v___x_529_ = lean_ptr_addr(v_value_520_);
v___x_530_ = lean_ptr_addr(v_a_510_);
v___x_531_ = lean_usize_dec_eq(v___x_529_, v___x_530_);
if (v___x_531_ == 0)
{
lean_object* v___x_532_; lean_object* v___x_533_; 
lean_dec_ref(v___y_522_);
v___x_532_ = l_Lean_Expr_letE___override(v_declName_509_, v_a_508_, v_a_510_, v_a_523_, v_nondep_511_);
v___x_533_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_512_, v_inst_513_, v_inst_514_, v_pre_515_, v_post_516_, v_x_517_, v_x_518_, v___x_532_, v___y_519_);
return v___x_533_;
}
else
{
size_t v___x_534_; size_t v___x_535_; uint8_t v___x_536_; 
v___x_534_ = lean_ptr_addr(v_body_521_);
v___x_535_ = lean_ptr_addr(v_a_523_);
v___x_536_ = lean_usize_dec_eq(v___x_534_, v___x_535_);
if (v___x_536_ == 0)
{
lean_object* v___x_537_; lean_object* v___x_538_; 
lean_dec_ref(v___y_522_);
v___x_537_ = l_Lean_Expr_letE___override(v_declName_509_, v_a_508_, v_a_510_, v_a_523_, v_nondep_511_);
v___x_538_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_512_, v_inst_513_, v_inst_514_, v_pre_515_, v_post_516_, v_x_517_, v_x_518_, v___x_537_, v___y_519_);
return v___x_538_;
}
else
{
lean_object* v___x_539_; 
lean_dec_ref(v_a_523_);
lean_dec_ref(v_a_510_);
lean_dec(v_declName_509_);
lean_dec_ref(v_a_508_);
v___x_539_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_512_, v_inst_513_, v_inst_514_, v_pre_515_, v_post_516_, v_x_517_, v_x_518_, v___y_522_, v___y_519_);
return v___x_539_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__12___boxed(lean_object** _args){
lean_object* v_type_540_ = _args[0];
lean_object* v_a_541_ = _args[1];
lean_object* v_declName_542_ = _args[2];
lean_object* v_a_543_ = _args[3];
lean_object* v_nondep_544_ = _args[4];
lean_object* v_inst_545_ = _args[5];
lean_object* v_inst_546_ = _args[6];
lean_object* v_inst_547_ = _args[7];
lean_object* v_pre_548_ = _args[8];
lean_object* v_post_549_ = _args[9];
lean_object* v_x_550_ = _args[10];
lean_object* v_x_551_ = _args[11];
lean_object* v___y_552_ = _args[12];
lean_object* v_value_553_ = _args[13];
lean_object* v_body_554_ = _args[14];
lean_object* v___y_555_ = _args[15];
lean_object* v_a_556_ = _args[16];
_start:
{
uint8_t v_nondep_2882__boxed_557_; lean_object* v_res_558_; 
v_nondep_2882__boxed_557_ = lean_unbox(v_nondep_544_);
v_res_558_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__12(v_type_540_, v_a_541_, v_declName_542_, v_a_543_, v_nondep_2882__boxed_557_, v_inst_545_, v_inst_546_, v_inst_547_, v_pre_548_, v_post_549_, v_x_550_, v_x_551_, v___y_552_, v_value_553_, v_body_554_, v___y_555_, v_a_556_);
lean_dec_ref(v_body_554_);
lean_dec_ref(v_value_553_);
lean_dec(v___y_552_);
lean_dec_ref(v_type_540_);
return v_res_558_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__13(lean_object* v_type_559_, lean_object* v_a_560_, lean_object* v_declName_561_, uint8_t v_nondep_562_, lean_object* v_inst_563_, lean_object* v_inst_564_, lean_object* v_inst_565_, lean_object* v_pre_566_, lean_object* v_post_567_, lean_object* v_x_568_, lean_object* v_x_569_, lean_object* v___y_570_, lean_object* v_value_571_, lean_object* v_body_572_, lean_object* v___y_573_, lean_object* v_toBind_574_, lean_object* v_a_575_){
_start:
{
lean_object* v___x_576_; lean_object* v___f_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_576_ = lean_box(v_nondep_562_);
lean_inc_ref(v_body_572_);
lean_inc(v___y_570_);
lean_inc(v_x_569_);
lean_inc(v_post_567_);
lean_inc(v_pre_566_);
lean_inc_ref(v_inst_565_);
lean_inc(v_inst_564_);
lean_inc_ref(v_inst_563_);
v___f_577_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__12___boxed), 17, 16);
lean_closure_set(v___f_577_, 0, v_type_559_);
lean_closure_set(v___f_577_, 1, v_a_560_);
lean_closure_set(v___f_577_, 2, v_declName_561_);
lean_closure_set(v___f_577_, 3, v_a_575_);
lean_closure_set(v___f_577_, 4, v___x_576_);
lean_closure_set(v___f_577_, 5, v_inst_563_);
lean_closure_set(v___f_577_, 6, v_inst_564_);
lean_closure_set(v___f_577_, 7, v_inst_565_);
lean_closure_set(v___f_577_, 8, v_pre_566_);
lean_closure_set(v___f_577_, 9, v_post_567_);
lean_closure_set(v___f_577_, 10, v_x_568_);
lean_closure_set(v___f_577_, 11, v_x_569_);
lean_closure_set(v___f_577_, 12, v___y_570_);
lean_closure_set(v___f_577_, 13, v_value_571_);
lean_closure_set(v___f_577_, 14, v_body_572_);
lean_closure_set(v___f_577_, 15, v___y_573_);
v___x_578_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_563_, v_inst_564_, v_inst_565_, v_pre_566_, v_post_567_, v_x_568_, v_x_569_, v_body_572_, v___y_570_);
v___x_579_ = lean_apply_4(v_toBind_574_, lean_box(0), lean_box(0), v___x_578_, v___f_577_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__13___boxed(lean_object** _args){
lean_object* v_type_580_ = _args[0];
lean_object* v_a_581_ = _args[1];
lean_object* v_declName_582_ = _args[2];
lean_object* v_nondep_583_ = _args[3];
lean_object* v_inst_584_ = _args[4];
lean_object* v_inst_585_ = _args[5];
lean_object* v_inst_586_ = _args[6];
lean_object* v_pre_587_ = _args[7];
lean_object* v_post_588_ = _args[8];
lean_object* v_x_589_ = _args[9];
lean_object* v_x_590_ = _args[10];
lean_object* v___y_591_ = _args[11];
lean_object* v_value_592_ = _args[12];
lean_object* v_body_593_ = _args[13];
lean_object* v___y_594_ = _args[14];
lean_object* v_toBind_595_ = _args[15];
lean_object* v_a_596_ = _args[16];
_start:
{
uint8_t v_nondep_2678__boxed_597_; lean_object* v_res_598_; 
v_nondep_2678__boxed_597_ = lean_unbox(v_nondep_583_);
v_res_598_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__13(v_type_580_, v_a_581_, v_declName_582_, v_nondep_2678__boxed_597_, v_inst_584_, v_inst_585_, v_inst_586_, v_pre_587_, v_post_588_, v_x_589_, v_x_590_, v___y_591_, v_value_592_, v_body_593_, v___y_594_, v_toBind_595_, v_a_596_);
lean_dec(v___y_591_);
return v_res_598_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__14(lean_object* v_type_599_, lean_object* v_declName_600_, uint8_t v_nondep_601_, lean_object* v_inst_602_, lean_object* v_inst_603_, lean_object* v_inst_604_, lean_object* v_pre_605_, lean_object* v_post_606_, lean_object* v_x_607_, lean_object* v_x_608_, lean_object* v___y_609_, lean_object* v_value_610_, lean_object* v_body_611_, lean_object* v___y_612_, lean_object* v_toBind_613_, lean_object* v_a_614_){
_start:
{
lean_object* v___x_615_; lean_object* v___f_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_615_ = lean_box(v_nondep_601_);
lean_inc(v_toBind_613_);
lean_inc_ref(v_value_610_);
lean_inc(v___y_609_);
lean_inc(v_x_608_);
lean_inc(v_post_606_);
lean_inc(v_pre_605_);
lean_inc_ref(v_inst_604_);
lean_inc(v_inst_603_);
lean_inc_ref(v_inst_602_);
v___f_616_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__13___boxed), 17, 16);
lean_closure_set(v___f_616_, 0, v_type_599_);
lean_closure_set(v___f_616_, 1, v_a_614_);
lean_closure_set(v___f_616_, 2, v_declName_600_);
lean_closure_set(v___f_616_, 3, v___x_615_);
lean_closure_set(v___f_616_, 4, v_inst_602_);
lean_closure_set(v___f_616_, 5, v_inst_603_);
lean_closure_set(v___f_616_, 6, v_inst_604_);
lean_closure_set(v___f_616_, 7, v_pre_605_);
lean_closure_set(v___f_616_, 8, v_post_606_);
lean_closure_set(v___f_616_, 9, v_x_607_);
lean_closure_set(v___f_616_, 10, v_x_608_);
lean_closure_set(v___f_616_, 11, v___y_609_);
lean_closure_set(v___f_616_, 12, v_value_610_);
lean_closure_set(v___f_616_, 13, v_body_611_);
lean_closure_set(v___f_616_, 14, v___y_612_);
lean_closure_set(v___f_616_, 15, v_toBind_613_);
v___x_617_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_602_, v_inst_603_, v_inst_604_, v_pre_605_, v_post_606_, v_x_607_, v_x_608_, v_value_610_, v___y_609_);
v___x_618_ = lean_apply_4(v_toBind_613_, lean_box(0), lean_box(0), v___x_617_, v___f_616_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__14___boxed(lean_object* v_type_619_, lean_object* v_declName_620_, lean_object* v_nondep_621_, lean_object* v_inst_622_, lean_object* v_inst_623_, lean_object* v_inst_624_, lean_object* v_pre_625_, lean_object* v_post_626_, lean_object* v_x_627_, lean_object* v_x_628_, lean_object* v___y_629_, lean_object* v_value_630_, lean_object* v_body_631_, lean_object* v___y_632_, lean_object* v_toBind_633_, lean_object* v_a_634_){
_start:
{
uint8_t v_nondep_2693__boxed_635_; lean_object* v_res_636_; 
v_nondep_2693__boxed_635_ = lean_unbox(v_nondep_621_);
v_res_636_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__14(v_type_619_, v_declName_620_, v_nondep_2693__boxed_635_, v_inst_622_, v_inst_623_, v_inst_624_, v_pre_625_, v_post_626_, v_x_627_, v_x_628_, v___y_629_, v_value_630_, v_body_631_, v___y_632_, v_toBind_633_, v_a_634_);
lean_dec(v___y_629_);
return v_res_636_;
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0(void){
_start:
{
lean_object* v___x_637_; lean_object* v_dummy_638_; 
v___x_637_ = lean_box(0);
v_dummy_638_ = l_Lean_Expr_sort___override(v___x_637_);
return v_dummy_638_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__15(lean_object* v_expr_639_, lean_object* v_data_640_, lean_object* v_inst_641_, lean_object* v_inst_642_, lean_object* v_inst_643_, lean_object* v_pre_644_, lean_object* v_post_645_, lean_object* v_x_646_, lean_object* v_x_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v_a_650_){
_start:
{
size_t v___x_651_; size_t v___x_652_; uint8_t v___x_653_; 
v___x_651_ = lean_ptr_addr(v_expr_639_);
v___x_652_ = lean_ptr_addr(v_a_650_);
v___x_653_ = lean_usize_dec_eq(v___x_651_, v___x_652_);
if (v___x_653_ == 0)
{
lean_object* v___x_654_; lean_object* v___x_655_; 
lean_dec_ref(v___y_649_);
v___x_654_ = l_Lean_Expr_mdata___override(v_data_640_, v_a_650_);
v___x_655_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_641_, v_inst_642_, v_inst_643_, v_pre_644_, v_post_645_, v_x_646_, v_x_647_, v___x_654_, v___y_648_);
return v___x_655_;
}
else
{
lean_object* v___x_656_; 
lean_dec_ref(v_a_650_);
lean_dec(v_data_640_);
v___x_656_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_641_, v_inst_642_, v_inst_643_, v_pre_644_, v_post_645_, v_x_646_, v_x_647_, v___y_649_, v___y_648_);
return v___x_656_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__15___boxed(lean_object* v_expr_657_, lean_object* v_data_658_, lean_object* v_inst_659_, lean_object* v_inst_660_, lean_object* v_inst_661_, lean_object* v_pre_662_, lean_object* v_post_663_, lean_object* v_x_664_, lean_object* v_x_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v_a_668_){
_start:
{
lean_object* v_res_669_; 
v_res_669_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__15(v_expr_657_, v_data_658_, v_inst_659_, v_inst_660_, v_inst_661_, v_pre_662_, v_post_663_, v_x_664_, v_x_665_, v___y_666_, v___y_667_, v_a_668_);
lean_dec(v___y_666_);
lean_dec_ref(v_expr_657_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__16(lean_object* v_struct_670_, lean_object* v_typeName_671_, lean_object* v_idx_672_, lean_object* v_inst_673_, lean_object* v_inst_674_, lean_object* v_inst_675_, lean_object* v_pre_676_, lean_object* v_post_677_, lean_object* v_x_678_, lean_object* v_x_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v_a_682_){
_start:
{
size_t v___x_683_; size_t v___x_684_; uint8_t v___x_685_; 
v___x_683_ = lean_ptr_addr(v_struct_670_);
v___x_684_ = lean_ptr_addr(v_a_682_);
v___x_685_ = lean_usize_dec_eq(v___x_683_, v___x_684_);
if (v___x_685_ == 0)
{
lean_object* v___x_686_; lean_object* v___x_687_; 
lean_dec_ref(v___y_681_);
v___x_686_ = l_Lean_Expr_proj___override(v_typeName_671_, v_idx_672_, v_a_682_);
v___x_687_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_673_, v_inst_674_, v_inst_675_, v_pre_676_, v_post_677_, v_x_678_, v_x_679_, v___x_686_, v___y_680_);
return v___x_687_;
}
else
{
lean_object* v___x_688_; 
lean_dec_ref(v_a_682_);
lean_dec(v_idx_672_);
lean_dec(v_typeName_671_);
v___x_688_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_673_, v_inst_674_, v_inst_675_, v_pre_676_, v_post_677_, v_x_678_, v_x_679_, v___y_681_, v___y_680_);
return v___x_688_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__16___boxed(lean_object* v_struct_689_, lean_object* v_typeName_690_, lean_object* v_idx_691_, lean_object* v_inst_692_, lean_object* v_inst_693_, lean_object* v_inst_694_, lean_object* v_pre_695_, lean_object* v_post_696_, lean_object* v_x_697_, lean_object* v_x_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v_a_701_){
_start:
{
lean_object* v_res_702_; 
v_res_702_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__16(v_struct_689_, v_typeName_690_, v_idx_691_, v_inst_692_, v_inst_693_, v_inst_694_, v_pre_695_, v_post_696_, v_x_697_, v_x_698_, v___y_699_, v___y_700_, v_a_701_);
lean_dec(v___y_699_);
lean_dec_ref(v_struct_689_);
return v_res_702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17(lean_object* v_toApplicative_703_, lean_object* v_inst_704_, lean_object* v_inst_705_, lean_object* v_inst_706_, lean_object* v_pre_707_, lean_object* v_post_708_, lean_object* v_x_709_, lean_object* v_x_710_, lean_object* v___y_711_, lean_object* v_toBind_712_, lean_object* v___f_713_, lean_object* v___f_714_, lean_object* v_e_715_, lean_object* v_a_716_){
_start:
{
lean_object* v___y_718_; 
switch(lean_obj_tag(v_a_716_))
{
case 0:
{
lean_object* v_e_763_; lean_object* v_toPure_764_; lean_object* v___x_765_; 
lean_dec_ref(v_e_715_);
lean_dec(v___f_714_);
lean_dec(v___f_713_);
lean_dec(v_toBind_712_);
lean_dec(v_x_710_);
lean_dec(v_post_708_);
lean_dec(v_pre_707_);
lean_dec_ref(v_inst_706_);
lean_dec(v_inst_705_);
lean_dec_ref(v_inst_704_);
v_e_763_ = lean_ctor_get(v_a_716_, 0);
lean_inc_ref(v_e_763_);
lean_dec_ref_known(v_a_716_, 1);
v_toPure_764_ = lean_ctor_get(v_toApplicative_703_, 1);
lean_inc(v_toPure_764_);
lean_dec_ref(v_toApplicative_703_);
v___x_765_ = lean_apply_2(v_toPure_764_, lean_box(0), v_e_763_);
return v___x_765_;
}
case 1:
{
lean_object* v_e_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
lean_dec_ref(v_e_715_);
lean_dec(v___f_714_);
lean_dec_ref(v_toApplicative_703_);
v_e_766_ = lean_ctor_get(v_a_716_, 0);
lean_inc_ref(v_e_766_);
lean_dec_ref_known(v_a_716_, 1);
v___x_767_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_704_, v_inst_705_, v_inst_706_, v_pre_707_, v_post_708_, v_x_709_, v_x_710_, v_e_766_, v___y_711_);
v___x_768_ = lean_apply_4(v_toBind_712_, lean_box(0), lean_box(0), v___x_767_, v___f_713_);
return v___x_768_;
}
default: 
{
lean_object* v_e_x3f_769_; 
lean_dec(v___f_713_);
lean_dec_ref(v_toApplicative_703_);
v_e_x3f_769_ = lean_ctor_get(v_a_716_, 0);
lean_inc(v_e_x3f_769_);
lean_dec_ref_known(v_a_716_, 1);
if (lean_obj_tag(v_e_x3f_769_) == 0)
{
v___y_718_ = v_e_715_;
goto v___jp_717_;
}
else
{
lean_object* v_val_770_; 
lean_dec_ref(v_e_715_);
v_val_770_ = lean_ctor_get(v_e_x3f_769_, 0);
lean_inc(v_val_770_);
lean_dec_ref_known(v_e_x3f_769_, 1);
v___y_718_ = v_val_770_;
goto v___jp_717_;
}
}
}
v___jp_717_:
{
switch(lean_obj_tag(v___y_718_))
{
case 7:
{
lean_object* v_binderName_719_; lean_object* v_binderType_720_; lean_object* v_body_721_; uint8_t v_binderInfo_722_; lean_object* v___x_723_; lean_object* v___f_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
lean_dec(v___f_714_);
v_binderName_719_ = lean_ctor_get(v___y_718_, 0);
lean_inc(v_binderName_719_);
v_binderType_720_ = lean_ctor_get(v___y_718_, 1);
lean_inc_ref_n(v_binderType_720_, 2);
v_body_721_ = lean_ctor_get(v___y_718_, 2);
lean_inc_ref(v_body_721_);
v_binderInfo_722_ = lean_ctor_get_uint8(v___y_718_, sizeof(void*)*3 + 8);
v___x_723_ = lean_box(v_binderInfo_722_);
lean_inc(v_toBind_712_);
lean_inc(v___y_711_);
lean_inc(v_x_710_);
lean_inc(v_post_708_);
lean_inc(v_pre_707_);
lean_inc_ref(v_inst_706_);
lean_inc(v_inst_705_);
lean_inc_ref(v_inst_704_);
v___f_724_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__9___boxed), 15, 14);
lean_closure_set(v___f_724_, 0, v_binderType_720_);
lean_closure_set(v___f_724_, 1, v_binderName_719_);
lean_closure_set(v___f_724_, 2, v___x_723_);
lean_closure_set(v___f_724_, 3, v_inst_704_);
lean_closure_set(v___f_724_, 4, v_inst_705_);
lean_closure_set(v___f_724_, 5, v_inst_706_);
lean_closure_set(v___f_724_, 6, v_pre_707_);
lean_closure_set(v___f_724_, 7, v_post_708_);
lean_closure_set(v___f_724_, 8, v_x_709_);
lean_closure_set(v___f_724_, 9, v_x_710_);
lean_closure_set(v___f_724_, 10, v___y_711_);
lean_closure_set(v___f_724_, 11, v_body_721_);
lean_closure_set(v___f_724_, 12, v___y_718_);
lean_closure_set(v___f_724_, 13, v_toBind_712_);
v___x_725_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_704_, v_inst_705_, v_inst_706_, v_pre_707_, v_post_708_, v_x_709_, v_x_710_, v_binderType_720_, v___y_711_);
v___x_726_ = lean_apply_4(v_toBind_712_, lean_box(0), lean_box(0), v___x_725_, v___f_724_);
return v___x_726_;
}
case 6:
{
lean_object* v_binderName_727_; lean_object* v_binderType_728_; lean_object* v_body_729_; uint8_t v_binderInfo_730_; lean_object* v___x_731_; lean_object* v___f_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
lean_dec(v___f_714_);
v_binderName_727_ = lean_ctor_get(v___y_718_, 0);
lean_inc(v_binderName_727_);
v_binderType_728_ = lean_ctor_get(v___y_718_, 1);
lean_inc_ref_n(v_binderType_728_, 2);
v_body_729_ = lean_ctor_get(v___y_718_, 2);
lean_inc_ref(v_body_729_);
v_binderInfo_730_ = lean_ctor_get_uint8(v___y_718_, sizeof(void*)*3 + 8);
v___x_731_ = lean_box(v_binderInfo_730_);
lean_inc(v_toBind_712_);
lean_inc(v___y_711_);
lean_inc(v_x_710_);
lean_inc(v_post_708_);
lean_inc(v_pre_707_);
lean_inc_ref(v_inst_706_);
lean_inc(v_inst_705_);
lean_inc_ref(v_inst_704_);
v___f_732_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__11___boxed), 15, 14);
lean_closure_set(v___f_732_, 0, v_binderType_728_);
lean_closure_set(v___f_732_, 1, v_binderName_727_);
lean_closure_set(v___f_732_, 2, v___x_731_);
lean_closure_set(v___f_732_, 3, v_inst_704_);
lean_closure_set(v___f_732_, 4, v_inst_705_);
lean_closure_set(v___f_732_, 5, v_inst_706_);
lean_closure_set(v___f_732_, 6, v_pre_707_);
lean_closure_set(v___f_732_, 7, v_post_708_);
lean_closure_set(v___f_732_, 8, v_x_709_);
lean_closure_set(v___f_732_, 9, v_x_710_);
lean_closure_set(v___f_732_, 10, v___y_711_);
lean_closure_set(v___f_732_, 11, v_body_729_);
lean_closure_set(v___f_732_, 12, v___y_718_);
lean_closure_set(v___f_732_, 13, v_toBind_712_);
v___x_733_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_704_, v_inst_705_, v_inst_706_, v_pre_707_, v_post_708_, v_x_709_, v_x_710_, v_binderType_728_, v___y_711_);
v___x_734_ = lean_apply_4(v_toBind_712_, lean_box(0), lean_box(0), v___x_733_, v___f_732_);
return v___x_734_;
}
case 8:
{
lean_object* v_declName_735_; lean_object* v_type_736_; lean_object* v_value_737_; lean_object* v_body_738_; uint8_t v_nondep_739_; lean_object* v___x_740_; lean_object* v___f_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
lean_dec(v___f_714_);
v_declName_735_ = lean_ctor_get(v___y_718_, 0);
lean_inc(v_declName_735_);
v_type_736_ = lean_ctor_get(v___y_718_, 1);
lean_inc_ref_n(v_type_736_, 2);
v_value_737_ = lean_ctor_get(v___y_718_, 2);
lean_inc_ref(v_value_737_);
v_body_738_ = lean_ctor_get(v___y_718_, 3);
lean_inc_ref(v_body_738_);
v_nondep_739_ = lean_ctor_get_uint8(v___y_718_, sizeof(void*)*4 + 8);
v___x_740_ = lean_box(v_nondep_739_);
lean_inc(v_toBind_712_);
lean_inc(v___y_711_);
lean_inc(v_x_710_);
lean_inc(v_post_708_);
lean_inc(v_pre_707_);
lean_inc_ref(v_inst_706_);
lean_inc(v_inst_705_);
lean_inc_ref(v_inst_704_);
v___f_741_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__14___boxed), 16, 15);
lean_closure_set(v___f_741_, 0, v_type_736_);
lean_closure_set(v___f_741_, 1, v_declName_735_);
lean_closure_set(v___f_741_, 2, v___x_740_);
lean_closure_set(v___f_741_, 3, v_inst_704_);
lean_closure_set(v___f_741_, 4, v_inst_705_);
lean_closure_set(v___f_741_, 5, v_inst_706_);
lean_closure_set(v___f_741_, 6, v_pre_707_);
lean_closure_set(v___f_741_, 7, v_post_708_);
lean_closure_set(v___f_741_, 8, v_x_709_);
lean_closure_set(v___f_741_, 9, v_x_710_);
lean_closure_set(v___f_741_, 10, v___y_711_);
lean_closure_set(v___f_741_, 11, v_value_737_);
lean_closure_set(v___f_741_, 12, v_body_738_);
lean_closure_set(v___f_741_, 13, v___y_718_);
lean_closure_set(v___f_741_, 14, v_toBind_712_);
v___x_742_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_704_, v_inst_705_, v_inst_706_, v_pre_707_, v_post_708_, v_x_709_, v_x_710_, v_type_736_, v___y_711_);
v___x_743_ = lean_apply_4(v_toBind_712_, lean_box(0), lean_box(0), v___x_742_, v___f_741_);
return v___x_743_;
}
case 5:
{
lean_object* v_dummy_744_; lean_object* v_nargs_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_2493__overap_749_; lean_object* v___x_750_; 
lean_dec(v_toBind_712_);
lean_dec(v_x_710_);
lean_dec(v_post_708_);
lean_dec(v_pre_707_);
lean_dec_ref(v_inst_706_);
lean_dec(v_inst_705_);
lean_dec_ref(v_inst_704_);
v_dummy_744_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_745_ = l_Lean_Expr_getAppNumArgs(v___y_718_);
lean_inc(v_nargs_745_);
v___x_746_ = lean_mk_array(v_nargs_745_, v_dummy_744_);
v___x_747_ = lean_unsigned_to_nat(1u);
v___x_748_ = lean_nat_sub(v_nargs_745_, v___x_747_);
lean_dec(v_nargs_745_);
v___x_2493__overap_749_ = l_Lean_Expr_withAppAux___redArg(v___f_714_, v___y_718_, v___x_746_, v___x_748_);
lean_inc(v___y_711_);
v___x_750_ = lean_apply_1(v___x_2493__overap_749_, v___y_711_);
return v___x_750_;
}
case 10:
{
lean_object* v_data_751_; lean_object* v_expr_752_; lean_object* v___f_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
lean_dec(v___f_714_);
v_data_751_ = lean_ctor_get(v___y_718_, 0);
lean_inc(v_data_751_);
v_expr_752_ = lean_ctor_get(v___y_718_, 1);
lean_inc_ref_n(v_expr_752_, 2);
lean_inc(v___y_711_);
lean_inc(v_x_710_);
lean_inc(v_post_708_);
lean_inc(v_pre_707_);
lean_inc_ref(v_inst_706_);
lean_inc(v_inst_705_);
lean_inc_ref(v_inst_704_);
v___f_753_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__15___boxed), 12, 11);
lean_closure_set(v___f_753_, 0, v_expr_752_);
lean_closure_set(v___f_753_, 1, v_data_751_);
lean_closure_set(v___f_753_, 2, v_inst_704_);
lean_closure_set(v___f_753_, 3, v_inst_705_);
lean_closure_set(v___f_753_, 4, v_inst_706_);
lean_closure_set(v___f_753_, 5, v_pre_707_);
lean_closure_set(v___f_753_, 6, v_post_708_);
lean_closure_set(v___f_753_, 7, v_x_709_);
lean_closure_set(v___f_753_, 8, v_x_710_);
lean_closure_set(v___f_753_, 9, v___y_711_);
lean_closure_set(v___f_753_, 10, v___y_718_);
v___x_754_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_704_, v_inst_705_, v_inst_706_, v_pre_707_, v_post_708_, v_x_709_, v_x_710_, v_expr_752_, v___y_711_);
v___x_755_ = lean_apply_4(v_toBind_712_, lean_box(0), lean_box(0), v___x_754_, v___f_753_);
return v___x_755_;
}
case 11:
{
lean_object* v_typeName_756_; lean_object* v_idx_757_; lean_object* v_struct_758_; lean_object* v___f_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
lean_dec(v___f_714_);
v_typeName_756_ = lean_ctor_get(v___y_718_, 0);
lean_inc(v_typeName_756_);
v_idx_757_ = lean_ctor_get(v___y_718_, 1);
lean_inc(v_idx_757_);
v_struct_758_ = lean_ctor_get(v___y_718_, 2);
lean_inc_ref_n(v_struct_758_, 2);
lean_inc(v___y_711_);
lean_inc(v_x_710_);
lean_inc(v_post_708_);
lean_inc(v_pre_707_);
lean_inc_ref(v_inst_706_);
lean_inc(v_inst_705_);
lean_inc_ref(v_inst_704_);
v___f_759_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__16___boxed), 13, 12);
lean_closure_set(v___f_759_, 0, v_struct_758_);
lean_closure_set(v___f_759_, 1, v_typeName_756_);
lean_closure_set(v___f_759_, 2, v_idx_757_);
lean_closure_set(v___f_759_, 3, v_inst_704_);
lean_closure_set(v___f_759_, 4, v_inst_705_);
lean_closure_set(v___f_759_, 5, v_inst_706_);
lean_closure_set(v___f_759_, 6, v_pre_707_);
lean_closure_set(v___f_759_, 7, v_post_708_);
lean_closure_set(v___f_759_, 8, v_x_709_);
lean_closure_set(v___f_759_, 9, v_x_710_);
lean_closure_set(v___f_759_, 10, v___y_711_);
lean_closure_set(v___f_759_, 11, v___y_718_);
v___x_760_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_704_, v_inst_705_, v_inst_706_, v_pre_707_, v_post_708_, v_x_709_, v_x_710_, v_struct_758_, v___y_711_);
v___x_761_ = lean_apply_4(v_toBind_712_, lean_box(0), lean_box(0), v___x_760_, v___f_759_);
return v___x_761_;
}
default: 
{
lean_object* v___x_762_; 
lean_dec(v___f_714_);
lean_dec(v_toBind_712_);
v___x_762_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_704_, v_inst_705_, v_inst_706_, v_pre_707_, v_post_708_, v_x_709_, v_x_710_, v___y_718_, v___y_711_);
return v___x_762_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___boxed(lean_object* v_toApplicative_771_, lean_object* v_inst_772_, lean_object* v_inst_773_, lean_object* v_inst_774_, lean_object* v_pre_775_, lean_object* v_post_776_, lean_object* v_x_777_, lean_object* v_x_778_, lean_object* v___y_779_, lean_object* v_toBind_780_, lean_object* v___f_781_, lean_object* v___f_782_, lean_object* v_e_783_, lean_object* v_a_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17(v_toApplicative_771_, v_inst_772_, v_inst_773_, v_inst_774_, v_pre_775_, v_post_776_, v_x_777_, v_x_778_, v___y_779_, v_toBind_780_, v___f_781_, v___f_782_, v_e_783_, v_a_784_);
lean_dec(v___y_779_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__18(lean_object* v_inst_786_, lean_object* v_inst_787_, lean_object* v_inst_788_, lean_object* v_pre_789_, lean_object* v_post_790_, lean_object* v_x_791_, lean_object* v_x_792_, lean_object* v_toApplicative_793_, lean_object* v_toBind_794_, lean_object* v___f_795_, lean_object* v_e_796_, lean_object* v_____r_797_, lean_object* v___y_798_){
_start:
{
lean_object* v___f_799_; lean_object* v___f_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
lean_inc_n(v___y_798_, 2);
lean_inc(v_x_792_);
lean_inc(v_post_790_);
lean_inc_n(v_pre_789_, 2);
lean_inc_ref(v_inst_788_);
lean_inc(v_inst_787_);
lean_inc_ref(v_inst_786_);
v___f_799_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__7___boxed), 9, 8);
lean_closure_set(v___f_799_, 0, v_inst_786_);
lean_closure_set(v___f_799_, 1, v_inst_787_);
lean_closure_set(v___f_799_, 2, v_inst_788_);
lean_closure_set(v___f_799_, 3, v_pre_789_);
lean_closure_set(v___f_799_, 4, v_post_790_);
lean_closure_set(v___f_799_, 5, v_x_791_);
lean_closure_set(v___f_799_, 6, v_x_792_);
lean_closure_set(v___f_799_, 7, v___y_798_);
lean_inc_ref(v_e_796_);
lean_inc(v_toBind_794_);
v___f_800_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___boxed), 14, 13);
lean_closure_set(v___f_800_, 0, v_toApplicative_793_);
lean_closure_set(v___f_800_, 1, v_inst_786_);
lean_closure_set(v___f_800_, 2, v_inst_787_);
lean_closure_set(v___f_800_, 3, v_inst_788_);
lean_closure_set(v___f_800_, 4, v_pre_789_);
lean_closure_set(v___f_800_, 5, v_post_790_);
lean_closure_set(v___f_800_, 6, v_x_791_);
lean_closure_set(v___f_800_, 7, v_x_792_);
lean_closure_set(v___f_800_, 8, v___y_798_);
lean_closure_set(v___f_800_, 9, v_toBind_794_);
lean_closure_set(v___f_800_, 10, v___f_799_);
lean_closure_set(v___f_800_, 11, v___f_795_);
lean_closure_set(v___f_800_, 12, v_e_796_);
v___x_801_ = lean_apply_1(v_pre_789_, v_e_796_);
v___x_802_ = lean_apply_4(v_toBind_794_, lean_box(0), lean_box(0), v___x_801_, v___f_800_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__18___boxed(lean_object* v_inst_803_, lean_object* v_inst_804_, lean_object* v_inst_805_, lean_object* v_pre_806_, lean_object* v_post_807_, lean_object* v_x_808_, lean_object* v_x_809_, lean_object* v_toApplicative_810_, lean_object* v_toBind_811_, lean_object* v___f_812_, lean_object* v_e_813_, lean_object* v_____r_814_, lean_object* v___y_815_){
_start:
{
lean_object* v_res_816_; 
v_res_816_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__18(v_inst_803_, v_inst_804_, v_inst_805_, v_pre_806_, v_post_807_, v_x_808_, v_x_809_, v_toApplicative_810_, v_toBind_811_, v___f_812_, v_e_813_, v_____r_814_, v___y_815_);
lean_dec(v___y_815_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(lean_object* v_inst_817_, lean_object* v_inst_818_, lean_object* v_inst_819_, lean_object* v_pre_820_, lean_object* v_post_821_, lean_object* v_x_822_, lean_object* v_x_823_, lean_object* v_e_824_, lean_object* v_a_825_){
_start:
{
lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___f_830_; lean_object* v___f_831_; lean_object* v___x_832_; lean_object* v_toApplicative_833_; lean_object* v_toBind_834_; lean_object* v___f_835_; lean_object* v___f_836_; lean_object* v___f_837_; lean_object* v___f_838_; lean_object* v___f_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; 
v___x_826_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0));
v___x_827_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1));
lean_inc_ref_n(v_inst_817_, 3);
v___x_828_ = l_Lean_MonadCacheT_instMonad___redArg(v_x_822_, v___x_826_, v___x_827_, v_inst_817_);
v___x_829_ = l_Lean_MonadCacheT_instMonadControl___redArg(v_x_822_, v___x_826_, v___x_827_);
lean_inc_ref_n(v_inst_819_, 3);
lean_inc_ref(v___x_829_);
v___f_830_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_830_, 0, v___x_829_);
lean_closure_set(v___f_830_, 1, v_inst_819_);
v___f_831_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_831_, 0, v___x_829_);
lean_closure_set(v___f_831_, 1, v_inst_819_);
v___x_832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_832_, 0, v___f_830_);
lean_ctor_set(v___x_832_, 1, v___f_831_);
v_toApplicative_833_ = lean_ctor_get(v_inst_817_, 0);
lean_inc_ref_n(v_toApplicative_833_, 4);
v_toBind_834_ = lean_ctor_get(v_inst_817_, 1);
lean_inc_n(v_toBind_834_, 6);
lean_inc_n(v_x_823_, 3);
lean_inc_n(v_a_825_, 3);
lean_inc_ref_n(v_e_824_, 2);
v___f_835_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_835_, 0, v_toApplicative_833_);
lean_closure_set(v___f_835_, 1, v___x_826_);
lean_closure_set(v___f_835_, 2, v___x_827_);
lean_closure_set(v___f_835_, 3, v_e_824_);
lean_closure_set(v___f_835_, 4, v_a_825_);
lean_closure_set(v___f_835_, 5, v_x_823_);
lean_closure_set(v___f_835_, 6, v_toBind_834_);
v___f_836_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__3___boxed), 5, 4);
lean_closure_set(v___f_836_, 0, v_toApplicative_833_);
lean_closure_set(v___f_836_, 1, v___x_826_);
lean_closure_set(v___f_836_, 2, v___x_827_);
lean_closure_set(v___f_836_, 3, v_e_824_);
lean_inc_ref(v___x_828_);
lean_inc(v_post_821_);
lean_inc(v_pre_820_);
lean_inc_n(v_inst_818_, 2);
v___f_837_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__6___boxed), 12, 9);
lean_closure_set(v___f_837_, 0, v_inst_817_);
lean_closure_set(v___f_837_, 1, v_inst_818_);
lean_closure_set(v___f_837_, 2, v_inst_819_);
lean_closure_set(v___f_837_, 3, v_pre_820_);
lean_closure_set(v___f_837_, 4, v_post_821_);
lean_closure_set(v___f_837_, 5, v_x_822_);
lean_closure_set(v___f_837_, 6, v_x_823_);
lean_closure_set(v___f_837_, 7, v___x_828_);
lean_closure_set(v___f_837_, 8, v_toBind_834_);
v___f_838_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__18___boxed), 13, 11);
lean_closure_set(v___f_838_, 0, v_inst_817_);
lean_closure_set(v___f_838_, 1, v_inst_818_);
lean_closure_set(v___f_838_, 2, v_inst_819_);
lean_closure_set(v___f_838_, 3, v_pre_820_);
lean_closure_set(v___f_838_, 4, v_post_821_);
lean_closure_set(v___f_838_, 5, v_x_822_);
lean_closure_set(v___f_838_, 6, v_x_823_);
lean_closure_set(v___f_838_, 7, v_toApplicative_833_);
lean_closure_set(v___f_838_, 8, v_toBind_834_);
lean_closure_set(v___f_838_, 9, v___f_837_);
lean_closure_set(v___f_838_, 10, v_e_824_);
v___f_839_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__19___boxed), 13, 12);
lean_closure_set(v___f_839_, 0, v_inst_818_);
lean_closure_set(v___f_839_, 1, v_x_822_);
lean_closure_set(v___f_839_, 2, v___x_826_);
lean_closure_set(v___f_839_, 3, v___x_827_);
lean_closure_set(v___f_839_, 4, v_inst_817_);
lean_closure_set(v___f_839_, 5, v___f_838_);
lean_closure_set(v___f_839_, 6, v___x_828_);
lean_closure_set(v___f_839_, 7, v___x_832_);
lean_closure_set(v___f_839_, 8, v_a_825_);
lean_closure_set(v___f_839_, 9, v_toBind_834_);
lean_closure_set(v___f_839_, 10, v___f_835_);
lean_closure_set(v___f_839_, 11, v_toApplicative_833_);
v___x_840_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_840_, 0, lean_box(0));
lean_closure_set(v___x_840_, 1, lean_box(0));
lean_closure_set(v___x_840_, 2, v_a_825_);
v___x_841_ = lean_apply_2(v_x_823_, lean_box(0), v___x_840_);
v___x_842_ = lean_apply_4(v_toBind_834_, lean_box(0), lean_box(0), v___x_841_, v___f_836_);
v___x_843_ = lean_apply_4(v_toBind_834_, lean_box(0), lean_box(0), v___x_842_, v___f_839_);
return v___x_843_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg___lam__0(lean_object* v_toApplicative_844_, lean_object* v_inst_845_, lean_object* v_inst_846_, lean_object* v_inst_847_, lean_object* v_pre_848_, lean_object* v_post_849_, lean_object* v_x_850_, lean_object* v_x_851_, lean_object* v_a_852_, lean_object* v_e_853_, lean_object* v_a_854_){
_start:
{
lean_object* v___y_856_; 
switch(lean_obj_tag(v_a_854_))
{
case 0:
{
lean_object* v_e_859_; lean_object* v_toPure_860_; lean_object* v___x_861_; 
lean_dec_ref(v_e_853_);
lean_dec(v_x_851_);
lean_dec(v_post_849_);
lean_dec(v_pre_848_);
lean_dec_ref(v_inst_847_);
lean_dec(v_inst_846_);
lean_dec_ref(v_inst_845_);
v_e_859_ = lean_ctor_get(v_a_854_, 0);
lean_inc_ref(v_e_859_);
lean_dec_ref_known(v_a_854_, 1);
v_toPure_860_ = lean_ctor_get(v_toApplicative_844_, 1);
lean_inc(v_toPure_860_);
lean_dec_ref(v_toApplicative_844_);
v___x_861_ = lean_apply_2(v_toPure_860_, lean_box(0), v_e_859_);
return v___x_861_;
}
case 1:
{
lean_object* v_e_862_; lean_object* v___x_863_; 
lean_dec_ref(v_e_853_);
lean_dec_ref(v_toApplicative_844_);
v_e_862_ = lean_ctor_get(v_a_854_, 0);
lean_inc_ref(v_e_862_);
lean_dec_ref_known(v_a_854_, 1);
v___x_863_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_845_, v_inst_846_, v_inst_847_, v_pre_848_, v_post_849_, v_x_850_, v_x_851_, v_e_862_, v_a_852_);
return v___x_863_;
}
default: 
{
lean_object* v_e_x3f_864_; 
lean_dec(v_x_851_);
lean_dec(v_post_849_);
lean_dec(v_pre_848_);
lean_dec_ref(v_inst_847_);
lean_dec(v_inst_846_);
lean_dec_ref(v_inst_845_);
v_e_x3f_864_ = lean_ctor_get(v_a_854_, 0);
lean_inc(v_e_x3f_864_);
lean_dec_ref_known(v_a_854_, 1);
if (lean_obj_tag(v_e_x3f_864_) == 0)
{
v___y_856_ = v_e_853_;
goto v___jp_855_;
}
else
{
lean_object* v_val_865_; 
lean_dec_ref(v_e_853_);
v_val_865_ = lean_ctor_get(v_e_x3f_864_, 0);
lean_inc(v_val_865_);
lean_dec_ref_known(v_e_x3f_864_, 1);
v___y_856_ = v_val_865_;
goto v___jp_855_;
}
}
}
v___jp_855_:
{
lean_object* v_toPure_857_; lean_object* v___x_858_; 
v_toPure_857_ = lean_ctor_get(v_toApplicative_844_, 1);
lean_inc(v_toPure_857_);
lean_dec_ref(v_toApplicative_844_);
v___x_858_ = lean_apply_2(v_toPure_857_, lean_box(0), v___y_856_);
return v___x_858_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg___lam__0___boxed(lean_object* v_toApplicative_866_, lean_object* v_inst_867_, lean_object* v_inst_868_, lean_object* v_inst_869_, lean_object* v_pre_870_, lean_object* v_post_871_, lean_object* v_x_872_, lean_object* v_x_873_, lean_object* v_a_874_, lean_object* v_e_875_, lean_object* v_a_876_){
_start:
{
lean_object* v_res_877_; 
v_res_877_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg___lam__0(v_toApplicative_866_, v_inst_867_, v_inst_868_, v_inst_869_, v_pre_870_, v_post_871_, v_x_872_, v_x_873_, v_a_874_, v_e_875_, v_a_876_);
lean_dec(v_a_874_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(lean_object* v_inst_878_, lean_object* v_inst_879_, lean_object* v_inst_880_, lean_object* v_pre_881_, lean_object* v_post_882_, lean_object* v_x_883_, lean_object* v_x_884_, lean_object* v_e_885_, lean_object* v_a_886_){
_start:
{
lean_object* v_toApplicative_887_; lean_object* v_toBind_888_; lean_object* v___f_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v_toApplicative_887_ = lean_ctor_get(v_inst_878_, 0);
lean_inc_ref(v_toApplicative_887_);
v_toBind_888_ = lean_ctor_get(v_inst_878_, 1);
lean_inc(v_toBind_888_);
lean_inc_ref(v_e_885_);
lean_inc(v_a_886_);
lean_inc(v_post_882_);
v___f_889_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg___lam__0___boxed), 11, 10);
lean_closure_set(v___f_889_, 0, v_toApplicative_887_);
lean_closure_set(v___f_889_, 1, v_inst_878_);
lean_closure_set(v___f_889_, 2, v_inst_879_);
lean_closure_set(v___f_889_, 3, v_inst_880_);
lean_closure_set(v___f_889_, 4, v_pre_881_);
lean_closure_set(v___f_889_, 5, v_post_882_);
lean_closure_set(v___f_889_, 6, v_x_883_);
lean_closure_set(v___f_889_, 7, v_x_884_);
lean_closure_set(v___f_889_, 8, v_a_886_);
lean_closure_set(v___f_889_, 9, v_e_885_);
v___x_890_ = lean_apply_1(v_post_882_, v_e_885_);
v___x_891_ = lean_apply_4(v_toBind_888_, lean_box(0), lean_box(0), v___x_890_, v___f_889_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__7(lean_object* v_inst_892_, lean_object* v_inst_893_, lean_object* v_inst_894_, lean_object* v_pre_895_, lean_object* v_post_896_, lean_object* v_x_897_, lean_object* v_x_898_, lean_object* v___y_899_, lean_object* v_a_900_){
_start:
{
lean_object* v___x_901_; 
v___x_901_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_892_, v_inst_893_, v_inst_894_, v_pre_895_, v_post_896_, v_x_897_, v_x_898_, v_a_900_, v___y_899_);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg___boxed(lean_object* v_inst_902_, lean_object* v_inst_903_, lean_object* v_inst_904_, lean_object* v_pre_905_, lean_object* v_post_906_, lean_object* v_x_907_, lean_object* v_x_908_, lean_object* v_e_909_, lean_object* v_a_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_902_, v_inst_903_, v_inst_904_, v_pre_905_, v_post_906_, v_x_907_, v_x_908_, v_e_909_, v_a_910_);
lean_dec(v_a_910_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit(lean_object* v_m_912_, lean_object* v_inst_913_, lean_object* v_inst_914_, lean_object* v_inst_915_, lean_object* v_pre_916_, lean_object* v_post_917_, lean_object* v_x_918_, lean_object* v_x_919_, lean_object* v_e_920_, lean_object* v_a_921_){
_start:
{
lean_object* v___x_922_; 
v___x_922_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_913_, v_inst_914_, v_inst_915_, v_pre_916_, v_post_917_, v_x_918_, v_x_919_, v_e_920_, v_a_921_);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___boxed(lean_object* v_m_923_, lean_object* v_inst_924_, lean_object* v_inst_925_, lean_object* v_inst_926_, lean_object* v_pre_927_, lean_object* v_post_928_, lean_object* v_x_929_, lean_object* v_x_930_, lean_object* v_e_931_, lean_object* v_a_932_){
_start:
{
lean_object* v_res_933_; 
v_res_933_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit(v_m_923_, v_inst_924_, v_inst_925_, v_inst_926_, v_pre_927_, v_post_928_, v_x_929_, v_x_930_, v_e_931_, v_a_932_);
lean_dec(v_a_932_);
return v_res_933_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost(lean_object* v_m_934_, lean_object* v_inst_935_, lean_object* v_inst_936_, lean_object* v_inst_937_, lean_object* v_pre_938_, lean_object* v_post_939_, lean_object* v_x_940_, lean_object* v_x_941_, lean_object* v_e_942_, lean_object* v_a_943_){
_start:
{
lean_object* v___x_944_; 
v___x_944_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_935_, v_inst_936_, v_inst_937_, v_pre_938_, v_post_939_, v_x_940_, v_x_941_, v_e_942_, v_a_943_);
return v___x_944_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___boxed(lean_object* v_m_945_, lean_object* v_inst_946_, lean_object* v_inst_947_, lean_object* v_inst_948_, lean_object* v_pre_949_, lean_object* v_post_950_, lean_object* v_x_951_, lean_object* v_x_952_, lean_object* v_e_953_, lean_object* v_a_954_){
_start:
{
lean_object* v_res_955_; 
v_res_955_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost(v_m_945_, v_inst_946_, v_inst_947_, v_inst_948_, v_pre_949_, v_post_950_, v_x_951_, v_x_952_, v_e_953_, v_a_954_);
lean_dec(v_a_954_);
return v_res_955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___redArg___lam__0(lean_object* v_x_956_){
_start:
{
lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_958_ = lean_apply_1(v_x_956_, lean_box(0));
v___x_959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_959_, 0, v___x_958_);
return v___x_959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___redArg___lam__0___boxed(lean_object* v_x_960_, lean_object* v___y_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l_Lean_Core_transform___redArg___lam__0(v_x_960_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___redArg___lam__1(lean_object* v_inst_963_, lean_object* v_00_u03b1_964_, lean_object* v_x_965_){
_start:
{
lean_object* v___f_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
v___f_966_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_966_, 0, v_x_965_);
v___x_967_ = lean_alloc_closure((void*)(l_Lean_Core_liftIOCore___boxed), 5, 2);
lean_closure_set(v___x_967_, 0, lean_box(0));
lean_closure_set(v___x_967_, 1, v___f_966_);
v___x_968_ = lean_apply_2(v_inst_963_, lean_box(0), v___x_967_);
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___redArg___lam__2(lean_object* v_toPure_969_, lean_object* v_____x_970_){
_start:
{
lean_object* v_fst_971_; lean_object* v___x_972_; 
v_fst_971_ = lean_ctor_get(v_____x_970_, 0);
lean_inc(v_fst_971_);
lean_dec_ref(v_____x_970_);
v___x_972_ = lean_apply_2(v_toPure_969_, lean_box(0), v_fst_971_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___redArg___lam__3(lean_object* v_a_973_, lean_object* v_toPure_974_, lean_object* v_s_975_){
_start:
{
lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_976_, 0, v_a_973_);
lean_ctor_set(v___x_976_, 1, v_s_975_);
v___x_977_ = lean_apply_2(v_toPure_974_, lean_box(0), v___x_976_);
return v___x_977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___redArg___lam__4(lean_object* v_toPure_978_, lean_object* v_ref_979_, lean_object* v_x_980_, lean_object* v_toBind_981_, lean_object* v_a_982_){
_start:
{
lean_object* v___f_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; 
v___f_983_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__3), 3, 2);
lean_closure_set(v___f_983_, 0, v_a_982_);
lean_closure_set(v___f_983_, 1, v_toPure_978_);
v___x_984_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_984_, 0, lean_box(0));
lean_closure_set(v___x_984_, 1, lean_box(0));
lean_closure_set(v___x_984_, 2, v_ref_979_);
v___x_985_ = lean_apply_2(v_x_980_, lean_box(0), v___x_984_);
v___x_986_ = lean_apply_4(v_toBind_981_, lean_box(0), lean_box(0), v___x_985_, v___f_983_);
return v___x_986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___redArg___lam__5(lean_object* v_toPure_987_, lean_object* v_x_988_, lean_object* v_toBind_989_, lean_object* v_inst_990_, lean_object* v_inst_991_, lean_object* v_inst_992_, lean_object* v_pre_993_, lean_object* v_post_994_, lean_object* v_x_995_, lean_object* v_input_996_, lean_object* v_ref_997_){
_start:
{
lean_object* v___f_998_; lean_object* v___x_999_; lean_object* v___x_1000_; 
lean_inc(v_toBind_989_);
lean_inc(v_x_988_);
lean_inc(v_ref_997_);
v___f_998_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__4), 5, 4);
lean_closure_set(v___f_998_, 0, v_toPure_987_);
lean_closure_set(v___f_998_, 1, v_ref_997_);
lean_closure_set(v___f_998_, 2, v_x_988_);
lean_closure_set(v___f_998_, 3, v_toBind_989_);
v___x_999_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_990_, v_inst_991_, v_inst_992_, v_pre_993_, v_post_994_, v_x_995_, v_x_988_, v_input_996_, v_ref_997_);
lean_dec(v_ref_997_);
v___x_1000_ = lean_apply_4(v_toBind_989_, lean_box(0), lean_box(0), v___x_999_, v___f_998_);
return v___x_1000_;
}
}
static lean_object* _init_l_Lean_Core_transform___redArg___closed__0(void){
_start:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_1001_ = lean_box(0);
v___x_1002_ = lean_unsigned_to_nat(16u);
v___x_1003_ = lean_mk_array(v___x_1002_, v___x_1001_);
return v___x_1003_;
}
}
static lean_object* _init_l_Lean_Core_transform___redArg___closed__1(void){
_start:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1004_ = lean_obj_once(&l_Lean_Core_transform___redArg___closed__0, &l_Lean_Core_transform___redArg___closed__0_once, _init_l_Lean_Core_transform___redArg___closed__0);
v___x_1005_ = lean_unsigned_to_nat(0u);
v___x_1006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1005_);
lean_ctor_set(v___x_1006_, 1, v___x_1004_);
return v___x_1006_;
}
}
static lean_object* _init_l_Lean_Core_transform___redArg___closed__2(void){
_start:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1007_ = lean_obj_once(&l_Lean_Core_transform___redArg___closed__1, &l_Lean_Core_transform___redArg___closed__1_once, _init_l_Lean_Core_transform___redArg___closed__1);
v___x_1008_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1008_, 0, lean_box(0));
lean_closure_set(v___x_1008_, 1, lean_box(0));
lean_closure_set(v___x_1008_, 2, v___x_1007_);
return v___x_1008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___redArg(lean_object* v_inst_1009_, lean_object* v_inst_1010_, lean_object* v_inst_1011_, lean_object* v_input_1012_, lean_object* v_pre_1013_, lean_object* v_post_1014_){
_start:
{
lean_object* v_x_1015_; lean_object* v_toApplicative_1016_; lean_object* v_toBind_1017_; lean_object* v_toPure_1018_; lean_object* v_x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___f_1022_; lean_object* v___f_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; 
v_x_1015_ = lean_box(0);
v_toApplicative_1016_ = lean_ctor_get(v_inst_1009_, 0);
v_toBind_1017_ = lean_ctor_get(v_inst_1009_, 1);
lean_inc_n(v_toBind_1017_, 3);
v_toPure_1018_ = lean_ctor_get(v_toApplicative_1016_, 1);
lean_inc_n(v_toPure_1018_, 2);
lean_inc_n(v_inst_1010_, 2);
v_x_1019_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__1), 3, 1);
lean_closure_set(v_x_1019_, 0, v_inst_1010_);
v___x_1020_ = lean_obj_once(&l_Lean_Core_transform___redArg___closed__2, &l_Lean_Core_transform___redArg___closed__2_once, _init_l_Lean_Core_transform___redArg___closed__2);
v___x_1021_ = l_Lean_Core_transform___redArg___lam__1(v_inst_1010_, lean_box(0), v___x_1020_);
v___f_1022_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__2), 2, 1);
lean_closure_set(v___f_1022_, 0, v_toPure_1018_);
v___f_1023_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__5), 11, 10);
lean_closure_set(v___f_1023_, 0, v_toPure_1018_);
lean_closure_set(v___f_1023_, 1, v_x_1019_);
lean_closure_set(v___f_1023_, 2, v_toBind_1017_);
lean_closure_set(v___f_1023_, 3, v_inst_1009_);
lean_closure_set(v___f_1023_, 4, v_inst_1010_);
lean_closure_set(v___f_1023_, 5, v_inst_1011_);
lean_closure_set(v___f_1023_, 6, v_pre_1013_);
lean_closure_set(v___f_1023_, 7, v_post_1014_);
lean_closure_set(v___f_1023_, 8, v_x_1015_);
lean_closure_set(v___f_1023_, 9, v_input_1012_);
v___x_1024_ = lean_apply_4(v_toBind_1017_, lean_box(0), lean_box(0), v___x_1021_, v___f_1023_);
v___x_1025_ = lean_apply_4(v_toBind_1017_, lean_box(0), lean_box(0), v___x_1024_, v___f_1022_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform(lean_object* v_m_1026_, lean_object* v_inst_1027_, lean_object* v_inst_1028_, lean_object* v_inst_1029_, lean_object* v_input_1030_, lean_object* v_pre_1031_, lean_object* v_post_1032_){
_start:
{
lean_object* v___x_1033_; 
v___x_1033_ = l_Lean_Core_transform___redArg(v_inst_1027_, v_inst_1028_, v_inst_1029_, v_input_1030_, v_pre_1031_, v_post_1032_);
return v___x_1033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_betaReduce___lam__0(lean_object* v_e_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_){
_start:
{
uint8_t v___x_1040_; uint8_t v___x_1041_; 
v___x_1040_ = 0;
v___x_1041_ = l_Lean_Expr_isHeadBetaTarget(v_e_1036_, v___x_1040_);
if (v___x_1041_ == 0)
{
lean_object* v___x_1042_; lean_object* v___x_1043_; 
lean_dec_ref(v_e_1036_);
v___x_1042_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_1043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1042_);
return v___x_1043_;
}
else
{
lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; 
v___x_1044_ = l_Lean_Expr_headBeta(v_e_1036_);
v___x_1045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1044_);
v___x_1046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1045_);
return v___x_1046_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_betaReduce___lam__0___boxed(lean_object* v_e_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
lean_object* v_res_1051_; 
v_res_1051_ = l_Lean_Core_betaReduce___lam__0(v_e_1047_, v___y_1048_, v___y_1049_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_betaReduce___lam__1(lean_object* v_e_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_){
_start:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1056_, 0, v_e_1052_);
v___x_1057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1056_);
return v___x_1057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_betaReduce___lam__1___boxed(lean_object* v_e_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_){
_start:
{
lean_object* v_res_1062_; 
v_res_1062_ = l_Lean_Core_betaReduce___lam__1(v_e_1058_, v___y_1059_, v___y_1060_);
lean_dec(v___y_1060_);
lean_dec_ref(v___y_1059_);
return v_res_1062_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1063_ = lean_box(0);
v___x_1064_ = l_Lean_interruptExceptionId;
v___x_1065_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1064_);
lean_ctor_set(v___x_1065_, 1, v___x_1063_);
return v___x_1065_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___redArg(){
_start:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; 
v___x_1067_ = lean_obj_once(&l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___redArg___closed__0, &l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___redArg___closed__0);
v___x_1068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1067_);
return v___x_1068_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___redArg___boxed(lean_object* v___y_1069_){
_start:
{
lean_object* v_res_1070_; 
v_res_1070_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___redArg();
return v_res_1070_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1076_ = l_Lean_maxRecDepthErrorMessage;
v___x_1077_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1076_);
return v___x_1077_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1078_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__3);
v___x_1079_ = l_Lean_MessageData_ofFormat(v___x_1078_);
return v___x_1079_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1080_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__4);
v___x_1081_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__2));
v___x_1082_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1081_);
lean_ctor_set(v___x_1082_, 1, v___x_1080_);
return v___x_1082_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg(lean_object* v_ref_1083_){
_start:
{
lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1085_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5);
v___x_1086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1086_, 0, v_ref_1083_);
lean_ctor_set(v___x_1086_, 1, v___x_1085_);
v___x_1087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1086_);
return v___x_1087_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object* v_ref_1088_, lean_object* v___y_1089_){
_start:
{
lean_object* v_res_1090_; 
v_res_1090_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_1088_);
return v_res_1090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___redArg(lean_object* v_x_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_){
_start:
{
lean_object* v___y_1097_; uint16_t v___y_1107_; lean_object* v___y_1108_; uint8_t v___y_1109_; lean_object* v___y_1110_; uint8_t v___y_1111_; lean_object* v___y_1112_; lean_object* v_toCold_1117_; lean_object* v_currRecDepth_1118_; lean_object* v_ref_1119_; uint16_t v_optionFlags_1120_; uint8_t v_suppressElabErrors_1121_; uint8_t v_isRecordingDeps_1122_; lean_object* v_maxRecDepth_1123_; lean_object* v_cancelTk_x3f_1124_; 
v_toCold_1117_ = lean_ctor_get(v___y_1093_, 0);
v_currRecDepth_1118_ = lean_ctor_get(v___y_1093_, 1);
v_ref_1119_ = lean_ctor_get(v___y_1093_, 2);
v_optionFlags_1120_ = lean_ctor_get_uint16(v___y_1093_, sizeof(void*)*3);
v_suppressElabErrors_1121_ = lean_ctor_get_uint8(v___y_1093_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1122_ = lean_ctor_get_uint8(v___y_1093_, sizeof(void*)*3 + 3);
v_maxRecDepth_1123_ = lean_ctor_get(v_toCold_1117_, 3);
v_cancelTk_x3f_1124_ = lean_ctor_get(v_toCold_1117_, 10);
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
lean_dec_ref(v_x_1091_);
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
v___jp_1096_:
{
if (lean_obj_tag(v___y_1097_) == 0)
{
return v___y_1097_;
}
else
{
lean_object* v_a_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1105_; 
v_a_1098_ = lean_ctor_get(v___y_1097_, 0);
v_isSharedCheck_1105_ = !lean_is_exclusive(v___y_1097_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1100_ = v___y_1097_;
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_a_1098_);
lean_dec(v___y_1097_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v___x_1103_; 
if (v_isShared_1101_ == 0)
{
v___x_1103_ = v___x_1100_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v_a_1098_);
v___x_1103_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
return v___x_1103_;
}
}
}
}
v___jp_1106_:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1113_ = lean_unsigned_to_nat(1u);
v___x_1114_ = lean_nat_add(v___y_1110_, v___x_1113_);
lean_inc_ref(v___y_1108_);
v___x_1115_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1115_, 0, v___y_1108_);
lean_ctor_set(v___x_1115_, 1, v___x_1114_);
lean_ctor_set(v___x_1115_, 2, v___y_1112_);
lean_ctor_set_uint16(v___x_1115_, sizeof(void*)*3, v___y_1107_);
lean_ctor_set_uint8(v___x_1115_, sizeof(void*)*3 + 2, v___y_1109_);
lean_ctor_set_uint8(v___x_1115_, sizeof(void*)*3 + 3, v___y_1111_);
lean_inc(v___y_1094_);
lean_inc(v___y_1092_);
v___x_1116_ = lean_apply_4(v_x_1091_, v___y_1092_, v___x_1115_, v___y_1094_, lean_box(0));
v___y_1097_ = v___x_1116_;
goto v___jp_1096_;
}
v___jp_1125_:
{
lean_object* v___x_1126_; uint8_t v___x_1127_; 
v___x_1126_ = lean_unsigned_to_nat(0u);
v___x_1127_ = lean_nat_dec_eq(v_maxRecDepth_1123_, v___x_1126_);
if (v___x_1127_ == 0)
{
uint8_t v___x_1128_; 
v___x_1128_ = lean_nat_dec_eq(v_currRecDepth_1118_, v_maxRecDepth_1123_);
if (v___x_1128_ == 0)
{
lean_inc(v_ref_1119_);
v___y_1107_ = v_optionFlags_1120_;
v___y_1108_ = v_toCold_1117_;
v___y_1109_ = v_suppressElabErrors_1121_;
v___y_1110_ = v_currRecDepth_1118_;
v___y_1111_ = v_isRecordingDeps_1122_;
v___y_1112_ = v_ref_1119_;
goto v___jp_1106_;
}
else
{
lean_object* v___x_1129_; 
lean_dec_ref(v_x_1091_);
lean_inc(v_ref_1119_);
v___x_1129_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_1119_);
v___y_1097_ = v___x_1129_;
goto v___jp_1096_;
}
}
else
{
lean_inc(v_ref_1119_);
v___y_1107_ = v_optionFlags_1120_;
v___y_1108_ = v_toCold_1117_;
v___y_1109_ = v_suppressElabErrors_1121_;
v___y_1110_ = v_currRecDepth_1118_;
v___y_1111_ = v_isRecordingDeps_1122_;
v___y_1112_ = v_ref_1119_;
goto v___jp_1106_;
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
v___x_1291_ = lean_box(0);
v___x_1292_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6___redArg(v___x_1290_, v_e_1287_, v_a_1288_);
v___x_1293_ = lean_st_ref_put(v_a_1286_, v___x_1292_);
return v___x_1291_;
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
lean_object* v_v_1343_; lean_object* v___x_1344_; lean_object* v_bs_x27_1345_; lean_object* v___x_1346_; 
v_v_1343_ = lean_array_uget(v_bs_1336_, v_i_1335_);
v___x_1344_ = lean_unsigned_to_nat(0u);
v_bs_x27_1345_ = lean_array_uset(v_bs_1336_, v_i_1335_, v___x_1344_);
lean_inc_ref(v_post_1333_);
lean_inc_ref(v_pre_1332_);
v___x_1346_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1332_, v_post_1333_, v_v_1343_, v___y_1337_, v___y_1338_, v___y_1339_);
if (lean_obj_tag(v___x_1346_) == 0)
{
lean_object* v_a_1347_; size_t v___x_1348_; size_t v___x_1349_; lean_object* v___x_1350_; 
v_a_1347_ = lean_ctor_get(v___x_1346_, 0);
lean_inc(v_a_1347_);
lean_dec_ref_known(v___x_1346_, 1);
v___x_1348_ = ((size_t)1ULL);
v___x_1349_ = lean_usize_add(v_i_1335_, v___x_1348_);
v___x_1350_ = lean_array_uset(v_bs_x27_1345_, v_i_1335_, v_a_1347_);
v_i_1335_ = v___x_1349_;
v_bs_1336_ = v___x_1350_;
goto _start;
}
else
{
lean_object* v_a_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1359_; 
lean_dec_ref(v_bs_x27_1345_);
lean_dec_ref(v_post_1333_);
lean_dec_ref(v_pre_1332_);
v_a_1352_ = lean_ctor_get(v___x_1346_, 0);
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1346_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1354_ = v___x_1346_;
v_isShared_1355_ = v_isSharedCheck_1359_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_a_1352_);
lean_dec(v___x_1346_);
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
lean_object* v___f_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_3322__overap_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; 
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
v___x_3322__overap_1839_ = l_Lean_Meta_withIncRecDepth___redArg(v___x_1828_, v___x_1829_, v___x_1838_);
lean_inc(v_a_1830_);
v___x_1840_ = lean_apply_1(v___x_3322__overap_1839_, v_a_1830_);
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
uint8_t v___x_1867_; lean_object* v___x_3341__overap_1868_; lean_object* v___x_1869_; 
v___x_1867_ = 0;
v___x_3341__overap_1868_ = l_Lean_Meta_withLetDecl___redArg(v___x_1859_, v___x_1860_, v_declName_1861_, v_a_1862_, v_a_1866_, v___f_1863_, v_nondep_1864_, v___x_1867_);
lean_inc(v_a_1865_);
v___x_1869_ = lean_apply_1(v___x_3341__overap_1868_, v_a_1865_);
return v___x_1869_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__1___boxed(lean_object* v___x_1870_, lean_object* v___x_1871_, lean_object* v_declName_1872_, lean_object* v_a_1873_, lean_object* v___f_1874_, lean_object* v_nondep_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_){
_start:
{
uint8_t v_nondep_3520__boxed_1878_; lean_object* v_res_1879_; 
v_nondep_3520__boxed_1878_ = lean_unbox(v_nondep_1875_);
v_res_1879_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__1(v___x_1870_, v___x_1871_, v_declName_1872_, v_a_1873_, v___f_1874_, v_nondep_3520__boxed_1878_, v_a_1876_, v_a_1877_);
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
uint8_t v___x_1934_; lean_object* v___x_3399__overap_1935_; lean_object* v___x_1936_; 
v___x_1934_ = 0;
v___x_3399__overap_1935_ = l_Lean_Meta_withLocalDecl___redArg(v___x_1927_, v___x_1928_, v_binderName_1929_, v_binderInfo_1930_, v_a_1933_, v___f_1931_, v___x_1934_);
lean_inc(v_a_1932_);
v___x_1936_ = lean_apply_1(v___x_3399__overap_1935_, v_a_1932_);
return v___x_1936_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1___boxed(lean_object* v___x_1937_, lean_object* v___x_1938_, lean_object* v_binderName_1939_, lean_object* v_binderInfo_1940_, lean_object* v___f_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_){
_start:
{
uint8_t v_binderInfo_3588__boxed_1944_; lean_object* v_res_1945_; 
v_binderInfo_3588__boxed_1944_ = lean_unbox(v_binderInfo_1940_);
v_res_1945_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1(v___x_1937_, v___x_1938_, v_binderName_1939_, v_binderInfo_3588__boxed_1944_, v___f_1941_, v_a_1942_, v_a_1943_);
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
lean_object* v_paramInfo_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___f_2146_; lean_object* v___x_3159__overap_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; 
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
v___x_3159__overap_2147_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_2146_, v___x_2142_, v_args_2137_, lean_box(0));
lean_inc(v___y_2138_);
v___x_2148_ = lean_apply_1(v___x_3159__overap_2147_, v___y_2138_);
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
lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___f_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; size_t v_sz_2197_; size_t v___x_2198_; lean_object* v___x_3172__overap_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; 
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
v___x_3172__overap_2199_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2183_, v___x_2196_, v_sz_2197_, v___x_2198_, v_args_2182_);
v___x_2200_ = lean_apply_1(v___x_3172__overap_2199_, v___y_2188_);
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
uint8_t v_nondep_3730__boxed_2538_; uint8_t v_usedLetOnly_boxed_2539_; uint8_t v_skipConstInApp_boxed_2540_; uint8_t v_skipInstances_boxed_2541_; lean_object* v_res_2542_; 
v_nondep_3730__boxed_2538_ = lean_unbox(v_nondep_2522_);
v_usedLetOnly_boxed_2539_ = lean_unbox(v_usedLetOnly_2531_);
v_skipConstInApp_boxed_2540_ = lean_unbox(v_skipConstInApp_2532_);
v_skipInstances_boxed_2541_ = lean_unbox(v_skipInstances_2533_);
v_res_2542_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__2(v___x_2518_, v___x_2519_, v_declName_2520_, v___f_2521_, v_nondep_3730__boxed_2538_, v_a_2523_, v_value_2524_, v_fvars_2525_, v_inst_2526_, v_inst_2527_, v_inst_2528_, v_pre_2529_, v_post_2530_, v_usedLetOnly_boxed_2539_, v_skipConstInApp_boxed_2540_, v_skipInstances_boxed_2541_, v_x_2534_, v_x_2535_, v_toBind_2536_, v_a_2537_);
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
lean_object* v_dummy_2697_; lean_object* v_nargs_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_3276__overap_2702_; lean_object* v___x_2703_; 
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
v___x_3276__overap_2702_ = l_Lean_Expr_withAppAux___redArg(v___f_2685_, v___y_2690_, v___x_2699_, v___x_2701_);
lean_inc(v___y_2684_);
v___x_2703_ = lean_apply_1(v___x_3276__overap_2702_, v___y_2684_);
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
uint8_t v_usedLetOnly_boxed_3292_; uint8_t v_skipConstInApp_boxed_3293_; uint8_t v___x_115__boxed_3294_; lean_object* v_res_3295_; 
v_usedLetOnly_boxed_3292_ = lean_unbox(v_usedLetOnly_3286_);
v_skipConstInApp_boxed_3293_ = lean_unbox(v_skipConstInApp_3287_);
v___x_115__boxed_3294_ = lean_unbox(v___x_3288_);
v_res_3295_ = l_Lean_Meta_transform___redArg___lam__5(v_toPure_3278_, v_x_3279_, v_toBind_3280_, v_inst_3281_, v_inst_3282_, v_inst_3283_, v_pre_3284_, v_post_3285_, v_usedLetOnly_boxed_3292_, v_skipConstInApp_boxed_3293_, v___x_115__boxed_3294_, v_x_3289_, v_input_3290_, v_ref_3291_);
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
lean_object* v___y_3737_; lean_object* v_toCold_3746_; lean_object* v_currRecDepth_3747_; lean_object* v_ref_3748_; uint16_t v_optionFlags_3749_; uint8_t v_suppressElabErrors_3750_; uint8_t v_isRecordingDeps_3751_; lean_object* v_maxRecDepth_3757_; lean_object* v___x_3758_; uint8_t v___x_3759_; 
v_toCold_3746_ = lean_ctor_get(v___y_3733_, 0);
v_currRecDepth_3747_ = lean_ctor_get(v___y_3733_, 1);
v_ref_3748_ = lean_ctor_get(v___y_3733_, 2);
v_optionFlags_3749_ = lean_ctor_get_uint16(v___y_3733_, sizeof(void*)*3);
v_suppressElabErrors_3750_ = lean_ctor_get_uint8(v___y_3733_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3751_ = lean_ctor_get_uint8(v___y_3733_, sizeof(void*)*3 + 3);
v_maxRecDepth_3757_ = lean_ctor_get(v_toCold_3746_, 3);
v___x_3758_ = lean_unsigned_to_nat(0u);
v___x_3759_ = lean_nat_dec_eq(v_maxRecDepth_3757_, v___x_3758_);
if (v___x_3759_ == 0)
{
uint8_t v___x_3760_; 
v___x_3760_ = lean_nat_dec_eq(v_currRecDepth_3747_, v_maxRecDepth_3757_);
if (v___x_3760_ == 0)
{
goto v___jp_3752_;
}
else
{
lean_object* v___x_3761_; 
lean_dec_ref(v_x_3729_);
lean_inc(v_ref_3748_);
v___x_3761_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg(v_ref_3748_);
v___y_3737_ = v___x_3761_;
goto v___jp_3736_;
}
}
else
{
goto v___jp_3752_;
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
v___jp_3752_:
{
lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; 
v___x_3753_ = lean_unsigned_to_nat(1u);
v___x_3754_ = lean_nat_add(v_currRecDepth_3747_, v___x_3753_);
lean_inc(v_ref_3748_);
lean_inc_ref(v_toCold_3746_);
v___x_3755_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3755_, 0, v_toCold_3746_);
lean_ctor_set(v___x_3755_, 1, v___x_3754_);
lean_ctor_set(v___x_3755_, 2, v_ref_3748_);
lean_ctor_set_uint16(v___x_3755_, sizeof(void*)*3, v_optionFlags_3749_);
lean_ctor_set_uint8(v___x_3755_, sizeof(void*)*3 + 2, v_suppressElabErrors_3750_);
lean_ctor_set_uint8(v___x_3755_, sizeof(void*)*3 + 3, v_isRecordingDeps_3751_);
lean_inc(v___y_3734_);
lean_inc(v___y_3732_);
lean_inc_ref(v___y_3731_);
lean_inc(v___y_3730_);
v___x_3756_ = lean_apply_6(v_x_3729_, v___y_3730_, v___y_3731_, v___y_3732_, v___x_3755_, v___y_3734_, lean_box(0));
v___y_3737_ = v___x_3756_;
goto v___jp_3736_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg___boxed(lean_object* v_x_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_){
_start:
{
lean_object* v_res_3769_; 
v_res_3769_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg(v_x_3762_, v___y_3763_, v___y_3764_, v___y_3765_, v___y_3766_, v___y_3767_);
lean_dec(v___y_3767_);
lean_dec_ref(v___y_3766_);
lean_dec(v___y_3765_);
lean_dec_ref(v___y_3764_);
lean_dec(v___y_3763_);
return v_res_3769_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___lam__0___boxed(lean_object* v_fvars_3770_, lean_object* v_pre_3771_, lean_object* v_post_3772_, lean_object* v_usedLetOnly_3773_, lean_object* v_skipConstInApp_3774_, lean_object* v_skipInstances_3775_, lean_object* v_body_3776_, lean_object* v_x_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_){
_start:
{
uint8_t v_usedLetOnly_boxed_3784_; uint8_t v_skipConstInApp_boxed_3785_; uint8_t v_skipInstances_boxed_3786_; lean_object* v_res_3787_; 
v_usedLetOnly_boxed_3784_ = lean_unbox(v_usedLetOnly_3773_);
v_skipConstInApp_boxed_3785_ = lean_unbox(v_skipConstInApp_3774_);
v_skipInstances_boxed_3786_ = lean_unbox(v_skipInstances_3775_);
v_res_3787_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___lam__0(v_fvars_3770_, v_pre_3771_, v_post_3772_, v_usedLetOnly_boxed_3784_, v_skipConstInApp_boxed_3785_, v_skipInstances_boxed_3786_, v_body_3776_, v_x_3777_, v___y_3778_, v___y_3779_, v___y_3780_, v___y_3781_, v___y_3782_);
lean_dec(v___y_3782_);
lean_dec_ref(v___y_3781_);
lean_dec(v___y_3780_);
lean_dec_ref(v___y_3779_);
lean_dec(v___y_3778_);
return v_res_3787_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___lam__0(lean_object* v_fvars_3788_, lean_object* v_pre_3789_, lean_object* v_post_3790_, uint8_t v_usedLetOnly_3791_, uint8_t v_skipConstInApp_3792_, uint8_t v_skipInstances_3793_, lean_object* v_body_3794_, lean_object* v_x_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_){
_start:
{
lean_object* v___x_3802_; lean_object* v___x_3803_; 
v___x_3802_ = lean_array_push(v_fvars_3788_, v_x_3795_);
v___x_3803_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6(v_pre_3789_, v_post_3790_, v_usedLetOnly_3791_, v_skipConstInApp_3792_, v_skipInstances_3793_, v___x_3802_, v_body_3794_, v___y_3796_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_);
return v___x_3803_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___lam__0___boxed(lean_object* v_fvars_3804_, lean_object* v_pre_3805_, lean_object* v_post_3806_, lean_object* v_usedLetOnly_3807_, lean_object* v_skipConstInApp_3808_, lean_object* v_skipInstances_3809_, lean_object* v_body_3810_, lean_object* v_x_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_){
_start:
{
uint8_t v_usedLetOnly_boxed_3818_; uint8_t v_skipConstInApp_boxed_3819_; uint8_t v_skipInstances_boxed_3820_; lean_object* v_res_3821_; 
v_usedLetOnly_boxed_3818_ = lean_unbox(v_usedLetOnly_3807_);
v_skipConstInApp_boxed_3819_ = lean_unbox(v_skipConstInApp_3808_);
v_skipInstances_boxed_3820_ = lean_unbox(v_skipInstances_3809_);
v_res_3821_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___lam__0(v_fvars_3804_, v_pre_3805_, v_post_3806_, v_usedLetOnly_boxed_3818_, v_skipConstInApp_boxed_3819_, v_skipInstances_boxed_3820_, v_body_3810_, v_x_3811_, v___y_3812_, v___y_3813_, v___y_3814_, v___y_3815_, v___y_3816_);
lean_dec(v___y_3816_);
lean_dec_ref(v___y_3815_);
lean_dec(v___y_3814_);
lean_dec_ref(v___y_3813_);
lean_dec(v___y_3812_);
return v_res_3821_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(lean_object* v_pre_3822_, lean_object* v_post_3823_, uint8_t v_usedLetOnly_3824_, uint8_t v_skipConstInApp_3825_, uint8_t v_skipInstances_3826_, lean_object* v_e_3827_, lean_object* v_a_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_){
_start:
{
lean_object* v___x_3834_; 
lean_inc_ref(v_post_3823_);
lean_inc(v___y_3832_);
lean_inc_ref(v___y_3831_);
lean_inc(v___y_3830_);
lean_inc_ref(v___y_3829_);
lean_inc_ref(v_e_3827_);
v___x_3834_ = lean_apply_6(v_post_3823_, v_e_3827_, v___y_3829_, v___y_3830_, v___y_3831_, v___y_3832_, lean_box(0));
if (lean_obj_tag(v___x_3834_) == 0)
{
lean_object* v_a_3835_; lean_object* v___x_3837_; uint8_t v_isShared_3838_; uint8_t v_isSharedCheck_3853_; 
v_a_3835_ = lean_ctor_get(v___x_3834_, 0);
v_isSharedCheck_3853_ = !lean_is_exclusive(v___x_3834_);
if (v_isSharedCheck_3853_ == 0)
{
v___x_3837_ = v___x_3834_;
v_isShared_3838_ = v_isSharedCheck_3853_;
goto v_resetjp_3836_;
}
else
{
lean_inc(v_a_3835_);
lean_dec(v___x_3834_);
v___x_3837_ = lean_box(0);
v_isShared_3838_ = v_isSharedCheck_3853_;
goto v_resetjp_3836_;
}
v_resetjp_3836_:
{
switch(lean_obj_tag(v_a_3835_))
{
case 0:
{
lean_object* v_e_3839_; lean_object* v___x_3841_; 
lean_dec_ref(v_e_3827_);
lean_dec_ref(v_post_3823_);
lean_dec_ref(v_pre_3822_);
v_e_3839_ = lean_ctor_get(v_a_3835_, 0);
lean_inc_ref(v_e_3839_);
lean_dec_ref_known(v_a_3835_, 1);
if (v_isShared_3838_ == 0)
{
lean_ctor_set(v___x_3837_, 0, v_e_3839_);
v___x_3841_ = v___x_3837_;
goto v_reusejp_3840_;
}
else
{
lean_object* v_reuseFailAlloc_3842_; 
v_reuseFailAlloc_3842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3842_, 0, v_e_3839_);
v___x_3841_ = v_reuseFailAlloc_3842_;
goto v_reusejp_3840_;
}
v_reusejp_3840_:
{
return v___x_3841_;
}
}
case 1:
{
lean_object* v_e_3843_; lean_object* v___x_3844_; 
lean_del_object(v___x_3837_);
lean_dec_ref(v_e_3827_);
v_e_3843_ = lean_ctor_get(v_a_3835_, 0);
lean_inc_ref(v_e_3843_);
lean_dec_ref_known(v_a_3835_, 1);
v___x_3844_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3822_, v_post_3823_, v_usedLetOnly_3824_, v_skipConstInApp_3825_, v_skipInstances_3826_, v_e_3843_, v_a_3828_, v___y_3829_, v___y_3830_, v___y_3831_, v___y_3832_);
return v___x_3844_;
}
default: 
{
lean_object* v_e_x3f_3845_; 
lean_dec_ref(v_post_3823_);
lean_dec_ref(v_pre_3822_);
v_e_x3f_3845_ = lean_ctor_get(v_a_3835_, 0);
lean_inc(v_e_x3f_3845_);
lean_dec_ref_known(v_a_3835_, 1);
if (lean_obj_tag(v_e_x3f_3845_) == 0)
{
lean_object* v___x_3847_; 
if (v_isShared_3838_ == 0)
{
lean_ctor_set(v___x_3837_, 0, v_e_3827_);
v___x_3847_ = v___x_3837_;
goto v_reusejp_3846_;
}
else
{
lean_object* v_reuseFailAlloc_3848_; 
v_reuseFailAlloc_3848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3848_, 0, v_e_3827_);
v___x_3847_ = v_reuseFailAlloc_3848_;
goto v_reusejp_3846_;
}
v_reusejp_3846_:
{
return v___x_3847_;
}
}
else
{
lean_object* v_val_3849_; lean_object* v___x_3851_; 
lean_dec_ref(v_e_3827_);
v_val_3849_ = lean_ctor_get(v_e_x3f_3845_, 0);
lean_inc(v_val_3849_);
lean_dec_ref_known(v_e_x3f_3845_, 1);
if (v_isShared_3838_ == 0)
{
lean_ctor_set(v___x_3837_, 0, v_val_3849_);
v___x_3851_ = v___x_3837_;
goto v_reusejp_3850_;
}
else
{
lean_object* v_reuseFailAlloc_3852_; 
v_reuseFailAlloc_3852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3852_, 0, v_val_3849_);
v___x_3851_ = v_reuseFailAlloc_3852_;
goto v_reusejp_3850_;
}
v_reusejp_3850_:
{
return v___x_3851_;
}
}
}
}
}
}
else
{
lean_object* v_a_3854_; lean_object* v___x_3856_; uint8_t v_isShared_3857_; uint8_t v_isSharedCheck_3861_; 
lean_dec_ref(v_e_3827_);
lean_dec_ref(v_post_3823_);
lean_dec_ref(v_pre_3822_);
v_a_3854_ = lean_ctor_get(v___x_3834_, 0);
v_isSharedCheck_3861_ = !lean_is_exclusive(v___x_3834_);
if (v_isSharedCheck_3861_ == 0)
{
v___x_3856_ = v___x_3834_;
v_isShared_3857_ = v_isSharedCheck_3861_;
goto v_resetjp_3855_;
}
else
{
lean_inc(v_a_3854_);
lean_dec(v___x_3834_);
v___x_3856_ = lean_box(0);
v_isShared_3857_ = v_isSharedCheck_3861_;
goto v_resetjp_3855_;
}
v_resetjp_3855_:
{
lean_object* v___x_3859_; 
if (v_isShared_3857_ == 0)
{
v___x_3859_ = v___x_3856_;
goto v_reusejp_3858_;
}
else
{
lean_object* v_reuseFailAlloc_3860_; 
v_reuseFailAlloc_3860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3860_, 0, v_a_3854_);
v___x_3859_ = v_reuseFailAlloc_3860_;
goto v_reusejp_3858_;
}
v_reusejp_3858_:
{
return v___x_3859_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6(lean_object* v_pre_3862_, lean_object* v_post_3863_, uint8_t v_usedLetOnly_3864_, uint8_t v_skipConstInApp_3865_, uint8_t v_skipInstances_3866_, lean_object* v_fvars_3867_, lean_object* v_e_3868_, lean_object* v_a_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_){
_start:
{
if (lean_obj_tag(v_e_3868_) == 6)
{
lean_object* v_binderName_3875_; lean_object* v_binderType_3876_; lean_object* v_body_3877_; uint8_t v_binderInfo_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___f_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; 
v_binderName_3875_ = lean_ctor_get(v_e_3868_, 0);
lean_inc(v_binderName_3875_);
v_binderType_3876_ = lean_ctor_get(v_e_3868_, 1);
lean_inc_ref(v_binderType_3876_);
v_body_3877_ = lean_ctor_get(v_e_3868_, 2);
lean_inc_ref(v_body_3877_);
v_binderInfo_3878_ = lean_ctor_get_uint8(v_e_3868_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_3868_, 3);
v___x_3879_ = lean_box(v_usedLetOnly_3864_);
v___x_3880_ = lean_box(v_skipConstInApp_3865_);
v___x_3881_ = lean_box(v_skipInstances_3866_);
lean_inc_ref(v_post_3863_);
lean_inc_ref(v_pre_3862_);
lean_inc_ref(v_fvars_3867_);
v___f_3882_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___lam__0___boxed), 14, 7);
lean_closure_set(v___f_3882_, 0, v_fvars_3867_);
lean_closure_set(v___f_3882_, 1, v_pre_3862_);
lean_closure_set(v___f_3882_, 2, v_post_3863_);
lean_closure_set(v___f_3882_, 3, v___x_3879_);
lean_closure_set(v___f_3882_, 4, v___x_3880_);
lean_closure_set(v___f_3882_, 5, v___x_3881_);
lean_closure_set(v___f_3882_, 6, v_body_3877_);
v___x_3883_ = lean_expr_instantiate_rev(v_binderType_3876_, v_fvars_3867_);
lean_dec_ref(v_fvars_3867_);
lean_dec_ref(v_binderType_3876_);
v___x_3884_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3862_, v_post_3863_, v_usedLetOnly_3864_, v_skipConstInApp_3865_, v_skipInstances_3866_, v___x_3883_, v_a_3869_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_);
if (lean_obj_tag(v___x_3884_) == 0)
{
lean_object* v_a_3885_; uint8_t v___x_3886_; lean_object* v___x_3887_; 
v_a_3885_ = lean_ctor_get(v___x_3884_, 0);
lean_inc(v_a_3885_);
lean_dec_ref_known(v___x_3884_, 1);
v___x_3886_ = 0;
v___x_3887_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_binderName_3875_, v_binderInfo_3878_, v_a_3885_, v___f_3882_, v___x_3886_, v_a_3869_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_);
return v___x_3887_;
}
else
{
lean_dec_ref(v___f_3882_);
lean_dec(v_binderName_3875_);
return v___x_3884_;
}
}
else
{
lean_object* v___x_3888_; lean_object* v___x_3889_; 
v___x_3888_ = lean_expr_instantiate_rev(v_e_3868_, v_fvars_3867_);
lean_dec_ref(v_e_3868_);
lean_inc_ref(v_post_3863_);
lean_inc_ref(v_pre_3862_);
v___x_3889_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3862_, v_post_3863_, v_usedLetOnly_3864_, v_skipConstInApp_3865_, v_skipInstances_3866_, v___x_3888_, v_a_3869_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_);
if (lean_obj_tag(v___x_3889_) == 0)
{
lean_object* v_a_3890_; uint8_t v___x_3891_; uint8_t v___x_3892_; uint8_t v___x_3893_; lean_object* v___x_3894_; 
v_a_3890_ = lean_ctor_get(v___x_3889_, 0);
lean_inc(v_a_3890_);
lean_dec_ref_known(v___x_3889_, 1);
v___x_3891_ = 0;
v___x_3892_ = 1;
v___x_3893_ = 1;
v___x_3894_ = l_Lean_Meta_mkLambdaFVars(v_fvars_3867_, v_a_3890_, v___x_3891_, v_usedLetOnly_3864_, v___x_3891_, v___x_3892_, v___x_3893_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_);
lean_dec_ref(v_fvars_3867_);
if (lean_obj_tag(v___x_3894_) == 0)
{
lean_object* v_a_3895_; lean_object* v___x_3896_; 
v_a_3895_ = lean_ctor_get(v___x_3894_, 0);
lean_inc(v_a_3895_);
lean_dec_ref_known(v___x_3894_, 1);
v___x_3896_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_3862_, v_post_3863_, v_usedLetOnly_3864_, v_skipConstInApp_3865_, v_skipInstances_3866_, v_a_3895_, v_a_3869_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_);
return v___x_3896_;
}
else
{
lean_dec_ref(v_post_3863_);
lean_dec_ref(v_pre_3862_);
return v___x_3894_;
}
}
else
{
lean_dec_ref(v_fvars_3867_);
lean_dec_ref(v_post_3863_);
lean_dec_ref(v_pre_3862_);
return v___x_3889_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___lam__0(lean_object* v_fvars_3897_, lean_object* v_pre_3898_, lean_object* v_post_3899_, uint8_t v_usedLetOnly_3900_, uint8_t v_skipConstInApp_3901_, uint8_t v_skipInstances_3902_, lean_object* v_body_3903_, lean_object* v_x_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_){
_start:
{
lean_object* v___x_3911_; lean_object* v___x_3912_; 
v___x_3911_ = lean_array_push(v_fvars_3897_, v_x_3904_);
v___x_3912_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7(v_pre_3898_, v_post_3899_, v_usedLetOnly_3900_, v_skipConstInApp_3901_, v_skipInstances_3902_, v___x_3911_, v_body_3903_, v___y_3905_, v___y_3906_, v___y_3907_, v___y_3908_, v___y_3909_);
return v___x_3912_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___lam__0___boxed(lean_object* v_fvars_3913_, lean_object* v_pre_3914_, lean_object* v_post_3915_, lean_object* v_usedLetOnly_3916_, lean_object* v_skipConstInApp_3917_, lean_object* v_skipInstances_3918_, lean_object* v_body_3919_, lean_object* v_x_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_){
_start:
{
uint8_t v_usedLetOnly_boxed_3927_; uint8_t v_skipConstInApp_boxed_3928_; uint8_t v_skipInstances_boxed_3929_; lean_object* v_res_3930_; 
v_usedLetOnly_boxed_3927_ = lean_unbox(v_usedLetOnly_3916_);
v_skipConstInApp_boxed_3928_ = lean_unbox(v_skipConstInApp_3917_);
v_skipInstances_boxed_3929_ = lean_unbox(v_skipInstances_3918_);
v_res_3930_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___lam__0(v_fvars_3913_, v_pre_3914_, v_post_3915_, v_usedLetOnly_boxed_3927_, v_skipConstInApp_boxed_3928_, v_skipInstances_boxed_3929_, v_body_3919_, v_x_3920_, v___y_3921_, v___y_3922_, v___y_3923_, v___y_3924_, v___y_3925_);
lean_dec(v___y_3925_);
lean_dec_ref(v___y_3924_);
lean_dec(v___y_3923_);
lean_dec_ref(v___y_3922_);
lean_dec(v___y_3921_);
return v_res_3930_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7(lean_object* v_pre_3931_, lean_object* v_post_3932_, uint8_t v_usedLetOnly_3933_, uint8_t v_skipConstInApp_3934_, uint8_t v_skipInstances_3935_, lean_object* v_fvars_3936_, lean_object* v_e_3937_, lean_object* v_a_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_){
_start:
{
if (lean_obj_tag(v_e_3937_) == 8)
{
lean_object* v_declName_3944_; lean_object* v_type_3945_; lean_object* v_value_3946_; lean_object* v_body_3947_; uint8_t v_nondep_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___f_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; 
v_declName_3944_ = lean_ctor_get(v_e_3937_, 0);
lean_inc(v_declName_3944_);
v_type_3945_ = lean_ctor_get(v_e_3937_, 1);
lean_inc_ref(v_type_3945_);
v_value_3946_ = lean_ctor_get(v_e_3937_, 2);
lean_inc_ref(v_value_3946_);
v_body_3947_ = lean_ctor_get(v_e_3937_, 3);
lean_inc_ref(v_body_3947_);
v_nondep_3948_ = lean_ctor_get_uint8(v_e_3937_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_3937_, 4);
v___x_3949_ = lean_box(v_usedLetOnly_3933_);
v___x_3950_ = lean_box(v_skipConstInApp_3934_);
v___x_3951_ = lean_box(v_skipInstances_3935_);
lean_inc_ref_n(v_post_3932_, 2);
lean_inc_ref_n(v_pre_3931_, 2);
lean_inc_ref(v_fvars_3936_);
v___f_3952_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___lam__0___boxed), 14, 7);
lean_closure_set(v___f_3952_, 0, v_fvars_3936_);
lean_closure_set(v___f_3952_, 1, v_pre_3931_);
lean_closure_set(v___f_3952_, 2, v_post_3932_);
lean_closure_set(v___f_3952_, 3, v___x_3949_);
lean_closure_set(v___f_3952_, 4, v___x_3950_);
lean_closure_set(v___f_3952_, 5, v___x_3951_);
lean_closure_set(v___f_3952_, 6, v_body_3947_);
v___x_3953_ = lean_expr_instantiate_rev(v_type_3945_, v_fvars_3936_);
lean_dec_ref(v_type_3945_);
v___x_3954_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3931_, v_post_3932_, v_usedLetOnly_3933_, v_skipConstInApp_3934_, v_skipInstances_3935_, v___x_3953_, v_a_3938_, v___y_3939_, v___y_3940_, v___y_3941_, v___y_3942_);
if (lean_obj_tag(v___x_3954_) == 0)
{
lean_object* v_a_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; 
v_a_3955_ = lean_ctor_get(v___x_3954_, 0);
lean_inc(v_a_3955_);
lean_dec_ref_known(v___x_3954_, 1);
v___x_3956_ = lean_expr_instantiate_rev(v_value_3946_, v_fvars_3936_);
lean_dec_ref(v_fvars_3936_);
lean_dec_ref(v_value_3946_);
v___x_3957_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3931_, v_post_3932_, v_usedLetOnly_3933_, v_skipConstInApp_3934_, v_skipInstances_3935_, v___x_3956_, v_a_3938_, v___y_3939_, v___y_3940_, v___y_3941_, v___y_3942_);
if (lean_obj_tag(v___x_3957_) == 0)
{
lean_object* v_a_3958_; uint8_t v___x_3959_; lean_object* v___x_3960_; 
v_a_3958_ = lean_ctor_get(v___x_3957_, 0);
lean_inc(v_a_3958_);
lean_dec_ref_known(v___x_3957_, 1);
v___x_3959_ = 0;
v___x_3960_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg(v_declName_3944_, v_a_3955_, v_a_3958_, v___f_3952_, v_nondep_3948_, v___x_3959_, v_a_3938_, v___y_3939_, v___y_3940_, v___y_3941_, v___y_3942_);
return v___x_3960_;
}
else
{
lean_dec(v_a_3955_);
lean_dec_ref(v___f_3952_);
lean_dec(v_declName_3944_);
return v___x_3957_;
}
}
else
{
lean_dec_ref(v___f_3952_);
lean_dec_ref(v_value_3946_);
lean_dec(v_declName_3944_);
lean_dec_ref(v_fvars_3936_);
lean_dec_ref(v_post_3932_);
lean_dec_ref(v_pre_3931_);
return v___x_3954_;
}
}
else
{
lean_object* v___x_3961_; lean_object* v___x_3962_; 
v___x_3961_ = lean_expr_instantiate_rev(v_e_3937_, v_fvars_3936_);
lean_dec_ref(v_e_3937_);
lean_inc_ref(v_post_3932_);
lean_inc_ref(v_pre_3931_);
v___x_3962_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3931_, v_post_3932_, v_usedLetOnly_3933_, v_skipConstInApp_3934_, v_skipInstances_3935_, v___x_3961_, v_a_3938_, v___y_3939_, v___y_3940_, v___y_3941_, v___y_3942_);
if (lean_obj_tag(v___x_3962_) == 0)
{
lean_object* v_a_3963_; uint8_t v___x_3964_; uint8_t v___x_3965_; lean_object* v___x_3966_; 
v_a_3963_ = lean_ctor_get(v___x_3962_, 0);
lean_inc(v_a_3963_);
lean_dec_ref_known(v___x_3962_, 1);
v___x_3964_ = 0;
v___x_3965_ = 1;
v___x_3966_ = l_Lean_Meta_mkLetFVars(v_fvars_3936_, v_a_3963_, v_usedLetOnly_3933_, v___x_3964_, v___x_3965_, v___y_3939_, v___y_3940_, v___y_3941_, v___y_3942_);
lean_dec_ref(v_fvars_3936_);
if (lean_obj_tag(v___x_3966_) == 0)
{
lean_object* v_a_3967_; lean_object* v___x_3968_; 
v_a_3967_ = lean_ctor_get(v___x_3966_, 0);
lean_inc(v_a_3967_);
lean_dec_ref_known(v___x_3966_, 1);
v___x_3968_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_3931_, v_post_3932_, v_usedLetOnly_3933_, v_skipConstInApp_3934_, v_skipInstances_3935_, v_a_3967_, v_a_3938_, v___y_3939_, v___y_3940_, v___y_3941_, v___y_3942_);
return v___x_3968_;
}
else
{
lean_dec_ref(v_post_3932_);
lean_dec_ref(v_pre_3931_);
return v___x_3966_;
}
}
else
{
lean_dec_ref(v_fvars_3936_);
lean_dec_ref(v_post_3932_);
lean_dec_ref(v_pre_3931_);
return v___x_3962_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__2(lean_object* v_pre_3969_, lean_object* v_post_3970_, uint8_t v_usedLetOnly_3971_, uint8_t v_skipConstInApp_3972_, uint8_t v_skipInstances_3973_, size_t v_sz_3974_, size_t v_i_3975_, lean_object* v_bs_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_){
_start:
{
uint8_t v___x_3983_; 
v___x_3983_ = lean_usize_dec_lt(v_i_3975_, v_sz_3974_);
if (v___x_3983_ == 0)
{
lean_object* v___x_3984_; 
lean_dec_ref(v_post_3970_);
lean_dec_ref(v_pre_3969_);
v___x_3984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3984_, 0, v_bs_3976_);
return v___x_3984_;
}
else
{
lean_object* v_v_3985_; lean_object* v___x_3986_; lean_object* v_bs_x27_3987_; lean_object* v___x_3988_; 
v_v_3985_ = lean_array_uget(v_bs_3976_, v_i_3975_);
v___x_3986_ = lean_unsigned_to_nat(0u);
v_bs_x27_3987_ = lean_array_uset(v_bs_3976_, v_i_3975_, v___x_3986_);
lean_inc_ref(v_post_3970_);
lean_inc_ref(v_pre_3969_);
v___x_3988_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3969_, v_post_3970_, v_usedLetOnly_3971_, v_skipConstInApp_3972_, v_skipInstances_3973_, v_v_3985_, v___y_3977_, v___y_3978_, v___y_3979_, v___y_3980_, v___y_3981_);
if (lean_obj_tag(v___x_3988_) == 0)
{
lean_object* v_a_3989_; size_t v___x_3990_; size_t v___x_3991_; lean_object* v___x_3992_; 
v_a_3989_ = lean_ctor_get(v___x_3988_, 0);
lean_inc(v_a_3989_);
lean_dec_ref_known(v___x_3988_, 1);
v___x_3990_ = ((size_t)1ULL);
v___x_3991_ = lean_usize_add(v_i_3975_, v___x_3990_);
v___x_3992_ = lean_array_uset(v_bs_x27_3987_, v_i_3975_, v_a_3989_);
v_i_3975_ = v___x_3991_;
v_bs_3976_ = v___x_3992_;
goto _start;
}
else
{
lean_object* v_a_3994_; lean_object* v___x_3996_; uint8_t v_isShared_3997_; uint8_t v_isSharedCheck_4001_; 
lean_dec_ref(v_bs_x27_3987_);
lean_dec_ref(v_post_3970_);
lean_dec_ref(v_pre_3969_);
v_a_3994_ = lean_ctor_get(v___x_3988_, 0);
v_isSharedCheck_4001_ = !lean_is_exclusive(v___x_3988_);
if (v_isSharedCheck_4001_ == 0)
{
v___x_3996_ = v___x_3988_;
v_isShared_3997_ = v_isSharedCheck_4001_;
goto v_resetjp_3995_;
}
else
{
lean_inc(v_a_3994_);
lean_dec(v___x_3988_);
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
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0(lean_object* v_pre_4002_, lean_object* v_post_4003_, uint8_t v_usedLetOnly_4004_, uint8_t v_skipConstInApp_4005_, uint8_t v_skipInstances_4006_, lean_object* v___x_4007_, lean_object* v___y_4008_, lean_object* v_b_4009_, lean_object* v_a_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_){
_start:
{
lean_object* v___x_4016_; 
v___x_4016_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4002_, v_post_4003_, v_usedLetOnly_4004_, v_skipConstInApp_4005_, v_skipInstances_4006_, v___x_4007_, v___y_4008_, v___y_4011_, v___y_4012_, v___y_4013_, v___y_4014_);
if (lean_obj_tag(v___x_4016_) == 0)
{
lean_object* v_a_4017_; lean_object* v___x_4019_; uint8_t v_isShared_4020_; uint8_t v_isSharedCheck_4026_; 
v_a_4017_ = lean_ctor_get(v___x_4016_, 0);
v_isSharedCheck_4026_ = !lean_is_exclusive(v___x_4016_);
if (v_isSharedCheck_4026_ == 0)
{
v___x_4019_ = v___x_4016_;
v_isShared_4020_ = v_isSharedCheck_4026_;
goto v_resetjp_4018_;
}
else
{
lean_inc(v_a_4017_);
lean_dec(v___x_4016_);
v___x_4019_ = lean_box(0);
v_isShared_4020_ = v_isSharedCheck_4026_;
goto v_resetjp_4018_;
}
v_resetjp_4018_:
{
lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4024_; 
v___x_4021_ = lean_array_fset(v_b_4009_, v_a_4010_, v_a_4017_);
v___x_4022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4022_, 0, v___x_4021_);
if (v_isShared_4020_ == 0)
{
lean_ctor_set(v___x_4019_, 0, v___x_4022_);
v___x_4024_ = v___x_4019_;
goto v_reusejp_4023_;
}
else
{
lean_object* v_reuseFailAlloc_4025_; 
v_reuseFailAlloc_4025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4025_, 0, v___x_4022_);
v___x_4024_ = v_reuseFailAlloc_4025_;
goto v_reusejp_4023_;
}
v_reusejp_4023_:
{
return v___x_4024_;
}
}
}
else
{
lean_object* v_a_4027_; lean_object* v___x_4029_; uint8_t v_isShared_4030_; uint8_t v_isSharedCheck_4034_; 
lean_dec_ref(v_b_4009_);
v_a_4027_ = lean_ctor_get(v___x_4016_, 0);
v_isSharedCheck_4034_ = !lean_is_exclusive(v___x_4016_);
if (v_isSharedCheck_4034_ == 0)
{
v___x_4029_ = v___x_4016_;
v_isShared_4030_ = v_isSharedCheck_4034_;
goto v_resetjp_4028_;
}
else
{
lean_inc(v_a_4027_);
lean_dec(v___x_4016_);
v___x_4029_ = lean_box(0);
v_isShared_4030_ = v_isSharedCheck_4034_;
goto v_resetjp_4028_;
}
v_resetjp_4028_:
{
lean_object* v___x_4032_; 
if (v_isShared_4030_ == 0)
{
v___x_4032_ = v___x_4029_;
goto v_reusejp_4031_;
}
else
{
lean_object* v_reuseFailAlloc_4033_; 
v_reuseFailAlloc_4033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4033_, 0, v_a_4027_);
v___x_4032_ = v_reuseFailAlloc_4033_;
goto v_reusejp_4031_;
}
v_reusejp_4031_:
{
return v___x_4032_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed(lean_object* v_pre_4035_, lean_object* v_post_4036_, lean_object* v_usedLetOnly_4037_, lean_object* v_skipConstInApp_4038_, lean_object* v_skipInstances_4039_, lean_object* v___x_4040_, lean_object* v___y_4041_, lean_object* v_b_4042_, lean_object* v_a_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_){
_start:
{
uint8_t v_usedLetOnly_boxed_4049_; uint8_t v_skipConstInApp_boxed_4050_; uint8_t v_skipInstances_boxed_4051_; lean_object* v_res_4052_; 
v_usedLetOnly_boxed_4049_ = lean_unbox(v_usedLetOnly_4037_);
v_skipConstInApp_boxed_4050_ = lean_unbox(v_skipConstInApp_4038_);
v_skipInstances_boxed_4051_ = lean_unbox(v_skipInstances_4039_);
v_res_4052_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0(v_pre_4035_, v_post_4036_, v_usedLetOnly_boxed_4049_, v_skipConstInApp_boxed_4050_, v_skipInstances_boxed_4051_, v___x_4040_, v___y_4041_, v_b_4042_, v_a_4043_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_);
lean_dec(v___y_4047_);
lean_dec_ref(v___y_4046_);
lean_dec(v___y_4045_);
lean_dec_ref(v___y_4044_);
lean_dec(v_a_4043_);
lean_dec(v___y_4041_);
return v_res_4052_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg(lean_object* v_upperBound_4053_, lean_object* v___x_4054_, lean_object* v_pre_4055_, lean_object* v_post_4056_, uint8_t v_usedLetOnly_4057_, uint8_t v_skipConstInApp_4058_, uint8_t v_skipInstances_4059_, lean_object* v_a_4060_, lean_object* v_b_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_){
_start:
{
lean_object* v___y_4069_; uint8_t v___x_4092_; 
v___x_4092_ = lean_nat_dec_lt(v_a_4060_, v_upperBound_4053_);
if (v___x_4092_ == 0)
{
lean_object* v___x_4093_; 
lean_dec(v_a_4060_);
lean_dec_ref(v_post_4056_);
lean_dec_ref(v_pre_4055_);
v___x_4093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4093_, 0, v_b_4061_);
return v___x_4093_;
}
else
{
lean_object* v___x_4094_; lean_object* v___x_4095_; uint8_t v___x_4096_; 
v___x_4094_ = lean_array_fget_borrowed(v_b_4061_, v_a_4060_);
v___x_4095_ = lean_array_get_size(v___x_4054_);
v___x_4096_ = lean_nat_dec_lt(v_a_4060_, v___x_4095_);
if (v___x_4096_ == 0)
{
lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___f_4100_; 
lean_inc(v___x_4094_);
v___x_4097_ = lean_box(v_usedLetOnly_4057_);
v___x_4098_ = lean_box(v_skipConstInApp_4058_);
v___x_4099_ = lean_box(v_skipInstances_4059_);
lean_inc(v_a_4060_);
lean_inc(v___y_4062_);
lean_inc_ref(v_post_4056_);
lean_inc_ref(v_pre_4055_);
v___f_4100_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_4100_, 0, v_pre_4055_);
lean_closure_set(v___f_4100_, 1, v_post_4056_);
lean_closure_set(v___f_4100_, 2, v___x_4097_);
lean_closure_set(v___f_4100_, 3, v___x_4098_);
lean_closure_set(v___f_4100_, 4, v___x_4099_);
lean_closure_set(v___f_4100_, 5, v___x_4094_);
lean_closure_set(v___f_4100_, 6, v___y_4062_);
lean_closure_set(v___f_4100_, 7, v_b_4061_);
lean_closure_set(v___f_4100_, 8, v_a_4060_);
v___y_4069_ = v___f_4100_;
goto v___jp_4068_;
}
else
{
lean_object* v___x_4101_; uint8_t v_isInstance_4102_; 
v___x_4101_ = lean_array_fget_borrowed(v___x_4054_, v_a_4060_);
v_isInstance_4102_ = lean_ctor_get_uint8(v___x_4101_, sizeof(void*)*1 + 4);
if (v_isInstance_4102_ == 0)
{
lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___f_4106_; 
lean_inc(v___x_4094_);
v___x_4103_ = lean_box(v_usedLetOnly_4057_);
v___x_4104_ = lean_box(v_skipConstInApp_4058_);
v___x_4105_ = lean_box(v_skipInstances_4059_);
lean_inc(v_a_4060_);
lean_inc(v___y_4062_);
lean_inc_ref(v_post_4056_);
lean_inc_ref(v_pre_4055_);
v___f_4106_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_4106_, 0, v_pre_4055_);
lean_closure_set(v___f_4106_, 1, v_post_4056_);
lean_closure_set(v___f_4106_, 2, v___x_4103_);
lean_closure_set(v___f_4106_, 3, v___x_4104_);
lean_closure_set(v___f_4106_, 4, v___x_4105_);
lean_closure_set(v___f_4106_, 5, v___x_4094_);
lean_closure_set(v___f_4106_, 6, v___y_4062_);
lean_closure_set(v___f_4106_, 7, v_b_4061_);
lean_closure_set(v___f_4106_, 8, v_a_4060_);
v___y_4069_ = v___f_4106_;
goto v___jp_4068_;
}
else
{
lean_object* v___x_4107_; lean_object* v___f_4108_; 
v___x_4107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4107_, 0, v_b_4061_);
v___f_4108_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_4108_, 0, v___x_4107_);
v___y_4069_ = v___f_4108_;
goto v___jp_4068_;
}
}
}
v___jp_4068_:
{
lean_object* v___x_4070_; 
lean_inc(v___y_4066_);
lean_inc_ref(v___y_4065_);
lean_inc(v___y_4064_);
lean_inc_ref(v___y_4063_);
v___x_4070_ = lean_apply_5(v___y_4069_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_, lean_box(0));
if (lean_obj_tag(v___x_4070_) == 0)
{
lean_object* v_a_4071_; lean_object* v___x_4073_; uint8_t v_isShared_4074_; uint8_t v_isSharedCheck_4083_; 
v_a_4071_ = lean_ctor_get(v___x_4070_, 0);
v_isSharedCheck_4083_ = !lean_is_exclusive(v___x_4070_);
if (v_isSharedCheck_4083_ == 0)
{
v___x_4073_ = v___x_4070_;
v_isShared_4074_ = v_isSharedCheck_4083_;
goto v_resetjp_4072_;
}
else
{
lean_inc(v_a_4071_);
lean_dec(v___x_4070_);
v___x_4073_ = lean_box(0);
v_isShared_4074_ = v_isSharedCheck_4083_;
goto v_resetjp_4072_;
}
v_resetjp_4072_:
{
if (lean_obj_tag(v_a_4071_) == 0)
{
lean_object* v_a_4075_; lean_object* v___x_4077_; 
lean_dec(v_a_4060_);
lean_dec_ref(v_post_4056_);
lean_dec_ref(v_pre_4055_);
v_a_4075_ = lean_ctor_get(v_a_4071_, 0);
lean_inc(v_a_4075_);
lean_dec_ref_known(v_a_4071_, 1);
if (v_isShared_4074_ == 0)
{
lean_ctor_set(v___x_4073_, 0, v_a_4075_);
v___x_4077_ = v___x_4073_;
goto v_reusejp_4076_;
}
else
{
lean_object* v_reuseFailAlloc_4078_; 
v_reuseFailAlloc_4078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4078_, 0, v_a_4075_);
v___x_4077_ = v_reuseFailAlloc_4078_;
goto v_reusejp_4076_;
}
v_reusejp_4076_:
{
return v___x_4077_;
}
}
else
{
lean_object* v_a_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; 
lean_del_object(v___x_4073_);
v_a_4079_ = lean_ctor_get(v_a_4071_, 0);
lean_inc(v_a_4079_);
lean_dec_ref_known(v_a_4071_, 1);
v___x_4080_ = lean_unsigned_to_nat(1u);
v___x_4081_ = lean_nat_add(v_a_4060_, v___x_4080_);
lean_dec(v_a_4060_);
v_a_4060_ = v___x_4081_;
v_b_4061_ = v_a_4079_;
goto _start;
}
}
}
else
{
lean_object* v_a_4084_; lean_object* v___x_4086_; uint8_t v_isShared_4087_; uint8_t v_isSharedCheck_4091_; 
lean_dec(v_a_4060_);
lean_dec_ref(v_post_4056_);
lean_dec_ref(v_pre_4055_);
v_a_4084_ = lean_ctor_get(v___x_4070_, 0);
v_isSharedCheck_4091_ = !lean_is_exclusive(v___x_4070_);
if (v_isSharedCheck_4091_ == 0)
{
v___x_4086_ = v___x_4070_;
v_isShared_4087_ = v_isSharedCheck_4091_;
goto v_resetjp_4085_;
}
else
{
lean_inc(v_a_4084_);
lean_dec(v___x_4070_);
v___x_4086_ = lean_box(0);
v_isShared_4087_ = v_isSharedCheck_4091_;
goto v_resetjp_4085_;
}
v_resetjp_4085_:
{
lean_object* v___x_4089_; 
if (v_isShared_4087_ == 0)
{
v___x_4089_ = v___x_4086_;
goto v_reusejp_4088_;
}
else
{
lean_object* v_reuseFailAlloc_4090_; 
v_reuseFailAlloc_4090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4090_, 0, v_a_4084_);
v___x_4089_ = v_reuseFailAlloc_4090_;
goto v_reusejp_4088_;
}
v_reusejp_4088_:
{
return v___x_4089_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__8(uint8_t v_skipInstances_4109_, lean_object* v_pre_4110_, lean_object* v_post_4111_, uint8_t v_usedLetOnly_4112_, uint8_t v_skipConstInApp_4113_, lean_object* v_x_4114_, lean_object* v_x_4115_, lean_object* v_x_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_){
_start:
{
lean_object* v_f_4124_; lean_object* v___y_4125_; lean_object* v___y_4126_; lean_object* v___y_4127_; lean_object* v___y_4128_; lean_object* v___y_4129_; 
if (lean_obj_tag(v_x_4114_) == 5)
{
lean_object* v_fn_4172_; lean_object* v_arg_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; 
v_fn_4172_ = lean_ctor_get(v_x_4114_, 0);
lean_inc_ref(v_fn_4172_);
v_arg_4173_ = lean_ctor_get(v_x_4114_, 1);
lean_inc_ref(v_arg_4173_);
lean_dec_ref_known(v_x_4114_, 2);
v___x_4174_ = lean_array_set(v_x_4115_, v_x_4116_, v_arg_4173_);
v___x_4175_ = lean_unsigned_to_nat(1u);
v___x_4176_ = lean_nat_sub(v_x_4116_, v___x_4175_);
lean_dec(v_x_4116_);
v_x_4114_ = v_fn_4172_;
v_x_4115_ = v___x_4174_;
v_x_4116_ = v___x_4176_;
goto _start;
}
else
{
lean_dec(v_x_4116_);
if (v_skipConstInApp_4113_ == 0)
{
goto v___jp_4169_;
}
else
{
uint8_t v___x_4178_; 
v___x_4178_ = l_Lean_Expr_isConst(v_x_4114_);
if (v___x_4178_ == 0)
{
goto v___jp_4169_;
}
else
{
v_f_4124_ = v_x_4114_;
v___y_4125_ = v___y_4117_;
v___y_4126_ = v___y_4118_;
v___y_4127_ = v___y_4119_;
v___y_4128_ = v___y_4120_;
v___y_4129_ = v___y_4121_;
goto v___jp_4123_;
}
}
}
v___jp_4123_:
{
if (v_skipInstances_4109_ == 0)
{
size_t v_sz_4130_; size_t v___x_4131_; lean_object* v___x_4132_; 
v_sz_4130_ = lean_array_size(v_x_4115_);
v___x_4131_ = ((size_t)0ULL);
lean_inc_ref(v_post_4111_);
lean_inc_ref(v_pre_4110_);
v___x_4132_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__2(v_pre_4110_, v_post_4111_, v_usedLetOnly_4112_, v_skipConstInApp_4113_, v_skipInstances_4109_, v_sz_4130_, v___x_4131_, v_x_4115_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_);
if (lean_obj_tag(v___x_4132_) == 0)
{
lean_object* v_a_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; 
v_a_4133_ = lean_ctor_get(v___x_4132_, 0);
lean_inc(v_a_4133_);
lean_dec_ref_known(v___x_4132_, 1);
v___x_4134_ = l_Lean_mkAppN(v_f_4124_, v_a_4133_);
lean_dec(v_a_4133_);
v___x_4135_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4110_, v_post_4111_, v_usedLetOnly_4112_, v_skipConstInApp_4113_, v_skipInstances_4109_, v___x_4134_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_);
return v___x_4135_;
}
else
{
lean_object* v_a_4136_; lean_object* v___x_4138_; uint8_t v_isShared_4139_; uint8_t v_isSharedCheck_4143_; 
lean_dec_ref(v_f_4124_);
lean_dec_ref(v_post_4111_);
lean_dec_ref(v_pre_4110_);
v_a_4136_ = lean_ctor_get(v___x_4132_, 0);
v_isSharedCheck_4143_ = !lean_is_exclusive(v___x_4132_);
if (v_isSharedCheck_4143_ == 0)
{
v___x_4138_ = v___x_4132_;
v_isShared_4139_ = v_isSharedCheck_4143_;
goto v_resetjp_4137_;
}
else
{
lean_inc(v_a_4136_);
lean_dec(v___x_4132_);
v___x_4138_ = lean_box(0);
v_isShared_4139_ = v_isSharedCheck_4143_;
goto v_resetjp_4137_;
}
v_resetjp_4137_:
{
lean_object* v___x_4141_; 
if (v_isShared_4139_ == 0)
{
v___x_4141_ = v___x_4138_;
goto v_reusejp_4140_;
}
else
{
lean_object* v_reuseFailAlloc_4142_; 
v_reuseFailAlloc_4142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4142_, 0, v_a_4136_);
v___x_4141_ = v_reuseFailAlloc_4142_;
goto v_reusejp_4140_;
}
v_reusejp_4140_:
{
return v___x_4141_;
}
}
}
}
else
{
lean_object* v___x_4144_; lean_object* v___x_4145_; 
v___x_4144_ = lean_array_get_size(v_x_4115_);
lean_inc_ref(v_f_4124_);
v___x_4145_ = l_Lean_Meta_getFunInfoNArgs(v_f_4124_, v___x_4144_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_);
if (lean_obj_tag(v___x_4145_) == 0)
{
lean_object* v_a_4146_; lean_object* v_paramInfo_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; 
v_a_4146_ = lean_ctor_get(v___x_4145_, 0);
lean_inc(v_a_4146_);
lean_dec_ref_known(v___x_4145_, 1);
v_paramInfo_4147_ = lean_ctor_get(v_a_4146_, 0);
lean_inc_ref(v_paramInfo_4147_);
lean_dec(v_a_4146_);
v___x_4148_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_4111_);
lean_inc_ref(v_pre_4110_);
v___x_4149_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg(v___x_4144_, v_paramInfo_4147_, v_pre_4110_, v_post_4111_, v_usedLetOnly_4112_, v_skipConstInApp_4113_, v_skipInstances_4109_, v___x_4148_, v_x_4115_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_);
lean_dec_ref(v_paramInfo_4147_);
if (lean_obj_tag(v___x_4149_) == 0)
{
lean_object* v_a_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; 
v_a_4150_ = lean_ctor_get(v___x_4149_, 0);
lean_inc(v_a_4150_);
lean_dec_ref_known(v___x_4149_, 1);
v___x_4151_ = l_Lean_mkAppN(v_f_4124_, v_a_4150_);
lean_dec(v_a_4150_);
v___x_4152_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4110_, v_post_4111_, v_usedLetOnly_4112_, v_skipConstInApp_4113_, v_skipInstances_4109_, v___x_4151_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_);
return v___x_4152_;
}
else
{
lean_object* v_a_4153_; lean_object* v___x_4155_; uint8_t v_isShared_4156_; uint8_t v_isSharedCheck_4160_; 
lean_dec_ref(v_f_4124_);
lean_dec_ref(v_post_4111_);
lean_dec_ref(v_pre_4110_);
v_a_4153_ = lean_ctor_get(v___x_4149_, 0);
v_isSharedCheck_4160_ = !lean_is_exclusive(v___x_4149_);
if (v_isSharedCheck_4160_ == 0)
{
v___x_4155_ = v___x_4149_;
v_isShared_4156_ = v_isSharedCheck_4160_;
goto v_resetjp_4154_;
}
else
{
lean_inc(v_a_4153_);
lean_dec(v___x_4149_);
v___x_4155_ = lean_box(0);
v_isShared_4156_ = v_isSharedCheck_4160_;
goto v_resetjp_4154_;
}
v_resetjp_4154_:
{
lean_object* v___x_4158_; 
if (v_isShared_4156_ == 0)
{
v___x_4158_ = v___x_4155_;
goto v_reusejp_4157_;
}
else
{
lean_object* v_reuseFailAlloc_4159_; 
v_reuseFailAlloc_4159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4159_, 0, v_a_4153_);
v___x_4158_ = v_reuseFailAlloc_4159_;
goto v_reusejp_4157_;
}
v_reusejp_4157_:
{
return v___x_4158_;
}
}
}
}
else
{
lean_object* v_a_4161_; lean_object* v___x_4163_; uint8_t v_isShared_4164_; uint8_t v_isSharedCheck_4168_; 
lean_dec_ref(v_f_4124_);
lean_dec_ref(v_x_4115_);
lean_dec_ref(v_post_4111_);
lean_dec_ref(v_pre_4110_);
v_a_4161_ = lean_ctor_get(v___x_4145_, 0);
v_isSharedCheck_4168_ = !lean_is_exclusive(v___x_4145_);
if (v_isSharedCheck_4168_ == 0)
{
v___x_4163_ = v___x_4145_;
v_isShared_4164_ = v_isSharedCheck_4168_;
goto v_resetjp_4162_;
}
else
{
lean_inc(v_a_4161_);
lean_dec(v___x_4145_);
v___x_4163_ = lean_box(0);
v_isShared_4164_ = v_isSharedCheck_4168_;
goto v_resetjp_4162_;
}
v_resetjp_4162_:
{
lean_object* v___x_4166_; 
if (v_isShared_4164_ == 0)
{
v___x_4166_ = v___x_4163_;
goto v_reusejp_4165_;
}
else
{
lean_object* v_reuseFailAlloc_4167_; 
v_reuseFailAlloc_4167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4167_, 0, v_a_4161_);
v___x_4166_ = v_reuseFailAlloc_4167_;
goto v_reusejp_4165_;
}
v_reusejp_4165_:
{
return v___x_4166_;
}
}
}
}
}
v___jp_4169_:
{
lean_object* v___x_4170_; 
lean_inc_ref(v_post_4111_);
lean_inc_ref(v_pre_4110_);
v___x_4170_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4110_, v_post_4111_, v_usedLetOnly_4112_, v_skipConstInApp_4113_, v_skipInstances_4109_, v_x_4114_, v___y_4117_, v___y_4118_, v___y_4119_, v___y_4120_, v___y_4121_);
if (lean_obj_tag(v___x_4170_) == 0)
{
lean_object* v_a_4171_; 
v_a_4171_ = lean_ctor_get(v___x_4170_, 0);
lean_inc(v_a_4171_);
lean_dec_ref_known(v___x_4170_, 1);
v_f_4124_ = v_a_4171_;
v___y_4125_ = v___y_4117_;
v___y_4126_ = v___y_4118_;
v___y_4127_ = v___y_4119_;
v___y_4128_ = v___y_4120_;
v___y_4129_ = v___y_4121_;
goto v___jp_4123_;
}
else
{
lean_dec_ref(v_x_4115_);
lean_dec_ref(v_post_4111_);
lean_dec_ref(v_pre_4110_);
return v___x_4170_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1(lean_object* v___x_4179_, lean_object* v_pre_4180_, lean_object* v_e_4181_, lean_object* v_post_4182_, uint8_t v_usedLetOnly_4183_, uint8_t v_skipConstInApp_4184_, uint8_t v_skipInstances_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_){
_start:
{
lean_object* v___x_4192_; 
v___x_4192_ = l_Lean_Core_checkSystem(v___x_4179_, v___y_4189_, v___y_4190_);
if (lean_obj_tag(v___x_4192_) == 0)
{
lean_object* v___x_4193_; 
lean_dec_ref_known(v___x_4192_, 1);
lean_inc_ref(v_pre_4180_);
lean_inc(v___y_4190_);
lean_inc_ref(v___y_4189_);
lean_inc(v___y_4188_);
lean_inc_ref(v___y_4187_);
lean_inc_ref(v_e_4181_);
v___x_4193_ = lean_apply_6(v_pre_4180_, v_e_4181_, v___y_4187_, v___y_4188_, v___y_4189_, v___y_4190_, lean_box(0));
if (lean_obj_tag(v___x_4193_) == 0)
{
lean_object* v_a_4194_; lean_object* v___x_4196_; uint8_t v_isShared_4197_; uint8_t v_isSharedCheck_4242_; 
v_a_4194_ = lean_ctor_get(v___x_4193_, 0);
v_isSharedCheck_4242_ = !lean_is_exclusive(v___x_4193_);
if (v_isSharedCheck_4242_ == 0)
{
v___x_4196_ = v___x_4193_;
v_isShared_4197_ = v_isSharedCheck_4242_;
goto v_resetjp_4195_;
}
else
{
lean_inc(v_a_4194_);
lean_dec(v___x_4193_);
v___x_4196_ = lean_box(0);
v_isShared_4197_ = v_isSharedCheck_4242_;
goto v_resetjp_4195_;
}
v_resetjp_4195_:
{
lean_object* v___y_4199_; 
switch(lean_obj_tag(v_a_4194_))
{
case 0:
{
lean_object* v_e_4234_; lean_object* v___x_4236_; 
lean_dec_ref(v_post_4182_);
lean_dec_ref(v_e_4181_);
lean_dec_ref(v_pre_4180_);
v_e_4234_ = lean_ctor_get(v_a_4194_, 0);
lean_inc_ref(v_e_4234_);
lean_dec_ref_known(v_a_4194_, 1);
if (v_isShared_4197_ == 0)
{
lean_ctor_set(v___x_4196_, 0, v_e_4234_);
v___x_4236_ = v___x_4196_;
goto v_reusejp_4235_;
}
else
{
lean_object* v_reuseFailAlloc_4237_; 
v_reuseFailAlloc_4237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4237_, 0, v_e_4234_);
v___x_4236_ = v_reuseFailAlloc_4237_;
goto v_reusejp_4235_;
}
v_reusejp_4235_:
{
return v___x_4236_;
}
}
case 1:
{
lean_object* v_e_4238_; lean_object* v___x_4239_; 
lean_del_object(v___x_4196_);
lean_dec_ref(v_e_4181_);
v_e_4238_ = lean_ctor_get(v_a_4194_, 0);
lean_inc_ref(v_e_4238_);
lean_dec_ref_known(v_a_4194_, 1);
v___x_4239_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4180_, v_post_4182_, v_usedLetOnly_4183_, v_skipConstInApp_4184_, v_skipInstances_4185_, v_e_4238_, v___y_4186_, v___y_4187_, v___y_4188_, v___y_4189_, v___y_4190_);
return v___x_4239_;
}
default: 
{
lean_object* v_e_x3f_4240_; 
lean_del_object(v___x_4196_);
v_e_x3f_4240_ = lean_ctor_get(v_a_4194_, 0);
lean_inc(v_e_x3f_4240_);
lean_dec_ref_known(v_a_4194_, 1);
if (lean_obj_tag(v_e_x3f_4240_) == 0)
{
v___y_4199_ = v_e_4181_;
goto v___jp_4198_;
}
else
{
lean_object* v_val_4241_; 
lean_dec_ref(v_e_4181_);
v_val_4241_ = lean_ctor_get(v_e_x3f_4240_, 0);
lean_inc(v_val_4241_);
lean_dec_ref_known(v_e_x3f_4240_, 1);
v___y_4199_ = v_val_4241_;
goto v___jp_4198_;
}
}
}
v___jp_4198_:
{
switch(lean_obj_tag(v___y_4199_))
{
case 7:
{
lean_object* v___x_4200_; lean_object* v___x_4201_; 
v___x_4200_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_4201_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5(v_pre_4180_, v_post_4182_, v_usedLetOnly_4183_, v_skipConstInApp_4184_, v_skipInstances_4185_, v___x_4200_, v___y_4199_, v___y_4186_, v___y_4187_, v___y_4188_, v___y_4189_, v___y_4190_);
return v___x_4201_;
}
case 6:
{
lean_object* v___x_4202_; lean_object* v___x_4203_; 
v___x_4202_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_4203_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6(v_pre_4180_, v_post_4182_, v_usedLetOnly_4183_, v_skipConstInApp_4184_, v_skipInstances_4185_, v___x_4202_, v___y_4199_, v___y_4186_, v___y_4187_, v___y_4188_, v___y_4189_, v___y_4190_);
return v___x_4203_;
}
case 8:
{
lean_object* v___x_4204_; lean_object* v___x_4205_; 
v___x_4204_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_4205_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7(v_pre_4180_, v_post_4182_, v_usedLetOnly_4183_, v_skipConstInApp_4184_, v_skipInstances_4185_, v___x_4204_, v___y_4199_, v___y_4186_, v___y_4187_, v___y_4188_, v___y_4189_, v___y_4190_);
return v___x_4205_;
}
case 5:
{
lean_object* v_dummy_4206_; lean_object* v_nargs_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; 
v_dummy_4206_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_4207_ = l_Lean_Expr_getAppNumArgs(v___y_4199_);
lean_inc(v_nargs_4207_);
v___x_4208_ = lean_mk_array(v_nargs_4207_, v_dummy_4206_);
v___x_4209_ = lean_unsigned_to_nat(1u);
v___x_4210_ = lean_nat_sub(v_nargs_4207_, v___x_4209_);
lean_dec(v_nargs_4207_);
v___x_4211_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__8(v_skipInstances_4185_, v_pre_4180_, v_post_4182_, v_usedLetOnly_4183_, v_skipConstInApp_4184_, v___y_4199_, v___x_4208_, v___x_4210_, v___y_4186_, v___y_4187_, v___y_4188_, v___y_4189_, v___y_4190_);
return v___x_4211_;
}
case 10:
{
lean_object* v_data_4212_; lean_object* v_expr_4213_; lean_object* v___x_4214_; 
v_data_4212_ = lean_ctor_get(v___y_4199_, 0);
v_expr_4213_ = lean_ctor_get(v___y_4199_, 1);
lean_inc_ref(v_expr_4213_);
lean_inc_ref(v_post_4182_);
lean_inc_ref(v_pre_4180_);
v___x_4214_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4180_, v_post_4182_, v_usedLetOnly_4183_, v_skipConstInApp_4184_, v_skipInstances_4185_, v_expr_4213_, v___y_4186_, v___y_4187_, v___y_4188_, v___y_4189_, v___y_4190_);
if (lean_obj_tag(v___x_4214_) == 0)
{
lean_object* v_a_4215_; size_t v___x_4216_; size_t v___x_4217_; uint8_t v___x_4218_; 
v_a_4215_ = lean_ctor_get(v___x_4214_, 0);
lean_inc(v_a_4215_);
lean_dec_ref_known(v___x_4214_, 1);
v___x_4216_ = lean_ptr_addr(v_expr_4213_);
v___x_4217_ = lean_ptr_addr(v_a_4215_);
v___x_4218_ = lean_usize_dec_eq(v___x_4216_, v___x_4217_);
if (v___x_4218_ == 0)
{
lean_object* v___x_4219_; lean_object* v___x_4220_; 
lean_inc(v_data_4212_);
lean_dec_ref_known(v___y_4199_, 2);
v___x_4219_ = l_Lean_Expr_mdata___override(v_data_4212_, v_a_4215_);
v___x_4220_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4180_, v_post_4182_, v_usedLetOnly_4183_, v_skipConstInApp_4184_, v_skipInstances_4185_, v___x_4219_, v___y_4186_, v___y_4187_, v___y_4188_, v___y_4189_, v___y_4190_);
return v___x_4220_;
}
else
{
lean_object* v___x_4221_; 
lean_dec(v_a_4215_);
v___x_4221_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4180_, v_post_4182_, v_usedLetOnly_4183_, v_skipConstInApp_4184_, v_skipInstances_4185_, v___y_4199_, v___y_4186_, v___y_4187_, v___y_4188_, v___y_4189_, v___y_4190_);
return v___x_4221_;
}
}
else
{
lean_dec_ref_known(v___y_4199_, 2);
lean_dec_ref(v_post_4182_);
lean_dec_ref(v_pre_4180_);
return v___x_4214_;
}
}
case 11:
{
lean_object* v_typeName_4222_; lean_object* v_idx_4223_; lean_object* v_struct_4224_; lean_object* v___x_4225_; 
v_typeName_4222_ = lean_ctor_get(v___y_4199_, 0);
v_idx_4223_ = lean_ctor_get(v___y_4199_, 1);
v_struct_4224_ = lean_ctor_get(v___y_4199_, 2);
lean_inc_ref(v_struct_4224_);
lean_inc_ref(v_post_4182_);
lean_inc_ref(v_pre_4180_);
v___x_4225_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4180_, v_post_4182_, v_usedLetOnly_4183_, v_skipConstInApp_4184_, v_skipInstances_4185_, v_struct_4224_, v___y_4186_, v___y_4187_, v___y_4188_, v___y_4189_, v___y_4190_);
if (lean_obj_tag(v___x_4225_) == 0)
{
lean_object* v_a_4226_; size_t v___x_4227_; size_t v___x_4228_; uint8_t v___x_4229_; 
v_a_4226_ = lean_ctor_get(v___x_4225_, 0);
lean_inc(v_a_4226_);
lean_dec_ref_known(v___x_4225_, 1);
v___x_4227_ = lean_ptr_addr(v_struct_4224_);
v___x_4228_ = lean_ptr_addr(v_a_4226_);
v___x_4229_ = lean_usize_dec_eq(v___x_4227_, v___x_4228_);
if (v___x_4229_ == 0)
{
lean_object* v___x_4230_; lean_object* v___x_4231_; 
lean_inc(v_idx_4223_);
lean_inc(v_typeName_4222_);
lean_dec_ref_known(v___y_4199_, 3);
v___x_4230_ = l_Lean_Expr_proj___override(v_typeName_4222_, v_idx_4223_, v_a_4226_);
v___x_4231_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4180_, v_post_4182_, v_usedLetOnly_4183_, v_skipConstInApp_4184_, v_skipInstances_4185_, v___x_4230_, v___y_4186_, v___y_4187_, v___y_4188_, v___y_4189_, v___y_4190_);
return v___x_4231_;
}
else
{
lean_object* v___x_4232_; 
lean_dec(v_a_4226_);
v___x_4232_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4180_, v_post_4182_, v_usedLetOnly_4183_, v_skipConstInApp_4184_, v_skipInstances_4185_, v___y_4199_, v___y_4186_, v___y_4187_, v___y_4188_, v___y_4189_, v___y_4190_);
return v___x_4232_;
}
}
else
{
lean_dec_ref_known(v___y_4199_, 3);
lean_dec_ref(v_post_4182_);
lean_dec_ref(v_pre_4180_);
return v___x_4225_;
}
}
default: 
{
lean_object* v___x_4233_; 
v___x_4233_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4180_, v_post_4182_, v_usedLetOnly_4183_, v_skipConstInApp_4184_, v_skipInstances_4185_, v___y_4199_, v___y_4186_, v___y_4187_, v___y_4188_, v___y_4189_, v___y_4190_);
return v___x_4233_;
}
}
}
}
}
else
{
lean_object* v_a_4243_; lean_object* v___x_4245_; uint8_t v_isShared_4246_; uint8_t v_isSharedCheck_4250_; 
lean_dec_ref(v_post_4182_);
lean_dec_ref(v_e_4181_);
lean_dec_ref(v_pre_4180_);
v_a_4243_ = lean_ctor_get(v___x_4193_, 0);
v_isSharedCheck_4250_ = !lean_is_exclusive(v___x_4193_);
if (v_isSharedCheck_4250_ == 0)
{
v___x_4245_ = v___x_4193_;
v_isShared_4246_ = v_isSharedCheck_4250_;
goto v_resetjp_4244_;
}
else
{
lean_inc(v_a_4243_);
lean_dec(v___x_4193_);
v___x_4245_ = lean_box(0);
v_isShared_4246_ = v_isSharedCheck_4250_;
goto v_resetjp_4244_;
}
v_resetjp_4244_:
{
lean_object* v___x_4248_; 
if (v_isShared_4246_ == 0)
{
v___x_4248_ = v___x_4245_;
goto v_reusejp_4247_;
}
else
{
lean_object* v_reuseFailAlloc_4249_; 
v_reuseFailAlloc_4249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4249_, 0, v_a_4243_);
v___x_4248_ = v_reuseFailAlloc_4249_;
goto v_reusejp_4247_;
}
v_reusejp_4247_:
{
return v___x_4248_;
}
}
}
}
else
{
lean_object* v_a_4251_; lean_object* v___x_4253_; uint8_t v_isShared_4254_; uint8_t v_isSharedCheck_4258_; 
lean_dec_ref(v_post_4182_);
lean_dec_ref(v_e_4181_);
lean_dec_ref(v_pre_4180_);
v_a_4251_ = lean_ctor_get(v___x_4192_, 0);
v_isSharedCheck_4258_ = !lean_is_exclusive(v___x_4192_);
if (v_isSharedCheck_4258_ == 0)
{
v___x_4253_ = v___x_4192_;
v_isShared_4254_ = v_isSharedCheck_4258_;
goto v_resetjp_4252_;
}
else
{
lean_inc(v_a_4251_);
lean_dec(v___x_4192_);
v___x_4253_ = lean_box(0);
v_isShared_4254_ = v_isSharedCheck_4258_;
goto v_resetjp_4252_;
}
v_resetjp_4252_:
{
lean_object* v___x_4256_; 
if (v_isShared_4254_ == 0)
{
v___x_4256_ = v___x_4253_;
goto v_reusejp_4255_;
}
else
{
lean_object* v_reuseFailAlloc_4257_; 
v_reuseFailAlloc_4257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4257_, 0, v_a_4251_);
v___x_4256_ = v_reuseFailAlloc_4257_;
goto v_reusejp_4255_;
}
v_reusejp_4255_:
{
return v___x_4256_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1___boxed(lean_object* v___x_4259_, lean_object* v_pre_4260_, lean_object* v_e_4261_, lean_object* v_post_4262_, lean_object* v_usedLetOnly_4263_, lean_object* v_skipConstInApp_4264_, lean_object* v_skipInstances_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_, lean_object* v___y_4271_){
_start:
{
uint8_t v_usedLetOnly_boxed_4272_; uint8_t v_skipConstInApp_boxed_4273_; uint8_t v_skipInstances_boxed_4274_; lean_object* v_res_4275_; 
v_usedLetOnly_boxed_4272_ = lean_unbox(v_usedLetOnly_4263_);
v_skipConstInApp_boxed_4273_ = lean_unbox(v_skipConstInApp_4264_);
v_skipInstances_boxed_4274_ = lean_unbox(v_skipInstances_4265_);
v_res_4275_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1(v___x_4259_, v_pre_4260_, v_e_4261_, v_post_4262_, v_usedLetOnly_boxed_4272_, v_skipConstInApp_boxed_4273_, v_skipInstances_boxed_4274_, v___y_4266_, v___y_4267_, v___y_4268_, v___y_4269_, v___y_4270_);
lean_dec(v___y_4270_);
lean_dec_ref(v___y_4269_);
lean_dec(v___y_4268_);
lean_dec_ref(v___y_4267_);
lean_dec(v___y_4266_);
return v_res_4275_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(lean_object* v_pre_4276_, lean_object* v_post_4277_, uint8_t v_usedLetOnly_4278_, uint8_t v_skipConstInApp_4279_, uint8_t v_skipInstances_4280_, lean_object* v_e_4281_, lean_object* v_a_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_){
_start:
{
lean_object* v___x_4288_; lean_object* v___x_4289_; 
lean_inc(v_a_4282_);
v___x_4288_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_4288_, 0, lean_box(0));
lean_closure_set(v___x_4288_, 1, lean_box(0));
lean_closure_set(v___x_4288_, 2, v_a_4282_);
v___x_4289_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0(lean_box(0), v___x_4288_, v___y_4283_, v___y_4284_, v___y_4285_, v___y_4286_);
if (lean_obj_tag(v___x_4289_) == 0)
{
lean_object* v_a_4290_; lean_object* v___x_4292_; uint8_t v_isShared_4293_; uint8_t v_isSharedCheck_4324_; 
v_a_4290_ = lean_ctor_get(v___x_4289_, 0);
v_isSharedCheck_4324_ = !lean_is_exclusive(v___x_4289_);
if (v_isSharedCheck_4324_ == 0)
{
v___x_4292_ = v___x_4289_;
v_isShared_4293_ = v_isSharedCheck_4324_;
goto v_resetjp_4291_;
}
else
{
lean_inc(v_a_4290_);
lean_dec(v___x_4289_);
v___x_4292_ = lean_box(0);
v_isShared_4293_ = v_isSharedCheck_4324_;
goto v_resetjp_4291_;
}
v_resetjp_4291_:
{
lean_object* v___x_4294_; 
v___x_4294_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg(v_a_4290_, v_e_4281_);
lean_dec(v_a_4290_);
if (lean_obj_tag(v___x_4294_) == 0)
{
lean_object* v___x_4295_; lean_object* v___x_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; lean_object* v___f_4299_; lean_object* v___x_4300_; 
lean_del_object(v___x_4292_);
v___x_4295_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__19___closed__0));
v___x_4296_ = lean_box(v_usedLetOnly_4278_);
v___x_4297_ = lean_box(v_skipConstInApp_4279_);
v___x_4298_ = lean_box(v_skipInstances_4280_);
lean_inc_ref(v_e_4281_);
v___f_4299_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1___boxed), 13, 7);
lean_closure_set(v___f_4299_, 0, v___x_4295_);
lean_closure_set(v___f_4299_, 1, v_pre_4276_);
lean_closure_set(v___f_4299_, 2, v_e_4281_);
lean_closure_set(v___f_4299_, 3, v_post_4277_);
lean_closure_set(v___f_4299_, 4, v___x_4296_);
lean_closure_set(v___f_4299_, 5, v___x_4297_);
lean_closure_set(v___f_4299_, 6, v___x_4298_);
v___x_4300_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg(v___f_4299_, v_a_4282_, v___y_4283_, v___y_4284_, v___y_4285_, v___y_4286_);
if (lean_obj_tag(v___x_4300_) == 0)
{
lean_object* v_a_4301_; lean_object* v___f_4302_; lean_object* v___x_4303_; 
v_a_4301_ = lean_ctor_get(v___x_4300_, 0);
lean_inc_n(v_a_4301_, 2);
lean_dec_ref_known(v___x_4300_, 1);
lean_inc(v_a_4282_);
v___f_4302_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_4302_, 0, v_a_4282_);
lean_closure_set(v___f_4302_, 1, v_e_4281_);
lean_closure_set(v___f_4302_, 2, v_a_4301_);
v___x_4303_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0(lean_box(0), v___f_4302_, v___y_4283_, v___y_4284_, v___y_4285_, v___y_4286_);
if (lean_obj_tag(v___x_4303_) == 0)
{
lean_object* v___x_4305_; uint8_t v_isShared_4306_; uint8_t v_isSharedCheck_4310_; 
v_isSharedCheck_4310_ = !lean_is_exclusive(v___x_4303_);
if (v_isSharedCheck_4310_ == 0)
{
lean_object* v_unused_4311_; 
v_unused_4311_ = lean_ctor_get(v___x_4303_, 0);
lean_dec(v_unused_4311_);
v___x_4305_ = v___x_4303_;
v_isShared_4306_ = v_isSharedCheck_4310_;
goto v_resetjp_4304_;
}
else
{
lean_dec(v___x_4303_);
v___x_4305_ = lean_box(0);
v_isShared_4306_ = v_isSharedCheck_4310_;
goto v_resetjp_4304_;
}
v_resetjp_4304_:
{
lean_object* v___x_4308_; 
if (v_isShared_4306_ == 0)
{
lean_ctor_set(v___x_4305_, 0, v_a_4301_);
v___x_4308_ = v___x_4305_;
goto v_reusejp_4307_;
}
else
{
lean_object* v_reuseFailAlloc_4309_; 
v_reuseFailAlloc_4309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4309_, 0, v_a_4301_);
v___x_4308_ = v_reuseFailAlloc_4309_;
goto v_reusejp_4307_;
}
v_reusejp_4307_:
{
return v___x_4308_;
}
}
}
else
{
lean_object* v_a_4312_; lean_object* v___x_4314_; uint8_t v_isShared_4315_; uint8_t v_isSharedCheck_4319_; 
lean_dec(v_a_4301_);
v_a_4312_ = lean_ctor_get(v___x_4303_, 0);
v_isSharedCheck_4319_ = !lean_is_exclusive(v___x_4303_);
if (v_isSharedCheck_4319_ == 0)
{
v___x_4314_ = v___x_4303_;
v_isShared_4315_ = v_isSharedCheck_4319_;
goto v_resetjp_4313_;
}
else
{
lean_inc(v_a_4312_);
lean_dec(v___x_4303_);
v___x_4314_ = lean_box(0);
v_isShared_4315_ = v_isSharedCheck_4319_;
goto v_resetjp_4313_;
}
v_resetjp_4313_:
{
lean_object* v___x_4317_; 
if (v_isShared_4315_ == 0)
{
v___x_4317_ = v___x_4314_;
goto v_reusejp_4316_;
}
else
{
lean_object* v_reuseFailAlloc_4318_; 
v_reuseFailAlloc_4318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4318_, 0, v_a_4312_);
v___x_4317_ = v_reuseFailAlloc_4318_;
goto v_reusejp_4316_;
}
v_reusejp_4316_:
{
return v___x_4317_;
}
}
}
}
else
{
lean_dec_ref(v_e_4281_);
return v___x_4300_;
}
}
else
{
lean_object* v_val_4320_; lean_object* v___x_4322_; 
lean_dec_ref(v_e_4281_);
lean_dec_ref(v_post_4277_);
lean_dec_ref(v_pre_4276_);
v_val_4320_ = lean_ctor_get(v___x_4294_, 0);
lean_inc(v_val_4320_);
lean_dec_ref_known(v___x_4294_, 1);
if (v_isShared_4293_ == 0)
{
lean_ctor_set(v___x_4292_, 0, v_val_4320_);
v___x_4322_ = v___x_4292_;
goto v_reusejp_4321_;
}
else
{
lean_object* v_reuseFailAlloc_4323_; 
v_reuseFailAlloc_4323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4323_, 0, v_val_4320_);
v___x_4322_ = v_reuseFailAlloc_4323_;
goto v_reusejp_4321_;
}
v_reusejp_4321_:
{
return v___x_4322_;
}
}
}
}
else
{
lean_object* v_a_4325_; lean_object* v___x_4327_; uint8_t v_isShared_4328_; uint8_t v_isSharedCheck_4332_; 
lean_dec_ref(v_e_4281_);
lean_dec_ref(v_post_4277_);
lean_dec_ref(v_pre_4276_);
v_a_4325_ = lean_ctor_get(v___x_4289_, 0);
v_isSharedCheck_4332_ = !lean_is_exclusive(v___x_4289_);
if (v_isSharedCheck_4332_ == 0)
{
v___x_4327_ = v___x_4289_;
v_isShared_4328_ = v_isSharedCheck_4332_;
goto v_resetjp_4326_;
}
else
{
lean_inc(v_a_4325_);
lean_dec(v___x_4289_);
v___x_4327_ = lean_box(0);
v_isShared_4328_ = v_isSharedCheck_4332_;
goto v_resetjp_4326_;
}
v_resetjp_4326_:
{
lean_object* v___x_4330_; 
if (v_isShared_4328_ == 0)
{
v___x_4330_ = v___x_4327_;
goto v_reusejp_4329_;
}
else
{
lean_object* v_reuseFailAlloc_4331_; 
v_reuseFailAlloc_4331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4331_, 0, v_a_4325_);
v___x_4330_ = v_reuseFailAlloc_4331_;
goto v_reusejp_4329_;
}
v_reusejp_4329_:
{
return v___x_4330_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5(lean_object* v_pre_4333_, lean_object* v_post_4334_, uint8_t v_usedLetOnly_4335_, uint8_t v_skipConstInApp_4336_, uint8_t v_skipInstances_4337_, lean_object* v_fvars_4338_, lean_object* v_e_4339_, lean_object* v_a_4340_, lean_object* v___y_4341_, lean_object* v___y_4342_, lean_object* v___y_4343_, lean_object* v___y_4344_){
_start:
{
if (lean_obj_tag(v_e_4339_) == 7)
{
lean_object* v_binderName_4346_; lean_object* v_binderType_4347_; lean_object* v_body_4348_; uint8_t v_binderInfo_4349_; lean_object* v___x_4350_; lean_object* v___x_4351_; lean_object* v___x_4352_; lean_object* v___f_4353_; lean_object* v___x_4354_; lean_object* v___x_4355_; 
v_binderName_4346_ = lean_ctor_get(v_e_4339_, 0);
lean_inc(v_binderName_4346_);
v_binderType_4347_ = lean_ctor_get(v_e_4339_, 1);
lean_inc_ref(v_binderType_4347_);
v_body_4348_ = lean_ctor_get(v_e_4339_, 2);
lean_inc_ref(v_body_4348_);
v_binderInfo_4349_ = lean_ctor_get_uint8(v_e_4339_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_4339_, 3);
v___x_4350_ = lean_box(v_usedLetOnly_4335_);
v___x_4351_ = lean_box(v_skipConstInApp_4336_);
v___x_4352_ = lean_box(v_skipInstances_4337_);
lean_inc_ref(v_post_4334_);
lean_inc_ref(v_pre_4333_);
lean_inc_ref(v_fvars_4338_);
v___f_4353_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___lam__0___boxed), 14, 7);
lean_closure_set(v___f_4353_, 0, v_fvars_4338_);
lean_closure_set(v___f_4353_, 1, v_pre_4333_);
lean_closure_set(v___f_4353_, 2, v_post_4334_);
lean_closure_set(v___f_4353_, 3, v___x_4350_);
lean_closure_set(v___f_4353_, 4, v___x_4351_);
lean_closure_set(v___f_4353_, 5, v___x_4352_);
lean_closure_set(v___f_4353_, 6, v_body_4348_);
v___x_4354_ = lean_expr_instantiate_rev(v_binderType_4347_, v_fvars_4338_);
lean_dec_ref(v_fvars_4338_);
lean_dec_ref(v_binderType_4347_);
v___x_4355_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4333_, v_post_4334_, v_usedLetOnly_4335_, v_skipConstInApp_4336_, v_skipInstances_4337_, v___x_4354_, v_a_4340_, v___y_4341_, v___y_4342_, v___y_4343_, v___y_4344_);
if (lean_obj_tag(v___x_4355_) == 0)
{
lean_object* v_a_4356_; uint8_t v___x_4357_; lean_object* v___x_4358_; 
v_a_4356_ = lean_ctor_get(v___x_4355_, 0);
lean_inc(v_a_4356_);
lean_dec_ref_known(v___x_4355_, 1);
v___x_4357_ = 0;
v___x_4358_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_binderName_4346_, v_binderInfo_4349_, v_a_4356_, v___f_4353_, v___x_4357_, v_a_4340_, v___y_4341_, v___y_4342_, v___y_4343_, v___y_4344_);
return v___x_4358_;
}
else
{
lean_dec_ref(v___f_4353_);
lean_dec(v_binderName_4346_);
return v___x_4355_;
}
}
else
{
lean_object* v___x_4359_; lean_object* v___x_4360_; 
v___x_4359_ = lean_expr_instantiate_rev(v_e_4339_, v_fvars_4338_);
lean_dec_ref(v_e_4339_);
lean_inc_ref(v_post_4334_);
lean_inc_ref(v_pre_4333_);
v___x_4360_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4333_, v_post_4334_, v_usedLetOnly_4335_, v_skipConstInApp_4336_, v_skipInstances_4337_, v___x_4359_, v_a_4340_, v___y_4341_, v___y_4342_, v___y_4343_, v___y_4344_);
if (lean_obj_tag(v___x_4360_) == 0)
{
lean_object* v_a_4361_; uint8_t v___x_4362_; uint8_t v___x_4363_; uint8_t v___x_4364_; lean_object* v___x_4365_; 
v_a_4361_ = lean_ctor_get(v___x_4360_, 0);
lean_inc(v_a_4361_);
lean_dec_ref_known(v___x_4360_, 1);
v___x_4362_ = 0;
v___x_4363_ = 1;
v___x_4364_ = 1;
v___x_4365_ = l_Lean_Meta_mkForallFVars(v_fvars_4338_, v_a_4361_, v___x_4362_, v_usedLetOnly_4335_, v___x_4363_, v___x_4364_, v___y_4341_, v___y_4342_, v___y_4343_, v___y_4344_);
lean_dec_ref(v_fvars_4338_);
if (lean_obj_tag(v___x_4365_) == 0)
{
lean_object* v_a_4366_; lean_object* v___x_4367_; 
v_a_4366_ = lean_ctor_get(v___x_4365_, 0);
lean_inc(v_a_4366_);
lean_dec_ref_known(v___x_4365_, 1);
v___x_4367_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4333_, v_post_4334_, v_usedLetOnly_4335_, v_skipConstInApp_4336_, v_skipInstances_4337_, v_a_4366_, v_a_4340_, v___y_4341_, v___y_4342_, v___y_4343_, v___y_4344_);
return v___x_4367_;
}
else
{
lean_dec_ref(v_post_4334_);
lean_dec_ref(v_pre_4333_);
return v___x_4365_;
}
}
else
{
lean_dec_ref(v_fvars_4338_);
lean_dec_ref(v_post_4334_);
lean_dec_ref(v_pre_4333_);
return v___x_4360_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___lam__0(lean_object* v_fvars_4368_, lean_object* v_pre_4369_, lean_object* v_post_4370_, uint8_t v_usedLetOnly_4371_, uint8_t v_skipConstInApp_4372_, uint8_t v_skipInstances_4373_, lean_object* v_body_4374_, lean_object* v_x_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_){
_start:
{
lean_object* v___x_4382_; lean_object* v___x_4383_; 
v___x_4382_ = lean_array_push(v_fvars_4368_, v_x_4375_);
v___x_4383_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5(v_pre_4369_, v_post_4370_, v_usedLetOnly_4371_, v_skipConstInApp_4372_, v_skipInstances_4373_, v___x_4382_, v_body_4374_, v___y_4376_, v___y_4377_, v___y_4378_, v___y_4379_, v___y_4380_);
return v___x_4383_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3___boxed(lean_object* v_pre_4384_, lean_object* v_post_4385_, lean_object* v_usedLetOnly_4386_, lean_object* v_skipConstInApp_4387_, lean_object* v_skipInstances_4388_, lean_object* v_e_4389_, lean_object* v_a_4390_, lean_object* v___y_4391_, lean_object* v___y_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_){
_start:
{
uint8_t v_usedLetOnly_boxed_4396_; uint8_t v_skipConstInApp_boxed_4397_; uint8_t v_skipInstances_boxed_4398_; lean_object* v_res_4399_; 
v_usedLetOnly_boxed_4396_ = lean_unbox(v_usedLetOnly_4386_);
v_skipConstInApp_boxed_4397_ = lean_unbox(v_skipConstInApp_4387_);
v_skipInstances_boxed_4398_ = lean_unbox(v_skipInstances_4388_);
v_res_4399_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4384_, v_post_4385_, v_usedLetOnly_boxed_4396_, v_skipConstInApp_boxed_4397_, v_skipInstances_boxed_4398_, v_e_4389_, v_a_4390_, v___y_4391_, v___y_4392_, v___y_4393_, v___y_4394_);
lean_dec(v___y_4394_);
lean_dec_ref(v___y_4393_);
lean_dec(v___y_4392_);
lean_dec_ref(v___y_4391_);
lean_dec(v_a_4390_);
return v_res_4399_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__2___boxed(lean_object* v_pre_4400_, lean_object* v_post_4401_, lean_object* v_usedLetOnly_4402_, lean_object* v_skipConstInApp_4403_, lean_object* v_skipInstances_4404_, lean_object* v_sz_4405_, lean_object* v_i_4406_, lean_object* v_bs_4407_, lean_object* v___y_4408_, lean_object* v___y_4409_, lean_object* v___y_4410_, lean_object* v___y_4411_, lean_object* v___y_4412_, lean_object* v___y_4413_){
_start:
{
uint8_t v_usedLetOnly_boxed_4414_; uint8_t v_skipConstInApp_boxed_4415_; uint8_t v_skipInstances_boxed_4416_; size_t v_sz_boxed_4417_; size_t v_i_boxed_4418_; lean_object* v_res_4419_; 
v_usedLetOnly_boxed_4414_ = lean_unbox(v_usedLetOnly_4402_);
v_skipConstInApp_boxed_4415_ = lean_unbox(v_skipConstInApp_4403_);
v_skipInstances_boxed_4416_ = lean_unbox(v_skipInstances_4404_);
v_sz_boxed_4417_ = lean_unbox_usize(v_sz_4405_);
lean_dec(v_sz_4405_);
v_i_boxed_4418_ = lean_unbox_usize(v_i_4406_);
lean_dec(v_i_4406_);
v_res_4419_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__2(v_pre_4400_, v_post_4401_, v_usedLetOnly_boxed_4414_, v_skipConstInApp_boxed_4415_, v_skipInstances_boxed_4416_, v_sz_boxed_4417_, v_i_boxed_4418_, v_bs_4407_, v___y_4408_, v___y_4409_, v___y_4410_, v___y_4411_, v___y_4412_);
lean_dec(v___y_4412_);
lean_dec_ref(v___y_4411_);
lean_dec(v___y_4410_);
lean_dec_ref(v___y_4409_);
lean_dec(v___y_4408_);
return v_res_4419_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___boxed(lean_object* v_pre_4420_, lean_object* v_post_4421_, lean_object* v_usedLetOnly_4422_, lean_object* v_skipConstInApp_4423_, lean_object* v_skipInstances_4424_, lean_object* v_e_4425_, lean_object* v_a_4426_, lean_object* v___y_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_, lean_object* v___y_4431_){
_start:
{
uint8_t v_usedLetOnly_boxed_4432_; uint8_t v_skipConstInApp_boxed_4433_; uint8_t v_skipInstances_boxed_4434_; lean_object* v_res_4435_; 
v_usedLetOnly_boxed_4432_ = lean_unbox(v_usedLetOnly_4422_);
v_skipConstInApp_boxed_4433_ = lean_unbox(v_skipConstInApp_4423_);
v_skipInstances_boxed_4434_ = lean_unbox(v_skipInstances_4424_);
v_res_4435_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4420_, v_post_4421_, v_usedLetOnly_boxed_4432_, v_skipConstInApp_boxed_4433_, v_skipInstances_boxed_4434_, v_e_4425_, v_a_4426_, v___y_4427_, v___y_4428_, v___y_4429_, v___y_4430_);
lean_dec(v___y_4430_);
lean_dec_ref(v___y_4429_);
lean_dec(v___y_4428_);
lean_dec_ref(v___y_4427_);
lean_dec(v_a_4426_);
return v_res_4435_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___boxed(lean_object* v_pre_4436_, lean_object* v_post_4437_, lean_object* v_usedLetOnly_4438_, lean_object* v_skipConstInApp_4439_, lean_object* v_skipInstances_4440_, lean_object* v_fvars_4441_, lean_object* v_e_4442_, lean_object* v_a_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_){
_start:
{
uint8_t v_usedLetOnly_boxed_4449_; uint8_t v_skipConstInApp_boxed_4450_; uint8_t v_skipInstances_boxed_4451_; lean_object* v_res_4452_; 
v_usedLetOnly_boxed_4449_ = lean_unbox(v_usedLetOnly_4438_);
v_skipConstInApp_boxed_4450_ = lean_unbox(v_skipConstInApp_4439_);
v_skipInstances_boxed_4451_ = lean_unbox(v_skipInstances_4440_);
v_res_4452_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5(v_pre_4436_, v_post_4437_, v_usedLetOnly_boxed_4449_, v_skipConstInApp_boxed_4450_, v_skipInstances_boxed_4451_, v_fvars_4441_, v_e_4442_, v_a_4443_, v___y_4444_, v___y_4445_, v___y_4446_, v___y_4447_);
lean_dec(v___y_4447_);
lean_dec_ref(v___y_4446_);
lean_dec(v___y_4445_);
lean_dec_ref(v___y_4444_);
lean_dec(v_a_4443_);
return v_res_4452_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___boxed(lean_object* v_pre_4453_, lean_object* v_post_4454_, lean_object* v_usedLetOnly_4455_, lean_object* v_skipConstInApp_4456_, lean_object* v_skipInstances_4457_, lean_object* v_fvars_4458_, lean_object* v_e_4459_, lean_object* v_a_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_, lean_object* v___y_4463_, lean_object* v___y_4464_, lean_object* v___y_4465_){
_start:
{
uint8_t v_usedLetOnly_boxed_4466_; uint8_t v_skipConstInApp_boxed_4467_; uint8_t v_skipInstances_boxed_4468_; lean_object* v_res_4469_; 
v_usedLetOnly_boxed_4466_ = lean_unbox(v_usedLetOnly_4455_);
v_skipConstInApp_boxed_4467_ = lean_unbox(v_skipConstInApp_4456_);
v_skipInstances_boxed_4468_ = lean_unbox(v_skipInstances_4457_);
v_res_4469_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6(v_pre_4453_, v_post_4454_, v_usedLetOnly_boxed_4466_, v_skipConstInApp_boxed_4467_, v_skipInstances_boxed_4468_, v_fvars_4458_, v_e_4459_, v_a_4460_, v___y_4461_, v___y_4462_, v___y_4463_, v___y_4464_);
lean_dec(v___y_4464_);
lean_dec_ref(v___y_4463_);
lean_dec(v___y_4462_);
lean_dec_ref(v___y_4461_);
lean_dec(v_a_4460_);
return v_res_4469_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___boxed(lean_object* v_pre_4470_, lean_object* v_post_4471_, lean_object* v_usedLetOnly_4472_, lean_object* v_skipConstInApp_4473_, lean_object* v_skipInstances_4474_, lean_object* v_fvars_4475_, lean_object* v_e_4476_, lean_object* v_a_4477_, lean_object* v___y_4478_, lean_object* v___y_4479_, lean_object* v___y_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_){
_start:
{
uint8_t v_usedLetOnly_boxed_4483_; uint8_t v_skipConstInApp_boxed_4484_; uint8_t v_skipInstances_boxed_4485_; lean_object* v_res_4486_; 
v_usedLetOnly_boxed_4483_ = lean_unbox(v_usedLetOnly_4472_);
v_skipConstInApp_boxed_4484_ = lean_unbox(v_skipConstInApp_4473_);
v_skipInstances_boxed_4485_ = lean_unbox(v_skipInstances_4474_);
v_res_4486_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7(v_pre_4470_, v_post_4471_, v_usedLetOnly_boxed_4483_, v_skipConstInApp_boxed_4484_, v_skipInstances_boxed_4485_, v_fvars_4475_, v_e_4476_, v_a_4477_, v___y_4478_, v___y_4479_, v___y_4480_, v___y_4481_);
lean_dec(v___y_4481_);
lean_dec_ref(v___y_4480_);
lean_dec(v___y_4479_);
lean_dec_ref(v___y_4478_);
lean_dec(v_a_4477_);
return v_res_4486_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_upperBound_4487_, lean_object* v___x_4488_, lean_object* v_pre_4489_, lean_object* v_post_4490_, lean_object* v_usedLetOnly_4491_, lean_object* v_skipConstInApp_4492_, lean_object* v_skipInstances_4493_, lean_object* v_a_4494_, lean_object* v_b_4495_, lean_object* v___y_4496_, lean_object* v___y_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_, lean_object* v___y_4500_, lean_object* v___y_4501_){
_start:
{
uint8_t v_usedLetOnly_boxed_4502_; uint8_t v_skipConstInApp_boxed_4503_; uint8_t v_skipInstances_boxed_4504_; lean_object* v_res_4505_; 
v_usedLetOnly_boxed_4502_ = lean_unbox(v_usedLetOnly_4491_);
v_skipConstInApp_boxed_4503_ = lean_unbox(v_skipConstInApp_4492_);
v_skipInstances_boxed_4504_ = lean_unbox(v_skipInstances_4493_);
v_res_4505_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg(v_upperBound_4487_, v___x_4488_, v_pre_4489_, v_post_4490_, v_usedLetOnly_boxed_4502_, v_skipConstInApp_boxed_4503_, v_skipInstances_boxed_4504_, v_a_4494_, v_b_4495_, v___y_4496_, v___y_4497_, v___y_4498_, v___y_4499_, v___y_4500_);
lean_dec(v___y_4500_);
lean_dec_ref(v___y_4499_);
lean_dec(v___y_4498_);
lean_dec_ref(v___y_4497_);
lean_dec(v___y_4496_);
lean_dec_ref(v___x_4488_);
lean_dec(v_upperBound_4487_);
return v_res_4505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__8___boxed(lean_object* v_skipInstances_4506_, lean_object* v_pre_4507_, lean_object* v_post_4508_, lean_object* v_usedLetOnly_4509_, lean_object* v_skipConstInApp_4510_, lean_object* v_x_4511_, lean_object* v_x_4512_, lean_object* v_x_4513_, lean_object* v___y_4514_, lean_object* v___y_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_){
_start:
{
uint8_t v_skipInstances_boxed_4520_; uint8_t v_usedLetOnly_boxed_4521_; uint8_t v_skipConstInApp_boxed_4522_; lean_object* v_res_4523_; 
v_skipInstances_boxed_4520_ = lean_unbox(v_skipInstances_4506_);
v_usedLetOnly_boxed_4521_ = lean_unbox(v_usedLetOnly_4509_);
v_skipConstInApp_boxed_4522_ = lean_unbox(v_skipConstInApp_4510_);
v_res_4523_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__8(v_skipInstances_boxed_4520_, v_pre_4507_, v_post_4508_, v_usedLetOnly_boxed_4521_, v_skipConstInApp_boxed_4522_, v_x_4511_, v_x_4512_, v_x_4513_, v___y_4514_, v___y_4515_, v___y_4516_, v___y_4517_, v___y_4518_);
lean_dec(v___y_4518_);
lean_dec_ref(v___y_4517_);
lean_dec(v___y_4516_);
lean_dec_ref(v___y_4515_);
lean_dec(v___y_4514_);
return v_res_4523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(lean_object* v_input_4524_, lean_object* v_pre_4525_, lean_object* v_post_4526_, uint8_t v_usedLetOnly_4527_, uint8_t v_skipConstInApp_4528_, lean_object* v___y_4529_, lean_object* v___y_4530_, lean_object* v___y_4531_, lean_object* v___y_4532_){
_start:
{
uint8_t v___x_4534_; lean_object* v___x_4535_; lean_object* v___x_4536_; lean_object* v_a_4537_; lean_object* v___x_4538_; 
v___x_4534_ = 0;
v___x_4535_ = lean_obj_once(&l_Lean_Core_transform___redArg___closed__2, &l_Lean_Core_transform___redArg___closed__2_once, _init_l_Lean_Core_transform___redArg___closed__2);
v___x_4536_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0(lean_box(0), v___x_4535_, v___y_4529_, v___y_4530_, v___y_4531_, v___y_4532_);
v_a_4537_ = lean_ctor_get(v___x_4536_, 0);
lean_inc(v_a_4537_);
lean_dec_ref(v___x_4536_);
v___x_4538_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4525_, v_post_4526_, v_usedLetOnly_4527_, v_skipConstInApp_4528_, v___x_4534_, v_input_4524_, v_a_4537_, v___y_4529_, v___y_4530_, v___y_4531_, v___y_4532_);
if (lean_obj_tag(v___x_4538_) == 0)
{
lean_object* v_a_4539_; lean_object* v___x_4540_; lean_object* v___x_4541_; lean_object* v___x_4543_; uint8_t v_isShared_4544_; uint8_t v_isSharedCheck_4548_; 
v_a_4539_ = lean_ctor_get(v___x_4538_, 0);
lean_inc(v_a_4539_);
lean_dec_ref_known(v___x_4538_, 1);
v___x_4540_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_4540_, 0, lean_box(0));
lean_closure_set(v___x_4540_, 1, lean_box(0));
lean_closure_set(v___x_4540_, 2, v_a_4537_);
v___x_4541_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0(lean_box(0), v___x_4540_, v___y_4529_, v___y_4530_, v___y_4531_, v___y_4532_);
v_isSharedCheck_4548_ = !lean_is_exclusive(v___x_4541_);
if (v_isSharedCheck_4548_ == 0)
{
lean_object* v_unused_4549_; 
v_unused_4549_ = lean_ctor_get(v___x_4541_, 0);
lean_dec(v_unused_4549_);
v___x_4543_ = v___x_4541_;
v_isShared_4544_ = v_isSharedCheck_4548_;
goto v_resetjp_4542_;
}
else
{
lean_dec(v___x_4541_);
v___x_4543_ = lean_box(0);
v_isShared_4544_ = v_isSharedCheck_4548_;
goto v_resetjp_4542_;
}
v_resetjp_4542_:
{
lean_object* v___x_4546_; 
if (v_isShared_4544_ == 0)
{
lean_ctor_set(v___x_4543_, 0, v_a_4539_);
v___x_4546_ = v___x_4543_;
goto v_reusejp_4545_;
}
else
{
lean_object* v_reuseFailAlloc_4547_; 
v_reuseFailAlloc_4547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4547_, 0, v_a_4539_);
v___x_4546_ = v_reuseFailAlloc_4547_;
goto v_reusejp_4545_;
}
v_reusejp_4545_:
{
return v___x_4546_;
}
}
}
else
{
lean_dec(v_a_4537_);
return v___x_4538_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___boxed(lean_object* v_input_4550_, lean_object* v_pre_4551_, lean_object* v_post_4552_, lean_object* v_usedLetOnly_4553_, lean_object* v_skipConstInApp_4554_, lean_object* v___y_4555_, lean_object* v___y_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_, lean_object* v___y_4559_){
_start:
{
uint8_t v_usedLetOnly_boxed_4560_; uint8_t v_skipConstInApp_boxed_4561_; lean_object* v_res_4562_; 
v_usedLetOnly_boxed_4560_ = lean_unbox(v_usedLetOnly_4553_);
v_skipConstInApp_boxed_4561_ = lean_unbox(v_skipConstInApp_4554_);
v_res_4562_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(v_input_4550_, v_pre_4551_, v_post_4552_, v_usedLetOnly_boxed_4560_, v_skipConstInApp_boxed_4561_, v___y_4555_, v___y_4556_, v___y_4557_, v___y_4558_);
lean_dec(v___y_4558_);
lean_dec_ref(v___y_4557_);
lean_dec(v___y_4556_);
lean_dec_ref(v___y_4555_);
return v_res_4562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce(lean_object* v_e_4564_, uint8_t v_zetaDelta_4565_, uint8_t v_zetaHave_4566_, uint8_t v_beta_4567_, lean_object* v_a_4568_, lean_object* v_a_4569_, lean_object* v_a_4570_, lean_object* v_a_4571_){
_start:
{
lean_object* v_lctx_4573_; lean_object* v___x_4574_; lean_object* v___x_4575_; lean_object* v___x_4576_; lean_object* v___f_4577_; uint8_t v___x_4578_; 
v_lctx_4573_ = lean_ctor_get(v_a_4568_, 2);
lean_inc_ref(v_lctx_4573_);
v___x_4574_ = lean_local_ctx_num_indices(v_lctx_4573_);
v___x_4575_ = lean_box(v_zetaHave_4566_);
v___x_4576_ = lean_box(v_zetaDelta_4565_);
v___f_4577_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaReduce___lam__0___boxed), 9, 3);
lean_closure_set(v___f_4577_, 0, v___x_4575_);
lean_closure_set(v___f_4577_, 1, v___x_4574_);
lean_closure_set(v___f_4577_, 2, v___x_4576_);
v___x_4578_ = 1;
if (v_beta_4567_ == 0)
{
lean_object* v___f_4579_; lean_object* v___f_4580_; lean_object* v___x_4581_; 
v___f_4579_ = ((lean_object*)(l_Lean_Meta_zetaReduce___closed__0));
v___f_4580_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaReduce___lam__2___boxed), 7, 1);
lean_closure_set(v___f_4580_, 0, v___f_4577_);
v___x_4581_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(v_e_4564_, v___f_4580_, v___f_4579_, v___x_4578_, v_beta_4567_, v_a_4568_, v_a_4569_, v_a_4570_, v_a_4571_);
return v___x_4581_;
}
else
{
lean_object* v___f_4582_; lean_object* v___f_4583_; uint8_t v___x_4584_; lean_object* v___x_4585_; 
v___f_4582_ = ((lean_object*)(l_Lean_Meta_zetaReduce___closed__0));
v___f_4583_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaReduce___lam__4___boxed), 7, 1);
lean_closure_set(v___f_4583_, 0, v___f_4577_);
v___x_4584_ = 0;
v___x_4585_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(v_e_4564_, v___f_4583_, v___f_4582_, v___x_4578_, v___x_4584_, v_a_4568_, v_a_4569_, v_a_4570_, v_a_4571_);
return v___x_4585_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___boxed(lean_object* v_e_4586_, lean_object* v_zetaDelta_4587_, lean_object* v_zetaHave_4588_, lean_object* v_beta_4589_, lean_object* v_a_4590_, lean_object* v_a_4591_, lean_object* v_a_4592_, lean_object* v_a_4593_, lean_object* v_a_4594_){
_start:
{
uint8_t v_zetaDelta_boxed_4595_; uint8_t v_zetaHave_boxed_4596_; uint8_t v_beta_boxed_4597_; lean_object* v_res_4598_; 
v_zetaDelta_boxed_4595_ = lean_unbox(v_zetaDelta_4587_);
v_zetaHave_boxed_4596_ = lean_unbox(v_zetaHave_4588_);
v_beta_boxed_4597_ = lean_unbox(v_beta_4589_);
v_res_4598_ = l_Lean_Meta_zetaReduce(v_e_4586_, v_zetaDelta_boxed_4595_, v_zetaHave_boxed_4596_, v_beta_boxed_4597_, v_a_4590_, v_a_4591_, v_a_4592_, v_a_4593_);
lean_dec(v_a_4593_);
lean_dec_ref(v_a_4592_);
lean_dec(v_a_4591_);
lean_dec_ref(v_a_4590_);
return v_res_4598_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4(lean_object* v_upperBound_4599_, lean_object* v___x_4600_, lean_object* v_pre_4601_, lean_object* v_post_4602_, uint8_t v_usedLetOnly_4603_, uint8_t v_skipConstInApp_4604_, uint8_t v_skipInstances_4605_, lean_object* v___x_4606_, lean_object* v_inst_4607_, lean_object* v_R_4608_, lean_object* v_a_4609_, lean_object* v_b_4610_, lean_object* v_c_4611_, lean_object* v___y_4612_, lean_object* v___y_4613_, lean_object* v___y_4614_, lean_object* v___y_4615_, lean_object* v___y_4616_){
_start:
{
lean_object* v___x_4618_; 
v___x_4618_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg(v_upperBound_4599_, v___x_4600_, v_pre_4601_, v_post_4602_, v_usedLetOnly_4603_, v_skipConstInApp_4604_, v_skipInstances_4605_, v_a_4609_, v_b_4610_, v___y_4612_, v___y_4613_, v___y_4614_, v___y_4615_, v___y_4616_);
return v___x_4618_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___boxed(lean_object** _args){
lean_object* v_upperBound_4619_ = _args[0];
lean_object* v___x_4620_ = _args[1];
lean_object* v_pre_4621_ = _args[2];
lean_object* v_post_4622_ = _args[3];
lean_object* v_usedLetOnly_4623_ = _args[4];
lean_object* v_skipConstInApp_4624_ = _args[5];
lean_object* v_skipInstances_4625_ = _args[6];
lean_object* v___x_4626_ = _args[7];
lean_object* v_inst_4627_ = _args[8];
lean_object* v_R_4628_ = _args[9];
lean_object* v_a_4629_ = _args[10];
lean_object* v_b_4630_ = _args[11];
lean_object* v_c_4631_ = _args[12];
lean_object* v___y_4632_ = _args[13];
lean_object* v___y_4633_ = _args[14];
lean_object* v___y_4634_ = _args[15];
lean_object* v___y_4635_ = _args[16];
lean_object* v___y_4636_ = _args[17];
lean_object* v___y_4637_ = _args[18];
_start:
{
uint8_t v_usedLetOnly_boxed_4638_; uint8_t v_skipConstInApp_boxed_4639_; uint8_t v_skipInstances_boxed_4640_; lean_object* v_res_4641_; 
v_usedLetOnly_boxed_4638_ = lean_unbox(v_usedLetOnly_4623_);
v_skipConstInApp_boxed_4639_ = lean_unbox(v_skipConstInApp_4624_);
v_skipInstances_boxed_4640_ = lean_unbox(v_skipInstances_4625_);
v_res_4641_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4(v_upperBound_4619_, v___x_4620_, v_pre_4621_, v_post_4622_, v_usedLetOnly_boxed_4638_, v_skipConstInApp_boxed_4639_, v_skipInstances_boxed_4640_, v___x_4626_, v_inst_4627_, v_R_4628_, v_a_4629_, v_b_4630_, v_c_4631_, v___y_4632_, v___y_4633_, v___y_4634_, v___y_4635_, v___y_4636_);
lean_dec(v___y_4636_);
lean_dec_ref(v___y_4635_);
lean_dec(v___y_4634_);
lean_dec_ref(v___y_4633_);
lean_dec(v___y_4632_);
lean_dec(v___x_4626_);
lean_dec_ref(v___x_4620_);
lean_dec(v_upperBound_4619_);
return v_res_4641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6(lean_object* v_00_u03b1_4642_, lean_object* v_name_4643_, uint8_t v_bi_4644_, lean_object* v_type_4645_, lean_object* v_k_4646_, uint8_t v_kind_4647_, lean_object* v___y_4648_, lean_object* v___y_4649_, lean_object* v___y_4650_, lean_object* v___y_4651_, lean_object* v___y_4652_){
_start:
{
lean_object* v___x_4654_; 
v___x_4654_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_name_4643_, v_bi_4644_, v_type_4645_, v_k_4646_, v_kind_4647_, v___y_4648_, v___y_4649_, v___y_4650_, v___y_4651_, v___y_4652_);
return v___x_4654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___boxed(lean_object* v_00_u03b1_4655_, lean_object* v_name_4656_, lean_object* v_bi_4657_, lean_object* v_type_4658_, lean_object* v_k_4659_, lean_object* v_kind_4660_, lean_object* v___y_4661_, lean_object* v___y_4662_, lean_object* v___y_4663_, lean_object* v___y_4664_, lean_object* v___y_4665_, lean_object* v___y_4666_){
_start:
{
uint8_t v_bi_boxed_4667_; uint8_t v_kind_boxed_4668_; lean_object* v_res_4669_; 
v_bi_boxed_4667_ = lean_unbox(v_bi_4657_);
v_kind_boxed_4668_ = lean_unbox(v_kind_4660_);
v_res_4669_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6(v_00_u03b1_4655_, v_name_4656_, v_bi_boxed_4667_, v_type_4658_, v_k_4659_, v_kind_boxed_4668_, v___y_4661_, v___y_4662_, v___y_4663_, v___y_4664_, v___y_4665_);
lean_dec(v___y_4665_);
lean_dec_ref(v___y_4664_);
lean_dec(v___y_4663_);
lean_dec_ref(v___y_4662_);
lean_dec(v___y_4661_);
return v_res_4669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9(lean_object* v_00_u03b1_4670_, lean_object* v_name_4671_, lean_object* v_type_4672_, lean_object* v_val_4673_, lean_object* v_k_4674_, uint8_t v_nondep_4675_, uint8_t v_kind_4676_, lean_object* v___y_4677_, lean_object* v___y_4678_, lean_object* v___y_4679_, lean_object* v___y_4680_, lean_object* v___y_4681_){
_start:
{
lean_object* v___x_4683_; 
v___x_4683_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg(v_name_4671_, v_type_4672_, v_val_4673_, v_k_4674_, v_nondep_4675_, v_kind_4676_, v___y_4677_, v___y_4678_, v___y_4679_, v___y_4680_, v___y_4681_);
return v___x_4683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___boxed(lean_object* v_00_u03b1_4684_, lean_object* v_name_4685_, lean_object* v_type_4686_, lean_object* v_val_4687_, lean_object* v_k_4688_, lean_object* v_nondep_4689_, lean_object* v_kind_4690_, lean_object* v___y_4691_, lean_object* v___y_4692_, lean_object* v___y_4693_, lean_object* v___y_4694_, lean_object* v___y_4695_, lean_object* v___y_4696_){
_start:
{
uint8_t v_nondep_boxed_4697_; uint8_t v_kind_boxed_4698_; lean_object* v_res_4699_; 
v_nondep_boxed_4697_ = lean_unbox(v_nondep_4689_);
v_kind_boxed_4698_ = lean_unbox(v_kind_4690_);
v_res_4699_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9(v_00_u03b1_4684_, v_name_4685_, v_type_4686_, v_val_4687_, v_k_4688_, v_nondep_boxed_4697_, v_kind_boxed_4698_, v___y_4691_, v___y_4692_, v___y_4693_, v___y_4694_, v___y_4695_);
lean_dec(v___y_4695_);
lean_dec_ref(v___y_4694_);
lean_dec(v___y_4693_);
lean_dec_ref(v___y_4692_);
lean_dec(v___y_4691_);
return v_res_4699_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12(lean_object* v_00_u03b1_4700_, lean_object* v_ref_4701_, lean_object* v___y_4702_, lean_object* v___y_4703_, lean_object* v___y_4704_, lean_object* v___y_4705_){
_start:
{
lean_object* v___x_4707_; 
v___x_4707_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg(v_ref_4701_);
return v___x_4707_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___boxed(lean_object* v_00_u03b1_4708_, lean_object* v_ref_4709_, lean_object* v___y_4710_, lean_object* v___y_4711_, lean_object* v___y_4712_, lean_object* v___y_4713_, lean_object* v___y_4714_){
_start:
{
lean_object* v_res_4715_; 
v_res_4715_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12(v_00_u03b1_4708_, v_ref_4709_, v___y_4710_, v___y_4711_, v___y_4712_, v___y_4713_);
lean_dec(v___y_4713_);
lean_dec_ref(v___y_4712_);
lean_dec(v___y_4711_);
lean_dec_ref(v___y_4710_);
return v_res_4715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9(lean_object* v_00_u03b1_4716_, lean_object* v_x_4717_, lean_object* v___y_4718_, lean_object* v___y_4719_, lean_object* v___y_4720_, lean_object* v___y_4721_, lean_object* v___y_4722_){
_start:
{
lean_object* v___x_4724_; 
v___x_4724_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg(v_x_4717_, v___y_4718_, v___y_4719_, v___y_4720_, v___y_4721_, v___y_4722_);
return v___x_4724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___boxed(lean_object* v_00_u03b1_4725_, lean_object* v_x_4726_, lean_object* v___y_4727_, lean_object* v___y_4728_, lean_object* v___y_4729_, lean_object* v___y_4730_, lean_object* v___y_4731_, lean_object* v___y_4732_){
_start:
{
lean_object* v_res_4733_; 
v_res_4733_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9(v_00_u03b1_4725_, v_x_4726_, v___y_4727_, v___y_4728_, v___y_4729_, v___y_4730_, v___y_4731_);
lean_dec(v___y_4731_);
lean_dec_ref(v___y_4730_);
lean_dec(v___y_4729_);
lean_dec_ref(v___y_4728_);
lean_dec(v___y_4727_);
return v_res_4733_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0_spec__0(lean_object* v_a_4734_, lean_object* v_as_4735_, size_t v_i_4736_, size_t v_stop_4737_){
_start:
{
uint8_t v___x_4738_; 
v___x_4738_ = lean_usize_dec_eq(v_i_4736_, v_stop_4737_);
if (v___x_4738_ == 0)
{
lean_object* v___x_4739_; uint8_t v___x_4740_; 
v___x_4739_ = lean_array_uget_borrowed(v_as_4735_, v_i_4736_);
v___x_4740_ = l_Lean_instBEqFVarId_beq(v_a_4734_, v___x_4739_);
if (v___x_4740_ == 0)
{
size_t v___x_4741_; size_t v___x_4742_; 
v___x_4741_ = ((size_t)1ULL);
v___x_4742_ = lean_usize_add(v_i_4736_, v___x_4741_);
v_i_4736_ = v___x_4742_;
goto _start;
}
else
{
return v___x_4740_;
}
}
else
{
uint8_t v___x_4744_; 
v___x_4744_ = 0;
return v___x_4744_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0_spec__0___boxed(lean_object* v_a_4745_, lean_object* v_as_4746_, lean_object* v_i_4747_, lean_object* v_stop_4748_){
_start:
{
size_t v_i_boxed_4749_; size_t v_stop_boxed_4750_; uint8_t v_res_4751_; lean_object* v_r_4752_; 
v_i_boxed_4749_ = lean_unbox_usize(v_i_4747_);
lean_dec(v_i_4747_);
v_stop_boxed_4750_ = lean_unbox_usize(v_stop_4748_);
lean_dec(v_stop_4748_);
v_res_4751_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0_spec__0(v_a_4745_, v_as_4746_, v_i_boxed_4749_, v_stop_boxed_4750_);
lean_dec_ref(v_as_4746_);
lean_dec(v_a_4745_);
v_r_4752_ = lean_box(v_res_4751_);
return v_r_4752_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0(lean_object* v_as_4753_, lean_object* v_a_4754_){
_start:
{
lean_object* v___x_4755_; lean_object* v___x_4756_; uint8_t v___x_4757_; 
v___x_4755_ = lean_unsigned_to_nat(0u);
v___x_4756_ = lean_array_get_size(v_as_4753_);
v___x_4757_ = lean_nat_dec_lt(v___x_4755_, v___x_4756_);
if (v___x_4757_ == 0)
{
return v___x_4757_;
}
else
{
if (v___x_4757_ == 0)
{
return v___x_4757_;
}
else
{
size_t v___x_4758_; size_t v___x_4759_; uint8_t v___x_4760_; 
v___x_4758_ = ((size_t)0ULL);
v___x_4759_ = lean_usize_of_nat(v___x_4756_);
v___x_4760_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0_spec__0(v_a_4754_, v_as_4753_, v___x_4758_, v___x_4759_);
return v___x_4760_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0___boxed(lean_object* v_as_4761_, lean_object* v_a_4762_){
_start:
{
uint8_t v_res_4763_; lean_object* v_r_4764_; 
v_res_4763_ = l_Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0(v_as_4761_, v_a_4762_);
lean_dec(v_a_4762_);
lean_dec_ref(v_as_4761_);
v_r_4764_ = lean_box(v_res_4763_);
return v_r_4764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaFVars___lam__1(lean_object* v_fvars_4765_, lean_object* v_e_4766_, lean_object* v___y_4767_, lean_object* v___y_4768_, lean_object* v___y_4769_, lean_object* v___y_4770_){
_start:
{
lean_object* v___x_4775_; 
v___x_4775_ = l_Lean_Expr_getAppFn(v_e_4766_);
if (lean_obj_tag(v___x_4775_) == 1)
{
lean_object* v_fvarId_4776_; uint8_t v___x_4777_; 
v_fvarId_4776_ = lean_ctor_get(v___x_4775_, 0);
lean_inc(v_fvarId_4776_);
lean_dec_ref_known(v___x_4775_, 1);
v___x_4777_ = l_Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0(v_fvars_4765_, v_fvarId_4776_);
if (v___x_4777_ == 0)
{
lean_dec(v_fvarId_4776_);
lean_dec_ref(v_e_4766_);
goto v___jp_4772_;
}
else
{
uint8_t v___x_4778_; lean_object* v___x_4779_; 
v___x_4778_ = 0;
v___x_4779_ = l_Lean_FVarId_getValue_x3f___redArg(v_fvarId_4776_, v___x_4778_, v___y_4767_, v___y_4769_, v___y_4770_);
if (lean_obj_tag(v___x_4779_) == 0)
{
lean_object* v_a_4780_; 
v_a_4780_ = lean_ctor_get(v___x_4779_, 0);
lean_inc(v_a_4780_);
lean_dec_ref_known(v___x_4779_, 1);
if (lean_obj_tag(v_a_4780_) == 1)
{
lean_object* v_val_4781_; lean_object* v___x_4783_; uint8_t v_isShared_4784_; uint8_t v_isSharedCheck_4804_; 
v_val_4781_ = lean_ctor_get(v_a_4780_, 0);
v_isSharedCheck_4804_ = !lean_is_exclusive(v_a_4780_);
if (v_isSharedCheck_4804_ == 0)
{
v___x_4783_ = v_a_4780_;
v_isShared_4784_ = v_isSharedCheck_4804_;
goto v_resetjp_4782_;
}
else
{
lean_inc(v_val_4781_);
lean_dec(v_a_4780_);
v___x_4783_ = lean_box(0);
v_isShared_4784_ = v_isSharedCheck_4804_;
goto v_resetjp_4782_;
}
v_resetjp_4782_:
{
lean_object* v___x_4785_; lean_object* v_a_4786_; lean_object* v___x_4788_; uint8_t v_isShared_4789_; uint8_t v_isSharedCheck_4803_; 
v___x_4785_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(v_val_4781_, v___y_4768_);
v_a_4786_ = lean_ctor_get(v___x_4785_, 0);
v_isSharedCheck_4803_ = !lean_is_exclusive(v___x_4785_);
if (v_isSharedCheck_4803_ == 0)
{
v___x_4788_ = v___x_4785_;
v_isShared_4789_ = v_isSharedCheck_4803_;
goto v_resetjp_4787_;
}
else
{
lean_inc(v_a_4786_);
lean_dec(v___x_4785_);
v___x_4788_ = lean_box(0);
v_isShared_4789_ = v_isSharedCheck_4803_;
goto v_resetjp_4787_;
}
v_resetjp_4787_:
{
lean_object* v_dummy_4790_; lean_object* v_nargs_4791_; lean_object* v___x_4792_; lean_object* v___x_4793_; lean_object* v___x_4794_; lean_object* v___x_4795_; lean_object* v___x_4796_; lean_object* v___x_4798_; 
v_dummy_4790_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_4791_ = l_Lean_Expr_getAppNumArgs(v_e_4766_);
lean_inc(v_nargs_4791_);
v___x_4792_ = lean_mk_array(v_nargs_4791_, v_dummy_4790_);
v___x_4793_ = lean_unsigned_to_nat(1u);
v___x_4794_ = lean_nat_sub(v_nargs_4791_, v___x_4793_);
lean_dec(v_nargs_4791_);
v___x_4795_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_4766_, v___x_4792_, v___x_4794_);
v___x_4796_ = l_Lean_Expr_beta(v_a_4786_, v___x_4795_);
if (v_isShared_4784_ == 0)
{
lean_ctor_set(v___x_4783_, 0, v___x_4796_);
v___x_4798_ = v___x_4783_;
goto v_reusejp_4797_;
}
else
{
lean_object* v_reuseFailAlloc_4802_; 
v_reuseFailAlloc_4802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4802_, 0, v___x_4796_);
v___x_4798_ = v_reuseFailAlloc_4802_;
goto v_reusejp_4797_;
}
v_reusejp_4797_:
{
lean_object* v___x_4800_; 
if (v_isShared_4789_ == 0)
{
lean_ctor_set(v___x_4788_, 0, v___x_4798_);
v___x_4800_ = v___x_4788_;
goto v_reusejp_4799_;
}
else
{
lean_object* v_reuseFailAlloc_4801_; 
v_reuseFailAlloc_4801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4801_, 0, v___x_4798_);
v___x_4800_ = v_reuseFailAlloc_4801_;
goto v_reusejp_4799_;
}
v_reusejp_4799_:
{
return v___x_4800_;
}
}
}
}
}
else
{
lean_dec(v_a_4780_);
lean_dec_ref(v_e_4766_);
goto v___jp_4772_;
}
}
else
{
lean_object* v_a_4805_; lean_object* v___x_4807_; uint8_t v_isShared_4808_; uint8_t v_isSharedCheck_4812_; 
lean_dec_ref(v_e_4766_);
v_a_4805_ = lean_ctor_get(v___x_4779_, 0);
v_isSharedCheck_4812_ = !lean_is_exclusive(v___x_4779_);
if (v_isSharedCheck_4812_ == 0)
{
v___x_4807_ = v___x_4779_;
v_isShared_4808_ = v_isSharedCheck_4812_;
goto v_resetjp_4806_;
}
else
{
lean_inc(v_a_4805_);
lean_dec(v___x_4779_);
v___x_4807_ = lean_box(0);
v_isShared_4808_ = v_isSharedCheck_4812_;
goto v_resetjp_4806_;
}
v_resetjp_4806_:
{
lean_object* v___x_4810_; 
if (v_isShared_4808_ == 0)
{
v___x_4810_ = v___x_4807_;
goto v_reusejp_4809_;
}
else
{
lean_object* v_reuseFailAlloc_4811_; 
v_reuseFailAlloc_4811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4811_, 0, v_a_4805_);
v___x_4810_ = v_reuseFailAlloc_4811_;
goto v_reusejp_4809_;
}
v_reusejp_4809_:
{
return v___x_4810_;
}
}
}
}
}
else
{
lean_object* v___x_4813_; lean_object* v___x_4814_; 
lean_dec_ref(v___x_4775_);
lean_dec_ref(v_e_4766_);
v___x_4813_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_4814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4814_, 0, v___x_4813_);
return v___x_4814_;
}
v___jp_4772_:
{
lean_object* v___x_4773_; lean_object* v___x_4774_; 
v___x_4773_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_4774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4774_, 0, v___x_4773_);
return v___x_4774_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaFVars___lam__1___boxed(lean_object* v_fvars_4815_, lean_object* v_e_4816_, lean_object* v___y_4817_, lean_object* v___y_4818_, lean_object* v___y_4819_, lean_object* v___y_4820_, lean_object* v___y_4821_){
_start:
{
lean_object* v_res_4822_; 
v_res_4822_ = l_Lean_Meta_zetaDeltaFVars___lam__1(v_fvars_4815_, v_e_4816_, v___y_4817_, v___y_4818_, v___y_4819_, v___y_4820_);
lean_dec(v___y_4820_);
lean_dec_ref(v___y_4819_);
lean_dec(v___y_4818_);
lean_dec_ref(v___y_4817_);
lean_dec_ref(v_fvars_4815_);
return v_res_4822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaFVars(lean_object* v_e_4823_, lean_object* v_fvars_4824_, lean_object* v_a_4825_, lean_object* v_a_4826_, lean_object* v_a_4827_, lean_object* v_a_4828_){
_start:
{
lean_object* v___f_4830_; lean_object* v_pre_4831_; uint8_t v___x_4832_; lean_object* v___x_4833_; 
v___f_4830_ = ((lean_object*)(l_Lean_Meta_zetaReduce___closed__0));
v_pre_4831_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaDeltaFVars___lam__1___boxed), 7, 1);
lean_closure_set(v_pre_4831_, 0, v_fvars_4824_);
v___x_4832_ = 0;
v___x_4833_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(v_e_4823_, v_pre_4831_, v___f_4830_, v___x_4832_, v___x_4832_, v_a_4825_, v_a_4826_, v_a_4827_, v_a_4828_);
return v___x_4833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaFVars___boxed(lean_object* v_e_4834_, lean_object* v_fvars_4835_, lean_object* v_a_4836_, lean_object* v_a_4837_, lean_object* v_a_4838_, lean_object* v_a_4839_, lean_object* v_a_4840_){
_start:
{
lean_object* v_res_4841_; 
v_res_4841_ = l_Lean_Meta_zetaDeltaFVars(v_e_4834_, v_fvars_4835_, v_a_4836_, v_a_4837_, v_a_4838_, v_a_4839_);
lean_dec(v_a_4839_);
lean_dec_ref(v_a_4838_);
lean_dec(v_a_4837_);
lean_dec_ref(v_a_4836_);
return v_res_4841_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_4842_; 
v___x_4842_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_4842_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_4843_; lean_object* v___x_4844_; 
v___x_4843_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__0, &l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__0);
v___x_4844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4844_, 0, v___x_4843_);
return v___x_4844_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_4845_; lean_object* v___x_4846_; 
v___x_4845_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__1, &l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__1);
v___x_4846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4846_, 0, v___x_4845_);
lean_ctor_set(v___x_4846_, 1, v___x_4845_);
return v___x_4846_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(lean_object* v_env_4847_, lean_object* v___y_4848_){
_start:
{
lean_object* v___x_4850_; lean_object* v_nextMacroScope_4851_; lean_object* v_ngen_4852_; lean_object* v_auxDeclNGen_4853_; lean_object* v_traceState_4854_; lean_object* v_recordedDeps_4855_; lean_object* v_messages_4856_; lean_object* v_infoState_4857_; lean_object* v_snapshotTasks_4858_; lean_object* v___x_4860_; uint8_t v_isShared_4861_; uint8_t v_isSharedCheck_4869_; 
v___x_4850_ = lean_st_ref_take(v___y_4848_);
v_nextMacroScope_4851_ = lean_ctor_get(v___x_4850_, 1);
v_ngen_4852_ = lean_ctor_get(v___x_4850_, 2);
v_auxDeclNGen_4853_ = lean_ctor_get(v___x_4850_, 3);
v_traceState_4854_ = lean_ctor_get(v___x_4850_, 4);
v_recordedDeps_4855_ = lean_ctor_get(v___x_4850_, 6);
v_messages_4856_ = lean_ctor_get(v___x_4850_, 7);
v_infoState_4857_ = lean_ctor_get(v___x_4850_, 8);
v_snapshotTasks_4858_ = lean_ctor_get(v___x_4850_, 9);
v_isSharedCheck_4869_ = !lean_is_exclusive(v___x_4850_);
if (v_isSharedCheck_4869_ == 0)
{
lean_object* v_unused_4870_; lean_object* v_unused_4871_; 
v_unused_4870_ = lean_ctor_get(v___x_4850_, 5);
lean_dec(v_unused_4870_);
v_unused_4871_ = lean_ctor_get(v___x_4850_, 0);
lean_dec(v_unused_4871_);
v___x_4860_ = v___x_4850_;
v_isShared_4861_ = v_isSharedCheck_4869_;
goto v_resetjp_4859_;
}
else
{
lean_inc(v_snapshotTasks_4858_);
lean_inc(v_infoState_4857_);
lean_inc(v_messages_4856_);
lean_inc(v_recordedDeps_4855_);
lean_inc(v_traceState_4854_);
lean_inc(v_auxDeclNGen_4853_);
lean_inc(v_ngen_4852_);
lean_inc(v_nextMacroScope_4851_);
lean_dec(v___x_4850_);
v___x_4860_ = lean_box(0);
v_isShared_4861_ = v_isSharedCheck_4869_;
goto v_resetjp_4859_;
}
v_resetjp_4859_:
{
lean_object* v___x_4862_; lean_object* v___x_4863_; lean_object* v___x_4865_; 
v___x_4862_ = lean_box(0);
v___x_4863_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2, &l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2);
if (v_isShared_4861_ == 0)
{
lean_ctor_set(v___x_4860_, 5, v___x_4863_);
lean_ctor_set(v___x_4860_, 0, v_env_4847_);
v___x_4865_ = v___x_4860_;
goto v_reusejp_4864_;
}
else
{
lean_object* v_reuseFailAlloc_4868_; 
v_reuseFailAlloc_4868_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4868_, 0, v_env_4847_);
lean_ctor_set(v_reuseFailAlloc_4868_, 1, v_nextMacroScope_4851_);
lean_ctor_set(v_reuseFailAlloc_4868_, 2, v_ngen_4852_);
lean_ctor_set(v_reuseFailAlloc_4868_, 3, v_auxDeclNGen_4853_);
lean_ctor_set(v_reuseFailAlloc_4868_, 4, v_traceState_4854_);
lean_ctor_set(v_reuseFailAlloc_4868_, 5, v___x_4863_);
lean_ctor_set(v_reuseFailAlloc_4868_, 6, v_recordedDeps_4855_);
lean_ctor_set(v_reuseFailAlloc_4868_, 7, v_messages_4856_);
lean_ctor_set(v_reuseFailAlloc_4868_, 8, v_infoState_4857_);
lean_ctor_set(v_reuseFailAlloc_4868_, 9, v_snapshotTasks_4858_);
v___x_4865_ = v_reuseFailAlloc_4868_;
goto v_reusejp_4864_;
}
v_reusejp_4864_:
{
lean_object* v___x_4866_; lean_object* v___x_4867_; 
v___x_4866_ = lean_st_ref_put(v___y_4848_, v___x_4865_);
v___x_4867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4867_, 0, v___x_4862_);
return v___x_4867_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___boxed(lean_object* v_env_4872_, lean_object* v___y_4873_, lean_object* v___y_4874_){
_start:
{
lean_object* v_res_4875_; 
v_res_4875_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_4872_, v___y_4873_);
lean_dec(v___y_4873_);
return v_res_4875_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0(lean_object* v_env_4876_, lean_object* v___y_4877_, lean_object* v___y_4878_){
_start:
{
lean_object* v___x_4880_; 
v___x_4880_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_4876_, v___y_4878_);
return v___x_4880_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___boxed(lean_object* v_env_4881_, lean_object* v___y_4882_, lean_object* v___y_4883_, lean_object* v___y_4884_){
_start:
{
lean_object* v_res_4885_; 
v_res_4885_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0(v_env_4881_, v___y_4882_, v___y_4883_);
lean_dec(v___y_4883_);
lean_dec_ref(v___y_4882_);
return v_res_4885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___lam__1(lean_object* v_env_4886_, lean_object* v___x_4887_, uint8_t v___x_4888_, lean_object* v_e_4889_, lean_object* v___y_4890_, lean_object* v___y_4891_){
_start:
{
if (lean_obj_tag(v_e_4889_) == 4)
{
lean_object* v_declName_4893_; lean_object* v_us_4894_; uint8_t v___x_4895_; uint8_t v___x_4896_; 
v_declName_4893_ = lean_ctor_get(v_e_4889_, 0);
v_us_4894_ = lean_ctor_get(v_e_4889_, 1);
v___x_4895_ = 1;
lean_inc(v_declName_4893_);
v___x_4896_ = l_Lean_Environment_contains(v_env_4886_, v_declName_4893_, v___x_4895_);
if (v___x_4896_ == 0)
{
lean_object* v___x_4897_; 
lean_inc(v_declName_4893_);
v___x_4897_ = l_Lean_Environment_find_x3f(v___x_4887_, v_declName_4893_, v___x_4888_);
if (lean_obj_tag(v___x_4897_) == 1)
{
lean_object* v_val_4898_; lean_object* v___x_4900_; uint8_t v_isShared_4901_; uint8_t v_isSharedCheck_4927_; 
v_val_4898_ = lean_ctor_get(v___x_4897_, 0);
v_isSharedCheck_4927_ = !lean_is_exclusive(v___x_4897_);
if (v_isSharedCheck_4927_ == 0)
{
v___x_4900_ = v___x_4897_;
v_isShared_4901_ = v_isSharedCheck_4927_;
goto v_resetjp_4899_;
}
else
{
lean_inc(v_val_4898_);
lean_dec(v___x_4897_);
v___x_4900_ = lean_box(0);
v_isShared_4901_ = v_isSharedCheck_4927_;
goto v_resetjp_4899_;
}
v_resetjp_4899_:
{
uint8_t v___x_4902_; 
v___x_4902_ = l_Lean_ConstantInfo_hasValue(v_val_4898_, v___x_4895_);
if (v___x_4902_ == 0)
{
lean_object* v___x_4904_; 
lean_dec(v_val_4898_);
if (v_isShared_4901_ == 0)
{
lean_ctor_set_tag(v___x_4900_, 0);
lean_ctor_set(v___x_4900_, 0, v_e_4889_);
v___x_4904_ = v___x_4900_;
goto v_reusejp_4903_;
}
else
{
lean_object* v_reuseFailAlloc_4906_; 
v_reuseFailAlloc_4906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4906_, 0, v_e_4889_);
v___x_4904_ = v_reuseFailAlloc_4906_;
goto v_reusejp_4903_;
}
v_reusejp_4903_:
{
lean_object* v___x_4905_; 
v___x_4905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4905_, 0, v___x_4904_);
return v___x_4905_;
}
}
else
{
lean_object* v___x_4907_; 
lean_inc(v_us_4894_);
lean_dec_ref_known(v_e_4889_, 2);
v___x_4907_ = l_Lean_Core_instantiateValueLevelParams(v_val_4898_, v_us_4894_, v___x_4895_, v___y_4890_, v___y_4891_);
lean_dec(v_val_4898_);
if (lean_obj_tag(v___x_4907_) == 0)
{
lean_object* v_a_4908_; lean_object* v___x_4910_; uint8_t v_isShared_4911_; uint8_t v_isSharedCheck_4918_; 
v_a_4908_ = lean_ctor_get(v___x_4907_, 0);
v_isSharedCheck_4918_ = !lean_is_exclusive(v___x_4907_);
if (v_isSharedCheck_4918_ == 0)
{
v___x_4910_ = v___x_4907_;
v_isShared_4911_ = v_isSharedCheck_4918_;
goto v_resetjp_4909_;
}
else
{
lean_inc(v_a_4908_);
lean_dec(v___x_4907_);
v___x_4910_ = lean_box(0);
v_isShared_4911_ = v_isSharedCheck_4918_;
goto v_resetjp_4909_;
}
v_resetjp_4909_:
{
lean_object* v___x_4913_; 
if (v_isShared_4901_ == 0)
{
lean_ctor_set(v___x_4900_, 0, v_a_4908_);
v___x_4913_ = v___x_4900_;
goto v_reusejp_4912_;
}
else
{
lean_object* v_reuseFailAlloc_4917_; 
v_reuseFailAlloc_4917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4917_, 0, v_a_4908_);
v___x_4913_ = v_reuseFailAlloc_4917_;
goto v_reusejp_4912_;
}
v_reusejp_4912_:
{
lean_object* v___x_4915_; 
if (v_isShared_4911_ == 0)
{
lean_ctor_set(v___x_4910_, 0, v___x_4913_);
v___x_4915_ = v___x_4910_;
goto v_reusejp_4914_;
}
else
{
lean_object* v_reuseFailAlloc_4916_; 
v_reuseFailAlloc_4916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4916_, 0, v___x_4913_);
v___x_4915_ = v_reuseFailAlloc_4916_;
goto v_reusejp_4914_;
}
v_reusejp_4914_:
{
return v___x_4915_;
}
}
}
}
else
{
lean_object* v_a_4919_; lean_object* v___x_4921_; uint8_t v_isShared_4922_; uint8_t v_isSharedCheck_4926_; 
lean_del_object(v___x_4900_);
v_a_4919_ = lean_ctor_get(v___x_4907_, 0);
v_isSharedCheck_4926_ = !lean_is_exclusive(v___x_4907_);
if (v_isSharedCheck_4926_ == 0)
{
v___x_4921_ = v___x_4907_;
v_isShared_4922_ = v_isSharedCheck_4926_;
goto v_resetjp_4920_;
}
else
{
lean_inc(v_a_4919_);
lean_dec(v___x_4907_);
v___x_4921_ = lean_box(0);
v_isShared_4922_ = v_isSharedCheck_4926_;
goto v_resetjp_4920_;
}
v_resetjp_4920_:
{
lean_object* v___x_4924_; 
if (v_isShared_4922_ == 0)
{
v___x_4924_ = v___x_4921_;
goto v_reusejp_4923_;
}
else
{
lean_object* v_reuseFailAlloc_4925_; 
v_reuseFailAlloc_4925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4925_, 0, v_a_4919_);
v___x_4924_ = v_reuseFailAlloc_4925_;
goto v_reusejp_4923_;
}
v_reusejp_4923_:
{
return v___x_4924_;
}
}
}
}
}
}
else
{
lean_object* v___x_4928_; lean_object* v___x_4929_; 
lean_dec(v___x_4897_);
v___x_4928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4928_, 0, v_e_4889_);
v___x_4929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4929_, 0, v___x_4928_);
return v___x_4929_;
}
}
else
{
lean_object* v___x_4930_; lean_object* v___x_4931_; 
lean_dec_ref(v___x_4887_);
v___x_4930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4930_, 0, v_e_4889_);
v___x_4931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4931_, 0, v___x_4930_);
return v___x_4931_;
}
}
else
{
lean_object* v___x_4932_; lean_object* v___x_4933_; 
lean_dec_ref(v_e_4889_);
lean_dec_ref(v___x_4887_);
lean_dec_ref(v_env_4886_);
v___x_4932_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_4933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4933_, 0, v___x_4932_);
return v___x_4933_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___lam__1___boxed(lean_object* v_env_4934_, lean_object* v___x_4935_, lean_object* v___x_4936_, lean_object* v_e_4937_, lean_object* v___y_4938_, lean_object* v___y_4939_, lean_object* v___y_4940_){
_start:
{
uint8_t v___x_1999__boxed_4941_; lean_object* v_res_4942_; 
v___x_1999__boxed_4941_ = lean_unbox(v___x_4936_);
v_res_4942_ = l_Lean_Meta_unfoldDeclsFrom___lam__1(v_env_4934_, v___x_4935_, v___x_1999__boxed_4941_, v_e_4937_, v___y_4938_, v___y_4939_);
lean_dec(v___y_4939_);
lean_dec_ref(v___y_4938_);
return v_res_4942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___lam__0(lean_object* v_biggerEnv_4943_, lean_object* v_e_4944_, lean_object* v___f_4945_, lean_object* v___y_4946_, lean_object* v___y_4947_){
_start:
{
lean_object* v___x_4949_; lean_object* v_env_4950_; uint8_t v___x_4951_; lean_object* v___x_4952_; lean_object* v___x_4953_; lean_object* v___f_4954_; lean_object* v___x_4955_; lean_object* v___x_4956_; 
v___x_4949_ = lean_st_ref_get(v___y_4947_);
v_env_4950_ = lean_ctor_get(v___x_4949_, 0);
lean_inc_ref(v_env_4950_);
lean_dec(v___x_4949_);
v___x_4951_ = 0;
v___x_4952_ = l_Lean_Environment_setExporting(v_biggerEnv_4943_, v___x_4951_);
v___x_4953_ = lean_box(v___x_4951_);
lean_inc_ref(v___x_4952_);
v___f_4954_ = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDeclsFrom___lam__1___boxed), 7, 3);
lean_closure_set(v___f_4954_, 0, v_env_4950_);
lean_closure_set(v___f_4954_, 1, v___x_4952_);
lean_closure_set(v___f_4954_, 2, v___x_4953_);
v___x_4955_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v___x_4952_, v___y_4947_);
lean_dec_ref(v___x_4955_);
v___x_4956_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_4944_, v___f_4954_, v___f_4945_, v___y_4946_, v___y_4947_);
return v___x_4956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___lam__0___boxed(lean_object* v_biggerEnv_4957_, lean_object* v_e_4958_, lean_object* v___f_4959_, lean_object* v___y_4960_, lean_object* v___y_4961_, lean_object* v___y_4962_){
_start:
{
lean_object* v_res_4963_; 
v_res_4963_ = l_Lean_Meta_unfoldDeclsFrom___lam__0(v_biggerEnv_4957_, v_e_4958_, v___f_4959_, v___y_4960_, v___y_4961_);
lean_dec(v___y_4961_);
lean_dec_ref(v___y_4960_);
return v_res_4963_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg(lean_object* v_env_4964_, lean_object* v_x_4965_, lean_object* v___y_4966_, lean_object* v___y_4967_){
_start:
{
lean_object* v___x_4969_; lean_object* v_env_4970_; lean_object* v_a_4972_; lean_object* v___x_4982_; lean_object* v___x_4983_; 
v___x_4969_ = lean_st_ref_get(v___y_4967_);
v_env_4970_ = lean_ctor_get(v___x_4969_, 0);
lean_inc_ref(v_env_4970_);
lean_dec(v___x_4969_);
v___x_4982_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_4964_, v___y_4967_);
lean_dec_ref(v___x_4982_);
lean_inc(v___y_4967_);
lean_inc_ref(v___y_4966_);
v___x_4983_ = lean_apply_3(v_x_4965_, v___y_4966_, v___y_4967_, lean_box(0));
if (lean_obj_tag(v___x_4983_) == 0)
{
lean_object* v_a_4984_; lean_object* v___x_4985_; lean_object* v___x_4987_; uint8_t v_isShared_4988_; uint8_t v_isSharedCheck_4992_; 
v_a_4984_ = lean_ctor_get(v___x_4983_, 0);
lean_inc(v_a_4984_);
lean_dec_ref_known(v___x_4983_, 1);
v___x_4985_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_4970_, v___y_4967_);
v_isSharedCheck_4992_ = !lean_is_exclusive(v___x_4985_);
if (v_isSharedCheck_4992_ == 0)
{
lean_object* v_unused_4993_; 
v_unused_4993_ = lean_ctor_get(v___x_4985_, 0);
lean_dec(v_unused_4993_);
v___x_4987_ = v___x_4985_;
v_isShared_4988_ = v_isSharedCheck_4992_;
goto v_resetjp_4986_;
}
else
{
lean_dec(v___x_4985_);
v___x_4987_ = lean_box(0);
v_isShared_4988_ = v_isSharedCheck_4992_;
goto v_resetjp_4986_;
}
v_resetjp_4986_:
{
lean_object* v___x_4990_; 
if (v_isShared_4988_ == 0)
{
lean_ctor_set(v___x_4987_, 0, v_a_4984_);
v___x_4990_ = v___x_4987_;
goto v_reusejp_4989_;
}
else
{
lean_object* v_reuseFailAlloc_4991_; 
v_reuseFailAlloc_4991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4991_, 0, v_a_4984_);
v___x_4990_ = v_reuseFailAlloc_4991_;
goto v_reusejp_4989_;
}
v_reusejp_4989_:
{
return v___x_4990_;
}
}
}
else
{
lean_object* v_a_4994_; 
v_a_4994_ = lean_ctor_get(v___x_4983_, 0);
lean_inc(v_a_4994_);
lean_dec_ref_known(v___x_4983_, 1);
v_a_4972_ = v_a_4994_;
goto v___jp_4971_;
}
v___jp_4971_:
{
lean_object* v___x_4973_; lean_object* v___x_4975_; uint8_t v_isShared_4976_; uint8_t v_isSharedCheck_4980_; 
v___x_4973_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_4970_, v___y_4967_);
v_isSharedCheck_4980_ = !lean_is_exclusive(v___x_4973_);
if (v_isSharedCheck_4980_ == 0)
{
lean_object* v_unused_4981_; 
v_unused_4981_ = lean_ctor_get(v___x_4973_, 0);
lean_dec(v_unused_4981_);
v___x_4975_ = v___x_4973_;
v_isShared_4976_ = v_isSharedCheck_4980_;
goto v_resetjp_4974_;
}
else
{
lean_dec(v___x_4973_);
v___x_4975_ = lean_box(0);
v_isShared_4976_ = v_isSharedCheck_4980_;
goto v_resetjp_4974_;
}
v_resetjp_4974_:
{
lean_object* v___x_4978_; 
if (v_isShared_4976_ == 0)
{
lean_ctor_set_tag(v___x_4975_, 1);
lean_ctor_set(v___x_4975_, 0, v_a_4972_);
v___x_4978_ = v___x_4975_;
goto v_reusejp_4977_;
}
else
{
lean_object* v_reuseFailAlloc_4979_; 
v_reuseFailAlloc_4979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4979_, 0, v_a_4972_);
v___x_4978_ = v_reuseFailAlloc_4979_;
goto v_reusejp_4977_;
}
v_reusejp_4977_:
{
return v___x_4978_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg___boxed(lean_object* v_env_4995_, lean_object* v_x_4996_, lean_object* v___y_4997_, lean_object* v___y_4998_, lean_object* v___y_4999_){
_start:
{
lean_object* v_res_5000_; 
v_res_5000_ = l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg(v_env_4995_, v_x_4996_, v___y_4997_, v___y_4998_);
lean_dec(v___y_4998_);
lean_dec_ref(v___y_4997_);
return v_res_5000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom(lean_object* v_biggerEnv_5001_, lean_object* v_e_5002_, lean_object* v_a_5003_, lean_object* v_a_5004_){
_start:
{
lean_object* v___f_5006_; lean_object* v___f_5007_; lean_object* v___x_5008_; lean_object* v_env_5009_; lean_object* v___x_5010_; lean_object* v___x_5011_; 
v___f_5006_ = ((lean_object*)(l_Lean_Core_betaReduce___closed__1));
v___f_5007_ = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDeclsFrom___lam__0___boxed), 6, 3);
lean_closure_set(v___f_5007_, 0, v_biggerEnv_5001_);
lean_closure_set(v___f_5007_, 1, v_e_5002_);
lean_closure_set(v___f_5007_, 2, v___f_5006_);
v___x_5008_ = lean_st_ref_get(v_a_5004_);
v_env_5009_ = lean_ctor_get(v___x_5008_, 0);
lean_inc_ref(v_env_5009_);
lean_dec(v___x_5008_);
v___x_5010_ = l_Lean_Environment_unlockAsync(v_env_5009_);
v___x_5011_ = l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg(v___x_5010_, v___f_5007_, v_a_5003_, v_a_5004_);
return v___x_5011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___boxed(lean_object* v_biggerEnv_5012_, lean_object* v_e_5013_, lean_object* v_a_5014_, lean_object* v_a_5015_, lean_object* v_a_5016_){
_start:
{
lean_object* v_res_5017_; 
v_res_5017_ = l_Lean_Meta_unfoldDeclsFrom(v_biggerEnv_5012_, v_e_5013_, v_a_5014_, v_a_5015_);
lean_dec(v_a_5015_);
lean_dec_ref(v_a_5014_);
return v_res_5017_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1(lean_object* v_00_u03b1_5018_, lean_object* v_env_5019_, lean_object* v_x_5020_, lean_object* v___y_5021_, lean_object* v___y_5022_){
_start:
{
lean_object* v___x_5024_; 
v___x_5024_ = l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg(v_env_5019_, v_x_5020_, v___y_5021_, v___y_5022_);
return v___x_5024_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___boxed(lean_object* v_00_u03b1_5025_, lean_object* v_env_5026_, lean_object* v_x_5027_, lean_object* v___y_5028_, lean_object* v___y_5029_, lean_object* v___y_5030_){
_start:
{
lean_object* v_res_5031_; 
v_res_5031_ = l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1(v_00_u03b1_5025_, v_env_5026_, v_x_5027_, v___y_5028_, v___y_5029_);
lean_dec(v___y_5029_);
lean_dec_ref(v___y_5028_);
return v_res_5031_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0(lean_object* v_af_5032_, lean_object* v_axs_5033_, lean_object* v_numSectionVars_5034_, lean_object* v_as_5035_, size_t v_i_5036_, size_t v_stop_5037_){
_start:
{
uint8_t v___x_5038_; 
v___x_5038_ = lean_usize_dec_eq(v_i_5036_, v_stop_5037_);
if (v___x_5038_ == 0)
{
uint8_t v___x_5039_; uint8_t v___y_5041_; lean_object* v___x_5045_; lean_object* v___x_5046_; uint8_t v___x_5047_; 
v___x_5039_ = 1;
v___x_5045_ = lean_array_uget_borrowed(v_as_5035_, v_i_5036_);
v___x_5046_ = l_Lean_Expr_constName_x21(v_af_5032_);
v___x_5047_ = lean_name_eq(v___x_5046_, v___x_5045_);
lean_dec(v___x_5046_);
if (v___x_5047_ == 0)
{
v___y_5041_ = v___x_5047_;
goto v___jp_5040_;
}
else
{
lean_object* v___x_5048_; uint8_t v___x_5049_; 
v___x_5048_ = lean_array_get_size(v_axs_5033_);
v___x_5049_ = lean_nat_dec_le(v___x_5048_, v_numSectionVars_5034_);
v___y_5041_ = v___x_5049_;
goto v___jp_5040_;
}
v___jp_5040_:
{
if (v___y_5041_ == 0)
{
size_t v___x_5042_; size_t v___x_5043_; 
v___x_5042_ = ((size_t)1ULL);
v___x_5043_ = lean_usize_add(v_i_5036_, v___x_5042_);
v_i_5036_ = v___x_5043_;
goto _start;
}
else
{
return v___x_5039_;
}
}
}
else
{
uint8_t v___x_5050_; 
v___x_5050_ = 0;
return v___x_5050_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0___boxed(lean_object* v_af_5051_, lean_object* v_axs_5052_, lean_object* v_numSectionVars_5053_, lean_object* v_as_5054_, lean_object* v_i_5055_, lean_object* v_stop_5056_){
_start:
{
size_t v_i_boxed_5057_; size_t v_stop_boxed_5058_; uint8_t v_res_5059_; lean_object* v_r_5060_; 
v_i_boxed_5057_ = lean_unbox_usize(v_i_5055_);
lean_dec(v_i_5055_);
v_stop_boxed_5058_ = lean_unbox_usize(v_stop_5056_);
lean_dec(v_stop_5056_);
v_res_5059_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0(v_af_5051_, v_axs_5052_, v_numSectionVars_5053_, v_as_5054_, v_i_boxed_5057_, v_stop_boxed_5058_);
lean_dec_ref(v_as_5054_);
lean_dec(v_numSectionVars_5053_);
lean_dec_ref(v_axs_5052_);
lean_dec_ref(v_af_5051_);
v_r_5060_ = lean_box(v_res_5059_);
return v_r_5060_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1_spec__1(lean_object* v_fnNames_5061_, lean_object* v_numSectionVars_5062_, lean_object* v_x_5063_, lean_object* v_x_5064_, lean_object* v_x_5065_){
_start:
{
if (lean_obj_tag(v_x_5063_) == 5)
{
lean_object* v_fn_5066_; lean_object* v_arg_5067_; lean_object* v___x_5068_; lean_object* v___x_5069_; lean_object* v___x_5070_; 
v_fn_5066_ = lean_ctor_get(v_x_5063_, 0);
lean_inc_ref(v_fn_5066_);
v_arg_5067_ = lean_ctor_get(v_x_5063_, 1);
lean_inc_ref(v_arg_5067_);
lean_dec_ref_known(v_x_5063_, 2);
v___x_5068_ = lean_array_set(v_x_5064_, v_x_5065_, v_arg_5067_);
v___x_5069_ = lean_unsigned_to_nat(1u);
v___x_5070_ = lean_nat_sub(v_x_5065_, v___x_5069_);
lean_dec(v_x_5065_);
v_x_5063_ = v_fn_5066_;
v_x_5064_ = v___x_5068_;
v_x_5065_ = v___x_5070_;
goto _start;
}
else
{
uint8_t v___x_5072_; 
lean_dec(v_x_5065_);
v___x_5072_ = l_Lean_Expr_isConst(v_x_5063_);
if (v___x_5072_ == 0)
{
lean_dec_ref(v_x_5064_);
lean_dec_ref(v_x_5063_);
return v___x_5072_;
}
else
{
lean_object* v___x_5073_; lean_object* v___x_5074_; uint8_t v___x_5075_; 
v___x_5073_ = lean_unsigned_to_nat(0u);
v___x_5074_ = lean_array_get_size(v_fnNames_5061_);
v___x_5075_ = lean_nat_dec_lt(v___x_5073_, v___x_5074_);
if (v___x_5075_ == 0)
{
lean_dec_ref(v_x_5064_);
lean_dec_ref(v_x_5063_);
return v___x_5075_;
}
else
{
if (v___x_5075_ == 0)
{
lean_dec_ref(v_x_5064_);
lean_dec_ref(v_x_5063_);
return v___x_5075_;
}
else
{
size_t v___x_5076_; size_t v___x_5077_; uint8_t v___x_5078_; 
v___x_5076_ = ((size_t)0ULL);
v___x_5077_ = lean_usize_of_nat(v___x_5074_);
v___x_5078_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0(v_x_5063_, v_x_5064_, v_numSectionVars_5062_, v_fnNames_5061_, v___x_5076_, v___x_5077_);
lean_dec_ref(v_x_5064_);
lean_dec_ref(v_x_5063_);
return v___x_5078_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1_spec__1___boxed(lean_object* v_fnNames_5079_, lean_object* v_numSectionVars_5080_, lean_object* v_x_5081_, lean_object* v_x_5082_, lean_object* v_x_5083_){
_start:
{
uint8_t v_res_5084_; lean_object* v_r_5085_; 
v_res_5084_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1_spec__1(v_fnNames_5079_, v_numSectionVars_5080_, v_x_5081_, v_x_5082_, v_x_5083_);
lean_dec(v_numSectionVars_5080_);
lean_dec_ref(v_fnNames_5079_);
v_r_5085_ = lean_box(v_res_5084_);
return v_r_5085_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1(lean_object* v_numSectionVars_5086_, lean_object* v_fnNames_5087_, lean_object* v_x_5088_, lean_object* v_x_5089_, lean_object* v_x_5090_){
_start:
{
if (lean_obj_tag(v_x_5088_) == 5)
{
lean_object* v_fn_5091_; lean_object* v_arg_5092_; lean_object* v___x_5093_; lean_object* v___x_5094_; lean_object* v___x_5095_; uint8_t v___x_5096_; 
v_fn_5091_ = lean_ctor_get(v_x_5088_, 0);
lean_inc_ref(v_fn_5091_);
v_arg_5092_ = lean_ctor_get(v_x_5088_, 1);
lean_inc_ref(v_arg_5092_);
lean_dec_ref_known(v_x_5088_, 2);
v___x_5093_ = lean_array_set(v_x_5089_, v_x_5090_, v_arg_5092_);
v___x_5094_ = lean_unsigned_to_nat(1u);
v___x_5095_ = lean_nat_sub(v_x_5090_, v___x_5094_);
v___x_5096_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1_spec__1(v_fnNames_5087_, v_numSectionVars_5086_, v_fn_5091_, v___x_5093_, v___x_5095_);
return v___x_5096_;
}
else
{
uint8_t v___x_5097_; 
v___x_5097_ = l_Lean_Expr_isConst(v_x_5088_);
if (v___x_5097_ == 0)
{
lean_dec_ref(v_x_5089_);
lean_dec_ref(v_x_5088_);
return v___x_5097_;
}
else
{
lean_object* v___x_5098_; lean_object* v___x_5099_; uint8_t v___x_5100_; 
v___x_5098_ = lean_unsigned_to_nat(0u);
v___x_5099_ = lean_array_get_size(v_fnNames_5087_);
v___x_5100_ = lean_nat_dec_lt(v___x_5098_, v___x_5099_);
if (v___x_5100_ == 0)
{
lean_dec_ref(v_x_5089_);
lean_dec_ref(v_x_5088_);
return v___x_5100_;
}
else
{
if (v___x_5100_ == 0)
{
lean_dec_ref(v_x_5089_);
lean_dec_ref(v_x_5088_);
return v___x_5100_;
}
else
{
size_t v___x_5101_; size_t v___x_5102_; uint8_t v___x_5103_; 
v___x_5101_ = ((size_t)0ULL);
v___x_5102_ = lean_usize_of_nat(v___x_5099_);
v___x_5103_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0(v_x_5088_, v_x_5089_, v_numSectionVars_5086_, v_fnNames_5087_, v___x_5101_, v___x_5102_);
lean_dec_ref(v_x_5089_);
lean_dec_ref(v_x_5088_);
return v___x_5103_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1___boxed(lean_object* v_numSectionVars_5104_, lean_object* v_fnNames_5105_, lean_object* v_x_5106_, lean_object* v_x_5107_, lean_object* v_x_5108_){
_start:
{
uint8_t v_res_5109_; lean_object* v_r_5110_; 
v_res_5109_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1(v_numSectionVars_5104_, v_fnNames_5105_, v_x_5106_, v_x_5107_, v_x_5108_);
lean_dec(v_x_5108_);
lean_dec_ref(v_fnNames_5105_);
lean_dec(v_numSectionVars_5104_);
v_r_5110_ = lean_box(v_res_5109_);
return v_r_5110_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg(lean_object* v_fnNames_5111_, lean_object* v_numSectionVars_5112_, lean_object* v_a_5113_){
_start:
{
lean_object* v_dummy_5114_; lean_object* v_nargs_5115_; lean_object* v___x_5116_; lean_object* v___x_5117_; lean_object* v___x_5118_; uint8_t v___x_5119_; 
v_dummy_5114_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_5115_ = l_Lean_Expr_getAppNumArgs(v_a_5113_);
lean_inc(v_nargs_5115_);
v___x_5116_ = lean_mk_array(v_nargs_5115_, v_dummy_5114_);
v___x_5117_ = lean_unsigned_to_nat(1u);
v___x_5118_ = lean_nat_sub(v_nargs_5115_, v___x_5117_);
lean_dec(v_nargs_5115_);
v___x_5119_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1(v_numSectionVars_5112_, v_fnNames_5111_, v_a_5113_, v___x_5116_, v___x_5118_);
lean_dec(v___x_5118_);
return v___x_5119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg___boxed(lean_object* v_fnNames_5120_, lean_object* v_numSectionVars_5121_, lean_object* v_a_5122_){
_start:
{
uint8_t v_res_5123_; lean_object* v_r_5124_; 
v_res_5123_ = l___private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg(v_fnNames_5120_, v_numSectionVars_5121_, v_a_5122_);
lean_dec(v_numSectionVars_5121_);
lean_dec_ref(v_fnNames_5120_);
v_r_5124_ = lean_box(v_res_5123_);
return v_r_5124_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__0(lean_object* v_fnNames_5125_, lean_object* v_numSectionVars_5126_, lean_object* v_as_5127_, size_t v_i_5128_, size_t v_stop_5129_){
_start:
{
uint8_t v___x_5130_; 
v___x_5130_ = lean_usize_dec_eq(v_i_5128_, v_stop_5129_);
if (v___x_5130_ == 0)
{
lean_object* v___x_5131_; uint8_t v___x_5132_; 
v___x_5131_ = lean_array_uget_borrowed(v_as_5127_, v_i_5128_);
lean_inc(v___x_5131_);
v___x_5132_ = l___private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg(v_fnNames_5125_, v_numSectionVars_5126_, v___x_5131_);
if (v___x_5132_ == 0)
{
size_t v___x_5133_; size_t v___x_5134_; 
v___x_5133_ = ((size_t)1ULL);
v___x_5134_ = lean_usize_add(v_i_5128_, v___x_5133_);
v_i_5128_ = v___x_5134_;
goto _start;
}
else
{
return v___x_5132_;
}
}
else
{
uint8_t v___x_5136_; 
v___x_5136_ = 0;
return v___x_5136_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__0___boxed(lean_object* v_fnNames_5137_, lean_object* v_numSectionVars_5138_, lean_object* v_as_5139_, lean_object* v_i_5140_, lean_object* v_stop_5141_){
_start:
{
size_t v_i_boxed_5142_; size_t v_stop_boxed_5143_; uint8_t v_res_5144_; lean_object* v_r_5145_; 
v_i_boxed_5142_ = lean_unbox_usize(v_i_5140_);
lean_dec(v_i_5140_);
v_stop_boxed_5143_ = lean_unbox_usize(v_stop_5141_);
lean_dec(v_stop_5141_);
v_res_5144_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__0(v_fnNames_5137_, v_numSectionVars_5138_, v_as_5139_, v_i_boxed_5142_, v_stop_boxed_5143_);
lean_dec_ref(v_as_5139_);
lean_dec(v_numSectionVars_5138_);
lean_dec_ref(v_fnNames_5137_);
v_r_5145_ = lean_box(v_res_5144_);
return v_r_5145_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__1(lean_object* v_fnNames_5146_, lean_object* v_numSectionVars_5147_, lean_object* v___x_5148_, lean_object* v_x_5149_, lean_object* v_x_5150_, lean_object* v___y_5151_, lean_object* v___y_5152_){
_start:
{
if (lean_obj_tag(v_x_5149_) == 5)
{
lean_object* v_fn_5157_; lean_object* v_arg_5158_; lean_object* v___x_5159_; 
v_fn_5157_ = lean_ctor_get(v_x_5149_, 0);
lean_inc_ref(v_fn_5157_);
v_arg_5158_ = lean_ctor_get(v_x_5149_, 1);
lean_inc_ref(v_arg_5158_);
lean_dec_ref_known(v_x_5149_, 2);
v___x_5159_ = lean_array_push(v_x_5150_, v_arg_5158_);
v_x_5149_ = v_fn_5157_;
v_x_5150_ = v___x_5159_;
goto _start;
}
else
{
uint8_t v___x_5161_; 
v___x_5161_ = l_Lean_Expr_isConst(v_x_5149_);
if (v___x_5161_ == 0)
{
lean_dec_ref(v_x_5150_);
lean_dec_ref(v_x_5149_);
lean_dec_ref(v___x_5148_);
goto v___jp_5154_;
}
else
{
lean_object* v___x_5162_; lean_object* v___x_5163_; uint8_t v___x_5164_; 
v___x_5162_ = lean_unsigned_to_nat(0u);
v___x_5163_ = lean_array_get_size(v_x_5150_);
v___x_5164_ = lean_nat_dec_lt(v___x_5162_, v___x_5163_);
if (v___x_5164_ == 0)
{
lean_dec_ref(v_x_5150_);
lean_dec_ref(v_x_5149_);
lean_dec_ref(v___x_5148_);
goto v___jp_5154_;
}
else
{
if (v___x_5164_ == 0)
{
lean_dec_ref(v_x_5150_);
lean_dec_ref(v_x_5149_);
lean_dec_ref(v___x_5148_);
goto v___jp_5154_;
}
else
{
size_t v___x_5165_; size_t v___x_5166_; uint8_t v___x_5167_; 
v___x_5165_ = ((size_t)0ULL);
v___x_5166_ = lean_usize_of_nat(v___x_5163_);
v___x_5167_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__0(v_fnNames_5146_, v_numSectionVars_5147_, v_x_5150_, v___x_5165_, v___x_5166_);
if (v___x_5167_ == 0)
{
lean_dec_ref(v_x_5150_);
lean_dec_ref(v_x_5149_);
lean_dec_ref(v___x_5148_);
goto v___jp_5154_;
}
else
{
lean_object* v___x_5168_; uint8_t v___x_5169_; lean_object* v___x_5170_; 
v___x_5168_ = l_Lean_Expr_constName_x21(v_x_5149_);
v___x_5169_ = 0;
v___x_5170_ = l_Lean_Environment_find_x3f(v___x_5148_, v___x_5168_, v___x_5169_);
if (lean_obj_tag(v___x_5170_) == 1)
{
lean_object* v_val_5171_; 
v_val_5171_ = lean_ctor_get(v___x_5170_, 0);
lean_inc(v_val_5171_);
lean_dec_ref_known(v___x_5170_, 1);
if (lean_obj_tag(v_val_5171_) == 2)
{
lean_object* v___x_5172_; lean_object* v___x_5173_; lean_object* v___x_5175_; uint8_t v_isShared_5176_; uint8_t v_isSharedCheck_5197_; 
v___x_5172_ = l_Lean_Expr_constLevels_x21(v_x_5149_);
lean_dec_ref(v_x_5149_);
v___x_5173_ = l_Lean_Core_instantiateValueLevelParams(v_val_5171_, v___x_5172_, v___x_5164_, v___y_5151_, v___y_5152_);
v_isSharedCheck_5197_ = !lean_is_exclusive(v_val_5171_);
if (v_isSharedCheck_5197_ == 0)
{
lean_object* v_unused_5198_; 
v_unused_5198_ = lean_ctor_get(v_val_5171_, 0);
lean_dec(v_unused_5198_);
v___x_5175_ = v_val_5171_;
v_isShared_5176_ = v_isSharedCheck_5197_;
goto v_resetjp_5174_;
}
else
{
lean_dec(v_val_5171_);
v___x_5175_ = lean_box(0);
v_isShared_5176_ = v_isSharedCheck_5197_;
goto v_resetjp_5174_;
}
v_resetjp_5174_:
{
if (lean_obj_tag(v___x_5173_) == 0)
{
lean_object* v_a_5177_; lean_object* v___x_5179_; uint8_t v_isShared_5180_; uint8_t v_isSharedCheck_5188_; 
v_a_5177_ = lean_ctor_get(v___x_5173_, 0);
v_isSharedCheck_5188_ = !lean_is_exclusive(v___x_5173_);
if (v_isSharedCheck_5188_ == 0)
{
v___x_5179_ = v___x_5173_;
v_isShared_5180_ = v_isSharedCheck_5188_;
goto v_resetjp_5178_;
}
else
{
lean_inc(v_a_5177_);
lean_dec(v___x_5173_);
v___x_5179_ = lean_box(0);
v_isShared_5180_ = v_isSharedCheck_5188_;
goto v_resetjp_5178_;
}
v_resetjp_5178_:
{
lean_object* v___x_5181_; lean_object* v___x_5183_; 
v___x_5181_ = l_Lean_Expr_betaRev(v_a_5177_, v_x_5150_, v___x_5169_, v___x_5169_);
lean_dec_ref(v_x_5150_);
if (v_isShared_5176_ == 0)
{
lean_ctor_set_tag(v___x_5175_, 1);
lean_ctor_set(v___x_5175_, 0, v___x_5181_);
v___x_5183_ = v___x_5175_;
goto v_reusejp_5182_;
}
else
{
lean_object* v_reuseFailAlloc_5187_; 
v_reuseFailAlloc_5187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5187_, 0, v___x_5181_);
v___x_5183_ = v_reuseFailAlloc_5187_;
goto v_reusejp_5182_;
}
v_reusejp_5182_:
{
lean_object* v___x_5185_; 
if (v_isShared_5180_ == 0)
{
lean_ctor_set(v___x_5179_, 0, v___x_5183_);
v___x_5185_ = v___x_5179_;
goto v_reusejp_5184_;
}
else
{
lean_object* v_reuseFailAlloc_5186_; 
v_reuseFailAlloc_5186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5186_, 0, v___x_5183_);
v___x_5185_ = v_reuseFailAlloc_5186_;
goto v_reusejp_5184_;
}
v_reusejp_5184_:
{
return v___x_5185_;
}
}
}
}
else
{
lean_object* v_a_5189_; lean_object* v___x_5191_; uint8_t v_isShared_5192_; uint8_t v_isSharedCheck_5196_; 
lean_del_object(v___x_5175_);
lean_dec_ref(v_x_5150_);
v_a_5189_ = lean_ctor_get(v___x_5173_, 0);
v_isSharedCheck_5196_ = !lean_is_exclusive(v___x_5173_);
if (v_isSharedCheck_5196_ == 0)
{
v___x_5191_ = v___x_5173_;
v_isShared_5192_ = v_isSharedCheck_5196_;
goto v_resetjp_5190_;
}
else
{
lean_inc(v_a_5189_);
lean_dec(v___x_5173_);
v___x_5191_ = lean_box(0);
v_isShared_5192_ = v_isSharedCheck_5196_;
goto v_resetjp_5190_;
}
v_resetjp_5190_:
{
lean_object* v___x_5194_; 
if (v_isShared_5192_ == 0)
{
v___x_5194_ = v___x_5191_;
goto v_reusejp_5193_;
}
else
{
lean_object* v_reuseFailAlloc_5195_; 
v_reuseFailAlloc_5195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5195_, 0, v_a_5189_);
v___x_5194_ = v_reuseFailAlloc_5195_;
goto v_reusejp_5193_;
}
v_reusejp_5193_:
{
return v___x_5194_;
}
}
}
}
}
else
{
lean_dec(v_val_5171_);
lean_dec_ref(v_x_5150_);
lean_dec_ref(v_x_5149_);
goto v___jp_5154_;
}
}
else
{
lean_dec(v___x_5170_);
lean_dec_ref(v_x_5150_);
lean_dec_ref(v_x_5149_);
goto v___jp_5154_;
}
}
}
}
}
}
v___jp_5154_:
{
lean_object* v___x_5155_; lean_object* v___x_5156_; 
v___x_5155_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_5156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5156_, 0, v___x_5155_);
return v___x_5156_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__1___boxed(lean_object* v_fnNames_5199_, lean_object* v_numSectionVars_5200_, lean_object* v___x_5201_, lean_object* v_x_5202_, lean_object* v_x_5203_, lean_object* v___y_5204_, lean_object* v___y_5205_, lean_object* v___y_5206_){
_start:
{
lean_object* v_res_5207_; 
v_res_5207_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__1(v_fnNames_5199_, v_numSectionVars_5200_, v___x_5201_, v_x_5202_, v_x_5203_, v___y_5204_, v___y_5205_);
lean_dec(v___y_5205_);
lean_dec_ref(v___y_5204_);
lean_dec(v_numSectionVars_5200_);
lean_dec_ref(v_fnNames_5199_);
return v_res_5207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___lam__1(lean_object* v_fnNames_5208_, lean_object* v_numSectionVars_5209_, lean_object* v_env_5210_, lean_object* v_e_5211_, lean_object* v___y_5212_, lean_object* v___y_5213_){
_start:
{
lean_object* v___x_5215_; lean_object* v___x_5216_; lean_object* v___x_5217_; 
v___x_5215_ = l_Lean_Expr_getAppNumArgs(v_e_5211_);
v___x_5216_ = lean_mk_empty_array_with_capacity(v___x_5215_);
lean_dec(v___x_5215_);
v___x_5217_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__1(v_fnNames_5208_, v_numSectionVars_5209_, v_env_5210_, v_e_5211_, v___x_5216_, v___y_5212_, v___y_5213_);
return v___x_5217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___lam__1___boxed(lean_object* v_fnNames_5218_, lean_object* v_numSectionVars_5219_, lean_object* v_env_5220_, lean_object* v_e_5221_, lean_object* v___y_5222_, lean_object* v___y_5223_, lean_object* v___y_5224_){
_start:
{
lean_object* v_res_5225_; 
v_res_5225_ = l_Lean_Meta_unfoldIfArgIsAppOf___lam__1(v_fnNames_5218_, v_numSectionVars_5219_, v_env_5220_, v_e_5221_, v___y_5222_, v___y_5223_);
lean_dec(v___y_5223_);
lean_dec_ref(v___y_5222_);
lean_dec(v_numSectionVars_5219_);
lean_dec_ref(v_fnNames_5218_);
return v_res_5225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___lam__0(lean_object* v_fnNames_5226_, lean_object* v_numSectionVars_5227_, lean_object* v_e_5228_, lean_object* v___f_5229_, lean_object* v___y_5230_, lean_object* v___y_5231_){
_start:
{
lean_object* v___x_5233_; lean_object* v_env_5234_; lean_object* v___f_5235_; lean_object* v___x_5236_; 
v___x_5233_ = lean_st_ref_get(v___y_5231_);
v_env_5234_ = lean_ctor_get(v___x_5233_, 0);
lean_inc_ref(v_env_5234_);
lean_dec(v___x_5233_);
v___f_5235_ = lean_alloc_closure((void*)(l_Lean_Meta_unfoldIfArgIsAppOf___lam__1___boxed), 7, 3);
lean_closure_set(v___f_5235_, 0, v_fnNames_5226_);
lean_closure_set(v___f_5235_, 1, v_numSectionVars_5227_);
lean_closure_set(v___f_5235_, 2, v_env_5234_);
v___x_5236_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_5228_, v___f_5235_, v___f_5229_, v___y_5230_, v___y_5231_);
return v___x_5236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___lam__0___boxed(lean_object* v_fnNames_5237_, lean_object* v_numSectionVars_5238_, lean_object* v_e_5239_, lean_object* v___f_5240_, lean_object* v___y_5241_, lean_object* v___y_5242_, lean_object* v___y_5243_){
_start:
{
lean_object* v_res_5244_; 
v_res_5244_ = l_Lean_Meta_unfoldIfArgIsAppOf___lam__0(v_fnNames_5237_, v_numSectionVars_5238_, v_e_5239_, v___f_5240_, v___y_5241_, v___y_5242_);
lean_dec(v___y_5242_);
lean_dec_ref(v___y_5241_);
return v_res_5244_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0(lean_object* v___y_5245_, uint8_t v_isExporting_5246_, lean_object* v___x_5247_, lean_object* v_a_x3f_5248_){
_start:
{
lean_object* v___x_5250_; lean_object* v_env_5251_; lean_object* v_nextMacroScope_5252_; lean_object* v_ngen_5253_; lean_object* v_auxDeclNGen_5254_; lean_object* v_traceState_5255_; lean_object* v_recordedDeps_5256_; lean_object* v_messages_5257_; lean_object* v_infoState_5258_; lean_object* v_snapshotTasks_5259_; lean_object* v___x_5261_; uint8_t v_isShared_5262_; uint8_t v_isSharedCheck_5270_; 
v___x_5250_ = lean_st_ref_take(v___y_5245_);
v_env_5251_ = lean_ctor_get(v___x_5250_, 0);
v_nextMacroScope_5252_ = lean_ctor_get(v___x_5250_, 1);
v_ngen_5253_ = lean_ctor_get(v___x_5250_, 2);
v_auxDeclNGen_5254_ = lean_ctor_get(v___x_5250_, 3);
v_traceState_5255_ = lean_ctor_get(v___x_5250_, 4);
v_recordedDeps_5256_ = lean_ctor_get(v___x_5250_, 6);
v_messages_5257_ = lean_ctor_get(v___x_5250_, 7);
v_infoState_5258_ = lean_ctor_get(v___x_5250_, 8);
v_snapshotTasks_5259_ = lean_ctor_get(v___x_5250_, 9);
v_isSharedCheck_5270_ = !lean_is_exclusive(v___x_5250_);
if (v_isSharedCheck_5270_ == 0)
{
lean_object* v_unused_5271_; 
v_unused_5271_ = lean_ctor_get(v___x_5250_, 5);
lean_dec(v_unused_5271_);
v___x_5261_ = v___x_5250_;
v_isShared_5262_ = v_isSharedCheck_5270_;
goto v_resetjp_5260_;
}
else
{
lean_inc(v_snapshotTasks_5259_);
lean_inc(v_infoState_5258_);
lean_inc(v_messages_5257_);
lean_inc(v_recordedDeps_5256_);
lean_inc(v_traceState_5255_);
lean_inc(v_auxDeclNGen_5254_);
lean_inc(v_ngen_5253_);
lean_inc(v_nextMacroScope_5252_);
lean_inc(v_env_5251_);
lean_dec(v___x_5250_);
v___x_5261_ = lean_box(0);
v_isShared_5262_ = v_isSharedCheck_5270_;
goto v_resetjp_5260_;
}
v_resetjp_5260_:
{
lean_object* v___x_5263_; lean_object* v___x_5264_; lean_object* v___x_5266_; 
v___x_5263_ = lean_box(0);
v___x_5264_ = l_Lean_Environment_setExporting(v_env_5251_, v_isExporting_5246_);
if (v_isShared_5262_ == 0)
{
lean_ctor_set(v___x_5261_, 5, v___x_5247_);
lean_ctor_set(v___x_5261_, 0, v___x_5264_);
v___x_5266_ = v___x_5261_;
goto v_reusejp_5265_;
}
else
{
lean_object* v_reuseFailAlloc_5269_; 
v_reuseFailAlloc_5269_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5269_, 0, v___x_5264_);
lean_ctor_set(v_reuseFailAlloc_5269_, 1, v_nextMacroScope_5252_);
lean_ctor_set(v_reuseFailAlloc_5269_, 2, v_ngen_5253_);
lean_ctor_set(v_reuseFailAlloc_5269_, 3, v_auxDeclNGen_5254_);
lean_ctor_set(v_reuseFailAlloc_5269_, 4, v_traceState_5255_);
lean_ctor_set(v_reuseFailAlloc_5269_, 5, v___x_5247_);
lean_ctor_set(v_reuseFailAlloc_5269_, 6, v_recordedDeps_5256_);
lean_ctor_set(v_reuseFailAlloc_5269_, 7, v_messages_5257_);
lean_ctor_set(v_reuseFailAlloc_5269_, 8, v_infoState_5258_);
lean_ctor_set(v_reuseFailAlloc_5269_, 9, v_snapshotTasks_5259_);
v___x_5266_ = v_reuseFailAlloc_5269_;
goto v_reusejp_5265_;
}
v_reusejp_5265_:
{
lean_object* v___x_5267_; lean_object* v___x_5268_; 
v___x_5267_ = lean_st_ref_put(v___y_5245_, v___x_5266_);
v___x_5268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5268_, 0, v___x_5263_);
return v___x_5268_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0___boxed(lean_object* v___y_5272_, lean_object* v_isExporting_5273_, lean_object* v___x_5274_, lean_object* v_a_x3f_5275_, lean_object* v___y_5276_){
_start:
{
uint8_t v_isExporting_boxed_5277_; lean_object* v_res_5278_; 
v_isExporting_boxed_5277_ = lean_unbox(v_isExporting_5273_);
v_res_5278_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0(v___y_5272_, v_isExporting_boxed_5277_, v___x_5274_, v_a_x3f_5275_);
lean_dec(v_a_x3f_5275_);
lean_dec(v___y_5272_);
return v_res_5278_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg(lean_object* v_x_5279_, uint8_t v_isExporting_5280_, lean_object* v___y_5281_, lean_object* v___y_5282_){
_start:
{
lean_object* v___x_5284_; lean_object* v_env_5285_; lean_object* v___x_5286_; uint8_t v_isModule_5287_; 
v___x_5284_ = lean_st_ref_get(v___y_5282_);
v_env_5285_ = lean_ctor_get(v___x_5284_, 0);
lean_inc_ref(v_env_5285_);
lean_dec(v___x_5284_);
v___x_5286_ = l_Lean_Environment_header(v_env_5285_);
v_isModule_5287_ = lean_ctor_get_uint8(v___x_5286_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_5286_);
if (v_isModule_5287_ == 0)
{
lean_object* v___x_5288_; 
lean_dec_ref(v_env_5285_);
lean_inc(v___y_5282_);
lean_inc_ref(v___y_5281_);
v___x_5288_ = lean_apply_3(v_x_5279_, v___y_5281_, v___y_5282_, lean_box(0));
return v___x_5288_;
}
else
{
uint8_t v_isExporting_5289_; 
v_isExporting_5289_ = lean_ctor_get_uint8(v_env_5285_, sizeof(void*)*13);
lean_dec_ref(v_env_5285_);
if (v_isExporting_5280_ == 0)
{
if (v_isExporting_5289_ == 0)
{
lean_object* v___x_5341_; 
lean_inc(v___y_5282_);
lean_inc_ref(v___y_5281_);
v___x_5341_ = lean_apply_3(v_x_5279_, v___y_5281_, v___y_5282_, lean_box(0));
return v___x_5341_;
}
else
{
goto v___jp_5290_;
}
}
else
{
if (v_isExporting_5289_ == 0)
{
goto v___jp_5290_;
}
else
{
lean_object* v___x_5342_; 
lean_inc(v___y_5282_);
lean_inc_ref(v___y_5281_);
v___x_5342_ = lean_apply_3(v_x_5279_, v___y_5281_, v___y_5282_, lean_box(0));
return v___x_5342_;
}
}
v___jp_5290_:
{
lean_object* v___x_5291_; lean_object* v_env_5292_; lean_object* v_nextMacroScope_5293_; lean_object* v_ngen_5294_; lean_object* v_auxDeclNGen_5295_; lean_object* v_traceState_5296_; lean_object* v_recordedDeps_5297_; lean_object* v_messages_5298_; lean_object* v_infoState_5299_; lean_object* v_snapshotTasks_5300_; lean_object* v___x_5302_; uint8_t v_isShared_5303_; uint8_t v_isSharedCheck_5339_; 
v___x_5291_ = lean_st_ref_take(v___y_5282_);
v_env_5292_ = lean_ctor_get(v___x_5291_, 0);
v_nextMacroScope_5293_ = lean_ctor_get(v___x_5291_, 1);
v_ngen_5294_ = lean_ctor_get(v___x_5291_, 2);
v_auxDeclNGen_5295_ = lean_ctor_get(v___x_5291_, 3);
v_traceState_5296_ = lean_ctor_get(v___x_5291_, 4);
v_recordedDeps_5297_ = lean_ctor_get(v___x_5291_, 6);
v_messages_5298_ = lean_ctor_get(v___x_5291_, 7);
v_infoState_5299_ = lean_ctor_get(v___x_5291_, 8);
v_snapshotTasks_5300_ = lean_ctor_get(v___x_5291_, 9);
v_isSharedCheck_5339_ = !lean_is_exclusive(v___x_5291_);
if (v_isSharedCheck_5339_ == 0)
{
lean_object* v_unused_5340_; 
v_unused_5340_ = lean_ctor_get(v___x_5291_, 5);
lean_dec(v_unused_5340_);
v___x_5302_ = v___x_5291_;
v_isShared_5303_ = v_isSharedCheck_5339_;
goto v_resetjp_5301_;
}
else
{
lean_inc(v_snapshotTasks_5300_);
lean_inc(v_infoState_5299_);
lean_inc(v_messages_5298_);
lean_inc(v_recordedDeps_5297_);
lean_inc(v_traceState_5296_);
lean_inc(v_auxDeclNGen_5295_);
lean_inc(v_ngen_5294_);
lean_inc(v_nextMacroScope_5293_);
lean_inc(v_env_5292_);
lean_dec(v___x_5291_);
v___x_5302_ = lean_box(0);
v_isShared_5303_ = v_isSharedCheck_5339_;
goto v_resetjp_5301_;
}
v_resetjp_5301_:
{
lean_object* v___x_5304_; lean_object* v___x_5305_; lean_object* v___x_5307_; 
v___x_5304_ = l_Lean_Environment_setExporting(v_env_5292_, v_isExporting_5280_);
v___x_5305_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2, &l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2);
if (v_isShared_5303_ == 0)
{
lean_ctor_set(v___x_5302_, 5, v___x_5305_);
lean_ctor_set(v___x_5302_, 0, v___x_5304_);
v___x_5307_ = v___x_5302_;
goto v_reusejp_5306_;
}
else
{
lean_object* v_reuseFailAlloc_5338_; 
v_reuseFailAlloc_5338_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5338_, 0, v___x_5304_);
lean_ctor_set(v_reuseFailAlloc_5338_, 1, v_nextMacroScope_5293_);
lean_ctor_set(v_reuseFailAlloc_5338_, 2, v_ngen_5294_);
lean_ctor_set(v_reuseFailAlloc_5338_, 3, v_auxDeclNGen_5295_);
lean_ctor_set(v_reuseFailAlloc_5338_, 4, v_traceState_5296_);
lean_ctor_set(v_reuseFailAlloc_5338_, 5, v___x_5305_);
lean_ctor_set(v_reuseFailAlloc_5338_, 6, v_recordedDeps_5297_);
lean_ctor_set(v_reuseFailAlloc_5338_, 7, v_messages_5298_);
lean_ctor_set(v_reuseFailAlloc_5338_, 8, v_infoState_5299_);
lean_ctor_set(v_reuseFailAlloc_5338_, 9, v_snapshotTasks_5300_);
v___x_5307_ = v_reuseFailAlloc_5338_;
goto v_reusejp_5306_;
}
v_reusejp_5306_:
{
lean_object* v___x_5308_; lean_object* v_r_5309_; 
v___x_5308_ = lean_st_ref_put(v___y_5282_, v___x_5307_);
lean_inc(v___y_5282_);
lean_inc_ref(v___y_5281_);
v_r_5309_ = lean_apply_3(v_x_5279_, v___y_5281_, v___y_5282_, lean_box(0));
if (lean_obj_tag(v_r_5309_) == 0)
{
lean_object* v_a_5310_; lean_object* v___x_5312_; uint8_t v_isShared_5313_; uint8_t v_isSharedCheck_5326_; 
v_a_5310_ = lean_ctor_get(v_r_5309_, 0);
v_isSharedCheck_5326_ = !lean_is_exclusive(v_r_5309_);
if (v_isSharedCheck_5326_ == 0)
{
v___x_5312_ = v_r_5309_;
v_isShared_5313_ = v_isSharedCheck_5326_;
goto v_resetjp_5311_;
}
else
{
lean_inc(v_a_5310_);
lean_dec(v_r_5309_);
v___x_5312_ = lean_box(0);
v_isShared_5313_ = v_isSharedCheck_5326_;
goto v_resetjp_5311_;
}
v_resetjp_5311_:
{
lean_object* v___x_5315_; 
lean_inc(v_a_5310_);
if (v_isShared_5313_ == 0)
{
lean_ctor_set_tag(v___x_5312_, 1);
v___x_5315_ = v___x_5312_;
goto v_reusejp_5314_;
}
else
{
lean_object* v_reuseFailAlloc_5325_; 
v_reuseFailAlloc_5325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5325_, 0, v_a_5310_);
v___x_5315_ = v_reuseFailAlloc_5325_;
goto v_reusejp_5314_;
}
v_reusejp_5314_:
{
lean_object* v___x_5316_; lean_object* v___x_5318_; uint8_t v_isShared_5319_; uint8_t v_isSharedCheck_5323_; 
v___x_5316_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0(v___y_5282_, v_isExporting_5289_, v___x_5305_, v___x_5315_);
lean_dec_ref(v___x_5315_);
v_isSharedCheck_5323_ = !lean_is_exclusive(v___x_5316_);
if (v_isSharedCheck_5323_ == 0)
{
lean_object* v_unused_5324_; 
v_unused_5324_ = lean_ctor_get(v___x_5316_, 0);
lean_dec(v_unused_5324_);
v___x_5318_ = v___x_5316_;
v_isShared_5319_ = v_isSharedCheck_5323_;
goto v_resetjp_5317_;
}
else
{
lean_dec(v___x_5316_);
v___x_5318_ = lean_box(0);
v_isShared_5319_ = v_isSharedCheck_5323_;
goto v_resetjp_5317_;
}
v_resetjp_5317_:
{
lean_object* v___x_5321_; 
if (v_isShared_5319_ == 0)
{
lean_ctor_set(v___x_5318_, 0, v_a_5310_);
v___x_5321_ = v___x_5318_;
goto v_reusejp_5320_;
}
else
{
lean_object* v_reuseFailAlloc_5322_; 
v_reuseFailAlloc_5322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5322_, 0, v_a_5310_);
v___x_5321_ = v_reuseFailAlloc_5322_;
goto v_reusejp_5320_;
}
v_reusejp_5320_:
{
return v___x_5321_;
}
}
}
}
}
else
{
lean_object* v_a_5327_; lean_object* v___x_5328_; lean_object* v___x_5329_; lean_object* v___x_5331_; uint8_t v_isShared_5332_; uint8_t v_isSharedCheck_5336_; 
v_a_5327_ = lean_ctor_get(v_r_5309_, 0);
lean_inc(v_a_5327_);
lean_dec_ref_known(v_r_5309_, 1);
v___x_5328_ = lean_box(0);
v___x_5329_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0(v___y_5282_, v_isExporting_5289_, v___x_5305_, v___x_5328_);
v_isSharedCheck_5336_ = !lean_is_exclusive(v___x_5329_);
if (v_isSharedCheck_5336_ == 0)
{
lean_object* v_unused_5337_; 
v_unused_5337_ = lean_ctor_get(v___x_5329_, 0);
lean_dec(v_unused_5337_);
v___x_5331_ = v___x_5329_;
v_isShared_5332_ = v_isSharedCheck_5336_;
goto v_resetjp_5330_;
}
else
{
lean_dec(v___x_5329_);
v___x_5331_ = lean_box(0);
v_isShared_5332_ = v_isSharedCheck_5336_;
goto v_resetjp_5330_;
}
v_resetjp_5330_:
{
lean_object* v___x_5334_; 
if (v_isShared_5332_ == 0)
{
lean_ctor_set_tag(v___x_5331_, 1);
lean_ctor_set(v___x_5331_, 0, v_a_5327_);
v___x_5334_ = v___x_5331_;
goto v_reusejp_5333_;
}
else
{
lean_object* v_reuseFailAlloc_5335_; 
v_reuseFailAlloc_5335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5335_, 0, v_a_5327_);
v___x_5334_ = v_reuseFailAlloc_5335_;
goto v_reusejp_5333_;
}
v_reusejp_5333_:
{
return v___x_5334_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___boxed(lean_object* v_x_5343_, lean_object* v_isExporting_5344_, lean_object* v___y_5345_, lean_object* v___y_5346_, lean_object* v___y_5347_){
_start:
{
uint8_t v_isExporting_boxed_5348_; lean_object* v_res_5349_; 
v_isExporting_boxed_5348_ = lean_unbox(v_isExporting_5344_);
v_res_5349_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg(v_x_5343_, v_isExporting_boxed_5348_, v___y_5345_, v___y_5346_);
lean_dec(v___y_5346_);
lean_dec_ref(v___y_5345_);
return v_res_5349_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg(lean_object* v_x_5350_, uint8_t v_when_5351_, lean_object* v___y_5352_, lean_object* v___y_5353_){
_start:
{
if (v_when_5351_ == 0)
{
lean_object* v___x_5355_; 
lean_inc(v___y_5353_);
lean_inc_ref(v___y_5352_);
v___x_5355_ = lean_apply_3(v_x_5350_, v___y_5352_, v___y_5353_, lean_box(0));
return v___x_5355_;
}
else
{
uint8_t v___x_5356_; lean_object* v___x_5357_; 
v___x_5356_ = 0;
v___x_5357_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg(v_x_5350_, v___x_5356_, v___y_5352_, v___y_5353_);
return v___x_5357_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg___boxed(lean_object* v_x_5358_, lean_object* v_when_5359_, lean_object* v___y_5360_, lean_object* v___y_5361_, lean_object* v___y_5362_){
_start:
{
uint8_t v_when_boxed_5363_; lean_object* v_res_5364_; 
v_when_boxed_5363_ = lean_unbox(v_when_5359_);
v_res_5364_ = l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg(v_x_5358_, v_when_boxed_5363_, v___y_5360_, v___y_5361_);
lean_dec(v___y_5361_);
lean_dec_ref(v___y_5360_);
return v_res_5364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf(lean_object* v_fnNames_5365_, lean_object* v_numSectionVars_5366_, lean_object* v_e_5367_, lean_object* v_a_5368_, lean_object* v_a_5369_){
_start:
{
lean_object* v___f_5371_; lean_object* v___f_5372_; uint8_t v___x_5373_; lean_object* v___x_5374_; 
v___f_5371_ = ((lean_object*)(l_Lean_Core_betaReduce___closed__1));
v___f_5372_ = lean_alloc_closure((void*)(l_Lean_Meta_unfoldIfArgIsAppOf___lam__0___boxed), 7, 4);
lean_closure_set(v___f_5372_, 0, v_fnNames_5365_);
lean_closure_set(v___f_5372_, 1, v_numSectionVars_5366_);
lean_closure_set(v___f_5372_, 2, v_e_5367_);
lean_closure_set(v___f_5372_, 3, v___f_5371_);
v___x_5373_ = 1;
v___x_5374_ = l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg(v___f_5372_, v___x_5373_, v_a_5368_, v_a_5369_);
return v___x_5374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___boxed(lean_object* v_fnNames_5375_, lean_object* v_numSectionVars_5376_, lean_object* v_e_5377_, lean_object* v_a_5378_, lean_object* v_a_5379_, lean_object* v_a_5380_){
_start:
{
lean_object* v_res_5381_; 
v_res_5381_ = l_Lean_Meta_unfoldIfArgIsAppOf(v_fnNames_5375_, v_numSectionVars_5376_, v_e_5377_, v_a_5378_, v_a_5379_);
lean_dec(v_a_5379_);
lean_dec_ref(v_a_5378_);
return v_res_5381_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2(lean_object* v_00_u03b1_5382_, lean_object* v_x_5383_, uint8_t v_isExporting_5384_, lean_object* v___y_5385_, lean_object* v___y_5386_){
_start:
{
lean_object* v___x_5388_; 
v___x_5388_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg(v_x_5383_, v_isExporting_5384_, v___y_5385_, v___y_5386_);
return v___x_5388_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___boxed(lean_object* v_00_u03b1_5389_, lean_object* v_x_5390_, lean_object* v_isExporting_5391_, lean_object* v___y_5392_, lean_object* v___y_5393_, lean_object* v___y_5394_){
_start:
{
uint8_t v_isExporting_boxed_5395_; lean_object* v_res_5396_; 
v_isExporting_boxed_5395_ = lean_unbox(v_isExporting_5391_);
v_res_5396_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2(v_00_u03b1_5389_, v_x_5390_, v_isExporting_boxed_5395_, v___y_5392_, v___y_5393_);
lean_dec(v___y_5393_);
lean_dec_ref(v___y_5392_);
return v_res_5396_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2(lean_object* v_00_u03b1_5397_, lean_object* v_x_5398_, uint8_t v_when_5399_, lean_object* v___y_5400_, lean_object* v___y_5401_){
_start:
{
lean_object* v___x_5403_; 
v___x_5403_ = l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg(v_x_5398_, v_when_5399_, v___y_5400_, v___y_5401_);
return v___x_5403_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___boxed(lean_object* v_00_u03b1_5404_, lean_object* v_x_5405_, lean_object* v_when_5406_, lean_object* v___y_5407_, lean_object* v___y_5408_, lean_object* v___y_5409_){
_start:
{
uint8_t v_when_boxed_5410_; lean_object* v_res_5411_; 
v_when_boxed_5410_ = lean_unbox(v_when_5406_);
v_res_5411_ = l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2(v_00_u03b1_5404_, v_x_5405_, v_when_boxed_5410_, v___y_5407_, v___y_5408_);
lean_dec(v___y_5408_);
lean_dec_ref(v___y_5407_);
return v_res_5411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___lam__0(lean_object* v_x_5412_, lean_object* v___y_5413_, lean_object* v___y_5414_){
_start:
{
lean_object* v___x_5416_; lean_object* v___x_5417_; 
v___x_5416_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_5417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5417_, 0, v___x_5416_);
return v___x_5417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___lam__0___boxed(lean_object* v_x_5418_, lean_object* v___y_5419_, lean_object* v___y_5420_, lean_object* v___y_5421_){
_start:
{
lean_object* v_res_5422_; 
v_res_5422_ = l_Lean_Meta_eraseInaccessibleAnnotations___lam__0(v_x_5418_, v___y_5419_, v___y_5420_);
lean_dec(v___y_5420_);
lean_dec_ref(v___y_5419_);
lean_dec_ref(v_x_5418_);
return v_res_5422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___lam__1(lean_object* v_e_5423_, lean_object* v___y_5424_, lean_object* v___y_5425_){
_start:
{
lean_object* v___y_5428_; lean_object* v___x_5431_; 
v___x_5431_ = l_Lean_inaccessible_x3f(v_e_5423_);
if (lean_obj_tag(v___x_5431_) == 1)
{
lean_object* v_val_5432_; 
lean_dec_ref(v_e_5423_);
v_val_5432_ = lean_ctor_get(v___x_5431_, 0);
lean_inc(v_val_5432_);
lean_dec_ref_known(v___x_5431_, 1);
v___y_5428_ = v_val_5432_;
goto v___jp_5427_;
}
else
{
lean_dec(v___x_5431_);
v___y_5428_ = v_e_5423_;
goto v___jp_5427_;
}
v___jp_5427_:
{
lean_object* v___x_5429_; lean_object* v___x_5430_; 
v___x_5429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5429_, 0, v___y_5428_);
v___x_5430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5430_, 0, v___x_5429_);
return v___x_5430_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___lam__1___boxed(lean_object* v_e_5433_, lean_object* v___y_5434_, lean_object* v___y_5435_, lean_object* v___y_5436_){
_start:
{
lean_object* v_res_5437_; 
v_res_5437_ = l_Lean_Meta_eraseInaccessibleAnnotations___lam__1(v_e_5433_, v___y_5434_, v___y_5435_);
lean_dec(v___y_5435_);
lean_dec_ref(v___y_5434_);
return v_res_5437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations(lean_object* v_e_5440_, lean_object* v_a_5441_, lean_object* v_a_5442_){
_start:
{
lean_object* v___f_5444_; lean_object* v___f_5445_; lean_object* v___x_5446_; 
v___f_5444_ = ((lean_object*)(l_Lean_Meta_eraseInaccessibleAnnotations___closed__0));
v___f_5445_ = ((lean_object*)(l_Lean_Meta_eraseInaccessibleAnnotations___closed__1));
v___x_5446_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_5440_, v___f_5444_, v___f_5445_, v_a_5441_, v_a_5442_);
return v___x_5446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___boxed(lean_object* v_e_5447_, lean_object* v_a_5448_, lean_object* v_a_5449_, lean_object* v_a_5450_){
_start:
{
lean_object* v_res_5451_; 
v_res_5451_ = l_Lean_Meta_eraseInaccessibleAnnotations(v_e_5447_, v_a_5448_, v_a_5449_);
lean_dec(v_a_5449_);
lean_dec_ref(v_a_5448_);
return v_res_5451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_erasePatternRefAnnotations___lam__1(lean_object* v_e_5452_, lean_object* v___y_5453_, lean_object* v___y_5454_){
_start:
{
lean_object* v___y_5457_; lean_object* v___x_5460_; 
v___x_5460_ = l_Lean_patternWithRef_x3f(v_e_5452_);
if (lean_obj_tag(v___x_5460_) == 1)
{
lean_object* v_val_5461_; lean_object* v_snd_5462_; 
lean_dec_ref(v_e_5452_);
v_val_5461_ = lean_ctor_get(v___x_5460_, 0);
lean_inc(v_val_5461_);
lean_dec_ref_known(v___x_5460_, 1);
v_snd_5462_ = lean_ctor_get(v_val_5461_, 1);
lean_inc(v_snd_5462_);
lean_dec(v_val_5461_);
v___y_5457_ = v_snd_5462_;
goto v___jp_5456_;
}
else
{
lean_dec(v___x_5460_);
v___y_5457_ = v_e_5452_;
goto v___jp_5456_;
}
v___jp_5456_:
{
lean_object* v___x_5458_; lean_object* v___x_5459_; 
v___x_5458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5458_, 0, v___y_5457_);
v___x_5459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5459_, 0, v___x_5458_);
return v___x_5459_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_erasePatternRefAnnotations___lam__1___boxed(lean_object* v_e_5463_, lean_object* v___y_5464_, lean_object* v___y_5465_, lean_object* v___y_5466_){
_start:
{
lean_object* v_res_5467_; 
v_res_5467_ = l_Lean_Meta_erasePatternRefAnnotations___lam__1(v_e_5463_, v___y_5464_, v___y_5465_);
lean_dec(v___y_5465_);
lean_dec_ref(v___y_5464_);
return v_res_5467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_erasePatternRefAnnotations(lean_object* v_e_5469_, lean_object* v_a_5470_, lean_object* v_a_5471_){
_start:
{
lean_object* v___f_5473_; lean_object* v___f_5474_; lean_object* v___x_5475_; 
v___f_5473_ = ((lean_object*)(l_Lean_Meta_eraseInaccessibleAnnotations___closed__0));
v___f_5474_ = ((lean_object*)(l_Lean_Meta_erasePatternRefAnnotations___closed__0));
v___x_5475_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_5469_, v___f_5473_, v___f_5474_, v_a_5470_, v_a_5471_);
return v___x_5475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_erasePatternRefAnnotations___boxed(lean_object* v_e_5476_, lean_object* v_a_5477_, lean_object* v_a_5478_, lean_object* v_a_5479_){
_start:
{
lean_object* v_res_5480_; 
v_res_5480_ = l_Lean_Meta_erasePatternRefAnnotations(v_e_5476_, v_a_5477_, v_a_5478_);
lean_dec(v_a_5478_);
lean_dec_ref(v_a_5477_);
return v_res_5480_;
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
