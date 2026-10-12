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
lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__8(lean_object* v_binderType_343_, lean_object* v_a_344_, lean_object* v_binderName_345_, uint8_t v_binderInfo_346_, lean_object* v_inst_347_, lean_object* v_inst_348_, lean_object* v_inst_349_, lean_object* v_pre_350_, lean_object* v_post_351_, lean_object* v_x_352_, lean_object* v_x_353_, lean_object* v___y_354_, lean_object* v_body_355_, lean_object* v___y_356_, lean_object* v_a_357_){
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
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_binderType_343_ = stack[0].m_obj;
lean_object* v_a_344_ = stack[1].m_obj;
lean_object* v_binderName_345_ = stack[2].m_obj;
uint8_t v_binderInfo_346_ = stack[3].m_num;
lean_object* v_inst_347_ = stack[4].m_obj;
lean_object* v_inst_348_ = stack[5].m_obj;
lean_object* v_inst_349_ = stack[6].m_obj;
lean_object* v_pre_350_ = stack[7].m_obj;
lean_object* v_post_351_ = stack[8].m_obj;
lean_object* v_x_352_ = stack[9].m_obj;
lean_object* v_x_353_ = stack[10].m_obj;
lean_object* v___y_354_ = stack[11].m_obj;
lean_object* v_body_355_ = stack[12].m_obj;
lean_object* v___y_356_ = stack[13].m_obj;
lean_object* v_a_357_ = stack[14].m_obj;
lean_object* v_res_372_;
v_res_372_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__8(v_binderType_343_, v_a_344_, v_binderName_345_, v_binderInfo_346_, v_inst_347_, v_inst_348_, v_inst_349_, v_pre_350_, v_post_351_, v_x_352_, v_x_353_, v___y_354_, v_body_355_, v___y_356_, v_a_357_);
stack->m_obj
 = v_res_372_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__8___boxed(lean_object* v_binderType_373_, lean_object* v_a_374_, lean_object* v_binderName_375_, lean_object* v_binderInfo_376_, lean_object* v_inst_377_, lean_object* v_inst_378_, lean_object* v_inst_379_, lean_object* v_pre_380_, lean_object* v_post_381_, lean_object* v_x_382_, lean_object* v_x_383_, lean_object* v___y_384_, lean_object* v_body_385_, lean_object* v___y_386_, lean_object* v_a_387_){
_start:
{
uint8_t v_binderInfo_2909__boxed_388_; lean_object* v_res_389_; 
v_binderInfo_2909__boxed_388_ = lean_unbox(v_binderInfo_376_);
v_res_389_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__8(v_binderType_373_, v_a_374_, v_binderName_375_, v_binderInfo_2909__boxed_388_, v_inst_377_, v_inst_378_, v_inst_379_, v_pre_380_, v_post_381_, v_x_382_, v_x_383_, v___y_384_, v_body_385_, v___y_386_, v_a_387_);
lean_dec_ref(v_body_385_);
lean_dec(v___y_384_);
lean_dec_ref(v_binderType_373_);
return v_res_389_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__9(lean_object* v_binderType_390_, lean_object* v_binderName_391_, uint8_t v_binderInfo_392_, lean_object* v_inst_393_, lean_object* v_inst_394_, lean_object* v_inst_395_, lean_object* v_pre_396_, lean_object* v_post_397_, lean_object* v_x_398_, lean_object* v_x_399_, lean_object* v___y_400_, lean_object* v_body_401_, lean_object* v___y_402_, lean_object* v_toBind_403_, lean_object* v_a_404_){
_start:
{
lean_object* v___x_405_; lean_object* v___f_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_405_ = lean_box(v_binderInfo_392_);
lean_inc_ref(v_body_401_);
lean_inc(v___y_400_);
lean_inc(v_x_399_);
lean_inc(v_post_397_);
lean_inc(v_pre_396_);
lean_inc_ref(v_inst_395_);
lean_inc(v_inst_394_);
lean_inc_ref(v_inst_393_);
v___f_406_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__8___boxed), 15, 14);
lean_closure_set(v___f_406_, 0, v_binderType_390_);
lean_closure_set(v___f_406_, 1, v_a_404_);
lean_closure_set(v___f_406_, 2, v_binderName_391_);
lean_closure_set(v___f_406_, 3, v___x_405_);
lean_closure_set(v___f_406_, 4, v_inst_393_);
lean_closure_set(v___f_406_, 5, v_inst_394_);
lean_closure_set(v___f_406_, 6, v_inst_395_);
lean_closure_set(v___f_406_, 7, v_pre_396_);
lean_closure_set(v___f_406_, 8, v_post_397_);
lean_closure_set(v___f_406_, 9, v_x_398_);
lean_closure_set(v___f_406_, 10, v_x_399_);
lean_closure_set(v___f_406_, 11, v___y_400_);
lean_closure_set(v___f_406_, 12, v_body_401_);
lean_closure_set(v___f_406_, 13, v___y_402_);
v___x_407_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_393_, v_inst_394_, v_inst_395_, v_pre_396_, v_post_397_, v_x_398_, v_x_399_, v_body_401_, v___y_400_);
v___x_408_ = lean_apply_4(v_toBind_403_, lean_box(0), lean_box(0), v___x_407_, v___f_406_);
return v___x_408_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_binderType_390_ = stack[0].m_obj;
lean_object* v_binderName_391_ = stack[1].m_obj;
uint8_t v_binderInfo_392_ = stack[2].m_num;
lean_object* v_inst_393_ = stack[3].m_obj;
lean_object* v_inst_394_ = stack[4].m_obj;
lean_object* v_inst_395_ = stack[5].m_obj;
lean_object* v_pre_396_ = stack[6].m_obj;
lean_object* v_post_397_ = stack[7].m_obj;
lean_object* v_x_398_ = stack[8].m_obj;
lean_object* v_x_399_ = stack[9].m_obj;
lean_object* v___y_400_ = stack[10].m_obj;
lean_object* v_body_401_ = stack[11].m_obj;
lean_object* v___y_402_ = stack[12].m_obj;
lean_object* v_toBind_403_ = stack[13].m_obj;
lean_object* v_a_404_ = stack[14].m_obj;
lean_object* v_res_409_;
v_res_409_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__9(v_binderType_390_, v_binderName_391_, v_binderInfo_392_, v_inst_393_, v_inst_394_, v_inst_395_, v_pre_396_, v_post_397_, v_x_398_, v_x_399_, v___y_400_, v_body_401_, v___y_402_, v_toBind_403_, v_a_404_);
stack->m_obj
 = v_res_409_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__9___boxed(lean_object* v_binderType_410_, lean_object* v_binderName_411_, lean_object* v_binderInfo_412_, lean_object* v_inst_413_, lean_object* v_inst_414_, lean_object* v_inst_415_, lean_object* v_pre_416_, lean_object* v_post_417_, lean_object* v_x_418_, lean_object* v_x_419_, lean_object* v___y_420_, lean_object* v_body_421_, lean_object* v___y_422_, lean_object* v_toBind_423_, lean_object* v_a_424_){
_start:
{
uint8_t v_binderInfo_2770__boxed_425_; lean_object* v_res_426_; 
v_binderInfo_2770__boxed_425_ = lean_unbox(v_binderInfo_412_);
v_res_426_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__9(v_binderType_410_, v_binderName_411_, v_binderInfo_2770__boxed_425_, v_inst_413_, v_inst_414_, v_inst_415_, v_pre_416_, v_post_417_, v_x_418_, v_x_419_, v___y_420_, v_body_421_, v___y_422_, v_toBind_423_, v_a_424_);
lean_dec(v___y_420_);
return v_res_426_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__10(lean_object* v_binderType_427_, lean_object* v_a_428_, lean_object* v_binderName_429_, uint8_t v_binderInfo_430_, lean_object* v_inst_431_, lean_object* v_inst_432_, lean_object* v_inst_433_, lean_object* v_pre_434_, lean_object* v_post_435_, lean_object* v_x_436_, lean_object* v_x_437_, lean_object* v___y_438_, lean_object* v_body_439_, lean_object* v___y_440_, lean_object* v_a_441_){
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
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_binderType_427_ = stack[0].m_obj;
lean_object* v_a_428_ = stack[1].m_obj;
lean_object* v_binderName_429_ = stack[2].m_obj;
uint8_t v_binderInfo_430_ = stack[3].m_num;
lean_object* v_inst_431_ = stack[4].m_obj;
lean_object* v_inst_432_ = stack[5].m_obj;
lean_object* v_inst_433_ = stack[6].m_obj;
lean_object* v_pre_434_ = stack[7].m_obj;
lean_object* v_post_435_ = stack[8].m_obj;
lean_object* v_x_436_ = stack[9].m_obj;
lean_object* v_x_437_ = stack[10].m_obj;
lean_object* v___y_438_ = stack[11].m_obj;
lean_object* v_body_439_ = stack[12].m_obj;
lean_object* v___y_440_ = stack[13].m_obj;
lean_object* v_a_441_ = stack[14].m_obj;
lean_object* v_res_456_;
v_res_456_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__10(v_binderType_427_, v_a_428_, v_binderName_429_, v_binderInfo_430_, v_inst_431_, v_inst_432_, v_inst_433_, v_pre_434_, v_post_435_, v_x_436_, v_x_437_, v___y_438_, v_body_439_, v___y_440_, v_a_441_);
stack->m_obj
 = v_res_456_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__10___boxed(lean_object* v_binderType_457_, lean_object* v_a_458_, lean_object* v_binderName_459_, lean_object* v_binderInfo_460_, lean_object* v_inst_461_, lean_object* v_inst_462_, lean_object* v_inst_463_, lean_object* v_pre_464_, lean_object* v_post_465_, lean_object* v_x_466_, lean_object* v_x_467_, lean_object* v___y_468_, lean_object* v_body_469_, lean_object* v___y_470_, lean_object* v_a_471_){
_start:
{
uint8_t v_binderInfo_2884__boxed_472_; lean_object* v_res_473_; 
v_binderInfo_2884__boxed_472_ = lean_unbox(v_binderInfo_460_);
v_res_473_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__10(v_binderType_457_, v_a_458_, v_binderName_459_, v_binderInfo_2884__boxed_472_, v_inst_461_, v_inst_462_, v_inst_463_, v_pre_464_, v_post_465_, v_x_466_, v_x_467_, v___y_468_, v_body_469_, v___y_470_, v_a_471_);
lean_dec_ref(v_body_469_);
lean_dec(v___y_468_);
lean_dec_ref(v_binderType_457_);
return v_res_473_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__11(lean_object* v_binderType_474_, lean_object* v_binderName_475_, uint8_t v_binderInfo_476_, lean_object* v_inst_477_, lean_object* v_inst_478_, lean_object* v_inst_479_, lean_object* v_pre_480_, lean_object* v_post_481_, lean_object* v_x_482_, lean_object* v_x_483_, lean_object* v___y_484_, lean_object* v_body_485_, lean_object* v___y_486_, lean_object* v_toBind_487_, lean_object* v_a_488_){
_start:
{
lean_object* v___x_489_; lean_object* v___f_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_489_ = lean_box(v_binderInfo_476_);
lean_inc_ref(v_body_485_);
lean_inc(v___y_484_);
lean_inc(v_x_483_);
lean_inc(v_post_481_);
lean_inc(v_pre_480_);
lean_inc_ref(v_inst_479_);
lean_inc(v_inst_478_);
lean_inc_ref(v_inst_477_);
v___f_490_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__10___boxed), 15, 14);
lean_closure_set(v___f_490_, 0, v_binderType_474_);
lean_closure_set(v___f_490_, 1, v_a_488_);
lean_closure_set(v___f_490_, 2, v_binderName_475_);
lean_closure_set(v___f_490_, 3, v___x_489_);
lean_closure_set(v___f_490_, 4, v_inst_477_);
lean_closure_set(v___f_490_, 5, v_inst_478_);
lean_closure_set(v___f_490_, 6, v_inst_479_);
lean_closure_set(v___f_490_, 7, v_pre_480_);
lean_closure_set(v___f_490_, 8, v_post_481_);
lean_closure_set(v___f_490_, 9, v_x_482_);
lean_closure_set(v___f_490_, 10, v_x_483_);
lean_closure_set(v___f_490_, 11, v___y_484_);
lean_closure_set(v___f_490_, 12, v_body_485_);
lean_closure_set(v___f_490_, 13, v___y_486_);
v___x_491_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_477_, v_inst_478_, v_inst_479_, v_pre_480_, v_post_481_, v_x_482_, v_x_483_, v_body_485_, v___y_484_);
v___x_492_ = lean_apply_4(v_toBind_487_, lean_box(0), lean_box(0), v___x_491_, v___f_490_);
return v___x_492_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_binderType_474_ = stack[0].m_obj;
lean_object* v_binderName_475_ = stack[1].m_obj;
uint8_t v_binderInfo_476_ = stack[2].m_num;
lean_object* v_inst_477_ = stack[3].m_obj;
lean_object* v_inst_478_ = stack[4].m_obj;
lean_object* v_inst_479_ = stack[5].m_obj;
lean_object* v_pre_480_ = stack[6].m_obj;
lean_object* v_post_481_ = stack[7].m_obj;
lean_object* v_x_482_ = stack[8].m_obj;
lean_object* v_x_483_ = stack[9].m_obj;
lean_object* v___y_484_ = stack[10].m_obj;
lean_object* v_body_485_ = stack[11].m_obj;
lean_object* v___y_486_ = stack[12].m_obj;
lean_object* v_toBind_487_ = stack[13].m_obj;
lean_object* v_a_488_ = stack[14].m_obj;
lean_object* v_res_493_;
v_res_493_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__11(v_binderType_474_, v_binderName_475_, v_binderInfo_476_, v_inst_477_, v_inst_478_, v_inst_479_, v_pre_480_, v_post_481_, v_x_482_, v_x_483_, v___y_484_, v_body_485_, v___y_486_, v_toBind_487_, v_a_488_);
stack->m_obj
 = v_res_493_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__11___boxed(lean_object* v_binderType_494_, lean_object* v_binderName_495_, lean_object* v_binderInfo_496_, lean_object* v_inst_497_, lean_object* v_inst_498_, lean_object* v_inst_499_, lean_object* v_pre_500_, lean_object* v_post_501_, lean_object* v_x_502_, lean_object* v_x_503_, lean_object* v___y_504_, lean_object* v_body_505_, lean_object* v___y_506_, lean_object* v_toBind_507_, lean_object* v_a_508_){
_start:
{
uint8_t v_binderInfo_2716__boxed_509_; lean_object* v_res_510_; 
v_binderInfo_2716__boxed_509_ = lean_unbox(v_binderInfo_496_);
v_res_510_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__11(v_binderType_494_, v_binderName_495_, v_binderInfo_2716__boxed_509_, v_inst_497_, v_inst_498_, v_inst_499_, v_pre_500_, v_post_501_, v_x_502_, v_x_503_, v___y_504_, v_body_505_, v___y_506_, v_toBind_507_, v_a_508_);
lean_dec(v___y_504_);
return v_res_510_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__12(lean_object* v_type_511_, lean_object* v_a_512_, lean_object* v_declName_513_, lean_object* v_a_514_, uint8_t v_nondep_515_, lean_object* v_inst_516_, lean_object* v_inst_517_, lean_object* v_inst_518_, lean_object* v_pre_519_, lean_object* v_post_520_, lean_object* v_x_521_, lean_object* v_x_522_, lean_object* v___y_523_, lean_object* v_value_524_, lean_object* v_body_525_, lean_object* v___y_526_, lean_object* v_a_527_){
_start:
{
size_t v___x_528_; size_t v___x_529_; uint8_t v___x_530_; 
v___x_528_ = lean_ptr_addr(v_type_511_);
v___x_529_ = lean_ptr_addr(v_a_512_);
v___x_530_ = lean_usize_dec_eq(v___x_528_, v___x_529_);
if (v___x_530_ == 0)
{
lean_object* v___x_531_; lean_object* v___x_532_; 
lean_dec_ref(v___y_526_);
v___x_531_ = l_Lean_Expr_letE___override(v_declName_513_, v_a_512_, v_a_514_, v_a_527_, v_nondep_515_);
v___x_532_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_516_, v_inst_517_, v_inst_518_, v_pre_519_, v_post_520_, v_x_521_, v_x_522_, v___x_531_, v___y_523_);
return v___x_532_;
}
else
{
size_t v___x_533_; size_t v___x_534_; uint8_t v___x_535_; 
v___x_533_ = lean_ptr_addr(v_value_524_);
v___x_534_ = lean_ptr_addr(v_a_514_);
v___x_535_ = lean_usize_dec_eq(v___x_533_, v___x_534_);
if (v___x_535_ == 0)
{
lean_object* v___x_536_; lean_object* v___x_537_; 
lean_dec_ref(v___y_526_);
v___x_536_ = l_Lean_Expr_letE___override(v_declName_513_, v_a_512_, v_a_514_, v_a_527_, v_nondep_515_);
v___x_537_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_516_, v_inst_517_, v_inst_518_, v_pre_519_, v_post_520_, v_x_521_, v_x_522_, v___x_536_, v___y_523_);
return v___x_537_;
}
else
{
size_t v___x_538_; size_t v___x_539_; uint8_t v___x_540_; 
v___x_538_ = lean_ptr_addr(v_body_525_);
v___x_539_ = lean_ptr_addr(v_a_527_);
v___x_540_ = lean_usize_dec_eq(v___x_538_, v___x_539_);
if (v___x_540_ == 0)
{
lean_object* v___x_541_; lean_object* v___x_542_; 
lean_dec_ref(v___y_526_);
v___x_541_ = l_Lean_Expr_letE___override(v_declName_513_, v_a_512_, v_a_514_, v_a_527_, v_nondep_515_);
v___x_542_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_516_, v_inst_517_, v_inst_518_, v_pre_519_, v_post_520_, v_x_521_, v_x_522_, v___x_541_, v___y_523_);
return v___x_542_;
}
else
{
lean_object* v___x_543_; 
lean_dec_ref(v_a_527_);
lean_dec_ref(v_a_514_);
lean_dec(v_declName_513_);
lean_dec_ref(v_a_512_);
v___x_543_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_516_, v_inst_517_, v_inst_518_, v_pre_519_, v_post_520_, v_x_521_, v_x_522_, v___y_526_, v___y_523_);
return v___x_543_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_511_ = stack[0].m_obj;
lean_object* v_a_512_ = stack[1].m_obj;
lean_object* v_declName_513_ = stack[2].m_obj;
lean_object* v_a_514_ = stack[3].m_obj;
uint8_t v_nondep_515_ = stack[4].m_num;
lean_object* v_inst_516_ = stack[5].m_obj;
lean_object* v_inst_517_ = stack[6].m_obj;
lean_object* v_inst_518_ = stack[7].m_obj;
lean_object* v_pre_519_ = stack[8].m_obj;
lean_object* v_post_520_ = stack[9].m_obj;
lean_object* v_x_521_ = stack[10].m_obj;
lean_object* v_x_522_ = stack[11].m_obj;
lean_object* v___y_523_ = stack[12].m_obj;
lean_object* v_value_524_ = stack[13].m_obj;
lean_object* v_body_525_ = stack[14].m_obj;
lean_object* v___y_526_ = stack[15].m_obj;
lean_object* v_a_527_ = stack[16].m_obj;
lean_object* v_res_544_;
v_res_544_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__12(v_type_511_, v_a_512_, v_declName_513_, v_a_514_, v_nondep_515_, v_inst_516_, v_inst_517_, v_inst_518_, v_pre_519_, v_post_520_, v_x_521_, v_x_522_, v___y_523_, v_value_524_, v_body_525_, v___y_526_, v_a_527_);
stack->m_obj
 = v_res_544_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__12___boxed(lean_object** _args){
lean_object* v_type_545_ = _args[0];
lean_object* v_a_546_ = _args[1];
lean_object* v_declName_547_ = _args[2];
lean_object* v_a_548_ = _args[3];
lean_object* v_nondep_549_ = _args[4];
lean_object* v_inst_550_ = _args[5];
lean_object* v_inst_551_ = _args[6];
lean_object* v_inst_552_ = _args[7];
lean_object* v_pre_553_ = _args[8];
lean_object* v_post_554_ = _args[9];
lean_object* v_x_555_ = _args[10];
lean_object* v_x_556_ = _args[11];
lean_object* v___y_557_ = _args[12];
lean_object* v_value_558_ = _args[13];
lean_object* v_body_559_ = _args[14];
lean_object* v___y_560_ = _args[15];
lean_object* v_a_561_ = _args[16];
_start:
{
uint8_t v_nondep_2934__boxed_562_; lean_object* v_res_563_; 
v_nondep_2934__boxed_562_ = lean_unbox(v_nondep_549_);
v_res_563_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__12(v_type_545_, v_a_546_, v_declName_547_, v_a_548_, v_nondep_2934__boxed_562_, v_inst_550_, v_inst_551_, v_inst_552_, v_pre_553_, v_post_554_, v_x_555_, v_x_556_, v___y_557_, v_value_558_, v_body_559_, v___y_560_, v_a_561_);
lean_dec_ref(v_body_559_);
lean_dec_ref(v_value_558_);
lean_dec(v___y_557_);
lean_dec_ref(v_type_545_);
return v_res_563_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__13(lean_object* v_type_564_, lean_object* v_a_565_, lean_object* v_declName_566_, uint8_t v_nondep_567_, lean_object* v_inst_568_, lean_object* v_inst_569_, lean_object* v_inst_570_, lean_object* v_pre_571_, lean_object* v_post_572_, lean_object* v_x_573_, lean_object* v_x_574_, lean_object* v___y_575_, lean_object* v_value_576_, lean_object* v_body_577_, lean_object* v___y_578_, lean_object* v_toBind_579_, lean_object* v_a_580_){
_start:
{
lean_object* v___x_581_; lean_object* v___f_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_581_ = lean_box(v_nondep_567_);
lean_inc_ref(v_body_577_);
lean_inc(v___y_575_);
lean_inc(v_x_574_);
lean_inc(v_post_572_);
lean_inc(v_pre_571_);
lean_inc_ref(v_inst_570_);
lean_inc(v_inst_569_);
lean_inc_ref(v_inst_568_);
v___f_582_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__12___boxed), 17, 16);
lean_closure_set(v___f_582_, 0, v_type_564_);
lean_closure_set(v___f_582_, 1, v_a_565_);
lean_closure_set(v___f_582_, 2, v_declName_566_);
lean_closure_set(v___f_582_, 3, v_a_580_);
lean_closure_set(v___f_582_, 4, v___x_581_);
lean_closure_set(v___f_582_, 5, v_inst_568_);
lean_closure_set(v___f_582_, 6, v_inst_569_);
lean_closure_set(v___f_582_, 7, v_inst_570_);
lean_closure_set(v___f_582_, 8, v_pre_571_);
lean_closure_set(v___f_582_, 9, v_post_572_);
lean_closure_set(v___f_582_, 10, v_x_573_);
lean_closure_set(v___f_582_, 11, v_x_574_);
lean_closure_set(v___f_582_, 12, v___y_575_);
lean_closure_set(v___f_582_, 13, v_value_576_);
lean_closure_set(v___f_582_, 14, v_body_577_);
lean_closure_set(v___f_582_, 15, v___y_578_);
v___x_583_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_568_, v_inst_569_, v_inst_570_, v_pre_571_, v_post_572_, v_x_573_, v_x_574_, v_body_577_, v___y_575_);
v___x_584_ = lean_apply_4(v_toBind_579_, lean_box(0), lean_box(0), v___x_583_, v___f_582_);
return v___x_584_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__13_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_564_ = stack[0].m_obj;
lean_object* v_a_565_ = stack[1].m_obj;
lean_object* v_declName_566_ = stack[2].m_obj;
uint8_t v_nondep_567_ = stack[3].m_num;
lean_object* v_inst_568_ = stack[4].m_obj;
lean_object* v_inst_569_ = stack[5].m_obj;
lean_object* v_inst_570_ = stack[6].m_obj;
lean_object* v_pre_571_ = stack[7].m_obj;
lean_object* v_post_572_ = stack[8].m_obj;
lean_object* v_x_573_ = stack[9].m_obj;
lean_object* v_x_574_ = stack[10].m_obj;
lean_object* v___y_575_ = stack[11].m_obj;
lean_object* v_value_576_ = stack[12].m_obj;
lean_object* v_body_577_ = stack[13].m_obj;
lean_object* v___y_578_ = stack[14].m_obj;
lean_object* v_toBind_579_ = stack[15].m_obj;
lean_object* v_a_580_ = stack[16].m_obj;
lean_object* v_res_585_;
v_res_585_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__13(v_type_564_, v_a_565_, v_declName_566_, v_nondep_567_, v_inst_568_, v_inst_569_, v_inst_570_, v_pre_571_, v_post_572_, v_x_573_, v_x_574_, v___y_575_, v_value_576_, v_body_577_, v___y_578_, v_toBind_579_, v_a_580_);
stack->m_obj
 = v_res_585_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__13___boxed(lean_object** _args){
lean_object* v_type_586_ = _args[0];
lean_object* v_a_587_ = _args[1];
lean_object* v_declName_588_ = _args[2];
lean_object* v_nondep_589_ = _args[3];
lean_object* v_inst_590_ = _args[4];
lean_object* v_inst_591_ = _args[5];
lean_object* v_inst_592_ = _args[6];
lean_object* v_pre_593_ = _args[7];
lean_object* v_post_594_ = _args[8];
lean_object* v_x_595_ = _args[9];
lean_object* v_x_596_ = _args[10];
lean_object* v___y_597_ = _args[11];
lean_object* v_value_598_ = _args[12];
lean_object* v_body_599_ = _args[13];
lean_object* v___y_600_ = _args[14];
lean_object* v_toBind_601_ = _args[15];
lean_object* v_a_602_ = _args[16];
_start:
{
uint8_t v_nondep_2730__boxed_603_; lean_object* v_res_604_; 
v_nondep_2730__boxed_603_ = lean_unbox(v_nondep_589_);
v_res_604_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__13(v_type_586_, v_a_587_, v_declName_588_, v_nondep_2730__boxed_603_, v_inst_590_, v_inst_591_, v_inst_592_, v_pre_593_, v_post_594_, v_x_595_, v_x_596_, v___y_597_, v_value_598_, v_body_599_, v___y_600_, v_toBind_601_, v_a_602_);
lean_dec(v___y_597_);
return v_res_604_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__14(lean_object* v_type_605_, lean_object* v_declName_606_, uint8_t v_nondep_607_, lean_object* v_inst_608_, lean_object* v_inst_609_, lean_object* v_inst_610_, lean_object* v_pre_611_, lean_object* v_post_612_, lean_object* v_x_613_, lean_object* v_x_614_, lean_object* v___y_615_, lean_object* v_value_616_, lean_object* v_body_617_, lean_object* v___y_618_, lean_object* v_toBind_619_, lean_object* v_a_620_){
_start:
{
lean_object* v___x_621_; lean_object* v___f_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_621_ = lean_box(v_nondep_607_);
lean_inc(v_toBind_619_);
lean_inc_ref(v_value_616_);
lean_inc(v___y_615_);
lean_inc(v_x_614_);
lean_inc(v_post_612_);
lean_inc(v_pre_611_);
lean_inc_ref(v_inst_610_);
lean_inc(v_inst_609_);
lean_inc_ref(v_inst_608_);
v___f_622_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__13___boxed), 17, 16);
lean_closure_set(v___f_622_, 0, v_type_605_);
lean_closure_set(v___f_622_, 1, v_a_620_);
lean_closure_set(v___f_622_, 2, v_declName_606_);
lean_closure_set(v___f_622_, 3, v___x_621_);
lean_closure_set(v___f_622_, 4, v_inst_608_);
lean_closure_set(v___f_622_, 5, v_inst_609_);
lean_closure_set(v___f_622_, 6, v_inst_610_);
lean_closure_set(v___f_622_, 7, v_pre_611_);
lean_closure_set(v___f_622_, 8, v_post_612_);
lean_closure_set(v___f_622_, 9, v_x_613_);
lean_closure_set(v___f_622_, 10, v_x_614_);
lean_closure_set(v___f_622_, 11, v___y_615_);
lean_closure_set(v___f_622_, 12, v_value_616_);
lean_closure_set(v___f_622_, 13, v_body_617_);
lean_closure_set(v___f_622_, 14, v___y_618_);
lean_closure_set(v___f_622_, 15, v_toBind_619_);
v___x_623_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_608_, v_inst_609_, v_inst_610_, v_pre_611_, v_post_612_, v_x_613_, v_x_614_, v_value_616_, v___y_615_);
v___x_624_ = lean_apply_4(v_toBind_619_, lean_box(0), lean_box(0), v___x_623_, v___f_622_);
return v___x_624_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__14_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_605_ = stack[0].m_obj;
lean_object* v_declName_606_ = stack[1].m_obj;
uint8_t v_nondep_607_ = stack[2].m_num;
lean_object* v_inst_608_ = stack[3].m_obj;
lean_object* v_inst_609_ = stack[4].m_obj;
lean_object* v_inst_610_ = stack[5].m_obj;
lean_object* v_pre_611_ = stack[6].m_obj;
lean_object* v_post_612_ = stack[7].m_obj;
lean_object* v_x_613_ = stack[8].m_obj;
lean_object* v_x_614_ = stack[9].m_obj;
lean_object* v___y_615_ = stack[10].m_obj;
lean_object* v_value_616_ = stack[11].m_obj;
lean_object* v_body_617_ = stack[12].m_obj;
lean_object* v___y_618_ = stack[13].m_obj;
lean_object* v_toBind_619_ = stack[14].m_obj;
lean_object* v_a_620_ = stack[15].m_obj;
lean_object* v_res_625_;
v_res_625_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__14(v_type_605_, v_declName_606_, v_nondep_607_, v_inst_608_, v_inst_609_, v_inst_610_, v_pre_611_, v_post_612_, v_x_613_, v_x_614_, v___y_615_, v_value_616_, v_body_617_, v___y_618_, v_toBind_619_, v_a_620_);
stack->m_obj
 = v_res_625_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__14___boxed(lean_object* v_type_626_, lean_object* v_declName_627_, lean_object* v_nondep_628_, lean_object* v_inst_629_, lean_object* v_inst_630_, lean_object* v_inst_631_, lean_object* v_pre_632_, lean_object* v_post_633_, lean_object* v_x_634_, lean_object* v_x_635_, lean_object* v___y_636_, lean_object* v_value_637_, lean_object* v_body_638_, lean_object* v___y_639_, lean_object* v_toBind_640_, lean_object* v_a_641_){
_start:
{
uint8_t v_nondep_2745__boxed_642_; lean_object* v_res_643_; 
v_nondep_2745__boxed_642_ = lean_unbox(v_nondep_628_);
v_res_643_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__14(v_type_626_, v_declName_627_, v_nondep_2745__boxed_642_, v_inst_629_, v_inst_630_, v_inst_631_, v_pre_632_, v_post_633_, v_x_634_, v_x_635_, v___y_636_, v_value_637_, v_body_638_, v___y_639_, v_toBind_640_, v_a_641_);
lean_dec(v___y_636_);
return v_res_643_;
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0(void){
_start:
{
lean_object* v___x_644_; lean_object* v_dummy_645_; 
v___x_644_ = lean_box(0);
v_dummy_645_ = l_Lean_Expr_sort___override(v___x_644_);
return v_dummy_645_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__15(lean_object* v_expr_646_, lean_object* v_data_647_, lean_object* v_inst_648_, lean_object* v_inst_649_, lean_object* v_inst_650_, lean_object* v_pre_651_, lean_object* v_post_652_, lean_object* v_x_653_, lean_object* v_x_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v_a_657_){
_start:
{
size_t v___x_658_; size_t v___x_659_; uint8_t v___x_660_; 
v___x_658_ = lean_ptr_addr(v_expr_646_);
v___x_659_ = lean_ptr_addr(v_a_657_);
v___x_660_ = lean_usize_dec_eq(v___x_658_, v___x_659_);
if (v___x_660_ == 0)
{
lean_object* v___x_661_; lean_object* v___x_662_; 
lean_dec_ref(v___y_656_);
v___x_661_ = l_Lean_Expr_mdata___override(v_data_647_, v_a_657_);
v___x_662_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_648_, v_inst_649_, v_inst_650_, v_pre_651_, v_post_652_, v_x_653_, v_x_654_, v___x_661_, v___y_655_);
return v___x_662_;
}
else
{
lean_object* v___x_663_; 
lean_dec_ref(v_a_657_);
lean_dec(v_data_647_);
v___x_663_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_648_, v_inst_649_, v_inst_650_, v_pre_651_, v_post_652_, v_x_653_, v_x_654_, v___y_656_, v___y_655_);
return v___x_663_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__15___boxed(lean_object* v_expr_664_, lean_object* v_data_665_, lean_object* v_inst_666_, lean_object* v_inst_667_, lean_object* v_inst_668_, lean_object* v_pre_669_, lean_object* v_post_670_, lean_object* v_x_671_, lean_object* v_x_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v_a_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__15(v_expr_664_, v_data_665_, v_inst_666_, v_inst_667_, v_inst_668_, v_pre_669_, v_post_670_, v_x_671_, v_x_672_, v___y_673_, v___y_674_, v_a_675_);
lean_dec(v___y_673_);
lean_dec_ref(v_expr_664_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__16(lean_object* v_struct_677_, lean_object* v_typeName_678_, lean_object* v_idx_679_, lean_object* v_inst_680_, lean_object* v_inst_681_, lean_object* v_inst_682_, lean_object* v_pre_683_, lean_object* v_post_684_, lean_object* v_x_685_, lean_object* v_x_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v_a_689_){
_start:
{
size_t v___x_690_; size_t v___x_691_; uint8_t v___x_692_; 
v___x_690_ = lean_ptr_addr(v_struct_677_);
v___x_691_ = lean_ptr_addr(v_a_689_);
v___x_692_ = lean_usize_dec_eq(v___x_690_, v___x_691_);
if (v___x_692_ == 0)
{
lean_object* v___x_693_; lean_object* v___x_694_; 
lean_dec_ref(v___y_688_);
v___x_693_ = l_Lean_Expr_proj___override(v_typeName_678_, v_idx_679_, v_a_689_);
v___x_694_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_680_, v_inst_681_, v_inst_682_, v_pre_683_, v_post_684_, v_x_685_, v_x_686_, v___x_693_, v___y_687_);
return v___x_694_;
}
else
{
lean_object* v___x_695_; 
lean_dec_ref(v_a_689_);
lean_dec(v_idx_679_);
lean_dec(v_typeName_678_);
v___x_695_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_680_, v_inst_681_, v_inst_682_, v_pre_683_, v_post_684_, v_x_685_, v_x_686_, v___y_688_, v___y_687_);
return v___x_695_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__16___boxed(lean_object* v_struct_696_, lean_object* v_typeName_697_, lean_object* v_idx_698_, lean_object* v_inst_699_, lean_object* v_inst_700_, lean_object* v_inst_701_, lean_object* v_pre_702_, lean_object* v_post_703_, lean_object* v_x_704_, lean_object* v_x_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v_a_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__16(v_struct_696_, v_typeName_697_, v_idx_698_, v_inst_699_, v_inst_700_, v_inst_701_, v_pre_702_, v_post_703_, v_x_704_, v_x_705_, v___y_706_, v___y_707_, v_a_708_);
lean_dec(v___y_706_);
lean_dec_ref(v_struct_696_);
return v_res_709_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17(lean_object* v_toApplicative_710_, lean_object* v_inst_711_, lean_object* v_inst_712_, lean_object* v_inst_713_, lean_object* v_pre_714_, lean_object* v_post_715_, lean_object* v_x_716_, lean_object* v_x_717_, lean_object* v___y_718_, lean_object* v_toBind_719_, lean_object* v___f_720_, lean_object* v___f_721_, lean_object* v_e_722_, lean_object* v_a_723_){
_start:
{
lean_object* v___y_725_; 
switch(lean_obj_tag(v_a_723_))
{
case 0:
{
lean_object* v_e_770_; lean_object* v_toPure_771_; lean_object* v___x_772_; 
lean_dec_ref(v_e_722_);
lean_dec(v___f_721_);
lean_dec(v___f_720_);
lean_dec(v_toBind_719_);
lean_dec(v_x_717_);
lean_dec(v_post_715_);
lean_dec(v_pre_714_);
lean_dec_ref(v_inst_713_);
lean_dec(v_inst_712_);
lean_dec_ref(v_inst_711_);
v_e_770_ = lean_ctor_get(v_a_723_, 0);
lean_inc_ref(v_e_770_);
lean_dec_ref_known(v_a_723_, 1);
v_toPure_771_ = lean_ctor_get(v_toApplicative_710_, 1);
lean_inc(v_toPure_771_);
lean_dec_ref(v_toApplicative_710_);
v___x_772_ = lean_apply_2(v_toPure_771_, lean_box(0), v_e_770_);
return v___x_772_;
}
case 1:
{
lean_object* v_e_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
lean_dec_ref(v_e_722_);
lean_dec(v___f_721_);
lean_dec_ref(v_toApplicative_710_);
v_e_773_ = lean_ctor_get(v_a_723_, 0);
lean_inc_ref(v_e_773_);
lean_dec_ref_known(v_a_723_, 1);
v___x_774_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_711_, v_inst_712_, v_inst_713_, v_pre_714_, v_post_715_, v_x_716_, v_x_717_, v_e_773_, v___y_718_);
v___x_775_ = lean_apply_4(v_toBind_719_, lean_box(0), lean_box(0), v___x_774_, v___f_720_);
return v___x_775_;
}
default: 
{
lean_object* v_e_x3f_776_; 
lean_dec(v___f_720_);
lean_dec_ref(v_toApplicative_710_);
v_e_x3f_776_ = lean_ctor_get(v_a_723_, 0);
lean_inc(v_e_x3f_776_);
lean_dec_ref_known(v_a_723_, 1);
if (lean_obj_tag(v_e_x3f_776_) == 0)
{
v___y_725_ = v_e_722_;
goto v___jp_724_;
}
else
{
lean_object* v_val_777_; 
lean_dec_ref(v_e_722_);
v_val_777_ = lean_ctor_get(v_e_x3f_776_, 0);
lean_inc(v_val_777_);
lean_dec_ref_known(v_e_x3f_776_, 1);
v___y_725_ = v_val_777_;
goto v___jp_724_;
}
}
}
v___jp_724_:
{
switch(lean_obj_tag(v___y_725_))
{
case 7:
{
lean_object* v_binderName_726_; lean_object* v_binderType_727_; lean_object* v_body_728_; uint8_t v_binderInfo_729_; lean_object* v___x_730_; lean_object* v___f_731_; lean_object* v___x_732_; lean_object* v___x_733_; 
lean_dec(v___f_721_);
v_binderName_726_ = lean_ctor_get(v___y_725_, 0);
lean_inc(v_binderName_726_);
v_binderType_727_ = lean_ctor_get(v___y_725_, 1);
lean_inc_ref_n(v_binderType_727_, 2);
v_body_728_ = lean_ctor_get(v___y_725_, 2);
lean_inc_ref(v_body_728_);
v_binderInfo_729_ = lean_ctor_get_uint8(v___y_725_, sizeof(void*)*3 + 8);
v___x_730_ = lean_box(v_binderInfo_729_);
lean_inc(v_toBind_719_);
lean_inc(v___y_718_);
lean_inc(v_x_717_);
lean_inc(v_post_715_);
lean_inc(v_pre_714_);
lean_inc_ref(v_inst_713_);
lean_inc(v_inst_712_);
lean_inc_ref(v_inst_711_);
v___f_731_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__9___boxed), 15, 14);
lean_closure_set(v___f_731_, 0, v_binderType_727_);
lean_closure_set(v___f_731_, 1, v_binderName_726_);
lean_closure_set(v___f_731_, 2, v___x_730_);
lean_closure_set(v___f_731_, 3, v_inst_711_);
lean_closure_set(v___f_731_, 4, v_inst_712_);
lean_closure_set(v___f_731_, 5, v_inst_713_);
lean_closure_set(v___f_731_, 6, v_pre_714_);
lean_closure_set(v___f_731_, 7, v_post_715_);
lean_closure_set(v___f_731_, 8, v_x_716_);
lean_closure_set(v___f_731_, 9, v_x_717_);
lean_closure_set(v___f_731_, 10, v___y_718_);
lean_closure_set(v___f_731_, 11, v_body_728_);
lean_closure_set(v___f_731_, 12, v___y_725_);
lean_closure_set(v___f_731_, 13, v_toBind_719_);
v___x_732_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_711_, v_inst_712_, v_inst_713_, v_pre_714_, v_post_715_, v_x_716_, v_x_717_, v_binderType_727_, v___y_718_);
v___x_733_ = lean_apply_4(v_toBind_719_, lean_box(0), lean_box(0), v___x_732_, v___f_731_);
return v___x_733_;
}
case 6:
{
lean_object* v_binderName_734_; lean_object* v_binderType_735_; lean_object* v_body_736_; uint8_t v_binderInfo_737_; lean_object* v___x_738_; lean_object* v___f_739_; lean_object* v___x_740_; lean_object* v___x_741_; 
lean_dec(v___f_721_);
v_binderName_734_ = lean_ctor_get(v___y_725_, 0);
lean_inc(v_binderName_734_);
v_binderType_735_ = lean_ctor_get(v___y_725_, 1);
lean_inc_ref_n(v_binderType_735_, 2);
v_body_736_ = lean_ctor_get(v___y_725_, 2);
lean_inc_ref(v_body_736_);
v_binderInfo_737_ = lean_ctor_get_uint8(v___y_725_, sizeof(void*)*3 + 8);
v___x_738_ = lean_box(v_binderInfo_737_);
lean_inc(v_toBind_719_);
lean_inc(v___y_718_);
lean_inc(v_x_717_);
lean_inc(v_post_715_);
lean_inc(v_pre_714_);
lean_inc_ref(v_inst_713_);
lean_inc(v_inst_712_);
lean_inc_ref(v_inst_711_);
v___f_739_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__11___boxed), 15, 14);
lean_closure_set(v___f_739_, 0, v_binderType_735_);
lean_closure_set(v___f_739_, 1, v_binderName_734_);
lean_closure_set(v___f_739_, 2, v___x_738_);
lean_closure_set(v___f_739_, 3, v_inst_711_);
lean_closure_set(v___f_739_, 4, v_inst_712_);
lean_closure_set(v___f_739_, 5, v_inst_713_);
lean_closure_set(v___f_739_, 6, v_pre_714_);
lean_closure_set(v___f_739_, 7, v_post_715_);
lean_closure_set(v___f_739_, 8, v_x_716_);
lean_closure_set(v___f_739_, 9, v_x_717_);
lean_closure_set(v___f_739_, 10, v___y_718_);
lean_closure_set(v___f_739_, 11, v_body_736_);
lean_closure_set(v___f_739_, 12, v___y_725_);
lean_closure_set(v___f_739_, 13, v_toBind_719_);
v___x_740_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_711_, v_inst_712_, v_inst_713_, v_pre_714_, v_post_715_, v_x_716_, v_x_717_, v_binderType_735_, v___y_718_);
v___x_741_ = lean_apply_4(v_toBind_719_, lean_box(0), lean_box(0), v___x_740_, v___f_739_);
return v___x_741_;
}
case 8:
{
lean_object* v_declName_742_; lean_object* v_type_743_; lean_object* v_value_744_; lean_object* v_body_745_; uint8_t v_nondep_746_; lean_object* v___x_747_; lean_object* v___f_748_; lean_object* v___x_749_; lean_object* v___x_750_; 
lean_dec(v___f_721_);
v_declName_742_ = lean_ctor_get(v___y_725_, 0);
lean_inc(v_declName_742_);
v_type_743_ = lean_ctor_get(v___y_725_, 1);
lean_inc_ref_n(v_type_743_, 2);
v_value_744_ = lean_ctor_get(v___y_725_, 2);
lean_inc_ref(v_value_744_);
v_body_745_ = lean_ctor_get(v___y_725_, 3);
lean_inc_ref(v_body_745_);
v_nondep_746_ = lean_ctor_get_uint8(v___y_725_, sizeof(void*)*4 + 8);
v___x_747_ = lean_box(v_nondep_746_);
lean_inc(v_toBind_719_);
lean_inc(v___y_718_);
lean_inc(v_x_717_);
lean_inc(v_post_715_);
lean_inc(v_pre_714_);
lean_inc_ref(v_inst_713_);
lean_inc(v_inst_712_);
lean_inc_ref(v_inst_711_);
v___f_748_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__14___boxed), 16, 15);
lean_closure_set(v___f_748_, 0, v_type_743_);
lean_closure_set(v___f_748_, 1, v_declName_742_);
lean_closure_set(v___f_748_, 2, v___x_747_);
lean_closure_set(v___f_748_, 3, v_inst_711_);
lean_closure_set(v___f_748_, 4, v_inst_712_);
lean_closure_set(v___f_748_, 5, v_inst_713_);
lean_closure_set(v___f_748_, 6, v_pre_714_);
lean_closure_set(v___f_748_, 7, v_post_715_);
lean_closure_set(v___f_748_, 8, v_x_716_);
lean_closure_set(v___f_748_, 9, v_x_717_);
lean_closure_set(v___f_748_, 10, v___y_718_);
lean_closure_set(v___f_748_, 11, v_value_744_);
lean_closure_set(v___f_748_, 12, v_body_745_);
lean_closure_set(v___f_748_, 13, v___y_725_);
lean_closure_set(v___f_748_, 14, v_toBind_719_);
v___x_749_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_711_, v_inst_712_, v_inst_713_, v_pre_714_, v_post_715_, v_x_716_, v_x_717_, v_type_743_, v___y_718_);
v___x_750_ = lean_apply_4(v_toBind_719_, lean_box(0), lean_box(0), v___x_749_, v___f_748_);
return v___x_750_;
}
case 5:
{
lean_object* v_dummy_751_; lean_object* v_nargs_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_2493__overap_756_; lean_object* v___x_757_; 
lean_dec(v_toBind_719_);
lean_dec(v_x_717_);
lean_dec(v_post_715_);
lean_dec(v_pre_714_);
lean_dec_ref(v_inst_713_);
lean_dec(v_inst_712_);
lean_dec_ref(v_inst_711_);
v_dummy_751_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_752_ = l_Lean_Expr_getAppNumArgs(v___y_725_);
lean_inc(v_nargs_752_);
v___x_753_ = lean_mk_array(v_nargs_752_, v_dummy_751_);
v___x_754_ = lean_unsigned_to_nat(1u);
v___x_755_ = lean_nat_sub(v_nargs_752_, v___x_754_);
lean_dec(v_nargs_752_);
v___x_2493__overap_756_ = l_Lean_Expr_withAppAux___redArg(v___f_721_, v___y_725_, v___x_753_, v___x_755_);
lean_inc(v___y_718_);
v___x_757_ = lean_apply_1(v___x_2493__overap_756_, v___y_718_);
return v___x_757_;
}
case 10:
{
lean_object* v_data_758_; lean_object* v_expr_759_; lean_object* v___f_760_; lean_object* v___x_761_; lean_object* v___x_762_; 
lean_dec(v___f_721_);
v_data_758_ = lean_ctor_get(v___y_725_, 0);
lean_inc(v_data_758_);
v_expr_759_ = lean_ctor_get(v___y_725_, 1);
lean_inc_ref_n(v_expr_759_, 2);
lean_inc(v___y_718_);
lean_inc(v_x_717_);
lean_inc(v_post_715_);
lean_inc(v_pre_714_);
lean_inc_ref(v_inst_713_);
lean_inc(v_inst_712_);
lean_inc_ref(v_inst_711_);
v___f_760_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__15___boxed), 12, 11);
lean_closure_set(v___f_760_, 0, v_expr_759_);
lean_closure_set(v___f_760_, 1, v_data_758_);
lean_closure_set(v___f_760_, 2, v_inst_711_);
lean_closure_set(v___f_760_, 3, v_inst_712_);
lean_closure_set(v___f_760_, 4, v_inst_713_);
lean_closure_set(v___f_760_, 5, v_pre_714_);
lean_closure_set(v___f_760_, 6, v_post_715_);
lean_closure_set(v___f_760_, 7, v_x_716_);
lean_closure_set(v___f_760_, 8, v_x_717_);
lean_closure_set(v___f_760_, 9, v___y_718_);
lean_closure_set(v___f_760_, 10, v___y_725_);
v___x_761_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_711_, v_inst_712_, v_inst_713_, v_pre_714_, v_post_715_, v_x_716_, v_x_717_, v_expr_759_, v___y_718_);
v___x_762_ = lean_apply_4(v_toBind_719_, lean_box(0), lean_box(0), v___x_761_, v___f_760_);
return v___x_762_;
}
case 11:
{
lean_object* v_typeName_763_; lean_object* v_idx_764_; lean_object* v_struct_765_; lean_object* v___f_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
lean_dec(v___f_721_);
v_typeName_763_ = lean_ctor_get(v___y_725_, 0);
lean_inc(v_typeName_763_);
v_idx_764_ = lean_ctor_get(v___y_725_, 1);
lean_inc(v_idx_764_);
v_struct_765_ = lean_ctor_get(v___y_725_, 2);
lean_inc_ref_n(v_struct_765_, 2);
lean_inc(v___y_718_);
lean_inc(v_x_717_);
lean_inc(v_post_715_);
lean_inc(v_pre_714_);
lean_inc_ref(v_inst_713_);
lean_inc(v_inst_712_);
lean_inc_ref(v_inst_711_);
v___f_766_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__16___boxed), 13, 12);
lean_closure_set(v___f_766_, 0, v_struct_765_);
lean_closure_set(v___f_766_, 1, v_typeName_763_);
lean_closure_set(v___f_766_, 2, v_idx_764_);
lean_closure_set(v___f_766_, 3, v_inst_711_);
lean_closure_set(v___f_766_, 4, v_inst_712_);
lean_closure_set(v___f_766_, 5, v_inst_713_);
lean_closure_set(v___f_766_, 6, v_pre_714_);
lean_closure_set(v___f_766_, 7, v_post_715_);
lean_closure_set(v___f_766_, 8, v_x_716_);
lean_closure_set(v___f_766_, 9, v_x_717_);
lean_closure_set(v___f_766_, 10, v___y_718_);
lean_closure_set(v___f_766_, 11, v___y_725_);
v___x_767_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_711_, v_inst_712_, v_inst_713_, v_pre_714_, v_post_715_, v_x_716_, v_x_717_, v_struct_765_, v___y_718_);
v___x_768_ = lean_apply_4(v_toBind_719_, lean_box(0), lean_box(0), v___x_767_, v___f_766_);
return v___x_768_;
}
default: 
{
lean_object* v___x_769_; 
lean_dec(v___f_721_);
lean_dec(v_toBind_719_);
v___x_769_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_711_, v_inst_712_, v_inst_713_, v_pre_714_, v_post_715_, v_x_716_, v_x_717_, v___y_725_, v___y_718_);
return v___x_769_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___boxed(lean_object* v_toApplicative_778_, lean_object* v_inst_779_, lean_object* v_inst_780_, lean_object* v_inst_781_, lean_object* v_pre_782_, lean_object* v_post_783_, lean_object* v_x_784_, lean_object* v_x_785_, lean_object* v___y_786_, lean_object* v_toBind_787_, lean_object* v___f_788_, lean_object* v___f_789_, lean_object* v_e_790_, lean_object* v_a_791_){
_start:
{
lean_object* v_res_792_; 
v_res_792_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17(v_toApplicative_778_, v_inst_779_, v_inst_780_, v_inst_781_, v_pre_782_, v_post_783_, v_x_784_, v_x_785_, v___y_786_, v_toBind_787_, v___f_788_, v___f_789_, v_e_790_, v_a_791_);
lean_dec(v___y_786_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__18(lean_object* v_inst_793_, lean_object* v_inst_794_, lean_object* v_inst_795_, lean_object* v_pre_796_, lean_object* v_post_797_, lean_object* v_x_798_, lean_object* v_x_799_, lean_object* v_toApplicative_800_, lean_object* v_toBind_801_, lean_object* v___f_802_, lean_object* v_e_803_, lean_object* v_____r_804_, lean_object* v___y_805_){
_start:
{
lean_object* v___f_806_; lean_object* v___f_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
lean_inc_n(v___y_805_, 2);
lean_inc(v_x_799_);
lean_inc(v_post_797_);
lean_inc_n(v_pre_796_, 2);
lean_inc_ref(v_inst_795_);
lean_inc(v_inst_794_);
lean_inc_ref(v_inst_793_);
v___f_806_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__7___boxed), 9, 8);
lean_closure_set(v___f_806_, 0, v_inst_793_);
lean_closure_set(v___f_806_, 1, v_inst_794_);
lean_closure_set(v___f_806_, 2, v_inst_795_);
lean_closure_set(v___f_806_, 3, v_pre_796_);
lean_closure_set(v___f_806_, 4, v_post_797_);
lean_closure_set(v___f_806_, 5, v_x_798_);
lean_closure_set(v___f_806_, 6, v_x_799_);
lean_closure_set(v___f_806_, 7, v___y_805_);
lean_inc_ref(v_e_803_);
lean_inc(v_toBind_801_);
v___f_807_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___boxed), 14, 13);
lean_closure_set(v___f_807_, 0, v_toApplicative_800_);
lean_closure_set(v___f_807_, 1, v_inst_793_);
lean_closure_set(v___f_807_, 2, v_inst_794_);
lean_closure_set(v___f_807_, 3, v_inst_795_);
lean_closure_set(v___f_807_, 4, v_pre_796_);
lean_closure_set(v___f_807_, 5, v_post_797_);
lean_closure_set(v___f_807_, 6, v_x_798_);
lean_closure_set(v___f_807_, 7, v_x_799_);
lean_closure_set(v___f_807_, 8, v___y_805_);
lean_closure_set(v___f_807_, 9, v_toBind_801_);
lean_closure_set(v___f_807_, 10, v___f_806_);
lean_closure_set(v___f_807_, 11, v___f_802_);
lean_closure_set(v___f_807_, 12, v_e_803_);
v___x_808_ = lean_apply_1(v_pre_796_, v_e_803_);
v___x_809_ = lean_apply_4(v_toBind_801_, lean_box(0), lean_box(0), v___x_808_, v___f_807_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__18___boxed(lean_object* v_inst_810_, lean_object* v_inst_811_, lean_object* v_inst_812_, lean_object* v_pre_813_, lean_object* v_post_814_, lean_object* v_x_815_, lean_object* v_x_816_, lean_object* v_toApplicative_817_, lean_object* v_toBind_818_, lean_object* v___f_819_, lean_object* v_e_820_, lean_object* v_____r_821_, lean_object* v___y_822_){
_start:
{
lean_object* v_res_823_; 
v_res_823_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__18(v_inst_810_, v_inst_811_, v_inst_812_, v_pre_813_, v_post_814_, v_x_815_, v_x_816_, v_toApplicative_817_, v_toBind_818_, v___f_819_, v_e_820_, v_____r_821_, v___y_822_);
lean_dec(v___y_822_);
return v_res_823_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(lean_object* v_inst_824_, lean_object* v_inst_825_, lean_object* v_inst_826_, lean_object* v_pre_827_, lean_object* v_post_828_, lean_object* v_x_829_, lean_object* v_x_830_, lean_object* v_e_831_, lean_object* v_a_832_){
_start:
{
lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___f_837_; lean_object* v___f_838_; lean_object* v___x_839_; lean_object* v_toApplicative_840_; lean_object* v_toBind_841_; lean_object* v___f_842_; lean_object* v___f_843_; lean_object* v___f_844_; lean_object* v___f_845_; lean_object* v___f_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_833_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0));
v___x_834_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1));
lean_inc_ref_n(v_inst_824_, 3);
v___x_835_ = l_Lean_MonadCacheT_instMonad___redArg(v_x_829_, v___x_833_, v___x_834_, v_inst_824_);
v___x_836_ = l_Lean_MonadCacheT_instMonadControl___redArg(v_x_829_, v___x_833_, v___x_834_);
lean_inc_ref_n(v_inst_826_, 3);
lean_inc_ref(v___x_836_);
v___f_837_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_837_, 0, v___x_836_);
lean_closure_set(v___f_837_, 1, v_inst_826_);
v___f_838_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_838_, 0, v___x_836_);
lean_closure_set(v___f_838_, 1, v_inst_826_);
v___x_839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_839_, 0, v___f_837_);
lean_ctor_set(v___x_839_, 1, v___f_838_);
v_toApplicative_840_ = lean_ctor_get(v_inst_824_, 0);
lean_inc_ref_n(v_toApplicative_840_, 4);
v_toBind_841_ = lean_ctor_get(v_inst_824_, 1);
lean_inc_n(v_toBind_841_, 6);
lean_inc_n(v_x_830_, 3);
lean_inc_n(v_a_832_, 3);
lean_inc_ref_n(v_e_831_, 2);
v___f_842_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_842_, 0, v_toApplicative_840_);
lean_closure_set(v___f_842_, 1, v___x_833_);
lean_closure_set(v___f_842_, 2, v___x_834_);
lean_closure_set(v___f_842_, 3, v_e_831_);
lean_closure_set(v___f_842_, 4, v_a_832_);
lean_closure_set(v___f_842_, 5, v_x_830_);
lean_closure_set(v___f_842_, 6, v_toBind_841_);
v___f_843_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__3___boxed), 5, 4);
lean_closure_set(v___f_843_, 0, v_toApplicative_840_);
lean_closure_set(v___f_843_, 1, v___x_833_);
lean_closure_set(v___f_843_, 2, v___x_834_);
lean_closure_set(v___f_843_, 3, v_e_831_);
lean_inc_ref(v___x_835_);
lean_inc(v_post_828_);
lean_inc(v_pre_827_);
lean_inc_n(v_inst_825_, 2);
v___f_844_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__6___boxed), 12, 9);
lean_closure_set(v___f_844_, 0, v_inst_824_);
lean_closure_set(v___f_844_, 1, v_inst_825_);
lean_closure_set(v___f_844_, 2, v_inst_826_);
lean_closure_set(v___f_844_, 3, v_pre_827_);
lean_closure_set(v___f_844_, 4, v_post_828_);
lean_closure_set(v___f_844_, 5, v_x_829_);
lean_closure_set(v___f_844_, 6, v_x_830_);
lean_closure_set(v___f_844_, 7, v___x_835_);
lean_closure_set(v___f_844_, 8, v_toBind_841_);
v___f_845_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__18___boxed), 13, 11);
lean_closure_set(v___f_845_, 0, v_inst_824_);
lean_closure_set(v___f_845_, 1, v_inst_825_);
lean_closure_set(v___f_845_, 2, v_inst_826_);
lean_closure_set(v___f_845_, 3, v_pre_827_);
lean_closure_set(v___f_845_, 4, v_post_828_);
lean_closure_set(v___f_845_, 5, v_x_829_);
lean_closure_set(v___f_845_, 6, v_x_830_);
lean_closure_set(v___f_845_, 7, v_toApplicative_840_);
lean_closure_set(v___f_845_, 8, v_toBind_841_);
lean_closure_set(v___f_845_, 9, v___f_844_);
lean_closure_set(v___f_845_, 10, v_e_831_);
v___f_846_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__19___boxed), 13, 12);
lean_closure_set(v___f_846_, 0, v_inst_825_);
lean_closure_set(v___f_846_, 1, v_x_829_);
lean_closure_set(v___f_846_, 2, v___x_833_);
lean_closure_set(v___f_846_, 3, v___x_834_);
lean_closure_set(v___f_846_, 4, v_inst_824_);
lean_closure_set(v___f_846_, 5, v___f_845_);
lean_closure_set(v___f_846_, 6, v___x_835_);
lean_closure_set(v___f_846_, 7, v___x_839_);
lean_closure_set(v___f_846_, 8, v_a_832_);
lean_closure_set(v___f_846_, 9, v_toBind_841_);
lean_closure_set(v___f_846_, 10, v___f_842_);
lean_closure_set(v___f_846_, 11, v_toApplicative_840_);
v___x_847_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_847_, 0, lean_box(0));
lean_closure_set(v___x_847_, 1, lean_box(0));
lean_closure_set(v___x_847_, 2, v_a_832_);
v___x_848_ = lean_apply_2(v_x_830_, lean_box(0), v___x_847_);
v___x_849_ = lean_apply_4(v_toBind_841_, lean_box(0), lean_box(0), v___x_848_, v___f_843_);
v___x_850_ = lean_apply_4(v_toBind_841_, lean_box(0), lean_box(0), v___x_849_, v___f_846_);
return v___x_850_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg___lam__0(lean_object* v_toApplicative_851_, lean_object* v_inst_852_, lean_object* v_inst_853_, lean_object* v_inst_854_, lean_object* v_pre_855_, lean_object* v_post_856_, lean_object* v_x_857_, lean_object* v_x_858_, lean_object* v_a_859_, lean_object* v_e_860_, lean_object* v_a_861_){
_start:
{
lean_object* v___y_863_; 
switch(lean_obj_tag(v_a_861_))
{
case 0:
{
lean_object* v_e_866_; lean_object* v_toPure_867_; lean_object* v___x_868_; 
lean_dec_ref(v_e_860_);
lean_dec(v_x_858_);
lean_dec(v_post_856_);
lean_dec(v_pre_855_);
lean_dec_ref(v_inst_854_);
lean_dec(v_inst_853_);
lean_dec_ref(v_inst_852_);
v_e_866_ = lean_ctor_get(v_a_861_, 0);
lean_inc_ref(v_e_866_);
lean_dec_ref_known(v_a_861_, 1);
v_toPure_867_ = lean_ctor_get(v_toApplicative_851_, 1);
lean_inc(v_toPure_867_);
lean_dec_ref(v_toApplicative_851_);
v___x_868_ = lean_apply_2(v_toPure_867_, lean_box(0), v_e_866_);
return v___x_868_;
}
case 1:
{
lean_object* v_e_869_; lean_object* v___x_870_; 
lean_dec_ref(v_e_860_);
lean_dec_ref(v_toApplicative_851_);
v_e_869_ = lean_ctor_get(v_a_861_, 0);
lean_inc_ref(v_e_869_);
lean_dec_ref_known(v_a_861_, 1);
v___x_870_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_852_, v_inst_853_, v_inst_854_, v_pre_855_, v_post_856_, v_x_857_, v_x_858_, v_e_869_, v_a_859_);
return v___x_870_;
}
default: 
{
lean_object* v_e_x3f_871_; 
lean_dec(v_x_858_);
lean_dec(v_post_856_);
lean_dec(v_pre_855_);
lean_dec_ref(v_inst_854_);
lean_dec(v_inst_853_);
lean_dec_ref(v_inst_852_);
v_e_x3f_871_ = lean_ctor_get(v_a_861_, 0);
lean_inc(v_e_x3f_871_);
lean_dec_ref_known(v_a_861_, 1);
if (lean_obj_tag(v_e_x3f_871_) == 0)
{
v___y_863_ = v_e_860_;
goto v___jp_862_;
}
else
{
lean_object* v_val_872_; 
lean_dec_ref(v_e_860_);
v_val_872_ = lean_ctor_get(v_e_x3f_871_, 0);
lean_inc(v_val_872_);
lean_dec_ref_known(v_e_x3f_871_, 1);
v___y_863_ = v_val_872_;
goto v___jp_862_;
}
}
}
v___jp_862_:
{
lean_object* v_toPure_864_; lean_object* v___x_865_; 
v_toPure_864_ = lean_ctor_get(v_toApplicative_851_, 1);
lean_inc(v_toPure_864_);
lean_dec_ref(v_toApplicative_851_);
v___x_865_ = lean_apply_2(v_toPure_864_, lean_box(0), v___y_863_);
return v___x_865_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg___lam__0___boxed(lean_object* v_toApplicative_873_, lean_object* v_inst_874_, lean_object* v_inst_875_, lean_object* v_inst_876_, lean_object* v_pre_877_, lean_object* v_post_878_, lean_object* v_x_879_, lean_object* v_x_880_, lean_object* v_a_881_, lean_object* v_e_882_, lean_object* v_a_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg___lam__0(v_toApplicative_873_, v_inst_874_, v_inst_875_, v_inst_876_, v_pre_877_, v_post_878_, v_x_879_, v_x_880_, v_a_881_, v_e_882_, v_a_883_);
lean_dec(v_a_881_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(lean_object* v_inst_885_, lean_object* v_inst_886_, lean_object* v_inst_887_, lean_object* v_pre_888_, lean_object* v_post_889_, lean_object* v_x_890_, lean_object* v_x_891_, lean_object* v_e_892_, lean_object* v_a_893_){
_start:
{
lean_object* v_toApplicative_894_; lean_object* v_toBind_895_; lean_object* v___f_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
v_toApplicative_894_ = lean_ctor_get(v_inst_885_, 0);
lean_inc_ref(v_toApplicative_894_);
v_toBind_895_ = lean_ctor_get(v_inst_885_, 1);
lean_inc(v_toBind_895_);
lean_inc_ref(v_e_892_);
lean_inc(v_a_893_);
lean_inc(v_post_889_);
v___f_896_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg___lam__0___boxed), 11, 10);
lean_closure_set(v___f_896_, 0, v_toApplicative_894_);
lean_closure_set(v___f_896_, 1, v_inst_885_);
lean_closure_set(v___f_896_, 2, v_inst_886_);
lean_closure_set(v___f_896_, 3, v_inst_887_);
lean_closure_set(v___f_896_, 4, v_pre_888_);
lean_closure_set(v___f_896_, 5, v_post_889_);
lean_closure_set(v___f_896_, 6, v_x_890_);
lean_closure_set(v___f_896_, 7, v_x_891_);
lean_closure_set(v___f_896_, 8, v_a_893_);
lean_closure_set(v___f_896_, 9, v_e_892_);
v___x_897_ = lean_apply_1(v_post_889_, v_e_892_);
v___x_898_ = lean_apply_4(v_toBind_895_, lean_box(0), lean_box(0), v___x_897_, v___f_896_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__7(lean_object* v_inst_899_, lean_object* v_inst_900_, lean_object* v_inst_901_, lean_object* v_pre_902_, lean_object* v_post_903_, lean_object* v_x_904_, lean_object* v_x_905_, lean_object* v___y_906_, lean_object* v_a_907_){
_start:
{
lean_object* v___x_908_; 
v___x_908_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_899_, v_inst_900_, v_inst_901_, v_pre_902_, v_post_903_, v_x_904_, v_x_905_, v_a_907_, v___y_906_);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg___boxed(lean_object* v_inst_909_, lean_object* v_inst_910_, lean_object* v_inst_911_, lean_object* v_pre_912_, lean_object* v_post_913_, lean_object* v_x_914_, lean_object* v_x_915_, lean_object* v_e_916_, lean_object* v_a_917_){
_start:
{
lean_object* v_res_918_; 
v_res_918_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_909_, v_inst_910_, v_inst_911_, v_pre_912_, v_post_913_, v_x_914_, v_x_915_, v_e_916_, v_a_917_);
lean_dec(v_a_917_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit(lean_object* v_m_919_, lean_object* v_inst_920_, lean_object* v_inst_921_, lean_object* v_inst_922_, lean_object* v_pre_923_, lean_object* v_post_924_, lean_object* v_x_925_, lean_object* v_x_926_, lean_object* v_e_927_, lean_object* v_a_928_){
_start:
{
lean_object* v___x_929_; 
v___x_929_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_920_, v_inst_921_, v_inst_922_, v_pre_923_, v_post_924_, v_x_925_, v_x_926_, v_e_927_, v_a_928_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___boxed(lean_object* v_m_930_, lean_object* v_inst_931_, lean_object* v_inst_932_, lean_object* v_inst_933_, lean_object* v_pre_934_, lean_object* v_post_935_, lean_object* v_x_936_, lean_object* v_x_937_, lean_object* v_e_938_, lean_object* v_a_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit(v_m_930_, v_inst_931_, v_inst_932_, v_inst_933_, v_pre_934_, v_post_935_, v_x_936_, v_x_937_, v_e_938_, v_a_939_);
lean_dec(v_a_939_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost(lean_object* v_m_941_, lean_object* v_inst_942_, lean_object* v_inst_943_, lean_object* v_inst_944_, lean_object* v_pre_945_, lean_object* v_post_946_, lean_object* v_x_947_, lean_object* v_x_948_, lean_object* v_e_949_, lean_object* v_a_950_){
_start:
{
lean_object* v___x_951_; 
v___x_951_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_942_, v_inst_943_, v_inst_944_, v_pre_945_, v_post_946_, v_x_947_, v_x_948_, v_e_949_, v_a_950_);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___boxed(lean_object* v_m_952_, lean_object* v_inst_953_, lean_object* v_inst_954_, lean_object* v_inst_955_, lean_object* v_pre_956_, lean_object* v_post_957_, lean_object* v_x_958_, lean_object* v_x_959_, lean_object* v_e_960_, lean_object* v_a_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost(v_m_952_, v_inst_953_, v_inst_954_, v_inst_955_, v_pre_956_, v_post_957_, v_x_958_, v_x_959_, v_e_960_, v_a_961_);
lean_dec(v_a_961_);
return v_res_962_;
}
}
lean_object* l_Lean_Core_transform___redArg___lam__0(lean_object* v_x_963_){
_start:
{
lean_object* v___x_965_; lean_object* v___x_966_; 
v___x_965_ = lean_apply_1(v_x_963_, lean_box(0));
v___x_966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_966_, 0, v___x_965_);
return v___x_966_;
}
}
LEAN_EXPORT void l_Lean_Core_transform___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_963_ = stack[0].m_obj;
lean_object* v_res_967_;
v_res_967_ = l_Lean_Core_transform___redArg___lam__0(v_x_963_);
stack->m_obj
 = v_res_967_;
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___redArg___lam__0___boxed(lean_object* v_x_968_, lean_object* v___y_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l_Lean_Core_transform___redArg___lam__0(v_x_968_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___redArg___lam__1(lean_object* v_inst_971_, lean_object* v_00_u03b1_972_, lean_object* v_x_973_){
_start:
{
lean_object* v___f_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
v___f_974_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_974_, 0, v_x_973_);
v___x_975_ = lean_alloc_closure((void*)(l_Lean_Core_liftIOCore___boxed), 5, 2);
lean_closure_set(v___x_975_, 0, lean_box(0));
lean_closure_set(v___x_975_, 1, v___f_974_);
v___x_976_ = lean_apply_2(v_inst_971_, lean_box(0), v___x_975_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___redArg___lam__2(lean_object* v_toPure_977_, lean_object* v_____x_978_){
_start:
{
lean_object* v_fst_979_; lean_object* v___x_980_; 
v_fst_979_ = lean_ctor_get(v_____x_978_, 0);
lean_inc(v_fst_979_);
lean_dec_ref(v_____x_978_);
v___x_980_ = lean_apply_2(v_toPure_977_, lean_box(0), v_fst_979_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___redArg___lam__3(lean_object* v_a_981_, lean_object* v_toPure_982_, lean_object* v_s_983_){
_start:
{
lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_984_, 0, v_a_981_);
lean_ctor_set(v___x_984_, 1, v_s_983_);
v___x_985_ = lean_apply_2(v_toPure_982_, lean_box(0), v___x_984_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___redArg___lam__4(lean_object* v_toPure_986_, lean_object* v_ref_987_, lean_object* v_x_988_, lean_object* v_toBind_989_, lean_object* v_a_990_){
_start:
{
lean_object* v___f_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; 
v___f_991_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__3), 3, 2);
lean_closure_set(v___f_991_, 0, v_a_990_);
lean_closure_set(v___f_991_, 1, v_toPure_986_);
v___x_992_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_992_, 0, lean_box(0));
lean_closure_set(v___x_992_, 1, lean_box(0));
lean_closure_set(v___x_992_, 2, v_ref_987_);
v___x_993_ = lean_apply_2(v_x_988_, lean_box(0), v___x_992_);
v___x_994_ = lean_apply_4(v_toBind_989_, lean_box(0), lean_box(0), v___x_993_, v___f_991_);
return v___x_994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___redArg___lam__5(lean_object* v_toPure_995_, lean_object* v_x_996_, lean_object* v_toBind_997_, lean_object* v_inst_998_, lean_object* v_inst_999_, lean_object* v_inst_1000_, lean_object* v_pre_1001_, lean_object* v_post_1002_, lean_object* v_x_1003_, lean_object* v_input_1004_, lean_object* v_ref_1005_){
_start:
{
lean_object* v___f_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
lean_inc(v_toBind_997_);
lean_inc(v_x_996_);
lean_inc(v_ref_1005_);
v___f_1006_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__4), 5, 4);
lean_closure_set(v___f_1006_, 0, v_toPure_995_);
lean_closure_set(v___f_1006_, 1, v_ref_1005_);
lean_closure_set(v___f_1006_, 2, v_x_996_);
lean_closure_set(v___f_1006_, 3, v_toBind_997_);
v___x_1007_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_998_, v_inst_999_, v_inst_1000_, v_pre_1001_, v_post_1002_, v_x_1003_, v_x_996_, v_input_1004_, v_ref_1005_);
lean_dec(v_ref_1005_);
v___x_1008_ = lean_apply_4(v_toBind_997_, lean_box(0), lean_box(0), v___x_1007_, v___f_1006_);
return v___x_1008_;
}
}
static lean_object* _init_l_Lean_Core_transform___redArg___closed__0(void){
_start:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1009_ = lean_box(0);
v___x_1010_ = lean_unsigned_to_nat(16u);
v___x_1011_ = lean_mk_array(v___x_1010_, v___x_1009_);
return v___x_1011_;
}
}
static lean_object* _init_l_Lean_Core_transform___redArg___closed__1(void){
_start:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1012_ = lean_obj_once(&l_Lean_Core_transform___redArg___closed__0, &l_Lean_Core_transform___redArg___closed__0_once, _init_l_Lean_Core_transform___redArg___closed__0);
v___x_1013_ = lean_unsigned_to_nat(0u);
v___x_1014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1013_);
lean_ctor_set(v___x_1014_, 1, v___x_1012_);
return v___x_1014_;
}
}
static lean_object* _init_l_Lean_Core_transform___redArg___closed__2(void){
_start:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1015_ = lean_obj_once(&l_Lean_Core_transform___redArg___closed__1, &l_Lean_Core_transform___redArg___closed__1_once, _init_l_Lean_Core_transform___redArg___closed__1);
v___x_1016_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1016_, 0, lean_box(0));
lean_closure_set(v___x_1016_, 1, lean_box(0));
lean_closure_set(v___x_1016_, 2, v___x_1015_);
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___redArg(lean_object* v_inst_1017_, lean_object* v_inst_1018_, lean_object* v_inst_1019_, lean_object* v_input_1020_, lean_object* v_pre_1021_, lean_object* v_post_1022_){
_start:
{
lean_object* v_x_1023_; lean_object* v_toApplicative_1024_; lean_object* v_toBind_1025_; lean_object* v_toPure_1026_; lean_object* v_x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___f_1030_; lean_object* v___f_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; 
v_x_1023_ = lean_box(0);
v_toApplicative_1024_ = lean_ctor_get(v_inst_1017_, 0);
v_toBind_1025_ = lean_ctor_get(v_inst_1017_, 1);
lean_inc_n(v_toBind_1025_, 3);
v_toPure_1026_ = lean_ctor_get(v_toApplicative_1024_, 1);
lean_inc_n(v_toPure_1026_, 2);
lean_inc_n(v_inst_1018_, 2);
v_x_1027_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__1), 3, 1);
lean_closure_set(v_x_1027_, 0, v_inst_1018_);
v___x_1028_ = lean_obj_once(&l_Lean_Core_transform___redArg___closed__2, &l_Lean_Core_transform___redArg___closed__2_once, _init_l_Lean_Core_transform___redArg___closed__2);
v___x_1029_ = l_Lean_Core_transform___redArg___lam__1(v_inst_1018_, lean_box(0), v___x_1028_);
v___f_1030_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__2), 2, 1);
lean_closure_set(v___f_1030_, 0, v_toPure_1026_);
v___f_1031_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__5), 11, 10);
lean_closure_set(v___f_1031_, 0, v_toPure_1026_);
lean_closure_set(v___f_1031_, 1, v_x_1027_);
lean_closure_set(v___f_1031_, 2, v_toBind_1025_);
lean_closure_set(v___f_1031_, 3, v_inst_1017_);
lean_closure_set(v___f_1031_, 4, v_inst_1018_);
lean_closure_set(v___f_1031_, 5, v_inst_1019_);
lean_closure_set(v___f_1031_, 6, v_pre_1021_);
lean_closure_set(v___f_1031_, 7, v_post_1022_);
lean_closure_set(v___f_1031_, 8, v_x_1023_);
lean_closure_set(v___f_1031_, 9, v_input_1020_);
v___x_1032_ = lean_apply_4(v_toBind_1025_, lean_box(0), lean_box(0), v___x_1029_, v___f_1031_);
v___x_1033_ = lean_apply_4(v_toBind_1025_, lean_box(0), lean_box(0), v___x_1032_, v___f_1030_);
return v___x_1033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform(lean_object* v_m_1034_, lean_object* v_inst_1035_, lean_object* v_inst_1036_, lean_object* v_inst_1037_, lean_object* v_input_1038_, lean_object* v_pre_1039_, lean_object* v_post_1040_){
_start:
{
lean_object* v___x_1041_; 
v___x_1041_ = l_Lean_Core_transform___redArg(v_inst_1035_, v_inst_1036_, v_inst_1037_, v_input_1038_, v_pre_1039_, v_post_1040_);
return v___x_1041_;
}
}
lean_object* l_Lean_Core_betaReduce___lam__0(lean_object* v_e_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_){
_start:
{
uint8_t v___x_1048_; uint8_t v___x_1049_; 
v___x_1048_ = 0;
v___x_1049_ = l_Lean_Expr_isHeadBetaTarget(v_e_1044_, v___x_1048_);
if (v___x_1049_ == 0)
{
lean_object* v___x_1050_; lean_object* v___x_1051_; 
lean_dec_ref(v_e_1044_);
v___x_1050_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_1051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1050_);
return v___x_1051_;
}
else
{
lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1052_ = l_Lean_Expr_headBeta(v_e_1044_);
v___x_1053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1052_);
v___x_1054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1053_);
return v___x_1054_;
}
}
}
LEAN_EXPORT void l_Lean_Core_betaReduce___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1044_ = stack[0].m_obj;
lean_object* v___y_1045_ = stack[1].m_obj;
lean_object* v___y_1046_ = stack[2].m_obj;
lean_object* v_res_1055_;
v_res_1055_ = l_Lean_Core_betaReduce___lam__0(v_e_1044_, v___y_1045_, v___y_1046_);
stack->m_obj
 = v_res_1055_;
}
LEAN_EXPORT lean_object* l_Lean_Core_betaReduce___lam__0___boxed(lean_object* v_e_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_){
_start:
{
lean_object* v_res_1060_; 
v_res_1060_ = l_Lean_Core_betaReduce___lam__0(v_e_1056_, v___y_1057_, v___y_1058_);
lean_dec(v___y_1058_);
lean_dec_ref(v___y_1057_);
return v_res_1060_;
}
}
lean_object* l_Lean_Core_betaReduce___lam__1(lean_object* v_e_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_){
_start:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1065_, 0, v_e_1061_);
v___x_1066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1065_);
return v___x_1066_;
}
}
LEAN_EXPORT void l_Lean_Core_betaReduce___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1061_ = stack[0].m_obj;
lean_object* v___y_1062_ = stack[1].m_obj;
lean_object* v___y_1063_ = stack[2].m_obj;
lean_object* v_res_1067_;
v_res_1067_ = l_Lean_Core_betaReduce___lam__1(v_e_1061_, v___y_1062_, v___y_1063_);
stack->m_obj
 = v_res_1067_;
}
LEAN_EXPORT lean_object* l_Lean_Core_betaReduce___lam__1___boxed(lean_object* v_e_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_){
_start:
{
lean_object* v_res_1072_; 
v_res_1072_ = l_Lean_Core_betaReduce___lam__1(v_e_1068_, v___y_1069_, v___y_1070_);
lean_dec(v___y_1070_);
lean_dec_ref(v___y_1069_);
return v_res_1072_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; 
v___x_1073_ = lean_box(0);
v___x_1074_ = l_Lean_interruptExceptionId;
v___x_1075_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1074_);
lean_ctor_set(v___x_1075_, 1, v___x_1073_);
return v___x_1075_;
}
}
lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___redArg(){
_start:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1077_ = lean_obj_once(&l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___redArg___closed__0, &l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___redArg___closed__0);
v___x_1078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1077_);
return v___x_1078_;
}
}
LEAN_EXPORT void l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1079_;
v_res_1079_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___redArg();
stack->m_obj
 = v_res_1079_;
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___redArg___boxed(lean_object* v___y_1080_){
_start:
{
lean_object* v_res_1081_; 
v_res_1081_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___redArg();
return v_res_1081_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___x_1087_ = l_Lean_maxRecDepthErrorMessage;
v___x_1088_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1088_, 0, v___x_1087_);
return v___x_1088_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1089_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__3);
v___x_1090_ = l_Lean_MessageData_ofFormat(v___x_1089_);
return v___x_1090_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1091_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__4);
v___x_1092_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__2));
v___x_1093_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1092_);
lean_ctor_set(v___x_1093_, 1, v___x_1091_);
return v___x_1093_;
}
}
lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg(lean_object* v_ref_1094_){
_start:
{
lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; 
v___x_1096_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5);
v___x_1097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1097_, 0, v_ref_1094_);
lean_ctor_set(v___x_1097_, 1, v___x_1096_);
v___x_1098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1097_);
return v___x_1098_;
}
}
LEAN_EXPORT void l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1094_ = stack[0].m_obj;
lean_object* v_res_1099_;
v_res_1099_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_1094_);
stack->m_obj
 = v_res_1099_;
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object* v_ref_1100_, lean_object* v___y_1101_){
_start:
{
lean_object* v_res_1102_; 
v_res_1102_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_1100_);
return v_res_1102_;
}
}
lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___redArg(lean_object* v_x_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_){
_start:
{
lean_object* v___y_1109_; uint16_t v___y_1119_; lean_object* v___y_1120_; uint8_t v___y_1121_; uint8_t v___y_1122_; lean_object* v___y_1123_; lean_object* v___y_1124_; lean_object* v_toCold_1129_; lean_object* v_currRecDepth_1130_; lean_object* v_ref_1131_; uint16_t v_optionFlags_1132_; uint8_t v_suppressElabErrors_1133_; uint8_t v_isRecordingDeps_1134_; lean_object* v_maxRecDepth_1135_; lean_object* v_cancelTk_x3f_1136_; 
v_toCold_1129_ = lean_ctor_get(v___y_1105_, 0);
v_currRecDepth_1130_ = lean_ctor_get(v___y_1105_, 1);
v_ref_1131_ = lean_ctor_get(v___y_1105_, 2);
v_optionFlags_1132_ = lean_ctor_get_uint16(v___y_1105_, sizeof(void*)*3);
v_suppressElabErrors_1133_ = lean_ctor_get_uint8(v___y_1105_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1134_ = lean_ctor_get_uint8(v___y_1105_, sizeof(void*)*3 + 3);
v_maxRecDepth_1135_ = lean_ctor_get(v_toCold_1129_, 3);
v_cancelTk_x3f_1136_ = lean_ctor_get(v_toCold_1129_, 10);
if (lean_obj_tag(v_cancelTk_x3f_1136_) == 1)
{
lean_object* v_val_1142_; uint8_t v___x_1143_; 
v_val_1142_ = lean_ctor_get(v_cancelTk_x3f_1136_, 0);
v___x_1143_ = l_IO_CancelToken_isSet(v_val_1142_);
if (v___x_1143_ == 0)
{
goto v___jp_1137_;
}
else
{
lean_object* v___x_1144_; lean_object* v_a_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1152_; 
lean_dec_ref(v_x_1103_);
v___x_1144_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___redArg();
v_a_1145_ = lean_ctor_get(v___x_1144_, 0);
v_isSharedCheck_1152_ = !lean_is_exclusive(v___x_1144_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1147_ = v___x_1144_;
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_a_1145_);
lean_dec(v___x_1144_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v___x_1150_; 
if (v_isShared_1148_ == 0)
{
v___x_1150_ = v___x_1147_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v_a_1145_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
}
}
else
{
goto v___jp_1137_;
}
v___jp_1108_:
{
if (lean_obj_tag(v___y_1109_) == 0)
{
return v___y_1109_;
}
else
{
lean_object* v_a_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1117_; 
v_a_1110_ = lean_ctor_get(v___y_1109_, 0);
v_isSharedCheck_1117_ = !lean_is_exclusive(v___y_1109_);
if (v_isSharedCheck_1117_ == 0)
{
v___x_1112_ = v___y_1109_;
v_isShared_1113_ = v_isSharedCheck_1117_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_a_1110_);
lean_dec(v___y_1109_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1117_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v___x_1115_; 
if (v_isShared_1113_ == 0)
{
v___x_1115_ = v___x_1112_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v_a_1110_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
return v___x_1115_;
}
}
}
}
v___jp_1118_:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; 
v___x_1125_ = lean_unsigned_to_nat(1u);
v___x_1126_ = lean_nat_add(v___y_1120_, v___x_1125_);
lean_inc_ref(v___y_1124_);
v___x_1127_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1127_, 0, v___y_1124_);
lean_ctor_set(v___x_1127_, 1, v___x_1126_);
lean_ctor_set(v___x_1127_, 2, v___y_1123_);
lean_ctor_set_uint16(v___x_1127_, sizeof(void*)*3, v___y_1119_);
lean_ctor_set_uint8(v___x_1127_, sizeof(void*)*3 + 2, v___y_1122_);
lean_ctor_set_uint8(v___x_1127_, sizeof(void*)*3 + 3, v___y_1121_);
lean_inc(v___y_1106_);
lean_inc(v___y_1104_);
v___x_1128_ = lean_apply_4(v_x_1103_, v___y_1104_, v___x_1127_, v___y_1106_, lean_box(0));
v___y_1109_ = v___x_1128_;
goto v___jp_1108_;
}
v___jp_1137_:
{
lean_object* v___x_1138_; uint8_t v___x_1139_; 
v___x_1138_ = lean_unsigned_to_nat(0u);
v___x_1139_ = lean_nat_dec_eq(v_maxRecDepth_1135_, v___x_1138_);
if (v___x_1139_ == 0)
{
uint8_t v___x_1140_; 
v___x_1140_ = lean_nat_dec_eq(v_currRecDepth_1130_, v_maxRecDepth_1135_);
if (v___x_1140_ == 0)
{
lean_inc(v_ref_1131_);
v___y_1119_ = v_optionFlags_1132_;
v___y_1120_ = v_currRecDepth_1130_;
v___y_1121_ = v_isRecordingDeps_1134_;
v___y_1122_ = v_suppressElabErrors_1133_;
v___y_1123_ = v_ref_1131_;
v___y_1124_ = v_toCold_1129_;
goto v___jp_1118_;
}
else
{
lean_object* v___x_1141_; 
lean_dec_ref(v_x_1103_);
lean_inc(v_ref_1131_);
v___x_1141_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_1131_);
v___y_1109_ = v___x_1141_;
goto v___jp_1108_;
}
}
else
{
lean_inc(v_ref_1131_);
v___y_1119_ = v_optionFlags_1132_;
v___y_1120_ = v_currRecDepth_1130_;
v___y_1121_ = v_isRecordingDeps_1134_;
v___y_1122_ = v_suppressElabErrors_1133_;
v___y_1123_ = v_ref_1131_;
v___y_1124_ = v_toCold_1129_;
goto v___jp_1118_;
}
}
}
}
LEAN_EXPORT void l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1103_ = stack[0].m_obj;
lean_object* v___y_1104_ = stack[1].m_obj;
lean_object* v___y_1105_ = stack[2].m_obj;
lean_object* v___y_1106_ = stack[3].m_obj;
lean_object* v_res_1153_;
v_res_1153_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___redArg(v_x_1103_, v___y_1104_, v___y_1105_, v___y_1106_);
stack->m_obj
 = v_res_1153_;
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
lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_1160_, lean_object* v_x_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_){
_start:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; 
v___x_1165_ = lean_apply_1(v_x_1161_, lean_box(0));
v___x_1166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1166_, 0, v___x_1165_);
return v___x_1166_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1161_ = stack[1].m_obj;
lean_object* v___y_1162_ = stack[2].m_obj;
lean_object* v___y_1163_ = stack[3].m_obj;
lean_object* v_res_1167_;
v_res_1167_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__0(lean_box(0), v_x_1161_, v___y_1162_, v___y_1163_);
stack->m_obj
 = v_res_1167_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_1168_, lean_object* v_x_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_){
_start:
{
lean_object* v_res_1173_; 
v_res_1173_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__0(v_00_u03b1_1168_, v_x_1169_, v___y_1170_, v___y_1171_);
lean_dec(v___y_1171_);
lean_dec_ref(v___y_1170_);
return v_res_1173_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___redArg(lean_object* v_a_1174_, lean_object* v_x_1175_){
_start:
{
if (lean_obj_tag(v_x_1175_) == 0)
{
uint8_t v___x_1176_; 
v___x_1176_ = 0;
return v___x_1176_;
}
else
{
lean_object* v_key_1177_; lean_object* v_tail_1178_; uint8_t v___x_1179_; 
v_key_1177_ = lean_ctor_get(v_x_1175_, 0);
v_tail_1178_ = lean_ctor_get(v_x_1175_, 2);
v___x_1179_ = l_Lean_ExprStructEq_beq(v_key_1177_, v_a_1174_);
if (v___x_1179_ == 0)
{
v_x_1175_ = v_tail_1178_;
goto _start;
}
else
{
return v___x_1179_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1174_ = stack[0].m_obj;
lean_object* v_x_1175_ = stack[1].m_obj;
uint8_t v_res_1181_;
v_res_1181_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___redArg(v_a_1174_, v_x_1175_);
stack->m_num = v_res_1181_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___redArg___boxed(lean_object* v_a_1182_, lean_object* v_x_1183_){
_start:
{
uint8_t v_res_1184_; lean_object* v_r_1185_; 
v_res_1184_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___redArg(v_a_1182_, v_x_1183_);
lean_dec(v_x_1183_);
lean_dec_ref(v_a_1182_);
v_r_1185_ = lean_box(v_res_1184_);
return v_r_1185_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(lean_object* v_x_1186_, lean_object* v_x_1187_){
_start:
{
if (lean_obj_tag(v_x_1187_) == 0)
{
return v_x_1186_;
}
else
{
lean_object* v_key_1188_; lean_object* v_value_1189_; lean_object* v_tail_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1213_; 
v_key_1188_ = lean_ctor_get(v_x_1187_, 0);
v_value_1189_ = lean_ctor_get(v_x_1187_, 1);
v_tail_1190_ = lean_ctor_get(v_x_1187_, 2);
v_isSharedCheck_1213_ = !lean_is_exclusive(v_x_1187_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1192_ = v_x_1187_;
v_isShared_1193_ = v_isSharedCheck_1213_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_tail_1190_);
lean_inc(v_value_1189_);
lean_inc(v_key_1188_);
lean_dec(v_x_1187_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1213_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v___x_1194_; uint64_t v___x_1195_; uint64_t v___x_1196_; uint64_t v___x_1197_; uint64_t v_fold_1198_; uint64_t v___x_1199_; uint64_t v___x_1200_; uint64_t v___x_1201_; size_t v___x_1202_; size_t v___x_1203_; size_t v___x_1204_; size_t v___x_1205_; size_t v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1209_; 
v___x_1194_ = lean_array_get_size(v_x_1186_);
v___x_1195_ = l_Lean_ExprStructEq_hash(v_key_1188_);
v___x_1196_ = 32ULL;
v___x_1197_ = lean_uint64_shift_right(v___x_1195_, v___x_1196_);
v_fold_1198_ = lean_uint64_xor(v___x_1195_, v___x_1197_);
v___x_1199_ = 16ULL;
v___x_1200_ = lean_uint64_shift_right(v_fold_1198_, v___x_1199_);
v___x_1201_ = lean_uint64_xor(v_fold_1198_, v___x_1200_);
v___x_1202_ = lean_uint64_to_usize(v___x_1201_);
v___x_1203_ = lean_usize_of_nat(v___x_1194_);
v___x_1204_ = ((size_t)1ULL);
v___x_1205_ = lean_usize_sub(v___x_1203_, v___x_1204_);
v___x_1206_ = lean_usize_land(v___x_1202_, v___x_1205_);
v___x_1207_ = lean_array_uget_borrowed(v_x_1186_, v___x_1206_);
lean_inc(v___x_1207_);
if (v_isShared_1193_ == 0)
{
lean_ctor_set(v___x_1192_, 2, v___x_1207_);
v___x_1209_ = v___x_1192_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_key_1188_);
lean_ctor_set(v_reuseFailAlloc_1212_, 1, v_value_1189_);
lean_ctor_set(v_reuseFailAlloc_1212_, 2, v___x_1207_);
v___x_1209_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
lean_object* v___x_1210_; 
v___x_1210_ = lean_array_uset(v_x_1186_, v___x_1206_, v___x_1209_);
v_x_1186_ = v___x_1210_;
v_x_1187_ = v_tail_1190_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(lean_object* v_i_1214_, lean_object* v_source_1215_, lean_object* v_target_1216_){
_start:
{
lean_object* v___x_1217_; uint8_t v___x_1218_; 
v___x_1217_ = lean_array_get_size(v_source_1215_);
v___x_1218_ = lean_nat_dec_lt(v_i_1214_, v___x_1217_);
if (v___x_1218_ == 0)
{
lean_dec_ref(v_source_1215_);
lean_dec(v_i_1214_);
return v_target_1216_;
}
else
{
lean_object* v_es_1219_; lean_object* v___x_1220_; lean_object* v_source_1221_; lean_object* v_target_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; 
v_es_1219_ = lean_array_fget(v_source_1215_, v_i_1214_);
v___x_1220_ = lean_box(0);
v_source_1221_ = lean_array_fset(v_source_1215_, v_i_1214_, v___x_1220_);
v_target_1222_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_target_1216_, v_es_1219_);
v___x_1223_ = lean_unsigned_to_nat(1u);
v___x_1224_ = lean_nat_add(v_i_1214_, v___x_1223_);
lean_dec(v_i_1214_);
v_i_1214_ = v___x_1224_;
v_source_1215_ = v_source_1221_;
v_target_1216_ = v_target_1222_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11___redArg(lean_object* v_data_1226_){
_start:
{
lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v_nbuckets_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; 
v___x_1227_ = lean_array_get_size(v_data_1226_);
v___x_1228_ = lean_unsigned_to_nat(2u);
v_nbuckets_1229_ = lean_nat_mul(v___x_1227_, v___x_1228_);
v___x_1230_ = lean_unsigned_to_nat(0u);
v___x_1231_ = lean_box(0);
v___x_1232_ = lean_mk_array(v_nbuckets_1229_, v___x_1231_);
v___x_1233_ = lean_array_propagate_mark(v_data_1226_, v___x_1232_);
v___x_1234_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v___x_1230_, v_data_1226_, v___x_1233_);
return v___x_1234_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__12___redArg(lean_object* v_a_1235_, lean_object* v_b_1236_, lean_object* v_x_1237_){
_start:
{
if (lean_obj_tag(v_x_1237_) == 0)
{
lean_dec(v_b_1236_);
lean_dec_ref(v_a_1235_);
return v_x_1237_;
}
else
{
lean_object* v_key_1238_; lean_object* v_value_1239_; lean_object* v_tail_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1252_; 
v_key_1238_ = lean_ctor_get(v_x_1237_, 0);
v_value_1239_ = lean_ctor_get(v_x_1237_, 1);
v_tail_1240_ = lean_ctor_get(v_x_1237_, 2);
v_isSharedCheck_1252_ = !lean_is_exclusive(v_x_1237_);
if (v_isSharedCheck_1252_ == 0)
{
v___x_1242_ = v_x_1237_;
v_isShared_1243_ = v_isSharedCheck_1252_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_tail_1240_);
lean_inc(v_value_1239_);
lean_inc(v_key_1238_);
lean_dec(v_x_1237_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1252_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
uint8_t v___x_1244_; 
v___x_1244_ = l_Lean_ExprStructEq_beq(v_key_1238_, v_a_1235_);
if (v___x_1244_ == 0)
{
lean_object* v___x_1245_; lean_object* v___x_1247_; 
v___x_1245_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__12___redArg(v_a_1235_, v_b_1236_, v_tail_1240_);
if (v_isShared_1243_ == 0)
{
lean_ctor_set(v___x_1242_, 2, v___x_1245_);
v___x_1247_ = v___x_1242_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v_key_1238_);
lean_ctor_set(v_reuseFailAlloc_1248_, 1, v_value_1239_);
lean_ctor_set(v_reuseFailAlloc_1248_, 2, v___x_1245_);
v___x_1247_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
return v___x_1247_;
}
}
else
{
lean_object* v___x_1250_; 
lean_dec(v_value_1239_);
lean_dec(v_key_1238_);
if (v_isShared_1243_ == 0)
{
lean_ctor_set(v___x_1242_, 1, v_b_1236_);
lean_ctor_set(v___x_1242_, 0, v_a_1235_);
v___x_1250_ = v___x_1242_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v_a_1235_);
lean_ctor_set(v_reuseFailAlloc_1251_, 1, v_b_1236_);
lean_ctor_set(v_reuseFailAlloc_1251_, 2, v_tail_1240_);
v___x_1250_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
return v___x_1250_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6___redArg(lean_object* v_m_1253_, lean_object* v_a_1254_, lean_object* v_b_1255_){
_start:
{
lean_object* v_size_1256_; lean_object* v_buckets_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1300_; 
v_size_1256_ = lean_ctor_get(v_m_1253_, 0);
v_buckets_1257_ = lean_ctor_get(v_m_1253_, 1);
v_isSharedCheck_1300_ = !lean_is_exclusive(v_m_1253_);
if (v_isSharedCheck_1300_ == 0)
{
v___x_1259_ = v_m_1253_;
v_isShared_1260_ = v_isSharedCheck_1300_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_buckets_1257_);
lean_inc(v_size_1256_);
lean_dec(v_m_1253_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1300_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v___x_1261_; uint64_t v___x_1262_; uint64_t v___x_1263_; uint64_t v___x_1264_; uint64_t v_fold_1265_; uint64_t v___x_1266_; uint64_t v___x_1267_; uint64_t v___x_1268_; size_t v___x_1269_; size_t v___x_1270_; size_t v___x_1271_; size_t v___x_1272_; size_t v___x_1273_; lean_object* v_bkt_1274_; uint8_t v___x_1275_; 
v___x_1261_ = lean_array_get_size(v_buckets_1257_);
v___x_1262_ = l_Lean_ExprStructEq_hash(v_a_1254_);
v___x_1263_ = 32ULL;
v___x_1264_ = lean_uint64_shift_right(v___x_1262_, v___x_1263_);
v_fold_1265_ = lean_uint64_xor(v___x_1262_, v___x_1264_);
v___x_1266_ = 16ULL;
v___x_1267_ = lean_uint64_shift_right(v_fold_1265_, v___x_1266_);
v___x_1268_ = lean_uint64_xor(v_fold_1265_, v___x_1267_);
v___x_1269_ = lean_uint64_to_usize(v___x_1268_);
v___x_1270_ = lean_usize_of_nat(v___x_1261_);
v___x_1271_ = ((size_t)1ULL);
v___x_1272_ = lean_usize_sub(v___x_1270_, v___x_1271_);
v___x_1273_ = lean_usize_land(v___x_1269_, v___x_1272_);
v_bkt_1274_ = lean_array_uget_borrowed(v_buckets_1257_, v___x_1273_);
v___x_1275_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___redArg(v_a_1254_, v_bkt_1274_);
if (v___x_1275_ == 0)
{
lean_object* v___x_1276_; lean_object* v_size_x27_1277_; lean_object* v___x_1278_; lean_object* v_buckets_x27_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; uint8_t v___x_1285_; 
v___x_1276_ = lean_unsigned_to_nat(1u);
v_size_x27_1277_ = lean_nat_add(v_size_1256_, v___x_1276_);
lean_dec(v_size_1256_);
lean_inc(v_bkt_1274_);
v___x_1278_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1278_, 0, v_a_1254_);
lean_ctor_set(v___x_1278_, 1, v_b_1255_);
lean_ctor_set(v___x_1278_, 2, v_bkt_1274_);
v_buckets_x27_1279_ = lean_array_uset(v_buckets_1257_, v___x_1273_, v___x_1278_);
v___x_1280_ = lean_unsigned_to_nat(4u);
v___x_1281_ = lean_nat_mul(v_size_x27_1277_, v___x_1280_);
v___x_1282_ = lean_unsigned_to_nat(3u);
v___x_1283_ = lean_nat_div(v___x_1281_, v___x_1282_);
lean_dec(v___x_1281_);
v___x_1284_ = lean_array_get_size(v_buckets_x27_1279_);
v___x_1285_ = lean_nat_dec_le(v___x_1283_, v___x_1284_);
lean_dec(v___x_1283_);
if (v___x_1285_ == 0)
{
lean_object* v_val_1286_; lean_object* v___x_1288_; 
v_val_1286_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11___redArg(v_buckets_x27_1279_);
if (v_isShared_1260_ == 0)
{
lean_ctor_set(v___x_1259_, 1, v_val_1286_);
lean_ctor_set(v___x_1259_, 0, v_size_x27_1277_);
v___x_1288_ = v___x_1259_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v_size_x27_1277_);
lean_ctor_set(v_reuseFailAlloc_1289_, 1, v_val_1286_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
return v___x_1288_;
}
}
else
{
lean_object* v___x_1291_; 
if (v_isShared_1260_ == 0)
{
lean_ctor_set(v___x_1259_, 1, v_buckets_x27_1279_);
lean_ctor_set(v___x_1259_, 0, v_size_x27_1277_);
v___x_1291_ = v___x_1259_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_size_x27_1277_);
lean_ctor_set(v_reuseFailAlloc_1292_, 1, v_buckets_x27_1279_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
}
else
{
lean_object* v___x_1293_; lean_object* v_buckets_x27_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1298_; 
lean_inc(v_bkt_1274_);
v___x_1293_ = lean_box(0);
v_buckets_x27_1294_ = lean_array_uset(v_buckets_1257_, v___x_1273_, v___x_1293_);
v___x_1295_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__12___redArg(v_a_1254_, v_b_1255_, v_bkt_1274_);
v___x_1296_ = lean_array_uset(v_buckets_x27_1294_, v___x_1273_, v___x_1295_);
if (v_isShared_1260_ == 0)
{
lean_ctor_set(v___x_1259_, 1, v___x_1296_);
v___x_1298_ = v___x_1259_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v_size_1256_);
lean_ctor_set(v_reuseFailAlloc_1299_, 1, v___x_1296_);
v___x_1298_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
return v___x_1298_;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__2(lean_object* v_a_1301_, lean_object* v_e_1302_, lean_object* v_a_1303_){
_start:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; 
v___x_1305_ = lean_st_ref_take(v_a_1301_);
v___x_1306_ = lean_box(0);
v___x_1307_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6___redArg(v___x_1305_, v_e_1302_, v_a_1303_);
v___x_1308_ = lean_st_ref_put(v_a_1301_, v___x_1307_);
return v___x_1306_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1301_ = stack[0].m_obj;
lean_object* v_e_1302_ = stack[1].m_obj;
lean_object* v_a_1303_ = stack[2].m_obj;
lean_object* v_res_1309_;
v_res_1309_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__2(v_a_1301_, v_e_1302_, v_a_1303_);
stack->m_obj
 = v_res_1309_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__2___boxed(lean_object* v_a_1310_, lean_object* v_e_1311_, lean_object* v_a_1312_, lean_object* v___y_1313_){
_start:
{
lean_object* v_res_1314_; 
v_res_1314_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__2(v_a_1310_, v_e_1311_, v_a_1312_);
lean_dec(v_a_1310_);
return v_res_1314_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___redArg(lean_object* v_a_1315_, lean_object* v_x_1316_){
_start:
{
if (lean_obj_tag(v_x_1316_) == 0)
{
lean_object* v___x_1317_; 
v___x_1317_ = lean_box(0);
return v___x_1317_;
}
else
{
lean_object* v_key_1318_; lean_object* v_value_1319_; lean_object* v_tail_1320_; uint8_t v___x_1321_; 
v_key_1318_ = lean_ctor_get(v_x_1316_, 0);
v_value_1319_ = lean_ctor_get(v_x_1316_, 1);
v_tail_1320_ = lean_ctor_get(v_x_1316_, 2);
v___x_1321_ = l_Lean_ExprStructEq_beq(v_key_1318_, v_a_1315_);
if (v___x_1321_ == 0)
{
v_x_1316_ = v_tail_1320_;
goto _start;
}
else
{
lean_object* v___x_1323_; 
lean_inc(v_value_1319_);
v___x_1323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1323_, 0, v_value_1319_);
return v___x_1323_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___redArg___boxed(lean_object* v_a_1324_, lean_object* v_x_1325_){
_start:
{
lean_object* v_res_1326_; 
v_res_1326_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___redArg(v_a_1324_, v_x_1325_);
lean_dec(v_x_1325_);
lean_dec_ref(v_a_1324_);
return v_res_1326_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg(lean_object* v_m_1327_, lean_object* v_a_1328_){
_start:
{
lean_object* v_buckets_1329_; lean_object* v___x_1330_; uint64_t v___x_1331_; uint64_t v___x_1332_; uint64_t v___x_1333_; uint64_t v_fold_1334_; uint64_t v___x_1335_; uint64_t v___x_1336_; uint64_t v___x_1337_; size_t v___x_1338_; size_t v___x_1339_; size_t v___x_1340_; size_t v___x_1341_; size_t v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; 
v_buckets_1329_ = lean_ctor_get(v_m_1327_, 1);
v___x_1330_ = lean_array_get_size(v_buckets_1329_);
v___x_1331_ = l_Lean_ExprStructEq_hash(v_a_1328_);
v___x_1332_ = 32ULL;
v___x_1333_ = lean_uint64_shift_right(v___x_1331_, v___x_1332_);
v_fold_1334_ = lean_uint64_xor(v___x_1331_, v___x_1333_);
v___x_1335_ = 16ULL;
v___x_1336_ = lean_uint64_shift_right(v_fold_1334_, v___x_1335_);
v___x_1337_ = lean_uint64_xor(v_fold_1334_, v___x_1336_);
v___x_1338_ = lean_uint64_to_usize(v___x_1337_);
v___x_1339_ = lean_usize_of_nat(v___x_1330_);
v___x_1340_ = ((size_t)1ULL);
v___x_1341_ = lean_usize_sub(v___x_1339_, v___x_1340_);
v___x_1342_ = lean_usize_land(v___x_1338_, v___x_1341_);
v___x_1343_ = lean_array_uget_borrowed(v_buckets_1329_, v___x_1342_);
v___x_1344_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___redArg(v_a_1328_, v___x_1343_);
return v___x_1344_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_m_1345_, lean_object* v_a_1346_){
_start:
{
lean_object* v_res_1347_; 
v_res_1347_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg(v_m_1345_, v_a_1346_);
lean_dec_ref(v_a_1346_);
lean_dec_ref(v_m_1345_);
return v_res_1347_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1(lean_object* v_pre_1348_, lean_object* v_post_1349_, size_t v_sz_1350_, size_t v_i_1351_, lean_object* v_bs_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_){
_start:
{
uint8_t v___x_1357_; 
v___x_1357_ = lean_usize_dec_lt(v_i_1351_, v_sz_1350_);
if (v___x_1357_ == 0)
{
lean_object* v___x_1358_; 
lean_dec_ref(v_post_1349_);
lean_dec_ref(v_pre_1348_);
v___x_1358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1358_, 0, v_bs_1352_);
return v___x_1358_;
}
else
{
lean_object* v_v_1359_; lean_object* v___x_1360_; lean_object* v_bs_x27_1361_; lean_object* v___x_1362_; 
v_v_1359_ = lean_array_uget(v_bs_1352_, v_i_1351_);
v___x_1360_ = lean_unsigned_to_nat(0u);
v_bs_x27_1361_ = lean_array_uset(v_bs_1352_, v_i_1351_, v___x_1360_);
lean_inc_ref(v_post_1349_);
lean_inc_ref(v_pre_1348_);
v___x_1362_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1348_, v_post_1349_, v_v_1359_, v___y_1353_, v___y_1354_, v___y_1355_);
if (lean_obj_tag(v___x_1362_) == 0)
{
lean_object* v_a_1363_; size_t v___x_1364_; size_t v___x_1365_; lean_object* v___x_1366_; 
v_a_1363_ = lean_ctor_get(v___x_1362_, 0);
lean_inc(v_a_1363_);
lean_dec_ref_known(v___x_1362_, 1);
v___x_1364_ = ((size_t)1ULL);
v___x_1365_ = lean_usize_add(v_i_1351_, v___x_1364_);
v___x_1366_ = lean_array_uset(v_bs_x27_1361_, v_i_1351_, v_a_1363_);
v_i_1351_ = v___x_1365_;
v_bs_1352_ = v___x_1366_;
goto _start;
}
else
{
lean_object* v_a_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1375_; 
lean_dec_ref(v_bs_x27_1361_);
lean_dec_ref(v_post_1349_);
lean_dec_ref(v_pre_1348_);
v_a_1368_ = lean_ctor_get(v___x_1362_, 0);
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1362_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1370_ = v___x_1362_;
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_a_1368_);
lean_dec(v___x_1362_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1373_; 
if (v_isShared_1371_ == 0)
{
v___x_1373_ = v___x_1370_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_a_1368_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
return v___x_1373_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_1348_ = stack[0].m_obj;
lean_object* v_post_1349_ = stack[1].m_obj;
size_t v_sz_1350_ = stack[2].m_num;
size_t v_i_1351_ = stack[3].m_num;
lean_object* v_bs_1352_ = stack[4].m_obj;
lean_object* v___y_1353_ = stack[5].m_obj;
lean_object* v___y_1354_ = stack[6].m_obj;
lean_object* v___y_1355_ = stack[7].m_obj;
lean_object* v_res_1376_;
v_res_1376_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1(v_pre_1348_, v_post_1349_, v_sz_1350_, v_i_1351_, v_bs_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
stack->m_obj
 = v_res_1376_;
}
lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__4(lean_object* v_pre_1377_, lean_object* v_post_1378_, lean_object* v_x_1379_, lean_object* v_x_1380_, lean_object* v_x_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_){
_start:
{
if (lean_obj_tag(v_x_1379_) == 5)
{
lean_object* v_fn_1386_; lean_object* v_arg_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; 
v_fn_1386_ = lean_ctor_get(v_x_1379_, 0);
lean_inc_ref(v_fn_1386_);
v_arg_1387_ = lean_ctor_get(v_x_1379_, 1);
lean_inc_ref(v_arg_1387_);
lean_dec_ref_known(v_x_1379_, 2);
v___x_1388_ = lean_array_set(v_x_1380_, v_x_1381_, v_arg_1387_);
v___x_1389_ = lean_unsigned_to_nat(1u);
v___x_1390_ = lean_nat_sub(v_x_1381_, v___x_1389_);
lean_dec(v_x_1381_);
v_x_1379_ = v_fn_1386_;
v_x_1380_ = v___x_1388_;
v_x_1381_ = v___x_1390_;
goto _start;
}
else
{
lean_object* v___x_1392_; 
lean_dec(v_x_1381_);
lean_inc_ref(v_post_1378_);
lean_inc_ref(v_pre_1377_);
v___x_1392_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1377_, v_post_1378_, v_x_1379_, v___y_1382_, v___y_1383_, v___y_1384_);
if (lean_obj_tag(v___x_1392_) == 0)
{
lean_object* v_a_1393_; size_t v_sz_1394_; size_t v___x_1395_; lean_object* v___x_1396_; 
v_a_1393_ = lean_ctor_get(v___x_1392_, 0);
lean_inc(v_a_1393_);
lean_dec_ref_known(v___x_1392_, 1);
v_sz_1394_ = lean_array_size(v_x_1380_);
v___x_1395_ = ((size_t)0ULL);
lean_inc_ref(v_post_1378_);
lean_inc_ref(v_pre_1377_);
v___x_1396_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1(v_pre_1377_, v_post_1378_, v_sz_1394_, v___x_1395_, v_x_1380_, v___y_1382_, v___y_1383_, v___y_1384_);
if (lean_obj_tag(v___x_1396_) == 0)
{
lean_object* v_a_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; 
v_a_1397_ = lean_ctor_get(v___x_1396_, 0);
lean_inc(v_a_1397_);
lean_dec_ref_known(v___x_1396_, 1);
v___x_1398_ = l_Lean_mkAppN(v_a_1393_, v_a_1397_);
lean_dec(v_a_1397_);
v___x_1399_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1377_, v_post_1378_, v___x_1398_, v___y_1382_, v___y_1383_, v___y_1384_);
return v___x_1399_;
}
else
{
lean_object* v_a_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1407_; 
lean_dec(v_a_1393_);
lean_dec_ref(v_post_1378_);
lean_dec_ref(v_pre_1377_);
v_a_1400_ = lean_ctor_get(v___x_1396_, 0);
v_isSharedCheck_1407_ = !lean_is_exclusive(v___x_1396_);
if (v_isSharedCheck_1407_ == 0)
{
v___x_1402_ = v___x_1396_;
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_a_1400_);
lean_dec(v___x_1396_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v___x_1405_; 
if (v_isShared_1403_ == 0)
{
v___x_1405_ = v___x_1402_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v_a_1400_);
v___x_1405_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
return v___x_1405_;
}
}
}
}
else
{
lean_dec_ref(v_x_1380_);
lean_dec_ref(v_post_1378_);
lean_dec_ref(v_pre_1377_);
return v___x_1392_;
}
}
}
}
LEAN_EXPORT void l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_1377_ = stack[0].m_obj;
lean_object* v_post_1378_ = stack[1].m_obj;
lean_object* v_x_1379_ = stack[2].m_obj;
lean_object* v_x_1380_ = stack[3].m_obj;
lean_object* v_x_1381_ = stack[4].m_obj;
lean_object* v___y_1382_ = stack[5].m_obj;
lean_object* v___y_1383_ = stack[6].m_obj;
lean_object* v___y_1384_ = stack[7].m_obj;
lean_object* v_res_1408_;
v_res_1408_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__4(v_pre_1377_, v_post_1378_, v_x_1379_, v_x_1380_, v_x_1381_, v___y_1382_, v___y_1383_, v___y_1384_);
stack->m_obj
 = v_res_1408_;
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__1(lean_object* v___x_1409_, lean_object* v_pre_1410_, lean_object* v_e_1411_, lean_object* v_post_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_){
_start:
{
lean_object* v___x_1417_; 
v___x_1417_ = l_Lean_Core_checkSystem(v___x_1409_, v___y_1414_, v___y_1415_);
if (lean_obj_tag(v___x_1417_) == 0)
{
lean_object* v___x_1418_; 
lean_dec_ref_known(v___x_1417_, 1);
lean_inc_ref(v_pre_1410_);
lean_inc(v___y_1415_);
lean_inc_ref(v___y_1414_);
lean_inc_ref(v_e_1411_);
v___x_1418_ = lean_apply_4(v_pre_1410_, v_e_1411_, v___y_1414_, v___y_1415_, lean_box(0));
if (lean_obj_tag(v___x_1418_) == 0)
{
lean_object* v_a_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1534_; 
v_a_1419_ = lean_ctor_get(v___x_1418_, 0);
v_isSharedCheck_1534_ = !lean_is_exclusive(v___x_1418_);
if (v_isSharedCheck_1534_ == 0)
{
v___x_1421_ = v___x_1418_;
v_isShared_1422_ = v_isSharedCheck_1534_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_a_1419_);
lean_dec(v___x_1418_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1534_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v___y_1424_; 
switch(lean_obj_tag(v_a_1419_))
{
case 0:
{
lean_object* v_e_1524_; lean_object* v___x_1526_; 
lean_dec_ref(v_post_1412_);
lean_dec_ref(v_e_1411_);
lean_dec_ref(v_pre_1410_);
v_e_1524_ = lean_ctor_get(v_a_1419_, 0);
lean_inc_ref(v_e_1524_);
lean_dec_ref_known(v_a_1419_, 1);
if (v_isShared_1422_ == 0)
{
lean_ctor_set(v___x_1421_, 0, v_e_1524_);
v___x_1526_ = v___x_1421_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v_e_1524_);
v___x_1526_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
return v___x_1526_;
}
}
case 1:
{
lean_object* v_e_1528_; lean_object* v___x_1529_; 
lean_del_object(v___x_1421_);
lean_dec_ref(v_e_1411_);
v_e_1528_ = lean_ctor_get(v_a_1419_, 0);
lean_inc_ref(v_e_1528_);
lean_dec_ref_known(v_a_1419_, 1);
lean_inc_ref(v_post_1412_);
lean_inc_ref(v_pre_1410_);
v___x_1529_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1410_, v_post_1412_, v_e_1528_, v___y_1413_, v___y_1414_, v___y_1415_);
if (lean_obj_tag(v___x_1529_) == 0)
{
lean_object* v_a_1530_; lean_object* v___x_1531_; 
v_a_1530_ = lean_ctor_get(v___x_1529_, 0);
lean_inc(v_a_1530_);
lean_dec_ref_known(v___x_1529_, 1);
v___x_1531_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1410_, v_post_1412_, v_a_1530_, v___y_1413_, v___y_1414_, v___y_1415_);
return v___x_1531_;
}
else
{
lean_dec_ref(v_post_1412_);
lean_dec_ref(v_pre_1410_);
return v___x_1529_;
}
}
default: 
{
lean_object* v_e_x3f_1532_; 
lean_del_object(v___x_1421_);
v_e_x3f_1532_ = lean_ctor_get(v_a_1419_, 0);
lean_inc(v_e_x3f_1532_);
lean_dec_ref_known(v_a_1419_, 1);
if (lean_obj_tag(v_e_x3f_1532_) == 0)
{
v___y_1424_ = v_e_1411_;
goto v___jp_1423_;
}
else
{
lean_object* v_val_1533_; 
lean_dec_ref(v_e_1411_);
v_val_1533_ = lean_ctor_get(v_e_x3f_1532_, 0);
lean_inc(v_val_1533_);
lean_dec_ref_known(v_e_x3f_1532_, 1);
v___y_1424_ = v_val_1533_;
goto v___jp_1423_;
}
}
}
v___jp_1423_:
{
switch(lean_obj_tag(v___y_1424_))
{
case 7:
{
lean_object* v_binderName_1425_; lean_object* v_binderType_1426_; lean_object* v_body_1427_; uint8_t v_binderInfo_1428_; lean_object* v___x_1429_; 
v_binderName_1425_ = lean_ctor_get(v___y_1424_, 0);
v_binderType_1426_ = lean_ctor_get(v___y_1424_, 1);
v_body_1427_ = lean_ctor_get(v___y_1424_, 2);
v_binderInfo_1428_ = lean_ctor_get_uint8(v___y_1424_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1426_);
lean_inc_ref(v_post_1412_);
lean_inc_ref(v_pre_1410_);
v___x_1429_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1410_, v_post_1412_, v_binderType_1426_, v___y_1413_, v___y_1414_, v___y_1415_);
if (lean_obj_tag(v___x_1429_) == 0)
{
lean_object* v_a_1430_; lean_object* v___x_1431_; 
v_a_1430_ = lean_ctor_get(v___x_1429_, 0);
lean_inc(v_a_1430_);
lean_dec_ref_known(v___x_1429_, 1);
lean_inc_ref(v_body_1427_);
lean_inc_ref(v_post_1412_);
lean_inc_ref(v_pre_1410_);
v___x_1431_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1410_, v_post_1412_, v_body_1427_, v___y_1413_, v___y_1414_, v___y_1415_);
if (lean_obj_tag(v___x_1431_) == 0)
{
lean_object* v_a_1432_; size_t v___x_1433_; size_t v___x_1434_; uint8_t v___x_1435_; 
v_a_1432_ = lean_ctor_get(v___x_1431_, 0);
lean_inc(v_a_1432_);
lean_dec_ref_known(v___x_1431_, 1);
v___x_1433_ = lean_ptr_addr(v_binderType_1426_);
v___x_1434_ = lean_ptr_addr(v_a_1430_);
v___x_1435_ = lean_usize_dec_eq(v___x_1433_, v___x_1434_);
if (v___x_1435_ == 0)
{
lean_object* v___x_1436_; lean_object* v___x_1437_; 
lean_inc(v_binderName_1425_);
lean_dec_ref_known(v___y_1424_, 3);
v___x_1436_ = l_Lean_Expr_forallE___override(v_binderName_1425_, v_a_1430_, v_a_1432_, v_binderInfo_1428_);
v___x_1437_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1410_, v_post_1412_, v___x_1436_, v___y_1413_, v___y_1414_, v___y_1415_);
return v___x_1437_;
}
else
{
size_t v___x_1438_; size_t v___x_1439_; uint8_t v___x_1440_; 
v___x_1438_ = lean_ptr_addr(v_body_1427_);
v___x_1439_ = lean_ptr_addr(v_a_1432_);
v___x_1440_ = lean_usize_dec_eq(v___x_1438_, v___x_1439_);
if (v___x_1440_ == 0)
{
lean_object* v___x_1441_; lean_object* v___x_1442_; 
lean_inc(v_binderName_1425_);
lean_dec_ref_known(v___y_1424_, 3);
v___x_1441_ = l_Lean_Expr_forallE___override(v_binderName_1425_, v_a_1430_, v_a_1432_, v_binderInfo_1428_);
v___x_1442_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1410_, v_post_1412_, v___x_1441_, v___y_1413_, v___y_1414_, v___y_1415_);
return v___x_1442_;
}
else
{
uint8_t v___x_1443_; 
v___x_1443_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1428_, v_binderInfo_1428_);
if (v___x_1443_ == 0)
{
lean_object* v___x_1444_; lean_object* v___x_1445_; 
lean_inc(v_binderName_1425_);
lean_dec_ref_known(v___y_1424_, 3);
v___x_1444_ = l_Lean_Expr_forallE___override(v_binderName_1425_, v_a_1430_, v_a_1432_, v_binderInfo_1428_);
v___x_1445_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1410_, v_post_1412_, v___x_1444_, v___y_1413_, v___y_1414_, v___y_1415_);
return v___x_1445_;
}
else
{
lean_object* v___x_1446_; 
lean_dec(v_a_1432_);
lean_dec(v_a_1430_);
v___x_1446_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1410_, v_post_1412_, v___y_1424_, v___y_1413_, v___y_1414_, v___y_1415_);
return v___x_1446_;
}
}
}
}
else
{
lean_dec(v_a_1430_);
lean_dec_ref_known(v___y_1424_, 3);
lean_dec_ref(v_post_1412_);
lean_dec_ref(v_pre_1410_);
return v___x_1431_;
}
}
else
{
lean_dec_ref_known(v___y_1424_, 3);
lean_dec_ref(v_post_1412_);
lean_dec_ref(v_pre_1410_);
return v___x_1429_;
}
}
case 6:
{
lean_object* v_binderName_1447_; lean_object* v_binderType_1448_; lean_object* v_body_1449_; uint8_t v_binderInfo_1450_; lean_object* v___x_1451_; 
v_binderName_1447_ = lean_ctor_get(v___y_1424_, 0);
v_binderType_1448_ = lean_ctor_get(v___y_1424_, 1);
v_body_1449_ = lean_ctor_get(v___y_1424_, 2);
v_binderInfo_1450_ = lean_ctor_get_uint8(v___y_1424_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1448_);
lean_inc_ref(v_post_1412_);
lean_inc_ref(v_pre_1410_);
v___x_1451_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1410_, v_post_1412_, v_binderType_1448_, v___y_1413_, v___y_1414_, v___y_1415_);
if (lean_obj_tag(v___x_1451_) == 0)
{
lean_object* v_a_1452_; lean_object* v___x_1453_; 
v_a_1452_ = lean_ctor_get(v___x_1451_, 0);
lean_inc(v_a_1452_);
lean_dec_ref_known(v___x_1451_, 1);
lean_inc_ref(v_body_1449_);
lean_inc_ref(v_post_1412_);
lean_inc_ref(v_pre_1410_);
v___x_1453_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1410_, v_post_1412_, v_body_1449_, v___y_1413_, v___y_1414_, v___y_1415_);
if (lean_obj_tag(v___x_1453_) == 0)
{
lean_object* v_a_1454_; size_t v___x_1455_; size_t v___x_1456_; uint8_t v___x_1457_; 
v_a_1454_ = lean_ctor_get(v___x_1453_, 0);
lean_inc(v_a_1454_);
lean_dec_ref_known(v___x_1453_, 1);
v___x_1455_ = lean_ptr_addr(v_binderType_1448_);
v___x_1456_ = lean_ptr_addr(v_a_1452_);
v___x_1457_ = lean_usize_dec_eq(v___x_1455_, v___x_1456_);
if (v___x_1457_ == 0)
{
lean_object* v___x_1458_; lean_object* v___x_1459_; 
lean_inc(v_binderName_1447_);
lean_dec_ref_known(v___y_1424_, 3);
v___x_1458_ = l_Lean_Expr_lam___override(v_binderName_1447_, v_a_1452_, v_a_1454_, v_binderInfo_1450_);
v___x_1459_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1410_, v_post_1412_, v___x_1458_, v___y_1413_, v___y_1414_, v___y_1415_);
return v___x_1459_;
}
else
{
size_t v___x_1460_; size_t v___x_1461_; uint8_t v___x_1462_; 
v___x_1460_ = lean_ptr_addr(v_body_1449_);
v___x_1461_ = lean_ptr_addr(v_a_1454_);
v___x_1462_ = lean_usize_dec_eq(v___x_1460_, v___x_1461_);
if (v___x_1462_ == 0)
{
lean_object* v___x_1463_; lean_object* v___x_1464_; 
lean_inc(v_binderName_1447_);
lean_dec_ref_known(v___y_1424_, 3);
v___x_1463_ = l_Lean_Expr_lam___override(v_binderName_1447_, v_a_1452_, v_a_1454_, v_binderInfo_1450_);
v___x_1464_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1410_, v_post_1412_, v___x_1463_, v___y_1413_, v___y_1414_, v___y_1415_);
return v___x_1464_;
}
else
{
uint8_t v___x_1465_; 
v___x_1465_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1450_, v_binderInfo_1450_);
if (v___x_1465_ == 0)
{
lean_object* v___x_1466_; lean_object* v___x_1467_; 
lean_inc(v_binderName_1447_);
lean_dec_ref_known(v___y_1424_, 3);
v___x_1466_ = l_Lean_Expr_lam___override(v_binderName_1447_, v_a_1452_, v_a_1454_, v_binderInfo_1450_);
v___x_1467_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1410_, v_post_1412_, v___x_1466_, v___y_1413_, v___y_1414_, v___y_1415_);
return v___x_1467_;
}
else
{
lean_object* v___x_1468_; 
lean_dec(v_a_1454_);
lean_dec(v_a_1452_);
v___x_1468_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1410_, v_post_1412_, v___y_1424_, v___y_1413_, v___y_1414_, v___y_1415_);
return v___x_1468_;
}
}
}
}
else
{
lean_dec(v_a_1452_);
lean_dec_ref_known(v___y_1424_, 3);
lean_dec_ref(v_post_1412_);
lean_dec_ref(v_pre_1410_);
return v___x_1453_;
}
}
else
{
lean_dec_ref_known(v___y_1424_, 3);
lean_dec_ref(v_post_1412_);
lean_dec_ref(v_pre_1410_);
return v___x_1451_;
}
}
case 8:
{
lean_object* v_declName_1469_; lean_object* v_type_1470_; lean_object* v_value_1471_; lean_object* v_body_1472_; uint8_t v_nondep_1473_; lean_object* v___x_1474_; 
v_declName_1469_ = lean_ctor_get(v___y_1424_, 0);
v_type_1470_ = lean_ctor_get(v___y_1424_, 1);
v_value_1471_ = lean_ctor_get(v___y_1424_, 2);
v_body_1472_ = lean_ctor_get(v___y_1424_, 3);
v_nondep_1473_ = lean_ctor_get_uint8(v___y_1424_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_1470_);
lean_inc_ref(v_post_1412_);
lean_inc_ref(v_pre_1410_);
v___x_1474_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1410_, v_post_1412_, v_type_1470_, v___y_1413_, v___y_1414_, v___y_1415_);
if (lean_obj_tag(v___x_1474_) == 0)
{
lean_object* v_a_1475_; lean_object* v___x_1476_; 
v_a_1475_ = lean_ctor_get(v___x_1474_, 0);
lean_inc(v_a_1475_);
lean_dec_ref_known(v___x_1474_, 1);
lean_inc_ref(v_value_1471_);
lean_inc_ref(v_post_1412_);
lean_inc_ref(v_pre_1410_);
v___x_1476_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1410_, v_post_1412_, v_value_1471_, v___y_1413_, v___y_1414_, v___y_1415_);
if (lean_obj_tag(v___x_1476_) == 0)
{
lean_object* v_a_1477_; lean_object* v___x_1478_; 
v_a_1477_ = lean_ctor_get(v___x_1476_, 0);
lean_inc(v_a_1477_);
lean_dec_ref_known(v___x_1476_, 1);
lean_inc_ref(v_body_1472_);
lean_inc_ref(v_post_1412_);
lean_inc_ref(v_pre_1410_);
v___x_1478_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1410_, v_post_1412_, v_body_1472_, v___y_1413_, v___y_1414_, v___y_1415_);
if (lean_obj_tag(v___x_1478_) == 0)
{
lean_object* v_a_1479_; size_t v___x_1480_; size_t v___x_1481_; uint8_t v___x_1482_; 
v_a_1479_ = lean_ctor_get(v___x_1478_, 0);
lean_inc(v_a_1479_);
lean_dec_ref_known(v___x_1478_, 1);
v___x_1480_ = lean_ptr_addr(v_type_1470_);
v___x_1481_ = lean_ptr_addr(v_a_1475_);
v___x_1482_ = lean_usize_dec_eq(v___x_1480_, v___x_1481_);
if (v___x_1482_ == 0)
{
lean_object* v___x_1483_; lean_object* v___x_1484_; 
lean_inc(v_declName_1469_);
lean_dec_ref_known(v___y_1424_, 4);
v___x_1483_ = l_Lean_Expr_letE___override(v_declName_1469_, v_a_1475_, v_a_1477_, v_a_1479_, v_nondep_1473_);
v___x_1484_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1410_, v_post_1412_, v___x_1483_, v___y_1413_, v___y_1414_, v___y_1415_);
return v___x_1484_;
}
else
{
size_t v___x_1485_; size_t v___x_1486_; uint8_t v___x_1487_; 
v___x_1485_ = lean_ptr_addr(v_value_1471_);
v___x_1486_ = lean_ptr_addr(v_a_1477_);
v___x_1487_ = lean_usize_dec_eq(v___x_1485_, v___x_1486_);
if (v___x_1487_ == 0)
{
lean_object* v___x_1488_; lean_object* v___x_1489_; 
lean_inc(v_declName_1469_);
lean_dec_ref_known(v___y_1424_, 4);
v___x_1488_ = l_Lean_Expr_letE___override(v_declName_1469_, v_a_1475_, v_a_1477_, v_a_1479_, v_nondep_1473_);
v___x_1489_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1410_, v_post_1412_, v___x_1488_, v___y_1413_, v___y_1414_, v___y_1415_);
return v___x_1489_;
}
else
{
size_t v___x_1490_; size_t v___x_1491_; uint8_t v___x_1492_; 
v___x_1490_ = lean_ptr_addr(v_body_1472_);
v___x_1491_ = lean_ptr_addr(v_a_1479_);
v___x_1492_ = lean_usize_dec_eq(v___x_1490_, v___x_1491_);
if (v___x_1492_ == 0)
{
lean_object* v___x_1493_; lean_object* v___x_1494_; 
lean_inc(v_declName_1469_);
lean_dec_ref_known(v___y_1424_, 4);
v___x_1493_ = l_Lean_Expr_letE___override(v_declName_1469_, v_a_1475_, v_a_1477_, v_a_1479_, v_nondep_1473_);
v___x_1494_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1410_, v_post_1412_, v___x_1493_, v___y_1413_, v___y_1414_, v___y_1415_);
return v___x_1494_;
}
else
{
lean_object* v___x_1495_; 
lean_dec(v_a_1479_);
lean_dec(v_a_1477_);
lean_dec(v_a_1475_);
v___x_1495_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1410_, v_post_1412_, v___y_1424_, v___y_1413_, v___y_1414_, v___y_1415_);
return v___x_1495_;
}
}
}
}
else
{
lean_dec(v_a_1477_);
lean_dec(v_a_1475_);
lean_dec_ref_known(v___y_1424_, 4);
lean_dec_ref(v_post_1412_);
lean_dec_ref(v_pre_1410_);
return v___x_1478_;
}
}
else
{
lean_dec(v_a_1475_);
lean_dec_ref_known(v___y_1424_, 4);
lean_dec_ref(v_post_1412_);
lean_dec_ref(v_pre_1410_);
return v___x_1476_;
}
}
else
{
lean_dec_ref_known(v___y_1424_, 4);
lean_dec_ref(v_post_1412_);
lean_dec_ref(v_pre_1410_);
return v___x_1474_;
}
}
case 5:
{
lean_object* v_dummy_1496_; lean_object* v_nargs_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; 
v_dummy_1496_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_1497_ = l_Lean_Expr_getAppNumArgs(v___y_1424_);
lean_inc(v_nargs_1497_);
v___x_1498_ = lean_mk_array(v_nargs_1497_, v_dummy_1496_);
v___x_1499_ = lean_unsigned_to_nat(1u);
v___x_1500_ = lean_nat_sub(v_nargs_1497_, v___x_1499_);
lean_dec(v_nargs_1497_);
v___x_1501_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__4(v_pre_1410_, v_post_1412_, v___y_1424_, v___x_1498_, v___x_1500_, v___y_1413_, v___y_1414_, v___y_1415_);
return v___x_1501_;
}
case 10:
{
lean_object* v_data_1502_; lean_object* v_expr_1503_; lean_object* v___x_1504_; 
v_data_1502_ = lean_ctor_get(v___y_1424_, 0);
v_expr_1503_ = lean_ctor_get(v___y_1424_, 1);
lean_inc_ref(v_expr_1503_);
lean_inc_ref(v_post_1412_);
lean_inc_ref(v_pre_1410_);
v___x_1504_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1410_, v_post_1412_, v_expr_1503_, v___y_1413_, v___y_1414_, v___y_1415_);
if (lean_obj_tag(v___x_1504_) == 0)
{
lean_object* v_a_1505_; size_t v___x_1506_; size_t v___x_1507_; uint8_t v___x_1508_; 
v_a_1505_ = lean_ctor_get(v___x_1504_, 0);
lean_inc(v_a_1505_);
lean_dec_ref_known(v___x_1504_, 1);
v___x_1506_ = lean_ptr_addr(v_expr_1503_);
v___x_1507_ = lean_ptr_addr(v_a_1505_);
v___x_1508_ = lean_usize_dec_eq(v___x_1506_, v___x_1507_);
if (v___x_1508_ == 0)
{
lean_object* v___x_1509_; lean_object* v___x_1510_; 
lean_inc(v_data_1502_);
lean_dec_ref_known(v___y_1424_, 2);
v___x_1509_ = l_Lean_Expr_mdata___override(v_data_1502_, v_a_1505_);
v___x_1510_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1410_, v_post_1412_, v___x_1509_, v___y_1413_, v___y_1414_, v___y_1415_);
return v___x_1510_;
}
else
{
lean_object* v___x_1511_; 
lean_dec(v_a_1505_);
v___x_1511_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1410_, v_post_1412_, v___y_1424_, v___y_1413_, v___y_1414_, v___y_1415_);
return v___x_1511_;
}
}
else
{
lean_dec_ref_known(v___y_1424_, 2);
lean_dec_ref(v_post_1412_);
lean_dec_ref(v_pre_1410_);
return v___x_1504_;
}
}
case 11:
{
lean_object* v_typeName_1512_; lean_object* v_idx_1513_; lean_object* v_struct_1514_; lean_object* v___x_1515_; 
v_typeName_1512_ = lean_ctor_get(v___y_1424_, 0);
v_idx_1513_ = lean_ctor_get(v___y_1424_, 1);
v_struct_1514_ = lean_ctor_get(v___y_1424_, 2);
lean_inc_ref(v_struct_1514_);
lean_inc_ref(v_post_1412_);
lean_inc_ref(v_pre_1410_);
v___x_1515_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1410_, v_post_1412_, v_struct_1514_, v___y_1413_, v___y_1414_, v___y_1415_);
if (lean_obj_tag(v___x_1515_) == 0)
{
lean_object* v_a_1516_; size_t v___x_1517_; size_t v___x_1518_; uint8_t v___x_1519_; 
v_a_1516_ = lean_ctor_get(v___x_1515_, 0);
lean_inc(v_a_1516_);
lean_dec_ref_known(v___x_1515_, 1);
v___x_1517_ = lean_ptr_addr(v_struct_1514_);
v___x_1518_ = lean_ptr_addr(v_a_1516_);
v___x_1519_ = lean_usize_dec_eq(v___x_1517_, v___x_1518_);
if (v___x_1519_ == 0)
{
lean_object* v___x_1520_; lean_object* v___x_1521_; 
lean_inc(v_idx_1513_);
lean_inc(v_typeName_1512_);
lean_dec_ref_known(v___y_1424_, 3);
v___x_1520_ = l_Lean_Expr_proj___override(v_typeName_1512_, v_idx_1513_, v_a_1516_);
v___x_1521_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1410_, v_post_1412_, v___x_1520_, v___y_1413_, v___y_1414_, v___y_1415_);
return v___x_1521_;
}
else
{
lean_object* v___x_1522_; 
lean_dec(v_a_1516_);
v___x_1522_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1410_, v_post_1412_, v___y_1424_, v___y_1413_, v___y_1414_, v___y_1415_);
return v___x_1522_;
}
}
else
{
lean_dec_ref_known(v___y_1424_, 3);
lean_dec_ref(v_post_1412_);
lean_dec_ref(v_pre_1410_);
return v___x_1515_;
}
}
default: 
{
lean_object* v___x_1523_; 
v___x_1523_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1410_, v_post_1412_, v___y_1424_, v___y_1413_, v___y_1414_, v___y_1415_);
return v___x_1523_;
}
}
}
}
}
else
{
lean_object* v_a_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1542_; 
lean_dec_ref(v_post_1412_);
lean_dec_ref(v_e_1411_);
lean_dec_ref(v_pre_1410_);
v_a_1535_ = lean_ctor_get(v___x_1418_, 0);
v_isSharedCheck_1542_ = !lean_is_exclusive(v___x_1418_);
if (v_isSharedCheck_1542_ == 0)
{
v___x_1537_ = v___x_1418_;
v_isShared_1538_ = v_isSharedCheck_1542_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_a_1535_);
lean_dec(v___x_1418_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1542_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
lean_object* v___x_1540_; 
if (v_isShared_1538_ == 0)
{
v___x_1540_ = v___x_1537_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v_a_1535_);
v___x_1540_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
return v___x_1540_;
}
}
}
}
else
{
lean_object* v_a_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1550_; 
lean_dec_ref(v_post_1412_);
lean_dec_ref(v_e_1411_);
lean_dec_ref(v_pre_1410_);
v_a_1543_ = lean_ctor_get(v___x_1417_, 0);
v_isSharedCheck_1550_ = !lean_is_exclusive(v___x_1417_);
if (v_isSharedCheck_1550_ == 0)
{
v___x_1545_ = v___x_1417_;
v_isShared_1546_ = v_isSharedCheck_1550_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_a_1543_);
lean_dec(v___x_1417_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1550_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
lean_object* v___x_1548_; 
if (v_isShared_1546_ == 0)
{
v___x_1548_ = v___x_1545_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v_a_1543_);
v___x_1548_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
return v___x_1548_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1409_ = stack[0].m_obj;
lean_object* v_pre_1410_ = stack[1].m_obj;
lean_object* v_e_1411_ = stack[2].m_obj;
lean_object* v_post_1412_ = stack[3].m_obj;
lean_object* v___y_1413_ = stack[4].m_obj;
lean_object* v___y_1414_ = stack[5].m_obj;
lean_object* v___y_1415_ = stack[6].m_obj;
lean_object* v_res_1551_;
v_res_1551_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__1(v___x_1409_, v_pre_1410_, v_e_1411_, v_post_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
stack->m_obj
 = v_res_1551_;
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
lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(lean_object* v_pre_1561_, lean_object* v_post_1562_, lean_object* v_e_1563_, lean_object* v_a_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_){
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
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_1561_ = stack[0].m_obj;
lean_object* v_post_1562_ = stack[1].m_obj;
lean_object* v_e_1563_ = stack[2].m_obj;
lean_object* v_a_1564_ = stack[3].m_obj;
lean_object* v___y_1565_ = stack[4].m_obj;
lean_object* v___y_1566_ = stack[5].m_obj;
lean_object* v_res_1610_;
v_res_1610_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1561_, v_post_1562_, v_e_1563_, v_a_1564_, v___y_1565_, v___y_1566_);
stack->m_obj
 = v_res_1610_;
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(lean_object* v_pre_1611_, lean_object* v_post_1612_, lean_object* v_e_1613_, lean_object* v_a_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_){
_start:
{
lean_object* v___x_1618_; 
lean_inc_ref(v_post_1612_);
lean_inc(v___y_1616_);
lean_inc_ref(v___y_1615_);
lean_inc_ref(v_e_1613_);
v___x_1618_ = lean_apply_4(v_post_1612_, v_e_1613_, v___y_1615_, v___y_1616_, lean_box(0));
if (lean_obj_tag(v___x_1618_) == 0)
{
lean_object* v_a_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1637_; 
v_a_1619_ = lean_ctor_get(v___x_1618_, 0);
v_isSharedCheck_1637_ = !lean_is_exclusive(v___x_1618_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1621_ = v___x_1618_;
v_isShared_1622_ = v_isSharedCheck_1637_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_a_1619_);
lean_dec(v___x_1618_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1637_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
switch(lean_obj_tag(v_a_1619_))
{
case 0:
{
lean_object* v_e_1623_; lean_object* v___x_1625_; 
lean_dec_ref(v_e_1613_);
lean_dec_ref(v_post_1612_);
lean_dec_ref(v_pre_1611_);
v_e_1623_ = lean_ctor_get(v_a_1619_, 0);
lean_inc_ref(v_e_1623_);
lean_dec_ref_known(v_a_1619_, 1);
if (v_isShared_1622_ == 0)
{
lean_ctor_set(v___x_1621_, 0, v_e_1623_);
v___x_1625_ = v___x_1621_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v_e_1623_);
v___x_1625_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
return v___x_1625_;
}
}
case 1:
{
lean_object* v_e_1627_; lean_object* v___x_1628_; 
lean_del_object(v___x_1621_);
lean_dec_ref(v_e_1613_);
v_e_1627_ = lean_ctor_get(v_a_1619_, 0);
lean_inc_ref(v_e_1627_);
lean_dec_ref_known(v_a_1619_, 1);
v___x_1628_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1611_, v_post_1612_, v_e_1627_, v_a_1614_, v___y_1615_, v___y_1616_);
return v___x_1628_;
}
default: 
{
lean_object* v_e_x3f_1629_; 
lean_dec_ref(v_post_1612_);
lean_dec_ref(v_pre_1611_);
v_e_x3f_1629_ = lean_ctor_get(v_a_1619_, 0);
lean_inc(v_e_x3f_1629_);
lean_dec_ref_known(v_a_1619_, 1);
if (lean_obj_tag(v_e_x3f_1629_) == 0)
{
lean_object* v___x_1631_; 
if (v_isShared_1622_ == 0)
{
lean_ctor_set(v___x_1621_, 0, v_e_1613_);
v___x_1631_ = v___x_1621_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v_e_1613_);
v___x_1631_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
return v___x_1631_;
}
}
else
{
lean_object* v_val_1633_; lean_object* v___x_1635_; 
lean_dec_ref(v_e_1613_);
v_val_1633_ = lean_ctor_get(v_e_x3f_1629_, 0);
lean_inc(v_val_1633_);
lean_dec_ref_known(v_e_x3f_1629_, 1);
if (v_isShared_1622_ == 0)
{
lean_ctor_set(v___x_1621_, 0, v_val_1633_);
v___x_1635_ = v___x_1621_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_val_1633_);
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
}
else
{
lean_object* v_a_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1645_; 
lean_dec_ref(v_e_1613_);
lean_dec_ref(v_post_1612_);
lean_dec_ref(v_pre_1611_);
v_a_1638_ = lean_ctor_get(v___x_1618_, 0);
v_isSharedCheck_1645_ = !lean_is_exclusive(v___x_1618_);
if (v_isSharedCheck_1645_ == 0)
{
v___x_1640_ = v___x_1618_;
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_a_1638_);
lean_dec(v___x_1618_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___x_1643_; 
if (v_isShared_1641_ == 0)
{
v___x_1643_ = v___x_1640_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v_a_1638_);
v___x_1643_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
return v___x_1643_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_1611_ = stack[0].m_obj;
lean_object* v_post_1612_ = stack[1].m_obj;
lean_object* v_e_1613_ = stack[2].m_obj;
lean_object* v_a_1614_ = stack[3].m_obj;
lean_object* v___y_1615_ = stack[4].m_obj;
lean_object* v___y_1616_ = stack[5].m_obj;
lean_object* v_res_1646_;
v_res_1646_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1611_, v_post_1612_, v_e_1613_, v_a_1614_, v___y_1615_, v___y_1616_);
stack->m_obj
 = v_res_1646_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_1647_, lean_object* v_post_1648_, lean_object* v_e_1649_, lean_object* v_a_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_){
_start:
{
lean_object* v_res_1654_; 
v_res_1654_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1647_, v_post_1648_, v_e_1649_, v_a_1650_, v___y_1651_, v___y_1652_);
lean_dec(v___y_1652_);
lean_dec_ref(v___y_1651_);
lean_dec(v_a_1650_);
return v_res_1654_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_1655_, lean_object* v_post_1656_, lean_object* v_sz_1657_, lean_object* v_i_1658_, lean_object* v_bs_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_){
_start:
{
size_t v_sz_boxed_1664_; size_t v_i_boxed_1665_; lean_object* v_res_1666_; 
v_sz_boxed_1664_ = lean_unbox_usize(v_sz_1657_);
lean_dec(v_sz_1657_);
v_i_boxed_1665_ = lean_unbox_usize(v_i_1658_);
lean_dec(v_i_1658_);
v_res_1666_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1(v_pre_1655_, v_post_1656_, v_sz_boxed_1664_, v_i_boxed_1665_, v_bs_1659_, v___y_1660_, v___y_1661_, v___y_1662_);
lean_dec(v___y_1662_);
lean_dec_ref(v___y_1661_);
lean_dec(v___y_1660_);
return v_res_1666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__4___boxed(lean_object* v_pre_1667_, lean_object* v_post_1668_, lean_object* v_x_1669_, lean_object* v_x_1670_, lean_object* v_x_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_){
_start:
{
lean_object* v_res_1676_; 
v_res_1676_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__4(v_pre_1667_, v_post_1668_, v_x_1669_, v_x_1670_, v_x_1671_, v___y_1672_, v___y_1673_, v___y_1674_);
lean_dec(v___y_1674_);
lean_dec_ref(v___y_1673_);
lean_dec(v___y_1672_);
return v_res_1676_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___boxed(lean_object* v_pre_1677_, lean_object* v_post_1678_, lean_object* v_e_1679_, lean_object* v_a_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_){
_start:
{
lean_object* v_res_1684_; 
v_res_1684_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1677_, v_post_1678_, v_e_1679_, v_a_1680_, v___y_1681_, v___y_1682_);
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1681_);
lean_dec(v_a_1680_);
return v_res_1684_;
}
}
lean_object* l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___lam__0(lean_object* v_00_u03b1_1685_, lean_object* v_x_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_){
_start:
{
lean_object* v___x_1690_; lean_object* v___x_1691_; 
v___x_1690_ = lean_apply_1(v_x_1686_, lean_box(0));
v___x_1691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1691_, 0, v___x_1690_);
return v___x_1691_;
}
}
LEAN_EXPORT void l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1686_ = stack[1].m_obj;
lean_object* v___y_1687_ = stack[2].m_obj;
lean_object* v___y_1688_ = stack[3].m_obj;
lean_object* v_res_1692_;
v_res_1692_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___lam__0(lean_box(0), v_x_1686_, v___y_1687_, v___y_1688_);
stack->m_obj
 = v_res_1692_;
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___lam__0___boxed(lean_object* v_00_u03b1_1693_, lean_object* v_x_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_){
_start:
{
lean_object* v_res_1698_; 
v_res_1698_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___lam__0(v_00_u03b1_1693_, v_x_1694_, v___y_1695_, v___y_1696_);
lean_dec(v___y_1696_);
lean_dec_ref(v___y_1695_);
return v_res_1698_;
}
}
lean_object* l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(lean_object* v_input_1699_, lean_object* v_pre_1700_, lean_object* v_post_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_){
_start:
{
lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v_a_1707_; lean_object* v___x_1708_; 
v___x_1705_ = lean_obj_once(&l_Lean_Core_transform___redArg___closed__2, &l_Lean_Core_transform___redArg___closed__2_once, _init_l_Lean_Core_transform___redArg___closed__2);
v___x_1706_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___lam__0(lean_box(0), v___x_1705_, v___y_1702_, v___y_1703_);
v_a_1707_ = lean_ctor_get(v___x_1706_, 0);
lean_inc(v_a_1707_);
lean_dec_ref(v___x_1706_);
v___x_1708_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1700_, v_post_1701_, v_input_1699_, v_a_1707_, v___y_1702_, v___y_1703_);
if (lean_obj_tag(v___x_1708_) == 0)
{
lean_object* v_a_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1718_; 
v_a_1709_ = lean_ctor_get(v___x_1708_, 0);
lean_inc(v_a_1709_);
lean_dec_ref_known(v___x_1708_, 1);
v___x_1710_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1710_, 0, lean_box(0));
lean_closure_set(v___x_1710_, 1, lean_box(0));
lean_closure_set(v___x_1710_, 2, v_a_1707_);
v___x_1711_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___lam__0(lean_box(0), v___x_1710_, v___y_1702_, v___y_1703_);
v_isSharedCheck_1718_ = !lean_is_exclusive(v___x_1711_);
if (v_isSharedCheck_1718_ == 0)
{
lean_object* v_unused_1719_; 
v_unused_1719_ = lean_ctor_get(v___x_1711_, 0);
lean_dec(v_unused_1719_);
v___x_1713_ = v___x_1711_;
v_isShared_1714_ = v_isSharedCheck_1718_;
goto v_resetjp_1712_;
}
else
{
lean_dec(v___x_1711_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1718_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
lean_object* v___x_1716_; 
if (v_isShared_1714_ == 0)
{
lean_ctor_set(v___x_1713_, 0, v_a_1709_);
v___x_1716_ = v___x_1713_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v_a_1709_);
v___x_1716_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
return v___x_1716_;
}
}
}
else
{
lean_dec(v_a_1707_);
return v___x_1708_;
}
}
}
LEAN_EXPORT void l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_input_1699_ = stack[0].m_obj;
lean_object* v_pre_1700_ = stack[1].m_obj;
lean_object* v_post_1701_ = stack[2].m_obj;
lean_object* v___y_1702_ = stack[3].m_obj;
lean_object* v___y_1703_ = stack[4].m_obj;
lean_object* v_res_1720_;
v_res_1720_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_input_1699_, v_pre_1700_, v_post_1701_, v___y_1702_, v___y_1703_);
stack->m_obj
 = v_res_1720_;
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___boxed(lean_object* v_input_1721_, lean_object* v_pre_1722_, lean_object* v_post_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_){
_start:
{
lean_object* v_res_1727_; 
v_res_1727_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_input_1721_, v_pre_1722_, v_post_1723_, v___y_1724_, v___y_1725_);
lean_dec(v___y_1725_);
lean_dec_ref(v___y_1724_);
return v_res_1727_;
}
}
lean_object* l_Lean_Core_betaReduce(lean_object* v_e_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_){
_start:
{
lean_object* v___f_1734_; lean_object* v___f_1735_; lean_object* v___x_1736_; 
v___f_1734_ = ((lean_object*)(l_Lean_Core_betaReduce___closed__0));
v___f_1735_ = ((lean_object*)(l_Lean_Core_betaReduce___closed__1));
v___x_1736_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_1730_, v___f_1734_, v___f_1735_, v_a_1731_, v_a_1732_);
return v___x_1736_;
}
}
LEAN_EXPORT void l_Lean_Core_betaReduce_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1730_ = stack[0].m_obj;
lean_object* v_a_1731_ = stack[1].m_obj;
lean_object* v_a_1732_ = stack[2].m_obj;
lean_object* v_res_1737_;
v_res_1737_ = l_Lean_Core_betaReduce(v_e_1730_, v_a_1731_, v_a_1732_);
stack->m_obj
 = v_res_1737_;
}
LEAN_EXPORT lean_object* l_Lean_Core_betaReduce___boxed(lean_object* v_e_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_){
_start:
{
lean_object* v_res_1742_; 
v_res_1742_ = l_Lean_Core_betaReduce(v_e_1738_, v_a_1739_, v_a_1740_);
lean_dec(v_a_1740_);
lean_dec_ref(v_a_1739_);
return v_res_1742_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_1743_, lean_object* v_m_1744_, lean_object* v_a_1745_){
_start:
{
lean_object* v___x_1746_; 
v___x_1746_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg(v_m_1744_, v_a_1745_);
return v___x_1746_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_1747_, lean_object* v_m_1748_, lean_object* v_a_1749_){
_start:
{
lean_object* v_res_1750_; 
v_res_1750_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3(v_00_u03b2_1747_, v_m_1748_, v_a_1749_);
lean_dec_ref(v_a_1749_);
lean_dec_ref(v_m_1748_);
return v_res_1750_;
}
}
lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_1751_, lean_object* v_ref_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_){
_start:
{
lean_object* v___x_1756_; 
v___x_1756_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_1752_);
return v___x_1756_;
}
}
LEAN_EXPORT void l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1752_ = stack[1].m_obj;
lean_object* v___y_1753_ = stack[2].m_obj;
lean_object* v___y_1754_ = stack[3].m_obj;
lean_object* v_res_1757_;
v_res_1757_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7(lean_box(0), v_ref_1752_, v___y_1753_, v___y_1754_);
stack->m_obj
 = v_res_1757_;
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1758_, lean_object* v_ref_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_){
_start:
{
lean_object* v_res_1763_; 
v_res_1763_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_1758_, v_ref_1759_, v___y_1760_, v___y_1761_);
lean_dec(v___y_1761_);
lean_dec_ref(v___y_1760_);
return v_res_1763_;
}
}
lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8(lean_object* v_00_u03b1_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_){
_start:
{
lean_object* v___x_1768_; 
v___x_1768_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___redArg();
return v___x_1768_;
}
}
LEAN_EXPORT void l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1765_ = stack[1].m_obj;
lean_object* v___y_1766_ = stack[2].m_obj;
lean_object* v_res_1769_;
v_res_1769_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8(lean_box(0), v___y_1765_, v___y_1766_);
stack->m_obj
 = v_res_1769_;
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___boxed(lean_object* v_00_u03b1_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_){
_start:
{
lean_object* v_res_1774_; 
v_res_1774_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8(v_00_u03b1_1770_, v___y_1771_, v___y_1772_);
lean_dec(v___y_1772_);
lean_dec_ref(v___y_1771_);
return v_res_1774_;
}
}
lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5(lean_object* v_00_u03b1_1775_, lean_object* v_x_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_){
_start:
{
lean_object* v___x_1781_; 
v___x_1781_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___redArg(v_x_1776_, v___y_1777_, v___y_1778_, v___y_1779_);
return v___x_1781_;
}
}
LEAN_EXPORT void l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1776_ = stack[1].m_obj;
lean_object* v___y_1777_ = stack[2].m_obj;
lean_object* v___y_1778_ = stack[3].m_obj;
lean_object* v___y_1779_ = stack[4].m_obj;
lean_object* v_res_1782_;
v_res_1782_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5(lean_box(0), v_x_1776_, v___y_1777_, v___y_1778_, v___y_1779_);
stack->m_obj
 = v_res_1782_;
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b1_1783_, lean_object* v_x_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_){
_start:
{
lean_object* v_res_1789_; 
v_res_1789_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5(v_00_u03b1_1783_, v_x_1784_, v___y_1785_, v___y_1786_, v___y_1787_);
lean_dec(v___y_1787_);
lean_dec_ref(v___y_1786_);
lean_dec(v___y_1785_);
return v_res_1789_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6(lean_object* v_00_u03b2_1790_, lean_object* v_m_1791_, lean_object* v_a_1792_, lean_object* v_b_1793_){
_start:
{
lean_object* v___x_1794_; 
v___x_1794_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6___redArg(v_m_1791_, v_a_1792_, v_b_1793_);
return v___x_1794_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4(lean_object* v_00_u03b2_1795_, lean_object* v_a_1796_, lean_object* v_x_1797_){
_start:
{
lean_object* v___x_1798_; 
v___x_1798_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___redArg(v_a_1796_, v_x_1797_);
return v___x_1798_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4___boxed(lean_object* v_00_u03b2_1799_, lean_object* v_a_1800_, lean_object* v_x_1801_){
_start:
{
lean_object* v_res_1802_; 
v_res_1802_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3_spec__4(v_00_u03b2_1799_, v_a_1800_, v_x_1801_);
lean_dec(v_x_1801_);
lean_dec_ref(v_a_1800_);
return v_res_1802_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10(lean_object* v_00_u03b2_1803_, lean_object* v_a_1804_, lean_object* v_x_1805_){
_start:
{
uint8_t v___x_1806_; 
v___x_1806_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___redArg(v_a_1804_, v_x_1805_);
return v___x_1806_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1804_ = stack[1].m_obj;
lean_object* v_x_1805_ = stack[2].m_obj;
uint8_t v_res_1807_;
v_res_1807_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10(lean_box(0), v_a_1804_, v_x_1805_);
stack->m_num = v_res_1807_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___boxed(lean_object* v_00_u03b2_1808_, lean_object* v_a_1809_, lean_object* v_x_1810_){
_start:
{
uint8_t v_res_1811_; lean_object* v_r_1812_; 
v_res_1811_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10(v_00_u03b2_1808_, v_a_1809_, v_x_1810_);
lean_dec(v_x_1810_);
lean_dec_ref(v_a_1809_);
v_r_1812_ = lean_box(v_res_1811_);
return v_r_1812_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11(lean_object* v_00_u03b2_1813_, lean_object* v_data_1814_){
_start:
{
lean_object* v___x_1815_; 
v___x_1815_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11___redArg(v_data_1814_);
return v___x_1815_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__12(lean_object* v_00_u03b2_1816_, lean_object* v_a_1817_, lean_object* v_b_1818_, lean_object* v_x_1819_){
_start:
{
lean_object* v___x_1820_; 
v___x_1820_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__12___redArg(v_a_1817_, v_b_1818_, v_x_1819_);
return v___x_1820_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12(lean_object* v_00_u03b2_1821_, lean_object* v_i_1822_, lean_object* v_source_1823_, lean_object* v_target_1824_){
_start:
{
lean_object* v___x_1825_; 
v___x_1825_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v_i_1822_, v_source_1823_, v_target_1824_);
return v___x_1825_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13(lean_object* v_00_u03b2_1826_, lean_object* v_x_1827_, lean_object* v_x_1828_){
_start:
{
lean_object* v___x_1829_; 
v___x_1829_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_x_1827_, v_x_1828_);
return v___x_1829_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__0(lean_object* v_toApplicative_1830_, lean_object* v_a_1831_){
_start:
{
lean_object* v_toPure_1832_; lean_object* v___x_1833_; 
v_toPure_1832_ = lean_ctor_get(v_toApplicative_1830_, 1);
lean_inc(v_toPure_1832_);
lean_dec_ref(v_toApplicative_1830_);
v___x_1833_ = lean_apply_2(v_toPure_1832_, lean_box(0), v_a_1831_);
return v___x_1833_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__13(lean_object* v___x_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_){
_start:
{
lean_object* v___x_1840_; 
v___x_1840_ = l_Lean_Core_checkSystem(v___x_1834_, v___y_1837_, v___y_1838_);
return v___x_1840_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__13_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1834_ = stack[0].m_obj;
lean_object* v___y_1835_ = stack[1].m_obj;
lean_object* v___y_1836_ = stack[2].m_obj;
lean_object* v___y_1837_ = stack[3].m_obj;
lean_object* v___y_1838_ = stack[4].m_obj;
lean_object* v_res_1841_;
v_res_1841_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__13(v___x_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_);
stack->m_obj
 = v_res_1841_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__13___boxed(lean_object* v___x_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_){
_start:
{
lean_object* v_res_1848_; 
v_res_1848_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__13(v___x_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_);
lean_dec(v___y_1846_);
lean_dec_ref(v___y_1845_);
lean_dec(v___y_1844_);
lean_dec_ref(v___y_1843_);
return v_res_1848_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14(lean_object* v_inst_1851_, lean_object* v_x_1852_, lean_object* v___x_1853_, lean_object* v___x_1854_, lean_object* v_inst_1855_, lean_object* v___f_1856_, lean_object* v___x_1857_, lean_object* v___x_1858_, lean_object* v_a_1859_, lean_object* v_toBind_1860_, lean_object* v___f_1861_, lean_object* v_toApplicative_1862_, lean_object* v_a_1863_){
_start:
{
if (lean_obj_tag(v_a_1863_) == 0)
{
lean_object* v___f_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_3322__overap_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; 
lean_dec_ref(v_toApplicative_1862_);
v___f_1864_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14___closed__0));
v___x_1865_ = lean_apply_2(v_inst_1851_, lean_box(0), v___f_1864_);
lean_inc_ref(v___x_1854_);
lean_inc_ref(v___x_1853_);
v___x_1866_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonadLift___aux__1___boxed), 10, 9);
lean_closure_set(v___x_1866_, 0, lean_box(0));
lean_closure_set(v___x_1866_, 1, lean_box(0));
lean_closure_set(v___x_1866_, 2, lean_box(0));
lean_closure_set(v___x_1866_, 3, lean_box(0));
lean_closure_set(v___x_1866_, 4, v_x_1852_);
lean_closure_set(v___x_1866_, 5, v___x_1853_);
lean_closure_set(v___x_1866_, 6, v___x_1854_);
lean_closure_set(v___x_1866_, 7, lean_box(0));
lean_closure_set(v___x_1866_, 8, v___x_1865_);
v___x_1867_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonad___aux__13___boxed), 13, 12);
lean_closure_set(v___x_1867_, 0, lean_box(0));
lean_closure_set(v___x_1867_, 1, lean_box(0));
lean_closure_set(v___x_1867_, 2, lean_box(0));
lean_closure_set(v___x_1867_, 3, lean_box(0));
lean_closure_set(v___x_1867_, 4, v_x_1852_);
lean_closure_set(v___x_1867_, 5, v___x_1853_);
lean_closure_set(v___x_1867_, 6, v___x_1854_);
lean_closure_set(v___x_1867_, 7, v_inst_1855_);
lean_closure_set(v___x_1867_, 8, lean_box(0));
lean_closure_set(v___x_1867_, 9, lean_box(0));
lean_closure_set(v___x_1867_, 10, v___x_1866_);
lean_closure_set(v___x_1867_, 11, v___f_1856_);
v___x_3322__overap_1868_ = l_Lean_Meta_withIncRecDepth___redArg(v___x_1857_, v___x_1858_, v___x_1867_);
lean_inc(v_a_1859_);
v___x_1869_ = lean_apply_1(v___x_3322__overap_1868_, v_a_1859_);
v___x_1870_ = lean_apply_4(v_toBind_1860_, lean_box(0), lean_box(0), v___x_1869_, v___f_1861_);
return v___x_1870_;
}
else
{
lean_object* v_val_1871_; lean_object* v_toPure_1872_; lean_object* v___x_1873_; 
lean_dec(v___f_1861_);
lean_dec(v_toBind_1860_);
lean_dec_ref(v___x_1858_);
lean_dec_ref(v___x_1857_);
lean_dec(v___f_1856_);
lean_dec_ref(v_inst_1855_);
lean_dec_ref(v___x_1854_);
lean_dec_ref(v___x_1853_);
lean_dec(v_inst_1851_);
v_val_1871_ = lean_ctor_get(v_a_1863_, 0);
lean_inc(v_val_1871_);
lean_dec_ref_known(v_a_1863_, 1);
v_toPure_1872_ = lean_ctor_get(v_toApplicative_1862_, 1);
lean_inc(v_toPure_1872_);
lean_dec_ref(v_toApplicative_1862_);
v___x_1873_ = lean_apply_2(v_toPure_1872_, lean_box(0), v_val_1871_);
return v___x_1873_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14___boxed(lean_object* v_inst_1874_, lean_object* v_x_1875_, lean_object* v___x_1876_, lean_object* v___x_1877_, lean_object* v_inst_1878_, lean_object* v___f_1879_, lean_object* v___x_1880_, lean_object* v___x_1881_, lean_object* v_a_1882_, lean_object* v_toBind_1883_, lean_object* v___f_1884_, lean_object* v_toApplicative_1885_, lean_object* v_a_1886_){
_start:
{
lean_object* v_res_1887_; 
v_res_1887_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14(v_inst_1874_, v_x_1875_, v___x_1876_, v___x_1877_, v_inst_1878_, v___f_1879_, v___x_1880_, v___x_1881_, v_a_1882_, v_toBind_1883_, v___f_1884_, v_toApplicative_1885_, v_a_1886_);
lean_dec(v_a_1882_);
return v_res_1887_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__1(lean_object* v___x_1888_, lean_object* v___x_1889_, lean_object* v_declName_1890_, lean_object* v_a_1891_, lean_object* v___f_1892_, uint8_t v_nondep_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_){
_start:
{
uint8_t v___x_1896_; lean_object* v___x_3341__overap_1897_; lean_object* v___x_1898_; 
v___x_1896_ = 0;
v___x_3341__overap_1897_ = l_Lean_Meta_withLetDecl___redArg(v___x_1888_, v___x_1889_, v_declName_1890_, v_a_1891_, v_a_1895_, v___f_1892_, v_nondep_1893_, v___x_1896_);
lean_inc(v_a_1894_);
v___x_1898_ = lean_apply_1(v___x_3341__overap_1897_, v_a_1894_);
return v___x_1898_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1888_ = stack[0].m_obj;
lean_object* v___x_1889_ = stack[1].m_obj;
lean_object* v_declName_1890_ = stack[2].m_obj;
lean_object* v_a_1891_ = stack[3].m_obj;
lean_object* v___f_1892_ = stack[4].m_obj;
uint8_t v_nondep_1893_ = stack[5].m_num;
lean_object* v_a_1894_ = stack[6].m_obj;
lean_object* v_a_1895_ = stack[7].m_obj;
lean_object* v_res_1899_;
v_res_1899_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__1(v___x_1888_, v___x_1889_, v_declName_1890_, v_a_1891_, v___f_1892_, v_nondep_1893_, v_a_1894_, v_a_1895_);
stack->m_obj
 = v_res_1899_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__1___boxed(lean_object* v___x_1900_, lean_object* v___x_1901_, lean_object* v_declName_1902_, lean_object* v_a_1903_, lean_object* v___f_1904_, lean_object* v_nondep_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_){
_start:
{
uint8_t v_nondep_3562__boxed_1908_; lean_object* v_res_1909_; 
v_nondep_3562__boxed_1908_ = lean_unbox(v_nondep_1905_);
v_res_1909_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__1(v___x_1900_, v___x_1901_, v_declName_1902_, v_a_1903_, v___f_1904_, v_nondep_3562__boxed_1908_, v_a_1906_, v_a_1907_);
lean_dec(v_a_1906_);
return v_res_1909_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__4(lean_object* v_fvars_1910_, uint8_t v_usedLetOnly_1911_, lean_object* v_inst_1912_, lean_object* v_toBind_1913_, lean_object* v___f_1914_, lean_object* v_a_1915_){
_start:
{
uint8_t v___x_1916_; uint8_t v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; 
v___x_1916_ = 0;
v___x_1917_ = 1;
v___x_1918_ = lean_box(v_usedLetOnly_1911_);
v___x_1919_ = lean_box(v___x_1916_);
v___x_1920_ = lean_box(v___x_1917_);
v___x_1921_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLetFVars___boxed), 10, 5);
lean_closure_set(v___x_1921_, 0, v_fvars_1910_);
lean_closure_set(v___x_1921_, 1, v_a_1915_);
lean_closure_set(v___x_1921_, 2, v___x_1918_);
lean_closure_set(v___x_1921_, 3, v___x_1919_);
lean_closure_set(v___x_1921_, 4, v___x_1920_);
v___x_1922_ = lean_apply_2(v_inst_1912_, lean_box(0), v___x_1921_);
v___x_1923_ = lean_apply_4(v_toBind_1913_, lean_box(0), lean_box(0), v___x_1922_, v___f_1914_);
return v___x_1923_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_1910_ = stack[0].m_obj;
uint8_t v_usedLetOnly_1911_ = stack[1].m_num;
lean_object* v_inst_1912_ = stack[2].m_obj;
lean_object* v_toBind_1913_ = stack[3].m_obj;
lean_object* v___f_1914_ = stack[4].m_obj;
lean_object* v_a_1915_ = stack[5].m_obj;
lean_object* v_res_1924_;
v_res_1924_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__4(v_fvars_1910_, v_usedLetOnly_1911_, v_inst_1912_, v_toBind_1913_, v___f_1914_, v_a_1915_);
stack->m_obj
 = v_res_1924_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__4___boxed(lean_object* v_fvars_1925_, lean_object* v_usedLetOnly_1926_, lean_object* v_inst_1927_, lean_object* v_toBind_1928_, lean_object* v___f_1929_, lean_object* v_a_1930_){
_start:
{
uint8_t v_usedLetOnly_boxed_1931_; lean_object* v_res_1932_; 
v_usedLetOnly_boxed_1931_ = lean_unbox(v_usedLetOnly_1926_);
v_res_1932_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__4(v_fvars_1925_, v_usedLetOnly_boxed_1931_, v_inst_1927_, v_toBind_1928_, v___f_1929_, v_a_1930_);
return v_res_1932_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__3(lean_object* v_fvars_1933_, uint8_t v_usedLetOnly_1934_, lean_object* v_inst_1935_, lean_object* v_toBind_1936_, lean_object* v___f_1937_, lean_object* v_a_1938_){
_start:
{
uint8_t v___x_1939_; uint8_t v___x_1940_; uint8_t v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; 
v___x_1939_ = 0;
v___x_1940_ = 1;
v___x_1941_ = 1;
v___x_1942_ = lean_box(v___x_1939_);
v___x_1943_ = lean_box(v_usedLetOnly_1934_);
v___x_1944_ = lean_box(v___x_1939_);
v___x_1945_ = lean_box(v___x_1940_);
v___x_1946_ = lean_box(v___x_1941_);
v___x_1947_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(v___x_1947_, 0, v_fvars_1933_);
lean_closure_set(v___x_1947_, 1, v_a_1938_);
lean_closure_set(v___x_1947_, 2, v___x_1942_);
lean_closure_set(v___x_1947_, 3, v___x_1943_);
lean_closure_set(v___x_1947_, 4, v___x_1944_);
lean_closure_set(v___x_1947_, 5, v___x_1945_);
lean_closure_set(v___x_1947_, 6, v___x_1946_);
v___x_1948_ = lean_apply_2(v_inst_1935_, lean_box(0), v___x_1947_);
v___x_1949_ = lean_apply_4(v_toBind_1936_, lean_box(0), lean_box(0), v___x_1948_, v___f_1937_);
return v___x_1949_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_1933_ = stack[0].m_obj;
uint8_t v_usedLetOnly_1934_ = stack[1].m_num;
lean_object* v_inst_1935_ = stack[2].m_obj;
lean_object* v_toBind_1936_ = stack[3].m_obj;
lean_object* v___f_1937_ = stack[4].m_obj;
lean_object* v_a_1938_ = stack[5].m_obj;
lean_object* v_res_1950_;
v_res_1950_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__3(v_fvars_1933_, v_usedLetOnly_1934_, v_inst_1935_, v_toBind_1936_, v___f_1937_, v_a_1938_);
stack->m_obj
 = v_res_1950_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__3___boxed(lean_object* v_fvars_1951_, lean_object* v_usedLetOnly_1952_, lean_object* v_inst_1953_, lean_object* v_toBind_1954_, lean_object* v___f_1955_, lean_object* v_a_1956_){
_start:
{
uint8_t v_usedLetOnly_boxed_1957_; lean_object* v_res_1958_; 
v_usedLetOnly_boxed_1957_ = lean_unbox(v_usedLetOnly_1952_);
v_res_1958_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__3(v_fvars_1951_, v_usedLetOnly_boxed_1957_, v_inst_1953_, v_toBind_1954_, v___f_1955_, v_a_1956_);
return v_res_1958_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1(lean_object* v___x_1959_, lean_object* v___x_1960_, lean_object* v_binderName_1961_, uint8_t v_binderInfo_1962_, lean_object* v___f_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_){
_start:
{
uint8_t v___x_1966_; lean_object* v___x_3399__overap_1967_; lean_object* v___x_1968_; 
v___x_1966_ = 0;
v___x_3399__overap_1967_ = l_Lean_Meta_withLocalDecl___redArg(v___x_1959_, v___x_1960_, v_binderName_1961_, v_binderInfo_1962_, v_a_1965_, v___f_1963_, v___x_1966_);
lean_inc(v_a_1964_);
v___x_1968_ = lean_apply_1(v___x_3399__overap_1967_, v_a_1964_);
return v___x_1968_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1959_ = stack[0].m_obj;
lean_object* v___x_1960_ = stack[1].m_obj;
lean_object* v_binderName_1961_ = stack[2].m_obj;
uint8_t v_binderInfo_1962_ = stack[3].m_num;
lean_object* v___f_1963_ = stack[4].m_obj;
lean_object* v_a_1964_ = stack[5].m_obj;
lean_object* v_a_1965_ = stack[6].m_obj;
lean_object* v_res_1969_;
v_res_1969_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1(v___x_1959_, v___x_1960_, v_binderName_1961_, v_binderInfo_1962_, v___f_1963_, v_a_1964_, v_a_1965_);
stack->m_obj
 = v_res_1969_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1___boxed(lean_object* v___x_1970_, lean_object* v___x_1971_, lean_object* v_binderName_1972_, lean_object* v_binderInfo_1973_, lean_object* v___f_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_){
_start:
{
uint8_t v_binderInfo_3669__boxed_1977_; lean_object* v_res_1978_; 
v_binderInfo_3669__boxed_1977_ = lean_unbox(v_binderInfo_1973_);
v_res_1978_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1(v___x_1970_, v___x_1971_, v_binderName_1972_, v_binderInfo_3669__boxed_1977_, v___f_1974_, v_a_1975_, v_a_1976_);
lean_dec(v_a_1975_);
return v_res_1978_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__3(lean_object* v_fvars_1979_, uint8_t v_usedLetOnly_1980_, lean_object* v_inst_1981_, lean_object* v_toBind_1982_, lean_object* v___f_1983_, lean_object* v_a_1984_){
_start:
{
uint8_t v___x_1985_; uint8_t v___x_1986_; uint8_t v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; 
v___x_1985_ = 0;
v___x_1986_ = 1;
v___x_1987_ = 1;
v___x_1988_ = lean_box(v___x_1985_);
v___x_1989_ = lean_box(v_usedLetOnly_1980_);
v___x_1990_ = lean_box(v___x_1986_);
v___x_1991_ = lean_box(v___x_1987_);
v___x_1992_ = lean_alloc_closure((void*)(l_Lean_Meta_mkForallFVars___boxed), 11, 6);
lean_closure_set(v___x_1992_, 0, v_fvars_1979_);
lean_closure_set(v___x_1992_, 1, v_a_1984_);
lean_closure_set(v___x_1992_, 2, v___x_1988_);
lean_closure_set(v___x_1992_, 3, v___x_1989_);
lean_closure_set(v___x_1992_, 4, v___x_1990_);
lean_closure_set(v___x_1992_, 5, v___x_1991_);
v___x_1993_ = lean_apply_2(v_inst_1981_, lean_box(0), v___x_1992_);
v___x_1994_ = lean_apply_4(v_toBind_1982_, lean_box(0), lean_box(0), v___x_1993_, v___f_1983_);
return v___x_1994_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_1979_ = stack[0].m_obj;
uint8_t v_usedLetOnly_1980_ = stack[1].m_num;
lean_object* v_inst_1981_ = stack[2].m_obj;
lean_object* v_toBind_1982_ = stack[3].m_obj;
lean_object* v___f_1983_ = stack[4].m_obj;
lean_object* v_a_1984_ = stack[5].m_obj;
lean_object* v_res_1995_;
v_res_1995_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__3(v_fvars_1979_, v_usedLetOnly_1980_, v_inst_1981_, v_toBind_1982_, v___f_1983_, v_a_1984_);
stack->m_obj
 = v_res_1995_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__3___boxed(lean_object* v_fvars_1996_, lean_object* v_usedLetOnly_1997_, lean_object* v_inst_1998_, lean_object* v_toBind_1999_, lean_object* v___f_2000_, lean_object* v_a_2001_){
_start:
{
uint8_t v_usedLetOnly_boxed_2002_; lean_object* v_res_2003_; 
v_usedLetOnly_boxed_2002_ = lean_unbox(v_usedLetOnly_1997_);
v_res_2003_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__3(v_fvars_1996_, v_usedLetOnly_boxed_2002_, v_inst_1998_, v_toBind_1999_, v___f_2000_, v_a_2001_);
return v_res_2003_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__7(lean_object* v___f_2004_, lean_object* v___y_2005_, lean_object* v_a_2006_){
_start:
{
lean_object* v___x_2007_; 
lean_inc(v___y_2005_);
v___x_2007_ = lean_apply_2(v___f_2004_, v_a_2006_, v___y_2005_);
return v___x_2007_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__7___boxed(lean_object* v___f_2008_, lean_object* v___y_2009_, lean_object* v_a_2010_){
_start:
{
lean_object* v_res_2011_; 
v_res_2011_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__7(v___f_2008_, v___y_2009_, v_a_2010_);
lean_dec(v___y_2009_);
return v_res_2011_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1(lean_object* v_toApplicative_2012_, lean_object* v_acc_2013_, lean_object* v_next_2014_, lean_object* v_a_2015_){
_start:
{
lean_object* v_toPure_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; 
v_toPure_2016_ = lean_ctor_get(v_toApplicative_2012_, 1);
lean_inc(v_toPure_2016_);
lean_dec_ref(v_toApplicative_2012_);
v___x_2017_ = lean_array_fset(v_acc_2013_, v_next_2014_, v_a_2015_);
v___x_2018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2018_, 0, v___x_2017_);
v___x_2019_ = lean_apply_2(v_toPure_2016_, lean_box(0), v___x_2018_);
return v___x_2019_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1___boxed(lean_object* v_toApplicative_2020_, lean_object* v_acc_2021_, lean_object* v_next_2022_, lean_object* v_a_2023_){
_start:
{
lean_object* v_res_2024_; 
v_res_2024_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1(v_toApplicative_2020_, v_acc_2021_, v_next_2022_, v_a_2023_);
lean_dec(v_next_2022_);
return v_res_2024_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__2(lean_object* v_toApplicative_2025_, lean_object* v_next_2026_, lean_object* v_G_2027_, lean_object* v___y_2028_, lean_object* v_a_2029_){
_start:
{
if (lean_obj_tag(v_a_2029_) == 0)
{
lean_object* v_a_2030_; lean_object* v_toPure_2031_; lean_object* v___x_2032_; 
lean_dec(v_G_2027_);
v_a_2030_ = lean_ctor_get(v_a_2029_, 0);
lean_inc(v_a_2030_);
lean_dec_ref_known(v_a_2029_, 1);
v_toPure_2031_ = lean_ctor_get(v_toApplicative_2025_, 1);
lean_inc(v_toPure_2031_);
lean_dec_ref(v_toApplicative_2025_);
v___x_2032_ = lean_apply_2(v_toPure_2031_, lean_box(0), v_a_2030_);
return v___x_2032_;
}
else
{
lean_object* v_a_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; 
lean_dec_ref(v_toApplicative_2025_);
v_a_2033_ = lean_ctor_get(v_a_2029_, 0);
lean_inc(v_a_2033_);
lean_dec_ref_known(v_a_2029_, 1);
v___x_2034_ = lean_unsigned_to_nat(1u);
v___x_2035_ = lean_nat_add(v_next_2026_, v___x_2034_);
lean_inc(v___y_2028_);
v___x_2036_ = lean_apply_5(v_G_2027_, v___x_2035_, v_a_2033_, lean_box(0), lean_box(0), v___y_2028_);
return v___x_2036_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__2___boxed(lean_object* v_toApplicative_2037_, lean_object* v_next_2038_, lean_object* v_G_2039_, lean_object* v___y_2040_, lean_object* v_a_2041_){
_start:
{
lean_object* v_res_2042_; 
v_res_2042_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__2(v_toApplicative_2037_, v_next_2038_, v_G_2039_, v___y_2040_, v_a_2041_);
lean_dec(v___y_2040_);
lean_dec(v_next_2038_);
return v_res_2042_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5(lean_object* v_f_2043_, lean_object* v_inst_2044_, lean_object* v_inst_2045_, lean_object* v_inst_2046_, lean_object* v_pre_2047_, lean_object* v_post_2048_, uint8_t v_usedLetOnly_2049_, uint8_t v_skipConstInApp_2050_, uint8_t v_skipInstances_2051_, lean_object* v_x_2052_, lean_object* v_x_2053_, lean_object* v___y_2054_, lean_object* v_a_2055_){
_start:
{
lean_object* v___x_2056_; lean_object* v___x_2057_; 
v___x_2056_ = l_Lean_mkAppN(v_f_2043_, v_a_2055_);
v___x_2057_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2044_, v_inst_2045_, v_inst_2046_, v_pre_2047_, v_post_2048_, v_usedLetOnly_2049_, v_skipConstInApp_2050_, v_skipInstances_2051_, v_x_2052_, v_x_2053_, v___x_2056_, v___y_2054_);
return v___x_2057_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2043_ = stack[0].m_obj;
lean_object* v_inst_2044_ = stack[1].m_obj;
lean_object* v_inst_2045_ = stack[2].m_obj;
lean_object* v_inst_2046_ = stack[3].m_obj;
lean_object* v_pre_2047_ = stack[4].m_obj;
lean_object* v_post_2048_ = stack[5].m_obj;
uint8_t v_usedLetOnly_2049_ = stack[6].m_num;
uint8_t v_skipConstInApp_2050_ = stack[7].m_num;
uint8_t v_skipInstances_2051_ = stack[8].m_num;
lean_object* v_x_2052_ = stack[9].m_obj;
lean_object* v_x_2053_ = stack[10].m_obj;
lean_object* v___y_2054_ = stack[11].m_obj;
lean_object* v_a_2055_ = stack[12].m_obj;
lean_object* v_res_2058_;
v_res_2058_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5(v_f_2043_, v_inst_2044_, v_inst_2045_, v_inst_2046_, v_pre_2047_, v_post_2048_, v_usedLetOnly_2049_, v_skipConstInApp_2050_, v_skipInstances_2051_, v_x_2052_, v_x_2053_, v___y_2054_, v_a_2055_);
stack->m_obj
 = v_res_2058_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5___boxed(lean_object* v_f_2059_, lean_object* v_inst_2060_, lean_object* v_inst_2061_, lean_object* v_inst_2062_, lean_object* v_pre_2063_, lean_object* v_post_2064_, lean_object* v_usedLetOnly_2065_, lean_object* v_skipConstInApp_2066_, lean_object* v_skipInstances_2067_, lean_object* v_x_2068_, lean_object* v_x_2069_, lean_object* v___y_2070_, lean_object* v_a_2071_){
_start:
{
uint8_t v_usedLetOnly_boxed_2072_; uint8_t v_skipConstInApp_boxed_2073_; uint8_t v_skipInstances_boxed_2074_; lean_object* v_res_2075_; 
v_usedLetOnly_boxed_2072_ = lean_unbox(v_usedLetOnly_2065_);
v_skipConstInApp_boxed_2073_ = lean_unbox(v_skipConstInApp_2066_);
v_skipInstances_boxed_2074_ = lean_unbox(v_skipInstances_2067_);
v_res_2075_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5(v_f_2059_, v_inst_2060_, v_inst_2061_, v_inst_2062_, v_pre_2063_, v_post_2064_, v_usedLetOnly_boxed_2072_, v_skipConstInApp_boxed_2073_, v_skipInstances_boxed_2074_, v_x_2068_, v_x_2069_, v___y_2070_, v_a_2071_);
lean_dec_ref(v_a_2071_);
lean_dec(v___y_2070_);
return v_res_2075_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___boxed(lean_object* v_inst_2076_, lean_object* v_inst_2077_, lean_object* v_inst_2078_, lean_object* v_pre_2079_, lean_object* v_post_2080_, lean_object* v_usedLetOnly_2081_, lean_object* v_skipConstInApp_2082_, lean_object* v_skipInstances_2083_, lean_object* v_x_2084_, lean_object* v_x_2085_, lean_object* v_e_2086_, lean_object* v_a_2087_){
_start:
{
uint8_t v_usedLetOnly_boxed_2088_; uint8_t v_skipConstInApp_boxed_2089_; uint8_t v_skipInstances_boxed_2090_; lean_object* v_res_2091_; 
v_usedLetOnly_boxed_2088_ = lean_unbox(v_usedLetOnly_2081_);
v_skipConstInApp_boxed_2089_ = lean_unbox(v_skipConstInApp_2082_);
v_skipInstances_boxed_2090_ = lean_unbox(v_skipInstances_2083_);
v_res_2091_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2076_, v_inst_2077_, v_inst_2078_, v_pre_2079_, v_post_2080_, v_usedLetOnly_boxed_2088_, v_skipConstInApp_boxed_2089_, v_skipInstances_boxed_2090_, v_x_2084_, v_x_2085_, v_e_2086_, v_a_2087_);
lean_dec(v_a_2087_);
return v_res_2091_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__4(lean_object* v___x_2092_, lean_object* v_toApplicative_2093_, lean_object* v_toBind_2094_, lean_object* v___f_2095_, lean_object* v_paramInfo_2096_, lean_object* v_inst_2097_, lean_object* v_inst_2098_, lean_object* v_inst_2099_, lean_object* v_pre_2100_, lean_object* v_post_2101_, uint8_t v_usedLetOnly_2102_, uint8_t v_skipConstInApp_2103_, uint8_t v_skipInstances_2104_, lean_object* v_x_2105_, lean_object* v_x_2106_, lean_object* v_next_2107_, lean_object* v_acc_2108_, lean_object* v_h_2109_, lean_object* v_G_2110_, lean_object* v___y_2111_){
_start:
{
uint8_t v___x_2112_; 
v___x_2112_ = lean_nat_dec_lt(v_next_2107_, v___x_2092_);
if (v___x_2112_ == 0)
{
lean_object* v_toPure_2113_; lean_object* v___x_2114_; 
lean_dec(v_G_2110_);
lean_dec(v_next_2107_);
lean_dec(v_x_2106_);
lean_dec(v_post_2101_);
lean_dec(v_pre_2100_);
lean_dec_ref(v_inst_2099_);
lean_dec(v_inst_2098_);
lean_dec_ref(v_inst_2097_);
lean_dec(v___f_2095_);
lean_dec(v_toBind_2094_);
v_toPure_2113_ = lean_ctor_get(v_toApplicative_2093_, 1);
lean_inc(v_toPure_2113_);
lean_dec_ref(v_toApplicative_2093_);
v___x_2114_ = lean_apply_2(v_toPure_2113_, lean_box(0), v_acc_2108_);
return v___x_2114_;
}
else
{
lean_object* v___f_2115_; lean_object* v___y_2117_; lean_object* v___x_2120_; lean_object* v___x_2121_; uint8_t v___x_2122_; 
lean_inc(v___y_2111_);
lean_inc(v_next_2107_);
lean_inc_ref(v_toApplicative_2093_);
v___f_2115_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__2___boxed), 5, 4);
lean_closure_set(v___f_2115_, 0, v_toApplicative_2093_);
lean_closure_set(v___f_2115_, 1, v_next_2107_);
lean_closure_set(v___f_2115_, 2, v_G_2110_);
lean_closure_set(v___f_2115_, 3, v___y_2111_);
v___x_2120_ = lean_array_fget_borrowed(v_acc_2108_, v_next_2107_);
v___x_2121_ = lean_array_get_size(v_paramInfo_2096_);
v___x_2122_ = lean_nat_dec_lt(v_next_2107_, v___x_2121_);
if (v___x_2122_ == 0)
{
lean_object* v___f_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; 
lean_inc(v___x_2120_);
v___f_2123_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2123_, 0, v_toApplicative_2093_);
lean_closure_set(v___f_2123_, 1, v_acc_2108_);
lean_closure_set(v___f_2123_, 2, v_next_2107_);
v___x_2124_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2097_, v_inst_2098_, v_inst_2099_, v_pre_2100_, v_post_2101_, v_usedLetOnly_2102_, v_skipConstInApp_2103_, v_skipInstances_2104_, v_x_2105_, v_x_2106_, v___x_2120_, v___y_2111_);
lean_inc(v_toBind_2094_);
v___x_2125_ = lean_apply_4(v_toBind_2094_, lean_box(0), lean_box(0), v___x_2124_, v___f_2123_);
v___y_2117_ = v___x_2125_;
goto v___jp_2116_;
}
else
{
lean_object* v___x_2126_; uint8_t v_isInstance_2127_; 
v___x_2126_ = lean_array_fget_borrowed(v_paramInfo_2096_, v_next_2107_);
v_isInstance_2127_ = lean_ctor_get_uint8(v___x_2126_, sizeof(void*)*1 + 4);
if (v_isInstance_2127_ == 0)
{
lean_object* v___f_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; 
lean_inc(v___x_2120_);
v___f_2128_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2128_, 0, v_toApplicative_2093_);
lean_closure_set(v___f_2128_, 1, v_acc_2108_);
lean_closure_set(v___f_2128_, 2, v_next_2107_);
v___x_2129_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2097_, v_inst_2098_, v_inst_2099_, v_pre_2100_, v_post_2101_, v_usedLetOnly_2102_, v_skipConstInApp_2103_, v_skipInstances_2104_, v_x_2105_, v_x_2106_, v___x_2120_, v___y_2111_);
lean_inc(v_toBind_2094_);
v___x_2130_ = lean_apply_4(v_toBind_2094_, lean_box(0), lean_box(0), v___x_2129_, v___f_2128_);
v___y_2117_ = v___x_2130_;
goto v___jp_2116_;
}
else
{
lean_object* v_toPure_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; 
lean_dec(v_next_2107_);
lean_dec(v_x_2106_);
lean_dec(v_post_2101_);
lean_dec(v_pre_2100_);
lean_dec_ref(v_inst_2099_);
lean_dec(v_inst_2098_);
lean_dec_ref(v_inst_2097_);
v_toPure_2131_ = lean_ctor_get(v_toApplicative_2093_, 1);
lean_inc(v_toPure_2131_);
lean_dec_ref(v_toApplicative_2093_);
v___x_2132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2132_, 0, v_acc_2108_);
v___x_2133_ = lean_apply_2(v_toPure_2131_, lean_box(0), v___x_2132_);
v___y_2117_ = v___x_2133_;
goto v___jp_2116_;
}
}
v___jp_2116_:
{
lean_object* v___x_2118_; lean_object* v___x_2119_; 
lean_inc(v_toBind_2094_);
v___x_2118_ = lean_apply_4(v_toBind_2094_, lean_box(0), lean_box(0), v___y_2117_, v___f_2095_);
v___x_2119_ = lean_apply_4(v_toBind_2094_, lean_box(0), lean_box(0), v___x_2118_, v___f_2115_);
return v___x_2119_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2092_ = stack[0].m_obj;
lean_object* v_toApplicative_2093_ = stack[1].m_obj;
lean_object* v_toBind_2094_ = stack[2].m_obj;
lean_object* v___f_2095_ = stack[3].m_obj;
lean_object* v_paramInfo_2096_ = stack[4].m_obj;
lean_object* v_inst_2097_ = stack[5].m_obj;
lean_object* v_inst_2098_ = stack[6].m_obj;
lean_object* v_inst_2099_ = stack[7].m_obj;
lean_object* v_pre_2100_ = stack[8].m_obj;
lean_object* v_post_2101_ = stack[9].m_obj;
uint8_t v_usedLetOnly_2102_ = stack[10].m_num;
uint8_t v_skipConstInApp_2103_ = stack[11].m_num;
uint8_t v_skipInstances_2104_ = stack[12].m_num;
lean_object* v_x_2105_ = stack[13].m_obj;
lean_object* v_x_2106_ = stack[14].m_obj;
lean_object* v_next_2107_ = stack[15].m_obj;
lean_object* v_acc_2108_ = stack[16].m_obj;
lean_object* v_G_2110_ = stack[18].m_obj;
lean_object* v___y_2111_ = stack[19].m_obj;
lean_object* v_res_2134_;
v_res_2134_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__4(v___x_2092_, v_toApplicative_2093_, v_toBind_2094_, v___f_2095_, v_paramInfo_2096_, v_inst_2097_, v_inst_2098_, v_inst_2099_, v_pre_2100_, v_post_2101_, v_usedLetOnly_2102_, v_skipConstInApp_2103_, v_skipInstances_2104_, v_x_2105_, v_x_2106_, v_next_2107_, v_acc_2108_, lean_box(0), v_G_2110_, v___y_2111_);
stack->m_obj
 = v_res_2134_;
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
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__3(lean_object* v___x_2159_, lean_object* v_toApplicative_2160_, lean_object* v_toBind_2161_, lean_object* v___f_2162_, lean_object* v_inst_2163_, lean_object* v_inst_2164_, lean_object* v_inst_2165_, lean_object* v_pre_2166_, lean_object* v_post_2167_, uint8_t v_usedLetOnly_2168_, uint8_t v_skipConstInApp_2169_, uint8_t v_skipInstances_2170_, lean_object* v_x_2171_, lean_object* v_x_2172_, lean_object* v_args_2173_, lean_object* v___y_2174_, lean_object* v___f_2175_, lean_object* v_a_2176_){
_start:
{
lean_object* v_paramInfo_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___f_2182_; lean_object* v___x_3159__overap_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; 
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
v___x_3159__overap_2183_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_2182_, v___x_2178_, v_args_2173_, lean_box(0));
lean_inc(v___y_2174_);
v___x_2184_ = lean_apply_1(v___x_3159__overap_2183_, v___y_2174_);
v___x_2185_ = lean_apply_4(v_toBind_2161_, lean_box(0), lean_box(0), v___x_2184_, v___f_2175_);
return v___x_2185_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2159_ = stack[0].m_obj;
lean_object* v_toApplicative_2160_ = stack[1].m_obj;
lean_object* v_toBind_2161_ = stack[2].m_obj;
lean_object* v___f_2162_ = stack[3].m_obj;
lean_object* v_inst_2163_ = stack[4].m_obj;
lean_object* v_inst_2164_ = stack[5].m_obj;
lean_object* v_inst_2165_ = stack[6].m_obj;
lean_object* v_pre_2166_ = stack[7].m_obj;
lean_object* v_post_2167_ = stack[8].m_obj;
uint8_t v_usedLetOnly_2168_ = stack[9].m_num;
uint8_t v_skipConstInApp_2169_ = stack[10].m_num;
uint8_t v_skipInstances_2170_ = stack[11].m_num;
lean_object* v_x_2171_ = stack[12].m_obj;
lean_object* v_x_2172_ = stack[13].m_obj;
lean_object* v_args_2173_ = stack[14].m_obj;
lean_object* v___y_2174_ = stack[15].m_obj;
lean_object* v___f_2175_ = stack[16].m_obj;
lean_object* v_a_2176_ = stack[17].m_obj;
lean_object* v_res_2186_;
v_res_2186_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__3(v___x_2159_, v_toApplicative_2160_, v_toBind_2161_, v___f_2162_, v_inst_2163_, v_inst_2164_, v_inst_2165_, v_pre_2166_, v_post_2167_, v_usedLetOnly_2168_, v_skipConstInApp_2169_, v_skipInstances_2170_, v_x_2171_, v_x_2172_, v_args_2173_, v___y_2174_, v___f_2175_, v_a_2176_);
stack->m_obj
 = v_res_2186_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__3___boxed(lean_object** _args){
lean_object* v___x_2187_ = _args[0];
lean_object* v_toApplicative_2188_ = _args[1];
lean_object* v_toBind_2189_ = _args[2];
lean_object* v___f_2190_ = _args[3];
lean_object* v_inst_2191_ = _args[4];
lean_object* v_inst_2192_ = _args[5];
lean_object* v_inst_2193_ = _args[6];
lean_object* v_pre_2194_ = _args[7];
lean_object* v_post_2195_ = _args[8];
lean_object* v_usedLetOnly_2196_ = _args[9];
lean_object* v_skipConstInApp_2197_ = _args[10];
lean_object* v_skipInstances_2198_ = _args[11];
lean_object* v_x_2199_ = _args[12];
lean_object* v_x_2200_ = _args[13];
lean_object* v_args_2201_ = _args[14];
lean_object* v___y_2202_ = _args[15];
lean_object* v___f_2203_ = _args[16];
lean_object* v_a_2204_ = _args[17];
_start:
{
uint8_t v_usedLetOnly_boxed_2205_; uint8_t v_skipConstInApp_boxed_2206_; uint8_t v_skipInstances_boxed_2207_; lean_object* v_res_2208_; 
v_usedLetOnly_boxed_2205_ = lean_unbox(v_usedLetOnly_2196_);
v_skipConstInApp_boxed_2206_ = lean_unbox(v_skipConstInApp_2197_);
v_skipInstances_boxed_2207_ = lean_unbox(v_skipInstances_2198_);
v_res_2208_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__3(v___x_2187_, v_toApplicative_2188_, v_toBind_2189_, v___f_2190_, v_inst_2191_, v_inst_2192_, v_inst_2193_, v_pre_2194_, v_post_2195_, v_usedLetOnly_boxed_2205_, v_skipConstInApp_boxed_2206_, v_skipInstances_boxed_2207_, v_x_2199_, v_x_2200_, v_args_2201_, v___y_2202_, v___f_2203_, v_a_2204_);
lean_dec(v___y_2202_);
return v_res_2208_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__6(uint8_t v_skipInstances_2209_, lean_object* v_inst_2210_, lean_object* v_inst_2211_, lean_object* v_inst_2212_, lean_object* v_pre_2213_, lean_object* v_post_2214_, uint8_t v_usedLetOnly_2215_, uint8_t v_skipConstInApp_2216_, lean_object* v_x_2217_, lean_object* v_x_2218_, lean_object* v_args_2219_, lean_object* v___x_2220_, lean_object* v_toBind_2221_, lean_object* v_toApplicative_2222_, lean_object* v___f_2223_, lean_object* v_f_2224_, lean_object* v___y_2225_){
_start:
{
if (v_skipInstances_2209_ == 0)
{
lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___f_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; size_t v_sz_2234_; size_t v___x_2235_; lean_object* v___x_3172__overap_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; 
lean_dec(v___f_2223_);
lean_dec_ref(v_toApplicative_2222_);
v___x_2226_ = lean_box(v_usedLetOnly_2215_);
v___x_2227_ = lean_box(v_skipConstInApp_2216_);
v___x_2228_ = lean_box(v_skipInstances_2209_);
lean_inc_n(v___y_2225_, 2);
lean_inc(v_x_2218_);
lean_inc(v_post_2214_);
lean_inc(v_pre_2213_);
lean_inc_ref(v_inst_2212_);
lean_inc(v_inst_2211_);
lean_inc_ref(v_inst_2210_);
v___f_2229_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5___boxed), 13, 12);
lean_closure_set(v___f_2229_, 0, v_f_2224_);
lean_closure_set(v___f_2229_, 1, v_inst_2210_);
lean_closure_set(v___f_2229_, 2, v_inst_2211_);
lean_closure_set(v___f_2229_, 3, v_inst_2212_);
lean_closure_set(v___f_2229_, 4, v_pre_2213_);
lean_closure_set(v___f_2229_, 5, v_post_2214_);
lean_closure_set(v___f_2229_, 6, v___x_2226_);
lean_closure_set(v___f_2229_, 7, v___x_2227_);
lean_closure_set(v___f_2229_, 8, v___x_2228_);
lean_closure_set(v___f_2229_, 9, v_x_2217_);
lean_closure_set(v___f_2229_, 10, v_x_2218_);
lean_closure_set(v___f_2229_, 11, v___y_2225_);
v___x_2230_ = lean_box(v_usedLetOnly_2215_);
v___x_2231_ = lean_box(v_skipConstInApp_2216_);
v___x_2232_ = lean_box(v_skipInstances_2209_);
v___x_2233_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___boxed), 12, 10);
lean_closure_set(v___x_2233_, 0, v_inst_2210_);
lean_closure_set(v___x_2233_, 1, v_inst_2211_);
lean_closure_set(v___x_2233_, 2, v_inst_2212_);
lean_closure_set(v___x_2233_, 3, v_pre_2213_);
lean_closure_set(v___x_2233_, 4, v_post_2214_);
lean_closure_set(v___x_2233_, 5, v___x_2230_);
lean_closure_set(v___x_2233_, 6, v___x_2231_);
lean_closure_set(v___x_2233_, 7, v___x_2232_);
lean_closure_set(v___x_2233_, 8, v_x_2217_);
lean_closure_set(v___x_2233_, 9, v_x_2218_);
v_sz_2234_ = lean_array_size(v_args_2219_);
v___x_2235_ = ((size_t)0ULL);
v___x_3172__overap_2236_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2220_, v___x_2233_, v_sz_2234_, v___x_2235_, v_args_2219_);
v___x_2237_ = lean_apply_1(v___x_3172__overap_2236_, v___y_2225_);
v___x_2238_ = lean_apply_4(v_toBind_2221_, lean_box(0), lean_box(0), v___x_2237_, v___f_2229_);
return v___x_2238_;
}
else
{
lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___f_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___f_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; 
lean_dec_ref(v___x_2220_);
v___x_2239_ = lean_box(v_usedLetOnly_2215_);
v___x_2240_ = lean_box(v_skipConstInApp_2216_);
v___x_2241_ = lean_box(v_skipInstances_2209_);
lean_inc_n(v___y_2225_, 2);
lean_inc(v_x_2218_);
lean_inc(v_post_2214_);
lean_inc(v_pre_2213_);
lean_inc_ref(v_inst_2212_);
lean_inc_n(v_inst_2211_, 2);
lean_inc_ref(v_inst_2210_);
lean_inc_ref(v_f_2224_);
v___f_2242_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5___boxed), 13, 12);
lean_closure_set(v___f_2242_, 0, v_f_2224_);
lean_closure_set(v___f_2242_, 1, v_inst_2210_);
lean_closure_set(v___f_2242_, 2, v_inst_2211_);
lean_closure_set(v___f_2242_, 3, v_inst_2212_);
lean_closure_set(v___f_2242_, 4, v_pre_2213_);
lean_closure_set(v___f_2242_, 5, v_post_2214_);
lean_closure_set(v___f_2242_, 6, v___x_2239_);
lean_closure_set(v___f_2242_, 7, v___x_2240_);
lean_closure_set(v___f_2242_, 8, v___x_2241_);
lean_closure_set(v___f_2242_, 9, v_x_2217_);
lean_closure_set(v___f_2242_, 10, v_x_2218_);
lean_closure_set(v___f_2242_, 11, v___y_2225_);
v___x_2243_ = lean_array_get_size(v_args_2219_);
v___x_2244_ = lean_box(v_usedLetOnly_2215_);
v___x_2245_ = lean_box(v_skipConstInApp_2216_);
v___x_2246_ = lean_box(v_skipInstances_2209_);
lean_inc(v_toBind_2221_);
v___f_2247_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__3___boxed), 18, 17);
lean_closure_set(v___f_2247_, 0, v___x_2243_);
lean_closure_set(v___f_2247_, 1, v_toApplicative_2222_);
lean_closure_set(v___f_2247_, 2, v_toBind_2221_);
lean_closure_set(v___f_2247_, 3, v___f_2223_);
lean_closure_set(v___f_2247_, 4, v_inst_2210_);
lean_closure_set(v___f_2247_, 5, v_inst_2211_);
lean_closure_set(v___f_2247_, 6, v_inst_2212_);
lean_closure_set(v___f_2247_, 7, v_pre_2213_);
lean_closure_set(v___f_2247_, 8, v_post_2214_);
lean_closure_set(v___f_2247_, 9, v___x_2244_);
lean_closure_set(v___f_2247_, 10, v___x_2245_);
lean_closure_set(v___f_2247_, 11, v___x_2246_);
lean_closure_set(v___f_2247_, 12, v_x_2217_);
lean_closure_set(v___f_2247_, 13, v_x_2218_);
lean_closure_set(v___f_2247_, 14, v_args_2219_);
lean_closure_set(v___f_2247_, 15, v___y_2225_);
lean_closure_set(v___f_2247_, 16, v___f_2242_);
v___x_2248_ = lean_alloc_closure((void*)(l_Lean_Meta_getFunInfoNArgs___boxed), 7, 2);
lean_closure_set(v___x_2248_, 0, v_f_2224_);
lean_closure_set(v___x_2248_, 1, v___x_2243_);
v___x_2249_ = lean_apply_2(v_inst_2211_, lean_box(0), v___x_2248_);
v___x_2250_ = lean_apply_4(v_toBind_2221_, lean_box(0), lean_box(0), v___x_2249_, v___f_2247_);
return v___x_2250_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__6_0interp(lean_interpreter_value* stack)
{
uint8_t v_skipInstances_2209_ = stack[0].m_num;
lean_object* v_inst_2210_ = stack[1].m_obj;
lean_object* v_inst_2211_ = stack[2].m_obj;
lean_object* v_inst_2212_ = stack[3].m_obj;
lean_object* v_pre_2213_ = stack[4].m_obj;
lean_object* v_post_2214_ = stack[5].m_obj;
uint8_t v_usedLetOnly_2215_ = stack[6].m_num;
uint8_t v_skipConstInApp_2216_ = stack[7].m_num;
lean_object* v_x_2217_ = stack[8].m_obj;
lean_object* v_x_2218_ = stack[9].m_obj;
lean_object* v_args_2219_ = stack[10].m_obj;
lean_object* v___x_2220_ = stack[11].m_obj;
lean_object* v_toBind_2221_ = stack[12].m_obj;
lean_object* v_toApplicative_2222_ = stack[13].m_obj;
lean_object* v___f_2223_ = stack[14].m_obj;
lean_object* v_f_2224_ = stack[15].m_obj;
lean_object* v___y_2225_ = stack[16].m_obj;
lean_object* v_res_2251_;
v_res_2251_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__6(v_skipInstances_2209_, v_inst_2210_, v_inst_2211_, v_inst_2212_, v_pre_2213_, v_post_2214_, v_usedLetOnly_2215_, v_skipConstInApp_2216_, v_x_2217_, v_x_2218_, v_args_2219_, v___x_2220_, v_toBind_2221_, v_toApplicative_2222_, v___f_2223_, v_f_2224_, v___y_2225_);
stack->m_obj
 = v_res_2251_;
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
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__9(uint8_t v_skipInstances_2273_, lean_object* v_inst_2274_, lean_object* v_inst_2275_, lean_object* v_inst_2276_, lean_object* v_pre_2277_, lean_object* v_post_2278_, uint8_t v_usedLetOnly_2279_, uint8_t v_skipConstInApp_2280_, lean_object* v_x_2281_, lean_object* v_x_2282_, lean_object* v___x_2283_, lean_object* v_toBind_2284_, lean_object* v_toApplicative_2285_, lean_object* v___f_2286_, lean_object* v_f_2287_, lean_object* v_args_2288_, lean_object* v___y_2289_){
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
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__9_0interp(lean_interpreter_value* stack)
{
uint8_t v_skipInstances_2273_ = stack[0].m_num;
lean_object* v_inst_2274_ = stack[1].m_obj;
lean_object* v_inst_2275_ = stack[2].m_obj;
lean_object* v_inst_2276_ = stack[3].m_obj;
lean_object* v_pre_2277_ = stack[4].m_obj;
lean_object* v_post_2278_ = stack[5].m_obj;
uint8_t v_usedLetOnly_2279_ = stack[6].m_num;
uint8_t v_skipConstInApp_2280_ = stack[7].m_num;
lean_object* v_x_2281_ = stack[8].m_obj;
lean_object* v_x_2282_ = stack[9].m_obj;
lean_object* v___x_2283_ = stack[10].m_obj;
lean_object* v_toBind_2284_ = stack[11].m_obj;
lean_object* v_toApplicative_2285_ = stack[12].m_obj;
lean_object* v___f_2286_ = stack[13].m_obj;
lean_object* v_f_2287_ = stack[14].m_obj;
lean_object* v_args_2288_ = stack[15].m_obj;
lean_object* v___y_2289_ = stack[16].m_obj;
lean_object* v_res_2302_;
v_res_2302_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__9(v_skipInstances_2273_, v_inst_2274_, v_inst_2275_, v_inst_2276_, v_pre_2277_, v_post_2278_, v_usedLetOnly_2279_, v_skipConstInApp_2280_, v_x_2281_, v_x_2282_, v___x_2283_, v_toBind_2284_, v_toApplicative_2285_, v___f_2286_, v_f_2287_, v_args_2288_, v___y_2289_);
stack->m_obj
 = v_res_2302_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__9___boxed(lean_object** _args){
lean_object* v_skipInstances_2303_ = _args[0];
lean_object* v_inst_2304_ = _args[1];
lean_object* v_inst_2305_ = _args[2];
lean_object* v_inst_2306_ = _args[3];
lean_object* v_pre_2307_ = _args[4];
lean_object* v_post_2308_ = _args[5];
lean_object* v_usedLetOnly_2309_ = _args[6];
lean_object* v_skipConstInApp_2310_ = _args[7];
lean_object* v_x_2311_ = _args[8];
lean_object* v_x_2312_ = _args[9];
lean_object* v___x_2313_ = _args[10];
lean_object* v_toBind_2314_ = _args[11];
lean_object* v_toApplicative_2315_ = _args[12];
lean_object* v___f_2316_ = _args[13];
lean_object* v_f_2317_ = _args[14];
lean_object* v_args_2318_ = _args[15];
lean_object* v___y_2319_ = _args[16];
_start:
{
uint8_t v_skipInstances_boxed_2320_; uint8_t v_usedLetOnly_boxed_2321_; uint8_t v_skipConstInApp_boxed_2322_; lean_object* v_res_2323_; 
v_skipInstances_boxed_2320_ = lean_unbox(v_skipInstances_2303_);
v_usedLetOnly_boxed_2321_ = lean_unbox(v_usedLetOnly_2309_);
v_skipConstInApp_boxed_2322_ = lean_unbox(v_skipConstInApp_2310_);
v_res_2323_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__9(v_skipInstances_boxed_2320_, v_inst_2304_, v_inst_2305_, v_inst_2306_, v_pre_2307_, v_post_2308_, v_usedLetOnly_boxed_2321_, v_skipConstInApp_boxed_2322_, v_x_2311_, v_x_2312_, v___x_2313_, v_toBind_2314_, v_toApplicative_2315_, v___f_2316_, v_f_2317_, v_args_2318_, v___y_2319_);
lean_dec(v___y_2319_);
return v_res_2323_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__0(lean_object* v_fvars_2326_, lean_object* v_inst_2327_, lean_object* v_inst_2328_, lean_object* v_inst_2329_, lean_object* v_pre_2330_, lean_object* v_post_2331_, uint8_t v_usedLetOnly_2332_, uint8_t v_skipConstInApp_2333_, uint8_t v_skipInstances_2334_, lean_object* v_x_2335_, lean_object* v_x_2336_, lean_object* v_body_2337_, lean_object* v_x_2338_, lean_object* v___y_2339_){
_start:
{
lean_object* v___x_2340_; lean_object* v___x_2341_; 
v___x_2340_ = lean_array_push(v_fvars_2326_, v_x_2338_);
v___x_2341_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(v_inst_2327_, v_inst_2328_, v_inst_2329_, v_pre_2330_, v_post_2331_, v_usedLetOnly_2332_, v_skipConstInApp_2333_, v_skipInstances_2334_, v_x_2335_, v_x_2336_, v___x_2340_, v_body_2337_, v___y_2339_);
return v___x_2341_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_2326_ = stack[0].m_obj;
lean_object* v_inst_2327_ = stack[1].m_obj;
lean_object* v_inst_2328_ = stack[2].m_obj;
lean_object* v_inst_2329_ = stack[3].m_obj;
lean_object* v_pre_2330_ = stack[4].m_obj;
lean_object* v_post_2331_ = stack[5].m_obj;
uint8_t v_usedLetOnly_2332_ = stack[6].m_num;
uint8_t v_skipConstInApp_2333_ = stack[7].m_num;
uint8_t v_skipInstances_2334_ = stack[8].m_num;
lean_object* v_x_2335_ = stack[9].m_obj;
lean_object* v_x_2336_ = stack[10].m_obj;
lean_object* v_body_2337_ = stack[11].m_obj;
lean_object* v_x_2338_ = stack[12].m_obj;
lean_object* v___y_2339_ = stack[13].m_obj;
lean_object* v_res_2342_;
v_res_2342_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__0(v_fvars_2326_, v_inst_2327_, v_inst_2328_, v_inst_2329_, v_pre_2330_, v_post_2331_, v_usedLetOnly_2332_, v_skipConstInApp_2333_, v_skipInstances_2334_, v_x_2335_, v_x_2336_, v_body_2337_, v_x_2338_, v___y_2339_);
stack->m_obj
 = v_res_2342_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__0___boxed(lean_object* v_fvars_2343_, lean_object* v_inst_2344_, lean_object* v_inst_2345_, lean_object* v_inst_2346_, lean_object* v_pre_2347_, lean_object* v_post_2348_, lean_object* v_usedLetOnly_2349_, lean_object* v_skipConstInApp_2350_, lean_object* v_skipInstances_2351_, lean_object* v_x_2352_, lean_object* v_x_2353_, lean_object* v_body_2354_, lean_object* v_x_2355_, lean_object* v___y_2356_){
_start:
{
uint8_t v_usedLetOnly_boxed_2357_; uint8_t v_skipConstInApp_boxed_2358_; uint8_t v_skipInstances_boxed_2359_; lean_object* v_res_2360_; 
v_usedLetOnly_boxed_2357_ = lean_unbox(v_usedLetOnly_2349_);
v_skipConstInApp_boxed_2358_ = lean_unbox(v_skipConstInApp_2350_);
v_skipInstances_boxed_2359_ = lean_unbox(v_skipInstances_2351_);
v_res_2360_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__0(v_fvars_2343_, v_inst_2344_, v_inst_2345_, v_inst_2346_, v_pre_2347_, v_post_2348_, v_usedLetOnly_boxed_2357_, v_skipConstInApp_boxed_2358_, v_skipInstances_boxed_2359_, v_x_2352_, v_x_2353_, v_body_2354_, v_x_2355_, v___y_2356_);
lean_dec(v___y_2356_);
return v_res_2360_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3___boxed(lean_object* v_inst_2361_, lean_object* v_inst_2362_, lean_object* v_inst_2363_, lean_object* v_pre_2364_, lean_object* v_post_2365_, lean_object* v_usedLetOnly_2366_, lean_object* v_skipConstInApp_2367_, lean_object* v_skipInstances_2368_, lean_object* v_x_2369_, lean_object* v_x_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_){
_start:
{
uint8_t v_usedLetOnly_boxed_2373_; uint8_t v_skipConstInApp_boxed_2374_; uint8_t v_skipInstances_boxed_2375_; lean_object* v_res_2376_; 
v_usedLetOnly_boxed_2373_ = lean_unbox(v_usedLetOnly_2366_);
v_skipConstInApp_boxed_2374_ = lean_unbox(v_skipConstInApp_2367_);
v_skipInstances_boxed_2375_ = lean_unbox(v_skipInstances_2368_);
v_res_2376_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3(v_inst_2361_, v_inst_2362_, v_inst_2363_, v_pre_2364_, v_post_2365_, v_usedLetOnly_boxed_2373_, v_skipConstInApp_boxed_2374_, v_skipInstances_boxed_2375_, v_x_2369_, v_x_2370_, v_a_2371_, v_a_2372_);
lean_dec(v_a_2371_);
return v_res_2376_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(lean_object* v_inst_2377_, lean_object* v_inst_2378_, lean_object* v_inst_2379_, lean_object* v_pre_2380_, lean_object* v_post_2381_, uint8_t v_usedLetOnly_2382_, uint8_t v_skipConstInApp_2383_, uint8_t v_skipInstances_2384_, lean_object* v_x_2385_, lean_object* v_x_2386_, lean_object* v_fvars_2387_, lean_object* v_e_2388_, lean_object* v_a_2389_){
_start:
{
lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___f_2394_; lean_object* v___f_2395_; lean_object* v___x_2396_; 
v___x_2390_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0));
v___x_2391_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1));
lean_inc_ref(v_inst_2377_);
v___x_2392_ = l_Lean_MonadCacheT_instMonad___redArg(v_x_2385_, v___x_2390_, v___x_2391_, v_inst_2377_);
v___x_2393_ = l_Lean_MonadCacheT_instMonadControl___redArg(v_x_2385_, v___x_2390_, v___x_2391_);
lean_inc_ref_n(v_inst_2379_, 2);
lean_inc_ref(v___x_2393_);
v___f_2394_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_2394_, 0, v___x_2393_);
lean_closure_set(v___f_2394_, 1, v_inst_2379_);
v___f_2395_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_2395_, 0, v___x_2393_);
lean_closure_set(v___f_2395_, 1, v_inst_2379_);
v___x_2396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2396_, 0, v___f_2394_);
lean_ctor_set(v___x_2396_, 1, v___f_2395_);
if (lean_obj_tag(v_e_2388_) == 7)
{
lean_object* v_binderName_2397_; lean_object* v_binderType_2398_; lean_object* v_body_2399_; uint8_t v_binderInfo_2400_; lean_object* v_toBind_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___f_2405_; lean_object* v___x_2406_; lean_object* v___f_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; 
v_binderName_2397_ = lean_ctor_get(v_e_2388_, 0);
lean_inc(v_binderName_2397_);
v_binderType_2398_ = lean_ctor_get(v_e_2388_, 1);
lean_inc_ref(v_binderType_2398_);
v_body_2399_ = lean_ctor_get(v_e_2388_, 2);
lean_inc_ref(v_body_2399_);
v_binderInfo_2400_ = lean_ctor_get_uint8(v_e_2388_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2388_, 3);
v_toBind_2401_ = lean_ctor_get(v_inst_2377_, 1);
lean_inc(v_toBind_2401_);
v___x_2402_ = lean_box(v_usedLetOnly_2382_);
v___x_2403_ = lean_box(v_skipConstInApp_2383_);
v___x_2404_ = lean_box(v_skipInstances_2384_);
lean_inc(v_x_2386_);
lean_inc(v_post_2381_);
lean_inc(v_pre_2380_);
lean_inc_ref(v_inst_2379_);
lean_inc(v_inst_2378_);
lean_inc_ref(v_inst_2377_);
lean_inc_ref(v_fvars_2387_);
v___f_2405_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__0___boxed), 14, 12);
lean_closure_set(v___f_2405_, 0, v_fvars_2387_);
lean_closure_set(v___f_2405_, 1, v_inst_2377_);
lean_closure_set(v___f_2405_, 2, v_inst_2378_);
lean_closure_set(v___f_2405_, 3, v_inst_2379_);
lean_closure_set(v___f_2405_, 4, v_pre_2380_);
lean_closure_set(v___f_2405_, 5, v_post_2381_);
lean_closure_set(v___f_2405_, 6, v___x_2402_);
lean_closure_set(v___f_2405_, 7, v___x_2403_);
lean_closure_set(v___f_2405_, 8, v___x_2404_);
lean_closure_set(v___f_2405_, 9, v_x_2385_);
lean_closure_set(v___f_2405_, 10, v_x_2386_);
lean_closure_set(v___f_2405_, 11, v_body_2399_);
v___x_2406_ = lean_box(v_binderInfo_2400_);
lean_inc(v_a_2389_);
v___f_2407_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_2407_, 0, v___x_2396_);
lean_closure_set(v___f_2407_, 1, v___x_2392_);
lean_closure_set(v___f_2407_, 2, v_binderName_2397_);
lean_closure_set(v___f_2407_, 3, v___x_2406_);
lean_closure_set(v___f_2407_, 4, v___f_2405_);
lean_closure_set(v___f_2407_, 5, v_a_2389_);
v___x_2408_ = lean_expr_instantiate_rev(v_binderType_2398_, v_fvars_2387_);
lean_dec_ref(v_fvars_2387_);
lean_dec_ref(v_binderType_2398_);
v___x_2409_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2377_, v_inst_2378_, v_inst_2379_, v_pre_2380_, v_post_2381_, v_usedLetOnly_2382_, v_skipConstInApp_2383_, v_skipInstances_2384_, v_x_2385_, v_x_2386_, v___x_2408_, v_a_2389_);
v___x_2410_ = lean_apply_4(v_toBind_2401_, lean_box(0), lean_box(0), v___x_2409_, v___f_2407_);
return v___x_2410_;
}
else
{
lean_object* v_toBind_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___f_2415_; lean_object* v___x_2416_; lean_object* v___f_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; 
lean_dec_ref_known(v___x_2396_, 2);
lean_dec_ref(v___x_2392_);
v_toBind_2411_ = lean_ctor_get(v_inst_2377_, 1);
lean_inc_n(v_toBind_2411_, 2);
v___x_2412_ = lean_box(v_usedLetOnly_2382_);
v___x_2413_ = lean_box(v_skipConstInApp_2383_);
v___x_2414_ = lean_box(v_skipInstances_2384_);
lean_inc(v_a_2389_);
lean_inc(v_x_2386_);
lean_inc(v_post_2381_);
lean_inc(v_pre_2380_);
lean_inc_ref(v_inst_2379_);
lean_inc_n(v_inst_2378_, 2);
lean_inc_ref(v_inst_2377_);
v___f_2415_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3___boxed), 12, 11);
lean_closure_set(v___f_2415_, 0, v_inst_2377_);
lean_closure_set(v___f_2415_, 1, v_inst_2378_);
lean_closure_set(v___f_2415_, 2, v_inst_2379_);
lean_closure_set(v___f_2415_, 3, v_pre_2380_);
lean_closure_set(v___f_2415_, 4, v_post_2381_);
lean_closure_set(v___f_2415_, 5, v___x_2412_);
lean_closure_set(v___f_2415_, 6, v___x_2413_);
lean_closure_set(v___f_2415_, 7, v___x_2414_);
lean_closure_set(v___f_2415_, 8, v_x_2385_);
lean_closure_set(v___f_2415_, 9, v_x_2386_);
lean_closure_set(v___f_2415_, 10, v_a_2389_);
v___x_2416_ = lean_box(v_usedLetOnly_2382_);
lean_inc_ref(v_fvars_2387_);
v___f_2417_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__3___boxed), 6, 5);
lean_closure_set(v___f_2417_, 0, v_fvars_2387_);
lean_closure_set(v___f_2417_, 1, v___x_2416_);
lean_closure_set(v___f_2417_, 2, v_inst_2378_);
lean_closure_set(v___f_2417_, 3, v_toBind_2411_);
lean_closure_set(v___f_2417_, 4, v___f_2415_);
v___x_2418_ = lean_expr_instantiate_rev(v_e_2388_, v_fvars_2387_);
lean_dec_ref(v_fvars_2387_);
lean_dec_ref(v_e_2388_);
v___x_2419_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2377_, v_inst_2378_, v_inst_2379_, v_pre_2380_, v_post_2381_, v_usedLetOnly_2382_, v_skipConstInApp_2383_, v_skipInstances_2384_, v_x_2385_, v_x_2386_, v___x_2418_, v_a_2389_);
v___x_2420_ = lean_apply_4(v_toBind_2411_, lean_box(0), lean_box(0), v___x_2419_, v___f_2417_);
return v___x_2420_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2377_ = stack[0].m_obj;
lean_object* v_inst_2378_ = stack[1].m_obj;
lean_object* v_inst_2379_ = stack[2].m_obj;
lean_object* v_pre_2380_ = stack[3].m_obj;
lean_object* v_post_2381_ = stack[4].m_obj;
uint8_t v_usedLetOnly_2382_ = stack[5].m_num;
uint8_t v_skipConstInApp_2383_ = stack[6].m_num;
uint8_t v_skipInstances_2384_ = stack[7].m_num;
lean_object* v_x_2385_ = stack[8].m_obj;
lean_object* v_x_2386_ = stack[9].m_obj;
lean_object* v_fvars_2387_ = stack[10].m_obj;
lean_object* v_e_2388_ = stack[11].m_obj;
lean_object* v_a_2389_ = stack[12].m_obj;
lean_object* v_res_2421_;
v_res_2421_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(v_inst_2377_, v_inst_2378_, v_inst_2379_, v_pre_2380_, v_post_2381_, v_usedLetOnly_2382_, v_skipConstInApp_2383_, v_skipInstances_2384_, v_x_2385_, v_x_2386_, v_fvars_2387_, v_e_2388_, v_a_2389_);
stack->m_obj
 = v_res_2421_;
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__0(lean_object* v_fvars_2422_, lean_object* v_inst_2423_, lean_object* v_inst_2424_, lean_object* v_inst_2425_, lean_object* v_pre_2426_, lean_object* v_post_2427_, uint8_t v_usedLetOnly_2428_, uint8_t v_skipConstInApp_2429_, uint8_t v_skipInstances_2430_, lean_object* v_x_2431_, lean_object* v_x_2432_, lean_object* v_body_2433_, lean_object* v_x_2434_, lean_object* v___y_2435_){
_start:
{
lean_object* v___x_2436_; lean_object* v___x_2437_; 
v___x_2436_ = lean_array_push(v_fvars_2422_, v_x_2434_);
v___x_2437_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(v_inst_2423_, v_inst_2424_, v_inst_2425_, v_pre_2426_, v_post_2427_, v_usedLetOnly_2428_, v_skipConstInApp_2429_, v_skipInstances_2430_, v_x_2431_, v_x_2432_, v___x_2436_, v_body_2433_, v___y_2435_);
return v___x_2437_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_2422_ = stack[0].m_obj;
lean_object* v_inst_2423_ = stack[1].m_obj;
lean_object* v_inst_2424_ = stack[2].m_obj;
lean_object* v_inst_2425_ = stack[3].m_obj;
lean_object* v_pre_2426_ = stack[4].m_obj;
lean_object* v_post_2427_ = stack[5].m_obj;
uint8_t v_usedLetOnly_2428_ = stack[6].m_num;
uint8_t v_skipConstInApp_2429_ = stack[7].m_num;
uint8_t v_skipInstances_2430_ = stack[8].m_num;
lean_object* v_x_2431_ = stack[9].m_obj;
lean_object* v_x_2432_ = stack[10].m_obj;
lean_object* v_body_2433_ = stack[11].m_obj;
lean_object* v_x_2434_ = stack[12].m_obj;
lean_object* v___y_2435_ = stack[13].m_obj;
lean_object* v_res_2438_;
v_res_2438_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__0(v_fvars_2422_, v_inst_2423_, v_inst_2424_, v_inst_2425_, v_pre_2426_, v_post_2427_, v_usedLetOnly_2428_, v_skipConstInApp_2429_, v_skipInstances_2430_, v_x_2431_, v_x_2432_, v_body_2433_, v_x_2434_, v___y_2435_);
stack->m_obj
 = v_res_2438_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__0___boxed(lean_object* v_fvars_2439_, lean_object* v_inst_2440_, lean_object* v_inst_2441_, lean_object* v_inst_2442_, lean_object* v_pre_2443_, lean_object* v_post_2444_, lean_object* v_usedLetOnly_2445_, lean_object* v_skipConstInApp_2446_, lean_object* v_skipInstances_2447_, lean_object* v_x_2448_, lean_object* v_x_2449_, lean_object* v_body_2450_, lean_object* v_x_2451_, lean_object* v___y_2452_){
_start:
{
uint8_t v_usedLetOnly_boxed_2453_; uint8_t v_skipConstInApp_boxed_2454_; uint8_t v_skipInstances_boxed_2455_; lean_object* v_res_2456_; 
v_usedLetOnly_boxed_2453_ = lean_unbox(v_usedLetOnly_2445_);
v_skipConstInApp_boxed_2454_ = lean_unbox(v_skipConstInApp_2446_);
v_skipInstances_boxed_2455_ = lean_unbox(v_skipInstances_2447_);
v_res_2456_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__0(v_fvars_2439_, v_inst_2440_, v_inst_2441_, v_inst_2442_, v_pre_2443_, v_post_2444_, v_usedLetOnly_boxed_2453_, v_skipConstInApp_boxed_2454_, v_skipInstances_boxed_2455_, v_x_2448_, v_x_2449_, v_body_2450_, v_x_2451_, v___y_2452_);
lean_dec(v___y_2452_);
return v_res_2456_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(lean_object* v_inst_2457_, lean_object* v_inst_2458_, lean_object* v_inst_2459_, lean_object* v_pre_2460_, lean_object* v_post_2461_, uint8_t v_usedLetOnly_2462_, uint8_t v_skipConstInApp_2463_, uint8_t v_skipInstances_2464_, lean_object* v_x_2465_, lean_object* v_x_2466_, lean_object* v_fvars_2467_, lean_object* v_e_2468_, lean_object* v_a_2469_){
_start:
{
lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___f_2474_; lean_object* v___f_2475_; lean_object* v___x_2476_; 
v___x_2470_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0));
v___x_2471_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1));
lean_inc_ref(v_inst_2457_);
v___x_2472_ = l_Lean_MonadCacheT_instMonad___redArg(v_x_2465_, v___x_2470_, v___x_2471_, v_inst_2457_);
v___x_2473_ = l_Lean_MonadCacheT_instMonadControl___redArg(v_x_2465_, v___x_2470_, v___x_2471_);
lean_inc_ref_n(v_inst_2459_, 2);
lean_inc_ref(v___x_2473_);
v___f_2474_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_2474_, 0, v___x_2473_);
lean_closure_set(v___f_2474_, 1, v_inst_2459_);
v___f_2475_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_2475_, 0, v___x_2473_);
lean_closure_set(v___f_2475_, 1, v_inst_2459_);
v___x_2476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2476_, 0, v___f_2474_);
lean_ctor_set(v___x_2476_, 1, v___f_2475_);
if (lean_obj_tag(v_e_2468_) == 6)
{
lean_object* v_binderName_2477_; lean_object* v_binderType_2478_; lean_object* v_body_2479_; uint8_t v_binderInfo_2480_; lean_object* v_toBind_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___f_2485_; lean_object* v___x_2486_; lean_object* v___f_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; 
v_binderName_2477_ = lean_ctor_get(v_e_2468_, 0);
lean_inc(v_binderName_2477_);
v_binderType_2478_ = lean_ctor_get(v_e_2468_, 1);
lean_inc_ref(v_binderType_2478_);
v_body_2479_ = lean_ctor_get(v_e_2468_, 2);
lean_inc_ref(v_body_2479_);
v_binderInfo_2480_ = lean_ctor_get_uint8(v_e_2468_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2468_, 3);
v_toBind_2481_ = lean_ctor_get(v_inst_2457_, 1);
lean_inc(v_toBind_2481_);
v___x_2482_ = lean_box(v_usedLetOnly_2462_);
v___x_2483_ = lean_box(v_skipConstInApp_2463_);
v___x_2484_ = lean_box(v_skipInstances_2464_);
lean_inc(v_x_2466_);
lean_inc(v_post_2461_);
lean_inc(v_pre_2460_);
lean_inc_ref(v_inst_2459_);
lean_inc(v_inst_2458_);
lean_inc_ref(v_inst_2457_);
lean_inc_ref(v_fvars_2467_);
v___f_2485_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__0___boxed), 14, 12);
lean_closure_set(v___f_2485_, 0, v_fvars_2467_);
lean_closure_set(v___f_2485_, 1, v_inst_2457_);
lean_closure_set(v___f_2485_, 2, v_inst_2458_);
lean_closure_set(v___f_2485_, 3, v_inst_2459_);
lean_closure_set(v___f_2485_, 4, v_pre_2460_);
lean_closure_set(v___f_2485_, 5, v_post_2461_);
lean_closure_set(v___f_2485_, 6, v___x_2482_);
lean_closure_set(v___f_2485_, 7, v___x_2483_);
lean_closure_set(v___f_2485_, 8, v___x_2484_);
lean_closure_set(v___f_2485_, 9, v_x_2465_);
lean_closure_set(v___f_2485_, 10, v_x_2466_);
lean_closure_set(v___f_2485_, 11, v_body_2479_);
v___x_2486_ = lean_box(v_binderInfo_2480_);
lean_inc(v_a_2469_);
v___f_2487_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_2487_, 0, v___x_2476_);
lean_closure_set(v___f_2487_, 1, v___x_2472_);
lean_closure_set(v___f_2487_, 2, v_binderName_2477_);
lean_closure_set(v___f_2487_, 3, v___x_2486_);
lean_closure_set(v___f_2487_, 4, v___f_2485_);
lean_closure_set(v___f_2487_, 5, v_a_2469_);
v___x_2488_ = lean_expr_instantiate_rev(v_binderType_2478_, v_fvars_2467_);
lean_dec_ref(v_fvars_2467_);
lean_dec_ref(v_binderType_2478_);
v___x_2489_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2457_, v_inst_2458_, v_inst_2459_, v_pre_2460_, v_post_2461_, v_usedLetOnly_2462_, v_skipConstInApp_2463_, v_skipInstances_2464_, v_x_2465_, v_x_2466_, v___x_2488_, v_a_2469_);
v___x_2490_ = lean_apply_4(v_toBind_2481_, lean_box(0), lean_box(0), v___x_2489_, v___f_2487_);
return v___x_2490_;
}
else
{
lean_object* v_toBind_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___f_2495_; lean_object* v___x_2496_; lean_object* v___f_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; 
lean_dec_ref_known(v___x_2476_, 2);
lean_dec_ref(v___x_2472_);
v_toBind_2491_ = lean_ctor_get(v_inst_2457_, 1);
lean_inc_n(v_toBind_2491_, 2);
v___x_2492_ = lean_box(v_usedLetOnly_2462_);
v___x_2493_ = lean_box(v_skipConstInApp_2463_);
v___x_2494_ = lean_box(v_skipInstances_2464_);
lean_inc(v_a_2469_);
lean_inc(v_x_2466_);
lean_inc(v_post_2461_);
lean_inc(v_pre_2460_);
lean_inc_ref(v_inst_2459_);
lean_inc_n(v_inst_2458_, 2);
lean_inc_ref(v_inst_2457_);
v___f_2495_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3___boxed), 12, 11);
lean_closure_set(v___f_2495_, 0, v_inst_2457_);
lean_closure_set(v___f_2495_, 1, v_inst_2458_);
lean_closure_set(v___f_2495_, 2, v_inst_2459_);
lean_closure_set(v___f_2495_, 3, v_pre_2460_);
lean_closure_set(v___f_2495_, 4, v_post_2461_);
lean_closure_set(v___f_2495_, 5, v___x_2492_);
lean_closure_set(v___f_2495_, 6, v___x_2493_);
lean_closure_set(v___f_2495_, 7, v___x_2494_);
lean_closure_set(v___f_2495_, 8, v_x_2465_);
lean_closure_set(v___f_2495_, 9, v_x_2466_);
lean_closure_set(v___f_2495_, 10, v_a_2469_);
v___x_2496_ = lean_box(v_usedLetOnly_2462_);
lean_inc_ref(v_fvars_2467_);
v___f_2497_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__3___boxed), 6, 5);
lean_closure_set(v___f_2497_, 0, v_fvars_2467_);
lean_closure_set(v___f_2497_, 1, v___x_2496_);
lean_closure_set(v___f_2497_, 2, v_inst_2458_);
lean_closure_set(v___f_2497_, 3, v_toBind_2491_);
lean_closure_set(v___f_2497_, 4, v___f_2495_);
v___x_2498_ = lean_expr_instantiate_rev(v_e_2468_, v_fvars_2467_);
lean_dec_ref(v_fvars_2467_);
lean_dec_ref(v_e_2468_);
v___x_2499_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2457_, v_inst_2458_, v_inst_2459_, v_pre_2460_, v_post_2461_, v_usedLetOnly_2462_, v_skipConstInApp_2463_, v_skipInstances_2464_, v_x_2465_, v_x_2466_, v___x_2498_, v_a_2469_);
v___x_2500_ = lean_apply_4(v_toBind_2491_, lean_box(0), lean_box(0), v___x_2499_, v___f_2497_);
return v___x_2500_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2457_ = stack[0].m_obj;
lean_object* v_inst_2458_ = stack[1].m_obj;
lean_object* v_inst_2459_ = stack[2].m_obj;
lean_object* v_pre_2460_ = stack[3].m_obj;
lean_object* v_post_2461_ = stack[4].m_obj;
uint8_t v_usedLetOnly_2462_ = stack[5].m_num;
uint8_t v_skipConstInApp_2463_ = stack[6].m_num;
uint8_t v_skipInstances_2464_ = stack[7].m_num;
lean_object* v_x_2465_ = stack[8].m_obj;
lean_object* v_x_2466_ = stack[9].m_obj;
lean_object* v_fvars_2467_ = stack[10].m_obj;
lean_object* v_e_2468_ = stack[11].m_obj;
lean_object* v_a_2469_ = stack[12].m_obj;
lean_object* v_res_2501_;
v_res_2501_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(v_inst_2457_, v_inst_2458_, v_inst_2459_, v_pre_2460_, v_post_2461_, v_usedLetOnly_2462_, v_skipConstInApp_2463_, v_skipInstances_2464_, v_x_2465_, v_x_2466_, v_fvars_2467_, v_e_2468_, v_a_2469_);
stack->m_obj
 = v_res_2501_;
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__0(lean_object* v_fvars_2502_, lean_object* v_inst_2503_, lean_object* v_inst_2504_, lean_object* v_inst_2505_, lean_object* v_pre_2506_, lean_object* v_post_2507_, uint8_t v_usedLetOnly_2508_, uint8_t v_skipConstInApp_2509_, uint8_t v_skipInstances_2510_, lean_object* v_x_2511_, lean_object* v_x_2512_, lean_object* v_body_2513_, lean_object* v_x_2514_, lean_object* v___y_2515_){
_start:
{
lean_object* v___x_2516_; lean_object* v___x_2517_; 
v___x_2516_ = lean_array_push(v_fvars_2502_, v_x_2514_);
v___x_2517_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(v_inst_2503_, v_inst_2504_, v_inst_2505_, v_pre_2506_, v_post_2507_, v_usedLetOnly_2508_, v_skipConstInApp_2509_, v_skipInstances_2510_, v_x_2511_, v_x_2512_, v___x_2516_, v_body_2513_, v___y_2515_);
return v___x_2517_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_2502_ = stack[0].m_obj;
lean_object* v_inst_2503_ = stack[1].m_obj;
lean_object* v_inst_2504_ = stack[2].m_obj;
lean_object* v_inst_2505_ = stack[3].m_obj;
lean_object* v_pre_2506_ = stack[4].m_obj;
lean_object* v_post_2507_ = stack[5].m_obj;
uint8_t v_usedLetOnly_2508_ = stack[6].m_num;
uint8_t v_skipConstInApp_2509_ = stack[7].m_num;
uint8_t v_skipInstances_2510_ = stack[8].m_num;
lean_object* v_x_2511_ = stack[9].m_obj;
lean_object* v_x_2512_ = stack[10].m_obj;
lean_object* v_body_2513_ = stack[11].m_obj;
lean_object* v_x_2514_ = stack[12].m_obj;
lean_object* v___y_2515_ = stack[13].m_obj;
lean_object* v_res_2518_;
v_res_2518_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__0(v_fvars_2502_, v_inst_2503_, v_inst_2504_, v_inst_2505_, v_pre_2506_, v_post_2507_, v_usedLetOnly_2508_, v_skipConstInApp_2509_, v_skipInstances_2510_, v_x_2511_, v_x_2512_, v_body_2513_, v_x_2514_, v___y_2515_);
stack->m_obj
 = v_res_2518_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__0___boxed(lean_object* v_fvars_2519_, lean_object* v_inst_2520_, lean_object* v_inst_2521_, lean_object* v_inst_2522_, lean_object* v_pre_2523_, lean_object* v_post_2524_, lean_object* v_usedLetOnly_2525_, lean_object* v_skipConstInApp_2526_, lean_object* v_skipInstances_2527_, lean_object* v_x_2528_, lean_object* v_x_2529_, lean_object* v_body_2530_, lean_object* v_x_2531_, lean_object* v___y_2532_){
_start:
{
uint8_t v_usedLetOnly_boxed_2533_; uint8_t v_skipConstInApp_boxed_2534_; uint8_t v_skipInstances_boxed_2535_; lean_object* v_res_2536_; 
v_usedLetOnly_boxed_2533_ = lean_unbox(v_usedLetOnly_2525_);
v_skipConstInApp_boxed_2534_ = lean_unbox(v_skipConstInApp_2526_);
v_skipInstances_boxed_2535_ = lean_unbox(v_skipInstances_2527_);
v_res_2536_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__0(v_fvars_2519_, v_inst_2520_, v_inst_2521_, v_inst_2522_, v_pre_2523_, v_post_2524_, v_usedLetOnly_boxed_2533_, v_skipConstInApp_boxed_2534_, v_skipInstances_boxed_2535_, v_x_2528_, v_x_2529_, v_body_2530_, v_x_2531_, v___y_2532_);
lean_dec(v___y_2532_);
return v_res_2536_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__2(lean_object* v___x_2537_, lean_object* v___x_2538_, lean_object* v_declName_2539_, lean_object* v___f_2540_, uint8_t v_nondep_2541_, lean_object* v_a_2542_, lean_object* v_value_2543_, lean_object* v_fvars_2544_, lean_object* v_inst_2545_, lean_object* v_inst_2546_, lean_object* v_inst_2547_, lean_object* v_pre_2548_, lean_object* v_post_2549_, uint8_t v_usedLetOnly_2550_, uint8_t v_skipConstInApp_2551_, uint8_t v_skipInstances_2552_, lean_object* v_x_2553_, lean_object* v_x_2554_, lean_object* v_toBind_2555_, lean_object* v_a_2556_){
_start:
{
lean_object* v___x_2557_; lean_object* v___f_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; 
v___x_2557_ = lean_box(v_nondep_2541_);
lean_inc(v_a_2542_);
v___f_2558_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_2558_, 0, v___x_2537_);
lean_closure_set(v___f_2558_, 1, v___x_2538_);
lean_closure_set(v___f_2558_, 2, v_declName_2539_);
lean_closure_set(v___f_2558_, 3, v_a_2556_);
lean_closure_set(v___f_2558_, 4, v___f_2540_);
lean_closure_set(v___f_2558_, 5, v___x_2557_);
lean_closure_set(v___f_2558_, 6, v_a_2542_);
v___x_2559_ = lean_expr_instantiate_rev(v_value_2543_, v_fvars_2544_);
v___x_2560_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2545_, v_inst_2546_, v_inst_2547_, v_pre_2548_, v_post_2549_, v_usedLetOnly_2550_, v_skipConstInApp_2551_, v_skipInstances_2552_, v_x_2553_, v_x_2554_, v___x_2559_, v_a_2542_);
v___x_2561_ = lean_apply_4(v_toBind_2555_, lean_box(0), lean_box(0), v___x_2560_, v___f_2558_);
return v___x_2561_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2537_ = stack[0].m_obj;
lean_object* v___x_2538_ = stack[1].m_obj;
lean_object* v_declName_2539_ = stack[2].m_obj;
lean_object* v___f_2540_ = stack[3].m_obj;
uint8_t v_nondep_2541_ = stack[4].m_num;
lean_object* v_a_2542_ = stack[5].m_obj;
lean_object* v_value_2543_ = stack[6].m_obj;
lean_object* v_fvars_2544_ = stack[7].m_obj;
lean_object* v_inst_2545_ = stack[8].m_obj;
lean_object* v_inst_2546_ = stack[9].m_obj;
lean_object* v_inst_2547_ = stack[10].m_obj;
lean_object* v_pre_2548_ = stack[11].m_obj;
lean_object* v_post_2549_ = stack[12].m_obj;
uint8_t v_usedLetOnly_2550_ = stack[13].m_num;
uint8_t v_skipConstInApp_2551_ = stack[14].m_num;
uint8_t v_skipInstances_2552_ = stack[15].m_num;
lean_object* v_x_2553_ = stack[16].m_obj;
lean_object* v_x_2554_ = stack[17].m_obj;
lean_object* v_toBind_2555_ = stack[18].m_obj;
lean_object* v_a_2556_ = stack[19].m_obj;
lean_object* v_res_2562_;
v_res_2562_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__2(v___x_2537_, v___x_2538_, v_declName_2539_, v___f_2540_, v_nondep_2541_, v_a_2542_, v_value_2543_, v_fvars_2544_, v_inst_2545_, v_inst_2546_, v_inst_2547_, v_pre_2548_, v_post_2549_, v_usedLetOnly_2550_, v_skipConstInApp_2551_, v_skipInstances_2552_, v_x_2553_, v_x_2554_, v_toBind_2555_, v_a_2556_);
stack->m_obj
 = v_res_2562_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__2___boxed(lean_object** _args){
lean_object* v___x_2563_ = _args[0];
lean_object* v___x_2564_ = _args[1];
lean_object* v_declName_2565_ = _args[2];
lean_object* v___f_2566_ = _args[3];
lean_object* v_nondep_2567_ = _args[4];
lean_object* v_a_2568_ = _args[5];
lean_object* v_value_2569_ = _args[6];
lean_object* v_fvars_2570_ = _args[7];
lean_object* v_inst_2571_ = _args[8];
lean_object* v_inst_2572_ = _args[9];
lean_object* v_inst_2573_ = _args[10];
lean_object* v_pre_2574_ = _args[11];
lean_object* v_post_2575_ = _args[12];
lean_object* v_usedLetOnly_2576_ = _args[13];
lean_object* v_skipConstInApp_2577_ = _args[14];
lean_object* v_skipInstances_2578_ = _args[15];
lean_object* v_x_2579_ = _args[16];
lean_object* v_x_2580_ = _args[17];
lean_object* v_toBind_2581_ = _args[18];
lean_object* v_a_2582_ = _args[19];
_start:
{
uint8_t v_nondep_3853__boxed_2583_; uint8_t v_usedLetOnly_boxed_2584_; uint8_t v_skipConstInApp_boxed_2585_; uint8_t v_skipInstances_boxed_2586_; lean_object* v_res_2587_; 
v_nondep_3853__boxed_2583_ = lean_unbox(v_nondep_2567_);
v_usedLetOnly_boxed_2584_ = lean_unbox(v_usedLetOnly_2576_);
v_skipConstInApp_boxed_2585_ = lean_unbox(v_skipConstInApp_2577_);
v_skipInstances_boxed_2586_ = lean_unbox(v_skipInstances_2578_);
v_res_2587_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__2(v___x_2563_, v___x_2564_, v_declName_2565_, v___f_2566_, v_nondep_3853__boxed_2583_, v_a_2568_, v_value_2569_, v_fvars_2570_, v_inst_2571_, v_inst_2572_, v_inst_2573_, v_pre_2574_, v_post_2575_, v_usedLetOnly_boxed_2584_, v_skipConstInApp_boxed_2585_, v_skipInstances_boxed_2586_, v_x_2579_, v_x_2580_, v_toBind_2581_, v_a_2582_);
lean_dec_ref(v_fvars_2570_);
lean_dec_ref(v_value_2569_);
lean_dec(v_a_2568_);
return v_res_2587_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(lean_object* v_inst_2588_, lean_object* v_inst_2589_, lean_object* v_inst_2590_, lean_object* v_pre_2591_, lean_object* v_post_2592_, uint8_t v_usedLetOnly_2593_, uint8_t v_skipConstInApp_2594_, uint8_t v_skipInstances_2595_, lean_object* v_x_2596_, lean_object* v_x_2597_, lean_object* v_fvars_2598_, lean_object* v_e_2599_, lean_object* v_a_2600_){
_start:
{
lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___f_2605_; lean_object* v___f_2606_; lean_object* v___x_2607_; 
v___x_2601_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0));
v___x_2602_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1));
lean_inc_ref(v_inst_2588_);
v___x_2603_ = l_Lean_MonadCacheT_instMonad___redArg(v_x_2596_, v___x_2601_, v___x_2602_, v_inst_2588_);
v___x_2604_ = l_Lean_MonadCacheT_instMonadControl___redArg(v_x_2596_, v___x_2601_, v___x_2602_);
lean_inc_ref_n(v_inst_2590_, 2);
lean_inc_ref(v___x_2604_);
v___f_2605_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_2605_, 0, v___x_2604_);
lean_closure_set(v___f_2605_, 1, v_inst_2590_);
v___f_2606_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_2606_, 0, v___x_2604_);
lean_closure_set(v___f_2606_, 1, v_inst_2590_);
v___x_2607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2607_, 0, v___f_2605_);
lean_ctor_set(v___x_2607_, 1, v___f_2606_);
if (lean_obj_tag(v_e_2599_) == 8)
{
lean_object* v_declName_2608_; lean_object* v_type_2609_; lean_object* v_value_2610_; lean_object* v_body_2611_; uint8_t v_nondep_2612_; lean_object* v_toBind_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___f_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___f_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; 
v_declName_2608_ = lean_ctor_get(v_e_2599_, 0);
lean_inc(v_declName_2608_);
v_type_2609_ = lean_ctor_get(v_e_2599_, 1);
lean_inc_ref(v_type_2609_);
v_value_2610_ = lean_ctor_get(v_e_2599_, 2);
lean_inc_ref(v_value_2610_);
v_body_2611_ = lean_ctor_get(v_e_2599_, 3);
lean_inc_ref(v_body_2611_);
v_nondep_2612_ = lean_ctor_get_uint8(v_e_2599_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_2599_, 4);
v_toBind_2613_ = lean_ctor_get(v_inst_2588_, 1);
lean_inc_n(v_toBind_2613_, 2);
v___x_2614_ = lean_box(v_usedLetOnly_2593_);
v___x_2615_ = lean_box(v_skipConstInApp_2594_);
v___x_2616_ = lean_box(v_skipInstances_2595_);
lean_inc_n(v_x_2597_, 2);
lean_inc_n(v_post_2592_, 2);
lean_inc_n(v_pre_2591_, 2);
lean_inc_ref_n(v_inst_2590_, 2);
lean_inc_n(v_inst_2589_, 2);
lean_inc_ref_n(v_inst_2588_, 2);
lean_inc_ref_n(v_fvars_2598_, 2);
v___f_2617_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__0___boxed), 14, 12);
lean_closure_set(v___f_2617_, 0, v_fvars_2598_);
lean_closure_set(v___f_2617_, 1, v_inst_2588_);
lean_closure_set(v___f_2617_, 2, v_inst_2589_);
lean_closure_set(v___f_2617_, 3, v_inst_2590_);
lean_closure_set(v___f_2617_, 4, v_pre_2591_);
lean_closure_set(v___f_2617_, 5, v_post_2592_);
lean_closure_set(v___f_2617_, 6, v___x_2614_);
lean_closure_set(v___f_2617_, 7, v___x_2615_);
lean_closure_set(v___f_2617_, 8, v___x_2616_);
lean_closure_set(v___f_2617_, 9, v_x_2596_);
lean_closure_set(v___f_2617_, 10, v_x_2597_);
lean_closure_set(v___f_2617_, 11, v_body_2611_);
v___x_2618_ = lean_box(v_nondep_2612_);
v___x_2619_ = lean_box(v_usedLetOnly_2593_);
v___x_2620_ = lean_box(v_skipConstInApp_2594_);
v___x_2621_ = lean_box(v_skipInstances_2595_);
lean_inc(v_a_2600_);
v___f_2622_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__2___boxed), 20, 19);
lean_closure_set(v___f_2622_, 0, v___x_2607_);
lean_closure_set(v___f_2622_, 1, v___x_2603_);
lean_closure_set(v___f_2622_, 2, v_declName_2608_);
lean_closure_set(v___f_2622_, 3, v___f_2617_);
lean_closure_set(v___f_2622_, 4, v___x_2618_);
lean_closure_set(v___f_2622_, 5, v_a_2600_);
lean_closure_set(v___f_2622_, 6, v_value_2610_);
lean_closure_set(v___f_2622_, 7, v_fvars_2598_);
lean_closure_set(v___f_2622_, 8, v_inst_2588_);
lean_closure_set(v___f_2622_, 9, v_inst_2589_);
lean_closure_set(v___f_2622_, 10, v_inst_2590_);
lean_closure_set(v___f_2622_, 11, v_pre_2591_);
lean_closure_set(v___f_2622_, 12, v_post_2592_);
lean_closure_set(v___f_2622_, 13, v___x_2619_);
lean_closure_set(v___f_2622_, 14, v___x_2620_);
lean_closure_set(v___f_2622_, 15, v___x_2621_);
lean_closure_set(v___f_2622_, 16, v_x_2596_);
lean_closure_set(v___f_2622_, 17, v_x_2597_);
lean_closure_set(v___f_2622_, 18, v_toBind_2613_);
v___x_2623_ = lean_expr_instantiate_rev(v_type_2609_, v_fvars_2598_);
lean_dec_ref(v_fvars_2598_);
lean_dec_ref(v_type_2609_);
v___x_2624_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2588_, v_inst_2589_, v_inst_2590_, v_pre_2591_, v_post_2592_, v_usedLetOnly_2593_, v_skipConstInApp_2594_, v_skipInstances_2595_, v_x_2596_, v_x_2597_, v___x_2623_, v_a_2600_);
v___x_2625_ = lean_apply_4(v_toBind_2613_, lean_box(0), lean_box(0), v___x_2624_, v___f_2622_);
return v___x_2625_;
}
else
{
lean_object* v_toBind_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___f_2630_; lean_object* v___x_2631_; lean_object* v___f_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; 
lean_dec_ref_known(v___x_2607_, 2);
lean_dec_ref(v___x_2603_);
v_toBind_2626_ = lean_ctor_get(v_inst_2588_, 1);
lean_inc_n(v_toBind_2626_, 2);
v___x_2627_ = lean_box(v_usedLetOnly_2593_);
v___x_2628_ = lean_box(v_skipConstInApp_2594_);
v___x_2629_ = lean_box(v_skipInstances_2595_);
lean_inc(v_a_2600_);
lean_inc(v_x_2597_);
lean_inc(v_post_2592_);
lean_inc(v_pre_2591_);
lean_inc_ref(v_inst_2590_);
lean_inc_n(v_inst_2589_, 2);
lean_inc_ref(v_inst_2588_);
v___f_2630_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3___boxed), 12, 11);
lean_closure_set(v___f_2630_, 0, v_inst_2588_);
lean_closure_set(v___f_2630_, 1, v_inst_2589_);
lean_closure_set(v___f_2630_, 2, v_inst_2590_);
lean_closure_set(v___f_2630_, 3, v_pre_2591_);
lean_closure_set(v___f_2630_, 4, v_post_2592_);
lean_closure_set(v___f_2630_, 5, v___x_2627_);
lean_closure_set(v___f_2630_, 6, v___x_2628_);
lean_closure_set(v___f_2630_, 7, v___x_2629_);
lean_closure_set(v___f_2630_, 8, v_x_2596_);
lean_closure_set(v___f_2630_, 9, v_x_2597_);
lean_closure_set(v___f_2630_, 10, v_a_2600_);
v___x_2631_ = lean_box(v_usedLetOnly_2593_);
lean_inc_ref(v_fvars_2598_);
v___f_2632_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__4___boxed), 6, 5);
lean_closure_set(v___f_2632_, 0, v_fvars_2598_);
lean_closure_set(v___f_2632_, 1, v___x_2631_);
lean_closure_set(v___f_2632_, 2, v_inst_2589_);
lean_closure_set(v___f_2632_, 3, v_toBind_2626_);
lean_closure_set(v___f_2632_, 4, v___f_2630_);
v___x_2633_ = lean_expr_instantiate_rev(v_e_2599_, v_fvars_2598_);
lean_dec_ref(v_fvars_2598_);
lean_dec_ref(v_e_2599_);
v___x_2634_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2588_, v_inst_2589_, v_inst_2590_, v_pre_2591_, v_post_2592_, v_usedLetOnly_2593_, v_skipConstInApp_2594_, v_skipInstances_2595_, v_x_2596_, v_x_2597_, v___x_2633_, v_a_2600_);
v___x_2635_ = lean_apply_4(v_toBind_2626_, lean_box(0), lean_box(0), v___x_2634_, v___f_2632_);
return v___x_2635_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2588_ = stack[0].m_obj;
lean_object* v_inst_2589_ = stack[1].m_obj;
lean_object* v_inst_2590_ = stack[2].m_obj;
lean_object* v_pre_2591_ = stack[3].m_obj;
lean_object* v_post_2592_ = stack[4].m_obj;
uint8_t v_usedLetOnly_2593_ = stack[5].m_num;
uint8_t v_skipConstInApp_2594_ = stack[6].m_num;
uint8_t v_skipInstances_2595_ = stack[7].m_num;
lean_object* v_x_2596_ = stack[8].m_obj;
lean_object* v_x_2597_ = stack[9].m_obj;
lean_object* v_fvars_2598_ = stack[10].m_obj;
lean_object* v_e_2599_ = stack[11].m_obj;
lean_object* v_a_2600_ = stack[12].m_obj;
lean_object* v_res_2636_;
v_res_2636_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(v_inst_2588_, v_inst_2589_, v_inst_2590_, v_pre_2591_, v_post_2592_, v_usedLetOnly_2593_, v_skipConstInApp_2594_, v_skipInstances_2595_, v_x_2596_, v_x_2597_, v_fvars_2598_, v_e_2599_, v_a_2600_);
stack->m_obj
 = v_res_2636_;
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__8(lean_object* v_expr_2637_, lean_object* v_data_2638_, lean_object* v_inst_2639_, lean_object* v_inst_2640_, lean_object* v_inst_2641_, lean_object* v_pre_2642_, lean_object* v_post_2643_, uint8_t v_usedLetOnly_2644_, uint8_t v_skipConstInApp_2645_, uint8_t v_skipInstances_2646_, lean_object* v_x_2647_, lean_object* v_x_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v_a_2651_){
_start:
{
size_t v___x_2652_; size_t v___x_2653_; uint8_t v___x_2654_; 
v___x_2652_ = lean_ptr_addr(v_expr_2637_);
v___x_2653_ = lean_ptr_addr(v_a_2651_);
v___x_2654_ = lean_usize_dec_eq(v___x_2652_, v___x_2653_);
if (v___x_2654_ == 0)
{
lean_object* v___x_2655_; lean_object* v___x_2656_; 
lean_dec_ref(v___y_2650_);
v___x_2655_ = l_Lean_Expr_mdata___override(v_data_2638_, v_a_2651_);
v___x_2656_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2639_, v_inst_2640_, v_inst_2641_, v_pre_2642_, v_post_2643_, v_usedLetOnly_2644_, v_skipConstInApp_2645_, v_skipInstances_2646_, v_x_2647_, v_x_2648_, v___x_2655_, v___y_2649_);
return v___x_2656_;
}
else
{
lean_object* v___x_2657_; 
lean_dec_ref(v_a_2651_);
lean_dec(v_data_2638_);
v___x_2657_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2639_, v_inst_2640_, v_inst_2641_, v_pre_2642_, v_post_2643_, v_usedLetOnly_2644_, v_skipConstInApp_2645_, v_skipInstances_2646_, v_x_2647_, v_x_2648_, v___y_2650_, v___y_2649_);
return v___x_2657_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_expr_2637_ = stack[0].m_obj;
lean_object* v_data_2638_ = stack[1].m_obj;
lean_object* v_inst_2639_ = stack[2].m_obj;
lean_object* v_inst_2640_ = stack[3].m_obj;
lean_object* v_inst_2641_ = stack[4].m_obj;
lean_object* v_pre_2642_ = stack[5].m_obj;
lean_object* v_post_2643_ = stack[6].m_obj;
uint8_t v_usedLetOnly_2644_ = stack[7].m_num;
uint8_t v_skipConstInApp_2645_ = stack[8].m_num;
uint8_t v_skipInstances_2646_ = stack[9].m_num;
lean_object* v_x_2647_ = stack[10].m_obj;
lean_object* v_x_2648_ = stack[11].m_obj;
lean_object* v___y_2649_ = stack[12].m_obj;
lean_object* v___y_2650_ = stack[13].m_obj;
lean_object* v_a_2651_ = stack[14].m_obj;
lean_object* v_res_2658_;
v_res_2658_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__8(v_expr_2637_, v_data_2638_, v_inst_2639_, v_inst_2640_, v_inst_2641_, v_pre_2642_, v_post_2643_, v_usedLetOnly_2644_, v_skipConstInApp_2645_, v_skipInstances_2646_, v_x_2647_, v_x_2648_, v___y_2649_, v___y_2650_, v_a_2651_);
stack->m_obj
 = v_res_2658_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__8___boxed(lean_object* v_expr_2659_, lean_object* v_data_2660_, lean_object* v_inst_2661_, lean_object* v_inst_2662_, lean_object* v_inst_2663_, lean_object* v_pre_2664_, lean_object* v_post_2665_, lean_object* v_usedLetOnly_2666_, lean_object* v_skipConstInApp_2667_, lean_object* v_skipInstances_2668_, lean_object* v_x_2669_, lean_object* v_x_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v_a_2673_){
_start:
{
uint8_t v_usedLetOnly_boxed_2674_; uint8_t v_skipConstInApp_boxed_2675_; uint8_t v_skipInstances_boxed_2676_; lean_object* v_res_2677_; 
v_usedLetOnly_boxed_2674_ = lean_unbox(v_usedLetOnly_2666_);
v_skipConstInApp_boxed_2675_ = lean_unbox(v_skipConstInApp_2667_);
v_skipInstances_boxed_2676_ = lean_unbox(v_skipInstances_2668_);
v_res_2677_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__8(v_expr_2659_, v_data_2660_, v_inst_2661_, v_inst_2662_, v_inst_2663_, v_pre_2664_, v_post_2665_, v_usedLetOnly_boxed_2674_, v_skipConstInApp_boxed_2675_, v_skipInstances_boxed_2676_, v_x_2669_, v_x_2670_, v___y_2671_, v___y_2672_, v_a_2673_);
lean_dec(v___y_2671_);
lean_dec_ref(v_expr_2659_);
return v_res_2677_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__10(lean_object* v_struct_2678_, lean_object* v_typeName_2679_, lean_object* v_idx_2680_, lean_object* v_inst_2681_, lean_object* v_inst_2682_, lean_object* v_inst_2683_, lean_object* v_pre_2684_, lean_object* v_post_2685_, uint8_t v_usedLetOnly_2686_, uint8_t v_skipConstInApp_2687_, uint8_t v_skipInstances_2688_, lean_object* v_x_2689_, lean_object* v_x_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v_a_2693_){
_start:
{
size_t v___x_2694_; size_t v___x_2695_; uint8_t v___x_2696_; 
v___x_2694_ = lean_ptr_addr(v_struct_2678_);
v___x_2695_ = lean_ptr_addr(v_a_2693_);
v___x_2696_ = lean_usize_dec_eq(v___x_2694_, v___x_2695_);
if (v___x_2696_ == 0)
{
lean_object* v___x_2697_; lean_object* v___x_2698_; 
lean_dec_ref(v___y_2692_);
v___x_2697_ = l_Lean_Expr_proj___override(v_typeName_2679_, v_idx_2680_, v_a_2693_);
v___x_2698_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2681_, v_inst_2682_, v_inst_2683_, v_pre_2684_, v_post_2685_, v_usedLetOnly_2686_, v_skipConstInApp_2687_, v_skipInstances_2688_, v_x_2689_, v_x_2690_, v___x_2697_, v___y_2691_);
return v___x_2698_;
}
else
{
lean_object* v___x_2699_; 
lean_dec_ref(v_a_2693_);
lean_dec(v_idx_2680_);
lean_dec(v_typeName_2679_);
v___x_2699_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2681_, v_inst_2682_, v_inst_2683_, v_pre_2684_, v_post_2685_, v_usedLetOnly_2686_, v_skipConstInApp_2687_, v_skipInstances_2688_, v_x_2689_, v_x_2690_, v___y_2692_, v___y_2691_);
return v___x_2699_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_struct_2678_ = stack[0].m_obj;
lean_object* v_typeName_2679_ = stack[1].m_obj;
lean_object* v_idx_2680_ = stack[2].m_obj;
lean_object* v_inst_2681_ = stack[3].m_obj;
lean_object* v_inst_2682_ = stack[4].m_obj;
lean_object* v_inst_2683_ = stack[5].m_obj;
lean_object* v_pre_2684_ = stack[6].m_obj;
lean_object* v_post_2685_ = stack[7].m_obj;
uint8_t v_usedLetOnly_2686_ = stack[8].m_num;
uint8_t v_skipConstInApp_2687_ = stack[9].m_num;
uint8_t v_skipInstances_2688_ = stack[10].m_num;
lean_object* v_x_2689_ = stack[11].m_obj;
lean_object* v_x_2690_ = stack[12].m_obj;
lean_object* v___y_2691_ = stack[13].m_obj;
lean_object* v___y_2692_ = stack[14].m_obj;
lean_object* v_a_2693_ = stack[15].m_obj;
lean_object* v_res_2700_;
v_res_2700_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__10(v_struct_2678_, v_typeName_2679_, v_idx_2680_, v_inst_2681_, v_inst_2682_, v_inst_2683_, v_pre_2684_, v_post_2685_, v_usedLetOnly_2686_, v_skipConstInApp_2687_, v_skipInstances_2688_, v_x_2689_, v_x_2690_, v___y_2691_, v___y_2692_, v_a_2693_);
stack->m_obj
 = v_res_2700_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__10___boxed(lean_object* v_struct_2701_, lean_object* v_typeName_2702_, lean_object* v_idx_2703_, lean_object* v_inst_2704_, lean_object* v_inst_2705_, lean_object* v_inst_2706_, lean_object* v_pre_2707_, lean_object* v_post_2708_, lean_object* v_usedLetOnly_2709_, lean_object* v_skipConstInApp_2710_, lean_object* v_skipInstances_2711_, lean_object* v_x_2712_, lean_object* v_x_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v_a_2716_){
_start:
{
uint8_t v_usedLetOnly_boxed_2717_; uint8_t v_skipConstInApp_boxed_2718_; uint8_t v_skipInstances_boxed_2719_; lean_object* v_res_2720_; 
v_usedLetOnly_boxed_2717_ = lean_unbox(v_usedLetOnly_2709_);
v_skipConstInApp_boxed_2718_ = lean_unbox(v_skipConstInApp_2710_);
v_skipInstances_boxed_2719_ = lean_unbox(v_skipInstances_2711_);
v_res_2720_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__10(v_struct_2701_, v_typeName_2702_, v_idx_2703_, v_inst_2704_, v_inst_2705_, v_inst_2706_, v_pre_2707_, v_post_2708_, v_usedLetOnly_boxed_2717_, v_skipConstInApp_boxed_2718_, v_skipInstances_boxed_2719_, v_x_2712_, v_x_2713_, v___y_2714_, v___y_2715_, v_a_2716_);
lean_dec(v___y_2714_);
lean_dec_ref(v_struct_2701_);
return v_res_2720_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11(lean_object* v_toApplicative_2721_, lean_object* v_inst_2722_, lean_object* v_inst_2723_, lean_object* v_inst_2724_, lean_object* v_pre_2725_, lean_object* v_post_2726_, uint8_t v_usedLetOnly_2727_, uint8_t v_skipConstInApp_2728_, uint8_t v_skipInstances_2729_, lean_object* v_x_2730_, lean_object* v_x_2731_, lean_object* v___y_2732_, lean_object* v___f_2733_, lean_object* v_toBind_2734_, lean_object* v_e_2735_, lean_object* v_a_2736_){
_start:
{
lean_object* v___y_2738_; 
switch(lean_obj_tag(v_a_2736_))
{
case 0:
{
lean_object* v_e_2770_; lean_object* v_toPure_2771_; lean_object* v___x_2772_; 
lean_dec_ref(v_e_2735_);
lean_dec(v_toBind_2734_);
lean_dec(v___f_2733_);
lean_dec(v_x_2731_);
lean_dec(v_post_2726_);
lean_dec(v_pre_2725_);
lean_dec_ref(v_inst_2724_);
lean_dec(v_inst_2723_);
lean_dec_ref(v_inst_2722_);
v_e_2770_ = lean_ctor_get(v_a_2736_, 0);
lean_inc_ref(v_e_2770_);
lean_dec_ref_known(v_a_2736_, 1);
v_toPure_2771_ = lean_ctor_get(v_toApplicative_2721_, 1);
lean_inc(v_toPure_2771_);
lean_dec_ref(v_toApplicative_2721_);
v___x_2772_ = lean_apply_2(v_toPure_2771_, lean_box(0), v_e_2770_);
return v___x_2772_;
}
case 1:
{
lean_object* v_e_2773_; lean_object* v___x_2774_; 
lean_dec_ref(v_e_2735_);
lean_dec(v_toBind_2734_);
lean_dec(v___f_2733_);
lean_dec_ref(v_toApplicative_2721_);
v_e_2773_ = lean_ctor_get(v_a_2736_, 0);
lean_inc_ref(v_e_2773_);
lean_dec_ref_known(v_a_2736_, 1);
v___x_2774_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2722_, v_inst_2723_, v_inst_2724_, v_pre_2725_, v_post_2726_, v_usedLetOnly_2727_, v_skipConstInApp_2728_, v_skipInstances_2729_, v_x_2730_, v_x_2731_, v_e_2773_, v___y_2732_);
return v___x_2774_;
}
default: 
{
lean_object* v_e_x3f_2775_; 
lean_dec_ref(v_toApplicative_2721_);
v_e_x3f_2775_ = lean_ctor_get(v_a_2736_, 0);
lean_inc(v_e_x3f_2775_);
lean_dec_ref_known(v_a_2736_, 1);
if (lean_obj_tag(v_e_x3f_2775_) == 0)
{
v___y_2738_ = v_e_2735_;
goto v___jp_2737_;
}
else
{
lean_object* v_val_2776_; 
lean_dec_ref(v_e_2735_);
v_val_2776_ = lean_ctor_get(v_e_x3f_2775_, 0);
lean_inc(v_val_2776_);
lean_dec_ref_known(v_e_x3f_2775_, 1);
v___y_2738_ = v_val_2776_;
goto v___jp_2737_;
}
}
}
v___jp_2737_:
{
switch(lean_obj_tag(v___y_2738_))
{
case 7:
{
lean_object* v___x_2739_; lean_object* v___x_2740_; 
lean_dec(v_toBind_2734_);
lean_dec(v___f_2733_);
v___x_2739_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_2740_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(v_inst_2722_, v_inst_2723_, v_inst_2724_, v_pre_2725_, v_post_2726_, v_usedLetOnly_2727_, v_skipConstInApp_2728_, v_skipInstances_2729_, v_x_2730_, v_x_2731_, v___x_2739_, v___y_2738_, v___y_2732_);
return v___x_2740_;
}
case 6:
{
lean_object* v___x_2741_; lean_object* v___x_2742_; 
lean_dec(v_toBind_2734_);
lean_dec(v___f_2733_);
v___x_2741_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_2742_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(v_inst_2722_, v_inst_2723_, v_inst_2724_, v_pre_2725_, v_post_2726_, v_usedLetOnly_2727_, v_skipConstInApp_2728_, v_skipInstances_2729_, v_x_2730_, v_x_2731_, v___x_2741_, v___y_2738_, v___y_2732_);
return v___x_2742_;
}
case 8:
{
lean_object* v___x_2743_; lean_object* v___x_2744_; 
lean_dec(v_toBind_2734_);
lean_dec(v___f_2733_);
v___x_2743_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_2744_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(v_inst_2722_, v_inst_2723_, v_inst_2724_, v_pre_2725_, v_post_2726_, v_usedLetOnly_2727_, v_skipConstInApp_2728_, v_skipInstances_2729_, v_x_2730_, v_x_2731_, v___x_2743_, v___y_2738_, v___y_2732_);
return v___x_2744_;
}
case 5:
{
lean_object* v_dummy_2745_; lean_object* v_nargs_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_3276__overap_2750_; lean_object* v___x_2751_; 
lean_dec(v_toBind_2734_);
lean_dec(v_x_2731_);
lean_dec(v_post_2726_);
lean_dec(v_pre_2725_);
lean_dec_ref(v_inst_2724_);
lean_dec(v_inst_2723_);
lean_dec_ref(v_inst_2722_);
v_dummy_2745_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_2746_ = l_Lean_Expr_getAppNumArgs(v___y_2738_);
lean_inc(v_nargs_2746_);
v___x_2747_ = lean_mk_array(v_nargs_2746_, v_dummy_2745_);
v___x_2748_ = lean_unsigned_to_nat(1u);
v___x_2749_ = lean_nat_sub(v_nargs_2746_, v___x_2748_);
lean_dec(v_nargs_2746_);
v___x_3276__overap_2750_ = l_Lean_Expr_withAppAux___redArg(v___f_2733_, v___y_2738_, v___x_2747_, v___x_2749_);
lean_inc(v___y_2732_);
v___x_2751_ = lean_apply_1(v___x_3276__overap_2750_, v___y_2732_);
return v___x_2751_;
}
case 10:
{
lean_object* v_data_2752_; lean_object* v_expr_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___f_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; 
lean_dec(v___f_2733_);
v_data_2752_ = lean_ctor_get(v___y_2738_, 0);
lean_inc(v_data_2752_);
v_expr_2753_ = lean_ctor_get(v___y_2738_, 1);
lean_inc_ref_n(v_expr_2753_, 2);
v___x_2754_ = lean_box(v_usedLetOnly_2727_);
v___x_2755_ = lean_box(v_skipConstInApp_2728_);
v___x_2756_ = lean_box(v_skipInstances_2729_);
lean_inc(v___y_2732_);
lean_inc(v_x_2731_);
lean_inc(v_post_2726_);
lean_inc(v_pre_2725_);
lean_inc_ref(v_inst_2724_);
lean_inc(v_inst_2723_);
lean_inc_ref(v_inst_2722_);
v___f_2757_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__8___boxed), 15, 14);
lean_closure_set(v___f_2757_, 0, v_expr_2753_);
lean_closure_set(v___f_2757_, 1, v_data_2752_);
lean_closure_set(v___f_2757_, 2, v_inst_2722_);
lean_closure_set(v___f_2757_, 3, v_inst_2723_);
lean_closure_set(v___f_2757_, 4, v_inst_2724_);
lean_closure_set(v___f_2757_, 5, v_pre_2725_);
lean_closure_set(v___f_2757_, 6, v_post_2726_);
lean_closure_set(v___f_2757_, 7, v___x_2754_);
lean_closure_set(v___f_2757_, 8, v___x_2755_);
lean_closure_set(v___f_2757_, 9, v___x_2756_);
lean_closure_set(v___f_2757_, 10, v_x_2730_);
lean_closure_set(v___f_2757_, 11, v_x_2731_);
lean_closure_set(v___f_2757_, 12, v___y_2732_);
lean_closure_set(v___f_2757_, 13, v___y_2738_);
v___x_2758_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2722_, v_inst_2723_, v_inst_2724_, v_pre_2725_, v_post_2726_, v_usedLetOnly_2727_, v_skipConstInApp_2728_, v_skipInstances_2729_, v_x_2730_, v_x_2731_, v_expr_2753_, v___y_2732_);
v___x_2759_ = lean_apply_4(v_toBind_2734_, lean_box(0), lean_box(0), v___x_2758_, v___f_2757_);
return v___x_2759_;
}
case 11:
{
lean_object* v_typeName_2760_; lean_object* v_idx_2761_; lean_object* v_struct_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___f_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; 
lean_dec(v___f_2733_);
v_typeName_2760_ = lean_ctor_get(v___y_2738_, 0);
lean_inc(v_typeName_2760_);
v_idx_2761_ = lean_ctor_get(v___y_2738_, 1);
lean_inc(v_idx_2761_);
v_struct_2762_ = lean_ctor_get(v___y_2738_, 2);
lean_inc_ref_n(v_struct_2762_, 2);
v___x_2763_ = lean_box(v_usedLetOnly_2727_);
v___x_2764_ = lean_box(v_skipConstInApp_2728_);
v___x_2765_ = lean_box(v_skipInstances_2729_);
lean_inc(v___y_2732_);
lean_inc(v_x_2731_);
lean_inc(v_post_2726_);
lean_inc(v_pre_2725_);
lean_inc_ref(v_inst_2724_);
lean_inc(v_inst_2723_);
lean_inc_ref(v_inst_2722_);
v___f_2766_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__10___boxed), 16, 15);
lean_closure_set(v___f_2766_, 0, v_struct_2762_);
lean_closure_set(v___f_2766_, 1, v_typeName_2760_);
lean_closure_set(v___f_2766_, 2, v_idx_2761_);
lean_closure_set(v___f_2766_, 3, v_inst_2722_);
lean_closure_set(v___f_2766_, 4, v_inst_2723_);
lean_closure_set(v___f_2766_, 5, v_inst_2724_);
lean_closure_set(v___f_2766_, 6, v_pre_2725_);
lean_closure_set(v___f_2766_, 7, v_post_2726_);
lean_closure_set(v___f_2766_, 8, v___x_2763_);
lean_closure_set(v___f_2766_, 9, v___x_2764_);
lean_closure_set(v___f_2766_, 10, v___x_2765_);
lean_closure_set(v___f_2766_, 11, v_x_2730_);
lean_closure_set(v___f_2766_, 12, v_x_2731_);
lean_closure_set(v___f_2766_, 13, v___y_2732_);
lean_closure_set(v___f_2766_, 14, v___y_2738_);
v___x_2767_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2722_, v_inst_2723_, v_inst_2724_, v_pre_2725_, v_post_2726_, v_usedLetOnly_2727_, v_skipConstInApp_2728_, v_skipInstances_2729_, v_x_2730_, v_x_2731_, v_struct_2762_, v___y_2732_);
v___x_2768_ = lean_apply_4(v_toBind_2734_, lean_box(0), lean_box(0), v___x_2767_, v___f_2766_);
return v___x_2768_;
}
default: 
{
lean_object* v___x_2769_; 
lean_dec(v_toBind_2734_);
lean_dec(v___f_2733_);
v___x_2769_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2722_, v_inst_2723_, v_inst_2724_, v_pre_2725_, v_post_2726_, v_usedLetOnly_2727_, v_skipConstInApp_2728_, v_skipInstances_2729_, v_x_2730_, v_x_2731_, v___y_2738_, v___y_2732_);
return v___x_2769_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_toApplicative_2721_ = stack[0].m_obj;
lean_object* v_inst_2722_ = stack[1].m_obj;
lean_object* v_inst_2723_ = stack[2].m_obj;
lean_object* v_inst_2724_ = stack[3].m_obj;
lean_object* v_pre_2725_ = stack[4].m_obj;
lean_object* v_post_2726_ = stack[5].m_obj;
uint8_t v_usedLetOnly_2727_ = stack[6].m_num;
uint8_t v_skipConstInApp_2728_ = stack[7].m_num;
uint8_t v_skipInstances_2729_ = stack[8].m_num;
lean_object* v_x_2730_ = stack[9].m_obj;
lean_object* v_x_2731_ = stack[10].m_obj;
lean_object* v___y_2732_ = stack[11].m_obj;
lean_object* v___f_2733_ = stack[12].m_obj;
lean_object* v_toBind_2734_ = stack[13].m_obj;
lean_object* v_e_2735_ = stack[14].m_obj;
lean_object* v_a_2736_ = stack[15].m_obj;
lean_object* v_res_2777_;
v_res_2777_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11(v_toApplicative_2721_, v_inst_2722_, v_inst_2723_, v_inst_2724_, v_pre_2725_, v_post_2726_, v_usedLetOnly_2727_, v_skipConstInApp_2728_, v_skipInstances_2729_, v_x_2730_, v_x_2731_, v___y_2732_, v___f_2733_, v_toBind_2734_, v_e_2735_, v_a_2736_);
stack->m_obj
 = v_res_2777_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___boxed(lean_object* v_toApplicative_2778_, lean_object* v_inst_2779_, lean_object* v_inst_2780_, lean_object* v_inst_2781_, lean_object* v_pre_2782_, lean_object* v_post_2783_, lean_object* v_usedLetOnly_2784_, lean_object* v_skipConstInApp_2785_, lean_object* v_skipInstances_2786_, lean_object* v_x_2787_, lean_object* v_x_2788_, lean_object* v___y_2789_, lean_object* v___f_2790_, lean_object* v_toBind_2791_, lean_object* v_e_2792_, lean_object* v_a_2793_){
_start:
{
uint8_t v_usedLetOnly_boxed_2794_; uint8_t v_skipConstInApp_boxed_2795_; uint8_t v_skipInstances_boxed_2796_; lean_object* v_res_2797_; 
v_usedLetOnly_boxed_2794_ = lean_unbox(v_usedLetOnly_2784_);
v_skipConstInApp_boxed_2795_ = lean_unbox(v_skipConstInApp_2785_);
v_skipInstances_boxed_2796_ = lean_unbox(v_skipInstances_2786_);
v_res_2797_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11(v_toApplicative_2778_, v_inst_2779_, v_inst_2780_, v_inst_2781_, v_pre_2782_, v_post_2783_, v_usedLetOnly_boxed_2794_, v_skipConstInApp_boxed_2795_, v_skipInstances_boxed_2796_, v_x_2787_, v_x_2788_, v___y_2789_, v___f_2790_, v_toBind_2791_, v_e_2792_, v_a_2793_);
lean_dec(v___y_2789_);
return v_res_2797_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12(lean_object* v_toApplicative_2798_, lean_object* v_inst_2799_, lean_object* v_inst_2800_, lean_object* v_inst_2801_, lean_object* v_pre_2802_, lean_object* v_post_2803_, uint8_t v_usedLetOnly_2804_, uint8_t v_skipConstInApp_2805_, uint8_t v_skipInstances_2806_, lean_object* v_x_2807_, lean_object* v_x_2808_, lean_object* v___f_2809_, lean_object* v_toBind_2810_, lean_object* v_e_2811_, lean_object* v_____r_2812_, lean_object* v___y_2813_){
_start:
{
lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___f_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; 
v___x_2814_ = lean_box(v_usedLetOnly_2804_);
v___x_2815_ = lean_box(v_skipConstInApp_2805_);
v___x_2816_ = lean_box(v_skipInstances_2806_);
lean_inc_ref(v_e_2811_);
lean_inc(v_toBind_2810_);
lean_inc(v___y_2813_);
lean_inc(v_pre_2802_);
v___f_2817_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___boxed), 16, 15);
lean_closure_set(v___f_2817_, 0, v_toApplicative_2798_);
lean_closure_set(v___f_2817_, 1, v_inst_2799_);
lean_closure_set(v___f_2817_, 2, v_inst_2800_);
lean_closure_set(v___f_2817_, 3, v_inst_2801_);
lean_closure_set(v___f_2817_, 4, v_pre_2802_);
lean_closure_set(v___f_2817_, 5, v_post_2803_);
lean_closure_set(v___f_2817_, 6, v___x_2814_);
lean_closure_set(v___f_2817_, 7, v___x_2815_);
lean_closure_set(v___f_2817_, 8, v___x_2816_);
lean_closure_set(v___f_2817_, 9, v_x_2807_);
lean_closure_set(v___f_2817_, 10, v_x_2808_);
lean_closure_set(v___f_2817_, 11, v___y_2813_);
lean_closure_set(v___f_2817_, 12, v___f_2809_);
lean_closure_set(v___f_2817_, 13, v_toBind_2810_);
lean_closure_set(v___f_2817_, 14, v_e_2811_);
v___x_2818_ = lean_apply_1(v_pre_2802_, v_e_2811_);
v___x_2819_ = lean_apply_4(v_toBind_2810_, lean_box(0), lean_box(0), v___x_2818_, v___f_2817_);
return v___x_2819_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_toApplicative_2798_ = stack[0].m_obj;
lean_object* v_inst_2799_ = stack[1].m_obj;
lean_object* v_inst_2800_ = stack[2].m_obj;
lean_object* v_inst_2801_ = stack[3].m_obj;
lean_object* v_pre_2802_ = stack[4].m_obj;
lean_object* v_post_2803_ = stack[5].m_obj;
uint8_t v_usedLetOnly_2804_ = stack[6].m_num;
uint8_t v_skipConstInApp_2805_ = stack[7].m_num;
uint8_t v_skipInstances_2806_ = stack[8].m_num;
lean_object* v_x_2807_ = stack[9].m_obj;
lean_object* v_x_2808_ = stack[10].m_obj;
lean_object* v___f_2809_ = stack[11].m_obj;
lean_object* v_toBind_2810_ = stack[12].m_obj;
lean_object* v_e_2811_ = stack[13].m_obj;
lean_object* v_____r_2812_ = stack[14].m_obj;
lean_object* v___y_2813_ = stack[15].m_obj;
lean_object* v_res_2820_;
v_res_2820_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12(v_toApplicative_2798_, v_inst_2799_, v_inst_2800_, v_inst_2801_, v_pre_2802_, v_post_2803_, v_usedLetOnly_2804_, v_skipConstInApp_2805_, v_skipInstances_2806_, v_x_2807_, v_x_2808_, v___f_2809_, v_toBind_2810_, v_e_2811_, v_____r_2812_, v___y_2813_);
stack->m_obj
 = v_res_2820_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12___boxed(lean_object* v_toApplicative_2821_, lean_object* v_inst_2822_, lean_object* v_inst_2823_, lean_object* v_inst_2824_, lean_object* v_pre_2825_, lean_object* v_post_2826_, lean_object* v_usedLetOnly_2827_, lean_object* v_skipConstInApp_2828_, lean_object* v_skipInstances_2829_, lean_object* v_x_2830_, lean_object* v_x_2831_, lean_object* v___f_2832_, lean_object* v_toBind_2833_, lean_object* v_e_2834_, lean_object* v_____r_2835_, lean_object* v___y_2836_){
_start:
{
uint8_t v_usedLetOnly_boxed_2837_; uint8_t v_skipConstInApp_boxed_2838_; uint8_t v_skipInstances_boxed_2839_; lean_object* v_res_2840_; 
v_usedLetOnly_boxed_2837_ = lean_unbox(v_usedLetOnly_2827_);
v_skipConstInApp_boxed_2838_ = lean_unbox(v_skipConstInApp_2828_);
v_skipInstances_boxed_2839_ = lean_unbox(v_skipInstances_2829_);
v_res_2840_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12(v_toApplicative_2821_, v_inst_2822_, v_inst_2823_, v_inst_2824_, v_pre_2825_, v_post_2826_, v_usedLetOnly_boxed_2837_, v_skipConstInApp_boxed_2838_, v_skipInstances_boxed_2839_, v_x_2830_, v_x_2831_, v___f_2832_, v_toBind_2833_, v_e_2834_, v_____r_2835_, v___y_2836_);
lean_dec(v___y_2836_);
return v_res_2840_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(lean_object* v_inst_2841_, lean_object* v_inst_2842_, lean_object* v_inst_2843_, lean_object* v_pre_2844_, lean_object* v_post_2845_, uint8_t v_usedLetOnly_2846_, uint8_t v_skipConstInApp_2847_, uint8_t v_skipInstances_2848_, lean_object* v_x_2849_, lean_object* v_x_2850_, lean_object* v_e_2851_, lean_object* v_a_2852_){
_start:
{
lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___f_2857_; lean_object* v___f_2858_; lean_object* v___x_2859_; lean_object* v_toApplicative_2860_; lean_object* v_toBind_2861_; lean_object* v___f_2862_; lean_object* v___f_2863_; lean_object* v___f_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___f_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___f_2872_; lean_object* v___f_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; 
v___x_2853_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0));
v___x_2854_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1));
lean_inc_ref_n(v_inst_2841_, 3);
v___x_2855_ = l_Lean_MonadCacheT_instMonad___redArg(v_x_2849_, v___x_2853_, v___x_2854_, v_inst_2841_);
v___x_2856_ = l_Lean_MonadCacheT_instMonadControl___redArg(v_x_2849_, v___x_2853_, v___x_2854_);
lean_inc_ref_n(v_inst_2843_, 3);
lean_inc_ref(v___x_2856_);
v___f_2857_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_2857_, 0, v___x_2856_);
lean_closure_set(v___f_2857_, 1, v_inst_2843_);
v___f_2858_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_2858_, 0, v___x_2856_);
lean_closure_set(v___f_2858_, 1, v_inst_2843_);
v___x_2859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2859_, 0, v___f_2857_);
lean_ctor_set(v___x_2859_, 1, v___f_2858_);
v_toApplicative_2860_ = lean_ctor_get(v_inst_2841_, 0);
lean_inc_ref_n(v_toApplicative_2860_, 6);
v_toBind_2861_ = lean_ctor_get(v_inst_2841_, 1);
lean_inc_n(v_toBind_2861_, 6);
v___f_2862_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2862_, 0, v_toApplicative_2860_);
lean_inc_n(v_x_2850_, 3);
lean_inc_n(v_a_2852_, 3);
lean_inc_ref_n(v_e_2851_, 2);
v___f_2863_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_2863_, 0, v_toApplicative_2860_);
lean_closure_set(v___f_2863_, 1, v___x_2853_);
lean_closure_set(v___f_2863_, 2, v___x_2854_);
lean_closure_set(v___f_2863_, 3, v_e_2851_);
lean_closure_set(v___f_2863_, 4, v_a_2852_);
lean_closure_set(v___f_2863_, 5, v_x_2850_);
lean_closure_set(v___f_2863_, 6, v_toBind_2861_);
v___f_2864_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__3___boxed), 5, 4);
lean_closure_set(v___f_2864_, 0, v_toApplicative_2860_);
lean_closure_set(v___f_2864_, 1, v___x_2853_);
lean_closure_set(v___f_2864_, 2, v___x_2854_);
lean_closure_set(v___f_2864_, 3, v_e_2851_);
v___x_2865_ = lean_box(v_skipInstances_2848_);
v___x_2866_ = lean_box(v_usedLetOnly_2846_);
v___x_2867_ = lean_box(v_skipConstInApp_2847_);
lean_inc_ref(v___x_2855_);
lean_inc(v_post_2845_);
lean_inc(v_pre_2844_);
lean_inc_n(v_inst_2842_, 2);
v___f_2868_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__9___boxed), 17, 14);
lean_closure_set(v___f_2868_, 0, v___x_2865_);
lean_closure_set(v___f_2868_, 1, v_inst_2841_);
lean_closure_set(v___f_2868_, 2, v_inst_2842_);
lean_closure_set(v___f_2868_, 3, v_inst_2843_);
lean_closure_set(v___f_2868_, 4, v_pre_2844_);
lean_closure_set(v___f_2868_, 5, v_post_2845_);
lean_closure_set(v___f_2868_, 6, v___x_2866_);
lean_closure_set(v___f_2868_, 7, v___x_2867_);
lean_closure_set(v___f_2868_, 8, v_x_2849_);
lean_closure_set(v___f_2868_, 9, v_x_2850_);
lean_closure_set(v___f_2868_, 10, v___x_2855_);
lean_closure_set(v___f_2868_, 11, v_toBind_2861_);
lean_closure_set(v___f_2868_, 12, v_toApplicative_2860_);
lean_closure_set(v___f_2868_, 13, v___f_2862_);
v___x_2869_ = lean_box(v_usedLetOnly_2846_);
v___x_2870_ = lean_box(v_skipConstInApp_2847_);
v___x_2871_ = lean_box(v_skipInstances_2848_);
v___f_2872_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12___boxed), 16, 14);
lean_closure_set(v___f_2872_, 0, v_toApplicative_2860_);
lean_closure_set(v___f_2872_, 1, v_inst_2841_);
lean_closure_set(v___f_2872_, 2, v_inst_2842_);
lean_closure_set(v___f_2872_, 3, v_inst_2843_);
lean_closure_set(v___f_2872_, 4, v_pre_2844_);
lean_closure_set(v___f_2872_, 5, v_post_2845_);
lean_closure_set(v___f_2872_, 6, v___x_2869_);
lean_closure_set(v___f_2872_, 7, v___x_2870_);
lean_closure_set(v___f_2872_, 8, v___x_2871_);
lean_closure_set(v___f_2872_, 9, v_x_2849_);
lean_closure_set(v___f_2872_, 10, v_x_2850_);
lean_closure_set(v___f_2872_, 11, v___f_2868_);
lean_closure_set(v___f_2872_, 12, v_toBind_2861_);
lean_closure_set(v___f_2872_, 13, v_e_2851_);
v___f_2873_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14___boxed), 13, 12);
lean_closure_set(v___f_2873_, 0, v_inst_2842_);
lean_closure_set(v___f_2873_, 1, v_x_2849_);
lean_closure_set(v___f_2873_, 2, v___x_2853_);
lean_closure_set(v___f_2873_, 3, v___x_2854_);
lean_closure_set(v___f_2873_, 4, v_inst_2841_);
lean_closure_set(v___f_2873_, 5, v___f_2872_);
lean_closure_set(v___f_2873_, 6, v___x_2859_);
lean_closure_set(v___f_2873_, 7, v___x_2855_);
lean_closure_set(v___f_2873_, 8, v_a_2852_);
lean_closure_set(v___f_2873_, 9, v_toBind_2861_);
lean_closure_set(v___f_2873_, 10, v___f_2863_);
lean_closure_set(v___f_2873_, 11, v_toApplicative_2860_);
v___x_2874_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2874_, 0, lean_box(0));
lean_closure_set(v___x_2874_, 1, lean_box(0));
lean_closure_set(v___x_2874_, 2, v_a_2852_);
v___x_2875_ = lean_apply_2(v_x_2850_, lean_box(0), v___x_2874_);
v___x_2876_ = lean_apply_4(v_toBind_2861_, lean_box(0), lean_box(0), v___x_2875_, v___f_2864_);
v___x_2877_ = lean_apply_4(v_toBind_2861_, lean_box(0), lean_box(0), v___x_2876_, v___f_2873_);
return v___x_2877_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2841_ = stack[0].m_obj;
lean_object* v_inst_2842_ = stack[1].m_obj;
lean_object* v_inst_2843_ = stack[2].m_obj;
lean_object* v_pre_2844_ = stack[3].m_obj;
lean_object* v_post_2845_ = stack[4].m_obj;
uint8_t v_usedLetOnly_2846_ = stack[5].m_num;
uint8_t v_skipConstInApp_2847_ = stack[6].m_num;
uint8_t v_skipInstances_2848_ = stack[7].m_num;
lean_object* v_x_2849_ = stack[8].m_obj;
lean_object* v_x_2850_ = stack[9].m_obj;
lean_object* v_e_2851_ = stack[10].m_obj;
lean_object* v_a_2852_ = stack[11].m_obj;
lean_object* v_res_2878_;
v_res_2878_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2841_, v_inst_2842_, v_inst_2843_, v_pre_2844_, v_post_2845_, v_usedLetOnly_2846_, v_skipConstInApp_2847_, v_skipInstances_2848_, v_x_2849_, v_x_2850_, v_e_2851_, v_a_2852_);
stack->m_obj
 = v_res_2878_;
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___lam__0(lean_object* v_toApplicative_2879_, lean_object* v_inst_2880_, lean_object* v_inst_2881_, lean_object* v_inst_2882_, lean_object* v_pre_2883_, lean_object* v_post_2884_, uint8_t v_usedLetOnly_2885_, uint8_t v_skipConstInApp_2886_, uint8_t v_skipInstances_2887_, lean_object* v_x_2888_, lean_object* v_x_2889_, lean_object* v_a_2890_, lean_object* v_e_2891_, lean_object* v_a_2892_){
_start:
{
lean_object* v___y_2894_; 
switch(lean_obj_tag(v_a_2892_))
{
case 0:
{
lean_object* v_e_2897_; lean_object* v_toPure_2898_; lean_object* v___x_2899_; 
lean_dec_ref(v_e_2891_);
lean_dec(v_x_2889_);
lean_dec(v_post_2884_);
lean_dec(v_pre_2883_);
lean_dec_ref(v_inst_2882_);
lean_dec(v_inst_2881_);
lean_dec_ref(v_inst_2880_);
v_e_2897_ = lean_ctor_get(v_a_2892_, 0);
lean_inc_ref(v_e_2897_);
lean_dec_ref_known(v_a_2892_, 1);
v_toPure_2898_ = lean_ctor_get(v_toApplicative_2879_, 1);
lean_inc(v_toPure_2898_);
lean_dec_ref(v_toApplicative_2879_);
v___x_2899_ = lean_apply_2(v_toPure_2898_, lean_box(0), v_e_2897_);
return v___x_2899_;
}
case 1:
{
lean_object* v_e_2900_; lean_object* v___x_2901_; 
lean_dec_ref(v_e_2891_);
lean_dec_ref(v_toApplicative_2879_);
v_e_2900_ = lean_ctor_get(v_a_2892_, 0);
lean_inc_ref(v_e_2900_);
lean_dec_ref_known(v_a_2892_, 1);
v___x_2901_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2880_, v_inst_2881_, v_inst_2882_, v_pre_2883_, v_post_2884_, v_usedLetOnly_2885_, v_skipConstInApp_2886_, v_skipInstances_2887_, v_x_2888_, v_x_2889_, v_e_2900_, v_a_2890_);
return v___x_2901_;
}
default: 
{
lean_object* v_e_x3f_2902_; 
lean_dec(v_x_2889_);
lean_dec(v_post_2884_);
lean_dec(v_pre_2883_);
lean_dec_ref(v_inst_2882_);
lean_dec(v_inst_2881_);
lean_dec_ref(v_inst_2880_);
v_e_x3f_2902_ = lean_ctor_get(v_a_2892_, 0);
lean_inc(v_e_x3f_2902_);
lean_dec_ref_known(v_a_2892_, 1);
if (lean_obj_tag(v_e_x3f_2902_) == 0)
{
v___y_2894_ = v_e_2891_;
goto v___jp_2893_;
}
else
{
lean_object* v_val_2903_; 
lean_dec_ref(v_e_2891_);
v_val_2903_ = lean_ctor_get(v_e_x3f_2902_, 0);
lean_inc(v_val_2903_);
lean_dec_ref_known(v_e_x3f_2902_, 1);
v___y_2894_ = v_val_2903_;
goto v___jp_2893_;
}
}
}
v___jp_2893_:
{
lean_object* v_toPure_2895_; lean_object* v___x_2896_; 
v_toPure_2895_ = lean_ctor_get(v_toApplicative_2879_, 1);
lean_inc(v_toPure_2895_);
lean_dec_ref(v_toApplicative_2879_);
v___x_2896_ = lean_apply_2(v_toPure_2895_, lean_box(0), v___y_2894_);
return v___x_2896_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_toApplicative_2879_ = stack[0].m_obj;
lean_object* v_inst_2880_ = stack[1].m_obj;
lean_object* v_inst_2881_ = stack[2].m_obj;
lean_object* v_inst_2882_ = stack[3].m_obj;
lean_object* v_pre_2883_ = stack[4].m_obj;
lean_object* v_post_2884_ = stack[5].m_obj;
uint8_t v_usedLetOnly_2885_ = stack[6].m_num;
uint8_t v_skipConstInApp_2886_ = stack[7].m_num;
uint8_t v_skipInstances_2887_ = stack[8].m_num;
lean_object* v_x_2888_ = stack[9].m_obj;
lean_object* v_x_2889_ = stack[10].m_obj;
lean_object* v_a_2890_ = stack[11].m_obj;
lean_object* v_e_2891_ = stack[12].m_obj;
lean_object* v_a_2892_ = stack[13].m_obj;
lean_object* v_res_2904_;
v_res_2904_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___lam__0(v_toApplicative_2879_, v_inst_2880_, v_inst_2881_, v_inst_2882_, v_pre_2883_, v_post_2884_, v_usedLetOnly_2885_, v_skipConstInApp_2886_, v_skipInstances_2887_, v_x_2888_, v_x_2889_, v_a_2890_, v_e_2891_, v_a_2892_);
stack->m_obj
 = v_res_2904_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___lam__0___boxed(lean_object* v_toApplicative_2905_, lean_object* v_inst_2906_, lean_object* v_inst_2907_, lean_object* v_inst_2908_, lean_object* v_pre_2909_, lean_object* v_post_2910_, lean_object* v_usedLetOnly_2911_, lean_object* v_skipConstInApp_2912_, lean_object* v_skipInstances_2913_, lean_object* v_x_2914_, lean_object* v_x_2915_, lean_object* v_a_2916_, lean_object* v_e_2917_, lean_object* v_a_2918_){
_start:
{
uint8_t v_usedLetOnly_boxed_2919_; uint8_t v_skipConstInApp_boxed_2920_; uint8_t v_skipInstances_boxed_2921_; lean_object* v_res_2922_; 
v_usedLetOnly_boxed_2919_ = lean_unbox(v_usedLetOnly_2911_);
v_skipConstInApp_boxed_2920_ = lean_unbox(v_skipConstInApp_2912_);
v_skipInstances_boxed_2921_ = lean_unbox(v_skipInstances_2913_);
v_res_2922_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___lam__0(v_toApplicative_2905_, v_inst_2906_, v_inst_2907_, v_inst_2908_, v_pre_2909_, v_post_2910_, v_usedLetOnly_boxed_2919_, v_skipConstInApp_boxed_2920_, v_skipInstances_boxed_2921_, v_x_2914_, v_x_2915_, v_a_2916_, v_e_2917_, v_a_2918_);
lean_dec(v_a_2916_);
return v_res_2922_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(lean_object* v_inst_2923_, lean_object* v_inst_2924_, lean_object* v_inst_2925_, lean_object* v_pre_2926_, lean_object* v_post_2927_, uint8_t v_usedLetOnly_2928_, uint8_t v_skipConstInApp_2929_, uint8_t v_skipInstances_2930_, lean_object* v_x_2931_, lean_object* v_x_2932_, lean_object* v_e_2933_, lean_object* v_a_2934_){
_start:
{
lean_object* v_toApplicative_2935_; lean_object* v_toBind_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___f_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; 
v_toApplicative_2935_ = lean_ctor_get(v_inst_2923_, 0);
lean_inc_ref(v_toApplicative_2935_);
v_toBind_2936_ = lean_ctor_get(v_inst_2923_, 1);
lean_inc(v_toBind_2936_);
v___x_2937_ = lean_box(v_usedLetOnly_2928_);
v___x_2938_ = lean_box(v_skipConstInApp_2929_);
v___x_2939_ = lean_box(v_skipInstances_2930_);
lean_inc_ref(v_e_2933_);
lean_inc(v_a_2934_);
lean_inc(v_post_2927_);
v___f_2940_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___lam__0___boxed), 14, 13);
lean_closure_set(v___f_2940_, 0, v_toApplicative_2935_);
lean_closure_set(v___f_2940_, 1, v_inst_2923_);
lean_closure_set(v___f_2940_, 2, v_inst_2924_);
lean_closure_set(v___f_2940_, 3, v_inst_2925_);
lean_closure_set(v___f_2940_, 4, v_pre_2926_);
lean_closure_set(v___f_2940_, 5, v_post_2927_);
lean_closure_set(v___f_2940_, 6, v___x_2937_);
lean_closure_set(v___f_2940_, 7, v___x_2938_);
lean_closure_set(v___f_2940_, 8, v___x_2939_);
lean_closure_set(v___f_2940_, 9, v_x_2931_);
lean_closure_set(v___f_2940_, 10, v_x_2932_);
lean_closure_set(v___f_2940_, 11, v_a_2934_);
lean_closure_set(v___f_2940_, 12, v_e_2933_);
v___x_2941_ = lean_apply_1(v_post_2927_, v_e_2933_);
v___x_2942_ = lean_apply_4(v_toBind_2936_, lean_box(0), lean_box(0), v___x_2941_, v___f_2940_);
return v___x_2942_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2923_ = stack[0].m_obj;
lean_object* v_inst_2924_ = stack[1].m_obj;
lean_object* v_inst_2925_ = stack[2].m_obj;
lean_object* v_pre_2926_ = stack[3].m_obj;
lean_object* v_post_2927_ = stack[4].m_obj;
uint8_t v_usedLetOnly_2928_ = stack[5].m_num;
uint8_t v_skipConstInApp_2929_ = stack[6].m_num;
uint8_t v_skipInstances_2930_ = stack[7].m_num;
lean_object* v_x_2931_ = stack[8].m_obj;
lean_object* v_x_2932_ = stack[9].m_obj;
lean_object* v_e_2933_ = stack[10].m_obj;
lean_object* v_a_2934_ = stack[11].m_obj;
lean_object* v_res_2943_;
v_res_2943_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2923_, v_inst_2924_, v_inst_2925_, v_pre_2926_, v_post_2927_, v_usedLetOnly_2928_, v_skipConstInApp_2929_, v_skipInstances_2930_, v_x_2931_, v_x_2932_, v_e_2933_, v_a_2934_);
stack->m_obj
 = v_res_2943_;
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3(lean_object* v_inst_2944_, lean_object* v_inst_2945_, lean_object* v_inst_2946_, lean_object* v_pre_2947_, lean_object* v_post_2948_, uint8_t v_usedLetOnly_2949_, uint8_t v_skipConstInApp_2950_, uint8_t v_skipInstances_2951_, lean_object* v_x_2952_, lean_object* v_x_2953_, lean_object* v_a_2954_, lean_object* v_a_2955_){
_start:
{
lean_object* v___x_2956_; 
v___x_2956_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2944_, v_inst_2945_, v_inst_2946_, v_pre_2947_, v_post_2948_, v_usedLetOnly_2949_, v_skipConstInApp_2950_, v_skipInstances_2951_, v_x_2952_, v_x_2953_, v_a_2955_, v_a_2954_);
return v___x_2956_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2944_ = stack[0].m_obj;
lean_object* v_inst_2945_ = stack[1].m_obj;
lean_object* v_inst_2946_ = stack[2].m_obj;
lean_object* v_pre_2947_ = stack[3].m_obj;
lean_object* v_post_2948_ = stack[4].m_obj;
uint8_t v_usedLetOnly_2949_ = stack[5].m_num;
uint8_t v_skipConstInApp_2950_ = stack[6].m_num;
uint8_t v_skipInstances_2951_ = stack[7].m_num;
lean_object* v_x_2952_ = stack[8].m_obj;
lean_object* v_x_2953_ = stack[9].m_obj;
lean_object* v_a_2954_ = stack[10].m_obj;
lean_object* v_a_2955_ = stack[11].m_obj;
lean_object* v_res_2957_;
v_res_2957_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3(v_inst_2944_, v_inst_2945_, v_inst_2946_, v_pre_2947_, v_post_2948_, v_usedLetOnly_2949_, v_skipConstInApp_2950_, v_skipInstances_2951_, v_x_2952_, v_x_2953_, v_a_2954_, v_a_2955_);
stack->m_obj
 = v_res_2957_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___boxed(lean_object* v_inst_2958_, lean_object* v_inst_2959_, lean_object* v_inst_2960_, lean_object* v_pre_2961_, lean_object* v_post_2962_, lean_object* v_usedLetOnly_2963_, lean_object* v_skipConstInApp_2964_, lean_object* v_skipInstances_2965_, lean_object* v_x_2966_, lean_object* v_x_2967_, lean_object* v_e_2968_, lean_object* v_a_2969_){
_start:
{
uint8_t v_usedLetOnly_boxed_2970_; uint8_t v_skipConstInApp_boxed_2971_; uint8_t v_skipInstances_boxed_2972_; lean_object* v_res_2973_; 
v_usedLetOnly_boxed_2970_ = lean_unbox(v_usedLetOnly_2963_);
v_skipConstInApp_boxed_2971_ = lean_unbox(v_skipConstInApp_2964_);
v_skipInstances_boxed_2972_ = lean_unbox(v_skipInstances_2965_);
v_res_2973_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2958_, v_inst_2959_, v_inst_2960_, v_pre_2961_, v_post_2962_, v_usedLetOnly_boxed_2970_, v_skipConstInApp_boxed_2971_, v_skipInstances_boxed_2972_, v_x_2966_, v_x_2967_, v_e_2968_, v_a_2969_);
lean_dec(v_a_2969_);
return v_res_2973_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___boxed(lean_object* v_inst_2974_, lean_object* v_inst_2975_, lean_object* v_inst_2976_, lean_object* v_pre_2977_, lean_object* v_post_2978_, lean_object* v_usedLetOnly_2979_, lean_object* v_skipConstInApp_2980_, lean_object* v_skipInstances_2981_, lean_object* v_x_2982_, lean_object* v_x_2983_, lean_object* v_fvars_2984_, lean_object* v_e_2985_, lean_object* v_a_2986_){
_start:
{
uint8_t v_usedLetOnly_boxed_2987_; uint8_t v_skipConstInApp_boxed_2988_; uint8_t v_skipInstances_boxed_2989_; lean_object* v_res_2990_; 
v_usedLetOnly_boxed_2987_ = lean_unbox(v_usedLetOnly_2979_);
v_skipConstInApp_boxed_2988_ = lean_unbox(v_skipConstInApp_2980_);
v_skipInstances_boxed_2989_ = lean_unbox(v_skipInstances_2981_);
v_res_2990_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(v_inst_2974_, v_inst_2975_, v_inst_2976_, v_pre_2977_, v_post_2978_, v_usedLetOnly_boxed_2987_, v_skipConstInApp_boxed_2988_, v_skipInstances_boxed_2989_, v_x_2982_, v_x_2983_, v_fvars_2984_, v_e_2985_, v_a_2986_);
lean_dec(v_a_2986_);
return v_res_2990_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___boxed(lean_object* v_inst_2991_, lean_object* v_inst_2992_, lean_object* v_inst_2993_, lean_object* v_pre_2994_, lean_object* v_post_2995_, lean_object* v_usedLetOnly_2996_, lean_object* v_skipConstInApp_2997_, lean_object* v_skipInstances_2998_, lean_object* v_x_2999_, lean_object* v_x_3000_, lean_object* v_fvars_3001_, lean_object* v_e_3002_, lean_object* v_a_3003_){
_start:
{
uint8_t v_usedLetOnly_boxed_3004_; uint8_t v_skipConstInApp_boxed_3005_; uint8_t v_skipInstances_boxed_3006_; lean_object* v_res_3007_; 
v_usedLetOnly_boxed_3004_ = lean_unbox(v_usedLetOnly_2996_);
v_skipConstInApp_boxed_3005_ = lean_unbox(v_skipConstInApp_2997_);
v_skipInstances_boxed_3006_ = lean_unbox(v_skipInstances_2998_);
v_res_3007_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(v_inst_2991_, v_inst_2992_, v_inst_2993_, v_pre_2994_, v_post_2995_, v_usedLetOnly_boxed_3004_, v_skipConstInApp_boxed_3005_, v_skipInstances_boxed_3006_, v_x_2999_, v_x_3000_, v_fvars_3001_, v_e_3002_, v_a_3003_);
lean_dec(v_a_3003_);
return v_res_3007_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___boxed(lean_object* v_inst_3008_, lean_object* v_inst_3009_, lean_object* v_inst_3010_, lean_object* v_pre_3011_, lean_object* v_post_3012_, lean_object* v_usedLetOnly_3013_, lean_object* v_skipConstInApp_3014_, lean_object* v_skipInstances_3015_, lean_object* v_x_3016_, lean_object* v_x_3017_, lean_object* v_fvars_3018_, lean_object* v_e_3019_, lean_object* v_a_3020_){
_start:
{
uint8_t v_usedLetOnly_boxed_3021_; uint8_t v_skipConstInApp_boxed_3022_; uint8_t v_skipInstances_boxed_3023_; lean_object* v_res_3024_; 
v_usedLetOnly_boxed_3021_ = lean_unbox(v_usedLetOnly_3013_);
v_skipConstInApp_boxed_3022_ = lean_unbox(v_skipConstInApp_3014_);
v_skipInstances_boxed_3023_ = lean_unbox(v_skipInstances_3015_);
v_res_3024_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(v_inst_3008_, v_inst_3009_, v_inst_3010_, v_pre_3011_, v_post_3012_, v_usedLetOnly_boxed_3021_, v_skipConstInApp_boxed_3022_, v_skipInstances_boxed_3023_, v_x_3016_, v_x_3017_, v_fvars_3018_, v_e_3019_, v_a_3020_);
lean_dec(v_a_3020_);
return v_res_3024_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit(lean_object* v_m_3025_, lean_object* v_inst_3026_, lean_object* v_inst_3027_, lean_object* v_inst_3028_, lean_object* v_pre_3029_, lean_object* v_post_3030_, uint8_t v_usedLetOnly_3031_, uint8_t v_skipConstInApp_3032_, uint8_t v_skipInstances_3033_, lean_object* v_x_3034_, lean_object* v_x_3035_, lean_object* v_e_3036_, lean_object* v_a_3037_){
_start:
{
lean_object* v___x_3038_; 
v___x_3038_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_3026_, v_inst_3027_, v_inst_3028_, v_pre_3029_, v_post_3030_, v_usedLetOnly_3031_, v_skipConstInApp_3032_, v_skipInstances_3033_, v_x_3034_, v_x_3035_, v_e_3036_, v_a_3037_);
return v___x_3038_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_3026_ = stack[1].m_obj;
lean_object* v_inst_3027_ = stack[2].m_obj;
lean_object* v_inst_3028_ = stack[3].m_obj;
lean_object* v_pre_3029_ = stack[4].m_obj;
lean_object* v_post_3030_ = stack[5].m_obj;
uint8_t v_usedLetOnly_3031_ = stack[6].m_num;
uint8_t v_skipConstInApp_3032_ = stack[7].m_num;
uint8_t v_skipInstances_3033_ = stack[8].m_num;
lean_object* v_x_3034_ = stack[9].m_obj;
lean_object* v_x_3035_ = stack[10].m_obj;
lean_object* v_e_3036_ = stack[11].m_obj;
lean_object* v_a_3037_ = stack[12].m_obj;
lean_object* v_res_3039_;
v_res_3039_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit(lean_box(0), v_inst_3026_, v_inst_3027_, v_inst_3028_, v_pre_3029_, v_post_3030_, v_usedLetOnly_3031_, v_skipConstInApp_3032_, v_skipInstances_3033_, v_x_3034_, v_x_3035_, v_e_3036_, v_a_3037_);
stack->m_obj
 = v_res_3039_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___boxed(lean_object* v_m_3040_, lean_object* v_inst_3041_, lean_object* v_inst_3042_, lean_object* v_inst_3043_, lean_object* v_pre_3044_, lean_object* v_post_3045_, lean_object* v_usedLetOnly_3046_, lean_object* v_skipConstInApp_3047_, lean_object* v_skipInstances_3048_, lean_object* v_x_3049_, lean_object* v_x_3050_, lean_object* v_e_3051_, lean_object* v_a_3052_){
_start:
{
uint8_t v_usedLetOnly_boxed_3053_; uint8_t v_skipConstInApp_boxed_3054_; uint8_t v_skipInstances_boxed_3055_; lean_object* v_res_3056_; 
v_usedLetOnly_boxed_3053_ = lean_unbox(v_usedLetOnly_3046_);
v_skipConstInApp_boxed_3054_ = lean_unbox(v_skipConstInApp_3047_);
v_skipInstances_boxed_3055_ = lean_unbox(v_skipInstances_3048_);
v_res_3056_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit(v_m_3040_, v_inst_3041_, v_inst_3042_, v_inst_3043_, v_pre_3044_, v_post_3045_, v_usedLetOnly_boxed_3053_, v_skipConstInApp_boxed_3054_, v_skipInstances_boxed_3055_, v_x_3049_, v_x_3050_, v_e_3051_, v_a_3052_);
lean_dec(v_a_3052_);
return v_res_3056_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet(lean_object* v_m_3057_, lean_object* v_inst_3058_, lean_object* v_inst_3059_, lean_object* v_inst_3060_, lean_object* v_pre_3061_, lean_object* v_post_3062_, uint8_t v_usedLetOnly_3063_, uint8_t v_skipConstInApp_3064_, uint8_t v_skipInstances_3065_, lean_object* v_x_3066_, lean_object* v_x_3067_, lean_object* v_fvars_3068_, lean_object* v_e_3069_, lean_object* v_a_3070_){
_start:
{
lean_object* v___x_3071_; 
v___x_3071_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(v_inst_3058_, v_inst_3059_, v_inst_3060_, v_pre_3061_, v_post_3062_, v_usedLetOnly_3063_, v_skipConstInApp_3064_, v_skipInstances_3065_, v_x_3066_, v_x_3067_, v_fvars_3068_, v_e_3069_, v_a_3070_);
return v___x_3071_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_3058_ = stack[1].m_obj;
lean_object* v_inst_3059_ = stack[2].m_obj;
lean_object* v_inst_3060_ = stack[3].m_obj;
lean_object* v_pre_3061_ = stack[4].m_obj;
lean_object* v_post_3062_ = stack[5].m_obj;
uint8_t v_usedLetOnly_3063_ = stack[6].m_num;
uint8_t v_skipConstInApp_3064_ = stack[7].m_num;
uint8_t v_skipInstances_3065_ = stack[8].m_num;
lean_object* v_x_3066_ = stack[9].m_obj;
lean_object* v_x_3067_ = stack[10].m_obj;
lean_object* v_fvars_3068_ = stack[11].m_obj;
lean_object* v_e_3069_ = stack[12].m_obj;
lean_object* v_a_3070_ = stack[13].m_obj;
lean_object* v_res_3072_;
v_res_3072_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet(lean_box(0), v_inst_3058_, v_inst_3059_, v_inst_3060_, v_pre_3061_, v_post_3062_, v_usedLetOnly_3063_, v_skipConstInApp_3064_, v_skipInstances_3065_, v_x_3066_, v_x_3067_, v_fvars_3068_, v_e_3069_, v_a_3070_);
stack->m_obj
 = v_res_3072_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___boxed(lean_object* v_m_3073_, lean_object* v_inst_3074_, lean_object* v_inst_3075_, lean_object* v_inst_3076_, lean_object* v_pre_3077_, lean_object* v_post_3078_, lean_object* v_usedLetOnly_3079_, lean_object* v_skipConstInApp_3080_, lean_object* v_skipInstances_3081_, lean_object* v_x_3082_, lean_object* v_x_3083_, lean_object* v_fvars_3084_, lean_object* v_e_3085_, lean_object* v_a_3086_){
_start:
{
uint8_t v_usedLetOnly_boxed_3087_; uint8_t v_skipConstInApp_boxed_3088_; uint8_t v_skipInstances_boxed_3089_; lean_object* v_res_3090_; 
v_usedLetOnly_boxed_3087_ = lean_unbox(v_usedLetOnly_3079_);
v_skipConstInApp_boxed_3088_ = lean_unbox(v_skipConstInApp_3080_);
v_skipInstances_boxed_3089_ = lean_unbox(v_skipInstances_3081_);
v_res_3090_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet(v_m_3073_, v_inst_3074_, v_inst_3075_, v_inst_3076_, v_pre_3077_, v_post_3078_, v_usedLetOnly_boxed_3087_, v_skipConstInApp_boxed_3088_, v_skipInstances_boxed_3089_, v_x_3082_, v_x_3083_, v_fvars_3084_, v_e_3085_, v_a_3086_);
lean_dec(v_a_3086_);
return v_res_3090_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost(lean_object* v_m_3091_, lean_object* v_inst_3092_, lean_object* v_inst_3093_, lean_object* v_inst_3094_, lean_object* v_pre_3095_, lean_object* v_post_3096_, uint8_t v_usedLetOnly_3097_, uint8_t v_skipConstInApp_3098_, uint8_t v_skipInstances_3099_, lean_object* v_x_3100_, lean_object* v_x_3101_, lean_object* v_e_3102_, lean_object* v_a_3103_){
_start:
{
lean_object* v___x_3104_; 
v___x_3104_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_3092_, v_inst_3093_, v_inst_3094_, v_pre_3095_, v_post_3096_, v_usedLetOnly_3097_, v_skipConstInApp_3098_, v_skipInstances_3099_, v_x_3100_, v_x_3101_, v_e_3102_, v_a_3103_);
return v___x_3104_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_3092_ = stack[1].m_obj;
lean_object* v_inst_3093_ = stack[2].m_obj;
lean_object* v_inst_3094_ = stack[3].m_obj;
lean_object* v_pre_3095_ = stack[4].m_obj;
lean_object* v_post_3096_ = stack[5].m_obj;
uint8_t v_usedLetOnly_3097_ = stack[6].m_num;
uint8_t v_skipConstInApp_3098_ = stack[7].m_num;
uint8_t v_skipInstances_3099_ = stack[8].m_num;
lean_object* v_x_3100_ = stack[9].m_obj;
lean_object* v_x_3101_ = stack[10].m_obj;
lean_object* v_e_3102_ = stack[11].m_obj;
lean_object* v_a_3103_ = stack[12].m_obj;
lean_object* v_res_3105_;
v_res_3105_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost(lean_box(0), v_inst_3092_, v_inst_3093_, v_inst_3094_, v_pre_3095_, v_post_3096_, v_usedLetOnly_3097_, v_skipConstInApp_3098_, v_skipInstances_3099_, v_x_3100_, v_x_3101_, v_e_3102_, v_a_3103_);
stack->m_obj
 = v_res_3105_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___boxed(lean_object* v_m_3106_, lean_object* v_inst_3107_, lean_object* v_inst_3108_, lean_object* v_inst_3109_, lean_object* v_pre_3110_, lean_object* v_post_3111_, lean_object* v_usedLetOnly_3112_, lean_object* v_skipConstInApp_3113_, lean_object* v_skipInstances_3114_, lean_object* v_x_3115_, lean_object* v_x_3116_, lean_object* v_e_3117_, lean_object* v_a_3118_){
_start:
{
uint8_t v_usedLetOnly_boxed_3119_; uint8_t v_skipConstInApp_boxed_3120_; uint8_t v_skipInstances_boxed_3121_; lean_object* v_res_3122_; 
v_usedLetOnly_boxed_3119_ = lean_unbox(v_usedLetOnly_3112_);
v_skipConstInApp_boxed_3120_ = lean_unbox(v_skipConstInApp_3113_);
v_skipInstances_boxed_3121_ = lean_unbox(v_skipInstances_3114_);
v_res_3122_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost(v_m_3106_, v_inst_3107_, v_inst_3108_, v_inst_3109_, v_pre_3110_, v_post_3111_, v_usedLetOnly_boxed_3119_, v_skipConstInApp_boxed_3120_, v_skipInstances_boxed_3121_, v_x_3115_, v_x_3116_, v_e_3117_, v_a_3118_);
lean_dec(v_a_3118_);
return v_res_3122_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda(lean_object* v_m_3123_, lean_object* v_inst_3124_, lean_object* v_inst_3125_, lean_object* v_inst_3126_, lean_object* v_pre_3127_, lean_object* v_post_3128_, uint8_t v_usedLetOnly_3129_, uint8_t v_skipConstInApp_3130_, uint8_t v_skipInstances_3131_, lean_object* v_x_3132_, lean_object* v_x_3133_, lean_object* v_fvars_3134_, lean_object* v_e_3135_, lean_object* v_a_3136_){
_start:
{
lean_object* v___x_3137_; 
v___x_3137_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(v_inst_3124_, v_inst_3125_, v_inst_3126_, v_pre_3127_, v_post_3128_, v_usedLetOnly_3129_, v_skipConstInApp_3130_, v_skipInstances_3131_, v_x_3132_, v_x_3133_, v_fvars_3134_, v_e_3135_, v_a_3136_);
return v___x_3137_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_3124_ = stack[1].m_obj;
lean_object* v_inst_3125_ = stack[2].m_obj;
lean_object* v_inst_3126_ = stack[3].m_obj;
lean_object* v_pre_3127_ = stack[4].m_obj;
lean_object* v_post_3128_ = stack[5].m_obj;
uint8_t v_usedLetOnly_3129_ = stack[6].m_num;
uint8_t v_skipConstInApp_3130_ = stack[7].m_num;
uint8_t v_skipInstances_3131_ = stack[8].m_num;
lean_object* v_x_3132_ = stack[9].m_obj;
lean_object* v_x_3133_ = stack[10].m_obj;
lean_object* v_fvars_3134_ = stack[11].m_obj;
lean_object* v_e_3135_ = stack[12].m_obj;
lean_object* v_a_3136_ = stack[13].m_obj;
lean_object* v_res_3138_;
v_res_3138_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda(lean_box(0), v_inst_3124_, v_inst_3125_, v_inst_3126_, v_pre_3127_, v_post_3128_, v_usedLetOnly_3129_, v_skipConstInApp_3130_, v_skipInstances_3131_, v_x_3132_, v_x_3133_, v_fvars_3134_, v_e_3135_, v_a_3136_);
stack->m_obj
 = v_res_3138_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___boxed(lean_object* v_m_3139_, lean_object* v_inst_3140_, lean_object* v_inst_3141_, lean_object* v_inst_3142_, lean_object* v_pre_3143_, lean_object* v_post_3144_, lean_object* v_usedLetOnly_3145_, lean_object* v_skipConstInApp_3146_, lean_object* v_skipInstances_3147_, lean_object* v_x_3148_, lean_object* v_x_3149_, lean_object* v_fvars_3150_, lean_object* v_e_3151_, lean_object* v_a_3152_){
_start:
{
uint8_t v_usedLetOnly_boxed_3153_; uint8_t v_skipConstInApp_boxed_3154_; uint8_t v_skipInstances_boxed_3155_; lean_object* v_res_3156_; 
v_usedLetOnly_boxed_3153_ = lean_unbox(v_usedLetOnly_3145_);
v_skipConstInApp_boxed_3154_ = lean_unbox(v_skipConstInApp_3146_);
v_skipInstances_boxed_3155_ = lean_unbox(v_skipInstances_3147_);
v_res_3156_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda(v_m_3139_, v_inst_3140_, v_inst_3141_, v_inst_3142_, v_pre_3143_, v_post_3144_, v_usedLetOnly_boxed_3153_, v_skipConstInApp_boxed_3154_, v_skipInstances_boxed_3155_, v_x_3148_, v_x_3149_, v_fvars_3150_, v_e_3151_, v_a_3152_);
lean_dec(v_a_3152_);
return v_res_3156_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall(lean_object* v_m_3157_, lean_object* v_inst_3158_, lean_object* v_inst_3159_, lean_object* v_inst_3160_, lean_object* v_pre_3161_, lean_object* v_post_3162_, uint8_t v_usedLetOnly_3163_, uint8_t v_skipConstInApp_3164_, uint8_t v_skipInstances_3165_, lean_object* v_x_3166_, lean_object* v_x_3167_, lean_object* v_fvars_3168_, lean_object* v_e_3169_, lean_object* v_a_3170_){
_start:
{
lean_object* v___x_3171_; 
v___x_3171_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(v_inst_3158_, v_inst_3159_, v_inst_3160_, v_pre_3161_, v_post_3162_, v_usedLetOnly_3163_, v_skipConstInApp_3164_, v_skipInstances_3165_, v_x_3166_, v_x_3167_, v_fvars_3168_, v_e_3169_, v_a_3170_);
return v___x_3171_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_3158_ = stack[1].m_obj;
lean_object* v_inst_3159_ = stack[2].m_obj;
lean_object* v_inst_3160_ = stack[3].m_obj;
lean_object* v_pre_3161_ = stack[4].m_obj;
lean_object* v_post_3162_ = stack[5].m_obj;
uint8_t v_usedLetOnly_3163_ = stack[6].m_num;
uint8_t v_skipConstInApp_3164_ = stack[7].m_num;
uint8_t v_skipInstances_3165_ = stack[8].m_num;
lean_object* v_x_3166_ = stack[9].m_obj;
lean_object* v_x_3167_ = stack[10].m_obj;
lean_object* v_fvars_3168_ = stack[11].m_obj;
lean_object* v_e_3169_ = stack[12].m_obj;
lean_object* v_a_3170_ = stack[13].m_obj;
lean_object* v_res_3172_;
v_res_3172_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall(lean_box(0), v_inst_3158_, v_inst_3159_, v_inst_3160_, v_pre_3161_, v_post_3162_, v_usedLetOnly_3163_, v_skipConstInApp_3164_, v_skipInstances_3165_, v_x_3166_, v_x_3167_, v_fvars_3168_, v_e_3169_, v_a_3170_);
stack->m_obj
 = v_res_3172_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___boxed(lean_object* v_m_3173_, lean_object* v_inst_3174_, lean_object* v_inst_3175_, lean_object* v_inst_3176_, lean_object* v_pre_3177_, lean_object* v_post_3178_, lean_object* v_usedLetOnly_3179_, lean_object* v_skipConstInApp_3180_, lean_object* v_skipInstances_3181_, lean_object* v_x_3182_, lean_object* v_x_3183_, lean_object* v_fvars_3184_, lean_object* v_e_3185_, lean_object* v_a_3186_){
_start:
{
uint8_t v_usedLetOnly_boxed_3187_; uint8_t v_skipConstInApp_boxed_3188_; uint8_t v_skipInstances_boxed_3189_; lean_object* v_res_3190_; 
v_usedLetOnly_boxed_3187_ = lean_unbox(v_usedLetOnly_3179_);
v_skipConstInApp_boxed_3188_ = lean_unbox(v_skipConstInApp_3180_);
v_skipInstances_boxed_3189_ = lean_unbox(v_skipInstances_3181_);
v_res_3190_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall(v_m_3173_, v_inst_3174_, v_inst_3175_, v_inst_3176_, v_pre_3177_, v_post_3178_, v_usedLetOnly_boxed_3187_, v_skipConstInApp_boxed_3188_, v_skipInstances_boxed_3189_, v_x_3182_, v_x_3183_, v_fvars_3184_, v_e_3185_, v_a_3186_);
lean_dec(v_a_3186_);
return v_res_3190_;
}
}
lean_object* l_Lean_Meta_transformWithCache___redArg___lam__0(lean_object* v_x_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_){
_start:
{
lean_object* v___x_3197_; lean_object* v___x_3198_; 
v___x_3197_ = lean_apply_1(v_x_3191_, lean_box(0));
v___x_3198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3198_, 0, v___x_3197_);
return v___x_3198_;
}
}
LEAN_EXPORT void l_Lean_Meta_transformWithCache___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3191_ = stack[0].m_obj;
lean_object* v___y_3192_ = stack[1].m_obj;
lean_object* v___y_3193_ = stack[2].m_obj;
lean_object* v___y_3194_ = stack[3].m_obj;
lean_object* v___y_3195_ = stack[4].m_obj;
lean_object* v_res_3199_;
v_res_3199_ = l_Lean_Meta_transformWithCache___redArg___lam__0(v_x_3191_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_);
stack->m_obj
 = v_res_3199_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__0___boxed(lean_object* v_x_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_){
_start:
{
lean_object* v_res_3206_; 
v_res_3206_ = l_Lean_Meta_transformWithCache___redArg___lam__0(v_x_3200_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_);
lean_dec(v___y_3204_);
lean_dec_ref(v___y_3203_);
lean_dec(v___y_3202_);
lean_dec_ref(v___y_3201_);
return v_res_3206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__1(lean_object* v_inst_3207_, lean_object* v_00_u03b1_3208_, lean_object* v_x_3209_){
_start:
{
lean_object* v___f_3210_; lean_object* v___x_3211_; 
v___f_3210_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_3210_, 0, v_x_3209_);
v___x_3211_ = lean_apply_2(v_inst_3207_, lean_box(0), v___f_3210_);
return v___x_3211_;
}
}
lean_object* l_Lean_Meta_transformWithCache___redArg___lam__4(lean_object* v_toPure_3212_, lean_object* v_x_3213_, lean_object* v_toBind_3214_, lean_object* v_inst_3215_, lean_object* v_inst_3216_, lean_object* v_inst_3217_, lean_object* v_pre_3218_, lean_object* v_post_3219_, uint8_t v_usedLetOnly_3220_, uint8_t v_skipConstInApp_3221_, uint8_t v_skipInstances_3222_, lean_object* v_x_3223_, lean_object* v_input_3224_, lean_object* v_ref_3225_){
_start:
{
lean_object* v___f_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; 
lean_inc(v_toBind_3214_);
lean_inc(v_x_3213_);
lean_inc(v_ref_3225_);
v___f_3226_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__4), 5, 4);
lean_closure_set(v___f_3226_, 0, v_toPure_3212_);
lean_closure_set(v___f_3226_, 1, v_ref_3225_);
lean_closure_set(v___f_3226_, 2, v_x_3213_);
lean_closure_set(v___f_3226_, 3, v_toBind_3214_);
v___x_3227_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_3215_, v_inst_3216_, v_inst_3217_, v_pre_3218_, v_post_3219_, v_usedLetOnly_3220_, v_skipConstInApp_3221_, v_skipInstances_3222_, v_x_3223_, v_x_3213_, v_input_3224_, v_ref_3225_);
lean_dec(v_ref_3225_);
v___x_3228_ = lean_apply_4(v_toBind_3214_, lean_box(0), lean_box(0), v___x_3227_, v___f_3226_);
return v___x_3228_;
}
}
LEAN_EXPORT void l_Lean_Meta_transformWithCache___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_toPure_3212_ = stack[0].m_obj;
lean_object* v_x_3213_ = stack[1].m_obj;
lean_object* v_toBind_3214_ = stack[2].m_obj;
lean_object* v_inst_3215_ = stack[3].m_obj;
lean_object* v_inst_3216_ = stack[4].m_obj;
lean_object* v_inst_3217_ = stack[5].m_obj;
lean_object* v_pre_3218_ = stack[6].m_obj;
lean_object* v_post_3219_ = stack[7].m_obj;
uint8_t v_usedLetOnly_3220_ = stack[8].m_num;
uint8_t v_skipConstInApp_3221_ = stack[9].m_num;
uint8_t v_skipInstances_3222_ = stack[10].m_num;
lean_object* v_x_3223_ = stack[11].m_obj;
lean_object* v_input_3224_ = stack[12].m_obj;
lean_object* v_ref_3225_ = stack[13].m_obj;
lean_object* v_res_3229_;
v_res_3229_ = l_Lean_Meta_transformWithCache___redArg___lam__4(v_toPure_3212_, v_x_3213_, v_toBind_3214_, v_inst_3215_, v_inst_3216_, v_inst_3217_, v_pre_3218_, v_post_3219_, v_usedLetOnly_3220_, v_skipConstInApp_3221_, v_skipInstances_3222_, v_x_3223_, v_input_3224_, v_ref_3225_);
stack->m_obj
 = v_res_3229_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__4___boxed(lean_object* v_toPure_3230_, lean_object* v_x_3231_, lean_object* v_toBind_3232_, lean_object* v_inst_3233_, lean_object* v_inst_3234_, lean_object* v_inst_3235_, lean_object* v_pre_3236_, lean_object* v_post_3237_, lean_object* v_usedLetOnly_3238_, lean_object* v_skipConstInApp_3239_, lean_object* v_skipInstances_3240_, lean_object* v_x_3241_, lean_object* v_input_3242_, lean_object* v_ref_3243_){
_start:
{
uint8_t v_usedLetOnly_boxed_3244_; uint8_t v_skipConstInApp_boxed_3245_; uint8_t v_skipInstances_boxed_3246_; lean_object* v_res_3247_; 
v_usedLetOnly_boxed_3244_ = lean_unbox(v_usedLetOnly_3238_);
v_skipConstInApp_boxed_3245_ = lean_unbox(v_skipConstInApp_3239_);
v_skipInstances_boxed_3246_ = lean_unbox(v_skipInstances_3240_);
v_res_3247_ = l_Lean_Meta_transformWithCache___redArg___lam__4(v_toPure_3230_, v_x_3231_, v_toBind_3232_, v_inst_3233_, v_inst_3234_, v_inst_3235_, v_pre_3236_, v_post_3237_, v_usedLetOnly_boxed_3244_, v_skipConstInApp_boxed_3245_, v_skipInstances_boxed_3246_, v_x_3241_, v_input_3242_, v_ref_3243_);
return v_res_3247_;
}
}
lean_object* l_Lean_Meta_transformWithCache___redArg(lean_object* v_inst_3248_, lean_object* v_inst_3249_, lean_object* v_inst_3250_, lean_object* v_input_3251_, lean_object* v_cache_3252_, lean_object* v_pre_3253_, lean_object* v_post_3254_, uint8_t v_usedLetOnly_3255_, uint8_t v_skipConstInApp_3256_, uint8_t v_skipInstances_3257_){
_start:
{
lean_object* v_x_3258_; lean_object* v_toApplicative_3259_; lean_object* v_toBind_3260_; lean_object* v_toPure_3261_; lean_object* v_x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___f_3268_; lean_object* v___x_3269_; 
v_x_3258_ = lean_box(0);
v_toApplicative_3259_ = lean_ctor_get(v_inst_3248_, 0);
v_toBind_3260_ = lean_ctor_get(v_inst_3248_, 1);
lean_inc_n(v_toBind_3260_, 2);
v_toPure_3261_ = lean_ctor_get(v_toApplicative_3259_, 1);
lean_inc(v_toPure_3261_);
lean_inc_n(v_inst_3249_, 2);
v_x_3262_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__1), 3, 1);
lean_closure_set(v_x_3262_, 0, v_inst_3249_);
v___x_3263_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_3263_, 0, lean_box(0));
lean_closure_set(v___x_3263_, 1, lean_box(0));
lean_closure_set(v___x_3263_, 2, v_cache_3252_);
v___x_3264_ = l_Lean_Meta_transformWithCache___redArg___lam__1(v_inst_3249_, lean_box(0), v___x_3263_);
v___x_3265_ = lean_box(v_usedLetOnly_3255_);
v___x_3266_ = lean_box(v_skipConstInApp_3256_);
v___x_3267_ = lean_box(v_skipInstances_3257_);
v___f_3268_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__4___boxed), 14, 13);
lean_closure_set(v___f_3268_, 0, v_toPure_3261_);
lean_closure_set(v___f_3268_, 1, v_x_3262_);
lean_closure_set(v___f_3268_, 2, v_toBind_3260_);
lean_closure_set(v___f_3268_, 3, v_inst_3248_);
lean_closure_set(v___f_3268_, 4, v_inst_3249_);
lean_closure_set(v___f_3268_, 5, v_inst_3250_);
lean_closure_set(v___f_3268_, 6, v_pre_3253_);
lean_closure_set(v___f_3268_, 7, v_post_3254_);
lean_closure_set(v___f_3268_, 8, v___x_3265_);
lean_closure_set(v___f_3268_, 9, v___x_3266_);
lean_closure_set(v___f_3268_, 10, v___x_3267_);
lean_closure_set(v___f_3268_, 11, v_x_3258_);
lean_closure_set(v___f_3268_, 12, v_input_3251_);
v___x_3269_ = lean_apply_4(v_toBind_3260_, lean_box(0), lean_box(0), v___x_3264_, v___f_3268_);
return v___x_3269_;
}
}
LEAN_EXPORT void l_Lean_Meta_transformWithCache___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_3248_ = stack[0].m_obj;
lean_object* v_inst_3249_ = stack[1].m_obj;
lean_object* v_inst_3250_ = stack[2].m_obj;
lean_object* v_input_3251_ = stack[3].m_obj;
lean_object* v_cache_3252_ = stack[4].m_obj;
lean_object* v_pre_3253_ = stack[5].m_obj;
lean_object* v_post_3254_ = stack[6].m_obj;
uint8_t v_usedLetOnly_3255_ = stack[7].m_num;
uint8_t v_skipConstInApp_3256_ = stack[8].m_num;
uint8_t v_skipInstances_3257_ = stack[9].m_num;
lean_object* v_res_3270_;
v_res_3270_ = l_Lean_Meta_transformWithCache___redArg(v_inst_3248_, v_inst_3249_, v_inst_3250_, v_input_3251_, v_cache_3252_, v_pre_3253_, v_post_3254_, v_usedLetOnly_3255_, v_skipConstInApp_3256_, v_skipInstances_3257_);
stack->m_obj
 = v_res_3270_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___boxed(lean_object* v_inst_3271_, lean_object* v_inst_3272_, lean_object* v_inst_3273_, lean_object* v_input_3274_, lean_object* v_cache_3275_, lean_object* v_pre_3276_, lean_object* v_post_3277_, lean_object* v_usedLetOnly_3278_, lean_object* v_skipConstInApp_3279_, lean_object* v_skipInstances_3280_){
_start:
{
uint8_t v_usedLetOnly_boxed_3281_; uint8_t v_skipConstInApp_boxed_3282_; uint8_t v_skipInstances_boxed_3283_; lean_object* v_res_3284_; 
v_usedLetOnly_boxed_3281_ = lean_unbox(v_usedLetOnly_3278_);
v_skipConstInApp_boxed_3282_ = lean_unbox(v_skipConstInApp_3279_);
v_skipInstances_boxed_3283_ = lean_unbox(v_skipInstances_3280_);
v_res_3284_ = l_Lean_Meta_transformWithCache___redArg(v_inst_3271_, v_inst_3272_, v_inst_3273_, v_input_3274_, v_cache_3275_, v_pre_3276_, v_post_3277_, v_usedLetOnly_boxed_3281_, v_skipConstInApp_boxed_3282_, v_skipInstances_boxed_3283_);
return v_res_3284_;
}
}
lean_object* l_Lean_Meta_transformWithCache(lean_object* v_m_3285_, lean_object* v_inst_3286_, lean_object* v_inst_3287_, lean_object* v_inst_3288_, lean_object* v_input_3289_, lean_object* v_cache_3290_, lean_object* v_pre_3291_, lean_object* v_post_3292_, uint8_t v_usedLetOnly_3293_, uint8_t v_skipConstInApp_3294_, uint8_t v_skipInstances_3295_){
_start:
{
lean_object* v_x_3296_; lean_object* v_toApplicative_3297_; lean_object* v_toBind_3298_; lean_object* v_toPure_3299_; lean_object* v_x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___f_3306_; lean_object* v___x_3307_; 
v_x_3296_ = lean_box(0);
v_toApplicative_3297_ = lean_ctor_get(v_inst_3286_, 0);
v_toBind_3298_ = lean_ctor_get(v_inst_3286_, 1);
lean_inc_n(v_toBind_3298_, 2);
v_toPure_3299_ = lean_ctor_get(v_toApplicative_3297_, 1);
lean_inc(v_toPure_3299_);
lean_inc_n(v_inst_3287_, 2);
v_x_3300_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__1), 3, 1);
lean_closure_set(v_x_3300_, 0, v_inst_3287_);
v___x_3301_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_3301_, 0, lean_box(0));
lean_closure_set(v___x_3301_, 1, lean_box(0));
lean_closure_set(v___x_3301_, 2, v_cache_3290_);
v___x_3302_ = l_Lean_Meta_transformWithCache___redArg___lam__1(v_inst_3287_, lean_box(0), v___x_3301_);
v___x_3303_ = lean_box(v_usedLetOnly_3293_);
v___x_3304_ = lean_box(v_skipConstInApp_3294_);
v___x_3305_ = lean_box(v_skipInstances_3295_);
v___f_3306_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__4___boxed), 14, 13);
lean_closure_set(v___f_3306_, 0, v_toPure_3299_);
lean_closure_set(v___f_3306_, 1, v_x_3300_);
lean_closure_set(v___f_3306_, 2, v_toBind_3298_);
lean_closure_set(v___f_3306_, 3, v_inst_3286_);
lean_closure_set(v___f_3306_, 4, v_inst_3287_);
lean_closure_set(v___f_3306_, 5, v_inst_3288_);
lean_closure_set(v___f_3306_, 6, v_pre_3291_);
lean_closure_set(v___f_3306_, 7, v_post_3292_);
lean_closure_set(v___f_3306_, 8, v___x_3303_);
lean_closure_set(v___f_3306_, 9, v___x_3304_);
lean_closure_set(v___f_3306_, 10, v___x_3305_);
lean_closure_set(v___f_3306_, 11, v_x_3296_);
lean_closure_set(v___f_3306_, 12, v_input_3289_);
v___x_3307_ = lean_apply_4(v_toBind_3298_, lean_box(0), lean_box(0), v___x_3302_, v___f_3306_);
return v___x_3307_;
}
}
LEAN_EXPORT void l_Lean_Meta_transformWithCache_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_3286_ = stack[1].m_obj;
lean_object* v_inst_3287_ = stack[2].m_obj;
lean_object* v_inst_3288_ = stack[3].m_obj;
lean_object* v_input_3289_ = stack[4].m_obj;
lean_object* v_cache_3290_ = stack[5].m_obj;
lean_object* v_pre_3291_ = stack[6].m_obj;
lean_object* v_post_3292_ = stack[7].m_obj;
uint8_t v_usedLetOnly_3293_ = stack[8].m_num;
uint8_t v_skipConstInApp_3294_ = stack[9].m_num;
uint8_t v_skipInstances_3295_ = stack[10].m_num;
lean_object* v_res_3308_;
v_res_3308_ = l_Lean_Meta_transformWithCache(lean_box(0), v_inst_3286_, v_inst_3287_, v_inst_3288_, v_input_3289_, v_cache_3290_, v_pre_3291_, v_post_3292_, v_usedLetOnly_3293_, v_skipConstInApp_3294_, v_skipInstances_3295_);
stack->m_obj
 = v_res_3308_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___boxed(lean_object* v_m_3309_, lean_object* v_inst_3310_, lean_object* v_inst_3311_, lean_object* v_inst_3312_, lean_object* v_input_3313_, lean_object* v_cache_3314_, lean_object* v_pre_3315_, lean_object* v_post_3316_, lean_object* v_usedLetOnly_3317_, lean_object* v_skipConstInApp_3318_, lean_object* v_skipInstances_3319_){
_start:
{
uint8_t v_usedLetOnly_boxed_3320_; uint8_t v_skipConstInApp_boxed_3321_; uint8_t v_skipInstances_boxed_3322_; lean_object* v_res_3323_; 
v_usedLetOnly_boxed_3320_ = lean_unbox(v_usedLetOnly_3317_);
v_skipConstInApp_boxed_3321_ = lean_unbox(v_skipConstInApp_3318_);
v_skipInstances_boxed_3322_ = lean_unbox(v_skipInstances_3319_);
v_res_3323_ = l_Lean_Meta_transformWithCache(v_m_3309_, v_inst_3310_, v_inst_3311_, v_inst_3312_, v_input_3313_, v_cache_3314_, v_pre_3315_, v_post_3316_, v_usedLetOnly_boxed_3320_, v_skipConstInApp_boxed_3321_, v_skipInstances_boxed_3322_);
return v_res_3323_;
}
}
lean_object* l_Lean_Meta_transform___redArg___lam__5(lean_object* v_toPure_3324_, lean_object* v_x_3325_, lean_object* v_toBind_3326_, lean_object* v_inst_3327_, lean_object* v_inst_3328_, lean_object* v_inst_3329_, lean_object* v_pre_3330_, lean_object* v_post_3331_, uint8_t v_usedLetOnly_3332_, uint8_t v_skipConstInApp_3333_, uint8_t v___x_3334_, lean_object* v_x_3335_, lean_object* v_input_3336_, lean_object* v_ref_3337_){
_start:
{
lean_object* v___f_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; 
lean_inc(v_toBind_3326_);
lean_inc(v_x_3325_);
lean_inc(v_ref_3337_);
v___f_3338_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__4), 5, 4);
lean_closure_set(v___f_3338_, 0, v_toPure_3324_);
lean_closure_set(v___f_3338_, 1, v_ref_3337_);
lean_closure_set(v___f_3338_, 2, v_x_3325_);
lean_closure_set(v___f_3338_, 3, v_toBind_3326_);
v___x_3339_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_3327_, v_inst_3328_, v_inst_3329_, v_pre_3330_, v_post_3331_, v_usedLetOnly_3332_, v_skipConstInApp_3333_, v___x_3334_, v_x_3335_, v_x_3325_, v_input_3336_, v_ref_3337_);
lean_dec(v_ref_3337_);
v___x_3340_ = lean_apply_4(v_toBind_3326_, lean_box(0), lean_box(0), v___x_3339_, v___f_3338_);
return v___x_3340_;
}
}
LEAN_EXPORT void l_Lean_Meta_transform___redArg___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_toPure_3324_ = stack[0].m_obj;
lean_object* v_x_3325_ = stack[1].m_obj;
lean_object* v_toBind_3326_ = stack[2].m_obj;
lean_object* v_inst_3327_ = stack[3].m_obj;
lean_object* v_inst_3328_ = stack[4].m_obj;
lean_object* v_inst_3329_ = stack[5].m_obj;
lean_object* v_pre_3330_ = stack[6].m_obj;
lean_object* v_post_3331_ = stack[7].m_obj;
uint8_t v_usedLetOnly_3332_ = stack[8].m_num;
uint8_t v_skipConstInApp_3333_ = stack[9].m_num;
uint8_t v___x_3334_ = stack[10].m_num;
lean_object* v_x_3335_ = stack[11].m_obj;
lean_object* v_input_3336_ = stack[12].m_obj;
lean_object* v_ref_3337_ = stack[13].m_obj;
lean_object* v_res_3341_;
v_res_3341_ = l_Lean_Meta_transform___redArg___lam__5(v_toPure_3324_, v_x_3325_, v_toBind_3326_, v_inst_3327_, v_inst_3328_, v_inst_3329_, v_pre_3330_, v_post_3331_, v_usedLetOnly_3332_, v_skipConstInApp_3333_, v___x_3334_, v_x_3335_, v_input_3336_, v_ref_3337_);
stack->m_obj
 = v_res_3341_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___redArg___lam__5___boxed(lean_object* v_toPure_3342_, lean_object* v_x_3343_, lean_object* v_toBind_3344_, lean_object* v_inst_3345_, lean_object* v_inst_3346_, lean_object* v_inst_3347_, lean_object* v_pre_3348_, lean_object* v_post_3349_, lean_object* v_usedLetOnly_3350_, lean_object* v_skipConstInApp_3351_, lean_object* v___x_3352_, lean_object* v_x_3353_, lean_object* v_input_3354_, lean_object* v_ref_3355_){
_start:
{
uint8_t v_usedLetOnly_boxed_3356_; uint8_t v_skipConstInApp_boxed_3357_; uint8_t v___x_115__boxed_3358_; lean_object* v_res_3359_; 
v_usedLetOnly_boxed_3356_ = lean_unbox(v_usedLetOnly_3350_);
v_skipConstInApp_boxed_3357_ = lean_unbox(v_skipConstInApp_3351_);
v___x_115__boxed_3358_ = lean_unbox(v___x_3352_);
v_res_3359_ = l_Lean_Meta_transform___redArg___lam__5(v_toPure_3342_, v_x_3343_, v_toBind_3344_, v_inst_3345_, v_inst_3346_, v_inst_3347_, v_pre_3348_, v_post_3349_, v_usedLetOnly_boxed_3356_, v_skipConstInApp_boxed_3357_, v___x_115__boxed_3358_, v_x_3353_, v_input_3354_, v_ref_3355_);
return v_res_3359_;
}
}
lean_object* l_Lean_Meta_transform___redArg(lean_object* v_inst_3360_, lean_object* v_inst_3361_, lean_object* v_inst_3362_, lean_object* v_input_3363_, lean_object* v_pre_3364_, lean_object* v_post_3365_, uint8_t v_usedLetOnly_3366_, uint8_t v_skipConstInApp_3367_){
_start:
{
lean_object* v_toApplicative_3368_; lean_object* v_toBind_3369_; lean_object* v_x_3370_; lean_object* v_toPure_3371_; lean_object* v_x_3372_; uint8_t v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___f_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___f_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; 
v_toApplicative_3368_ = lean_ctor_get(v_inst_3360_, 0);
v_toBind_3369_ = lean_ctor_get(v_inst_3360_, 1);
lean_inc_n(v_toBind_3369_, 3);
v_x_3370_ = lean_box(0);
v_toPure_3371_ = lean_ctor_get(v_toApplicative_3368_, 1);
lean_inc_n(v_toPure_3371_, 2);
lean_inc_n(v_inst_3361_, 2);
v_x_3372_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__1), 3, 1);
lean_closure_set(v_x_3372_, 0, v_inst_3361_);
v___x_3373_ = 0;
v___x_3374_ = lean_obj_once(&l_Lean_Core_transform___redArg___closed__2, &l_Lean_Core_transform___redArg___closed__2_once, _init_l_Lean_Core_transform___redArg___closed__2);
v___x_3375_ = l_Lean_Meta_transformWithCache___redArg___lam__1(v_inst_3361_, lean_box(0), v___x_3374_);
v___f_3376_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__2), 2, 1);
lean_closure_set(v___f_3376_, 0, v_toPure_3371_);
v___x_3377_ = lean_box(v_usedLetOnly_3366_);
v___x_3378_ = lean_box(v_skipConstInApp_3367_);
v___x_3379_ = lean_box(v___x_3373_);
v___f_3380_ = lean_alloc_closure((void*)(l_Lean_Meta_transform___redArg___lam__5___boxed), 14, 13);
lean_closure_set(v___f_3380_, 0, v_toPure_3371_);
lean_closure_set(v___f_3380_, 1, v_x_3372_);
lean_closure_set(v___f_3380_, 2, v_toBind_3369_);
lean_closure_set(v___f_3380_, 3, v_inst_3360_);
lean_closure_set(v___f_3380_, 4, v_inst_3361_);
lean_closure_set(v___f_3380_, 5, v_inst_3362_);
lean_closure_set(v___f_3380_, 6, v_pre_3364_);
lean_closure_set(v___f_3380_, 7, v_post_3365_);
lean_closure_set(v___f_3380_, 8, v___x_3377_);
lean_closure_set(v___f_3380_, 9, v___x_3378_);
lean_closure_set(v___f_3380_, 10, v___x_3379_);
lean_closure_set(v___f_3380_, 11, v_x_3370_);
lean_closure_set(v___f_3380_, 12, v_input_3363_);
v___x_3381_ = lean_apply_4(v_toBind_3369_, lean_box(0), lean_box(0), v___x_3375_, v___f_3380_);
v___x_3382_ = lean_apply_4(v_toBind_3369_, lean_box(0), lean_box(0), v___x_3381_, v___f_3376_);
return v___x_3382_;
}
}
LEAN_EXPORT void l_Lean_Meta_transform___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_3360_ = stack[0].m_obj;
lean_object* v_inst_3361_ = stack[1].m_obj;
lean_object* v_inst_3362_ = stack[2].m_obj;
lean_object* v_input_3363_ = stack[3].m_obj;
lean_object* v_pre_3364_ = stack[4].m_obj;
lean_object* v_post_3365_ = stack[5].m_obj;
uint8_t v_usedLetOnly_3366_ = stack[6].m_num;
uint8_t v_skipConstInApp_3367_ = stack[7].m_num;
lean_object* v_res_3383_;
v_res_3383_ = l_Lean_Meta_transform___redArg(v_inst_3360_, v_inst_3361_, v_inst_3362_, v_input_3363_, v_pre_3364_, v_post_3365_, v_usedLetOnly_3366_, v_skipConstInApp_3367_);
stack->m_obj
 = v_res_3383_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___redArg___boxed(lean_object* v_inst_3384_, lean_object* v_inst_3385_, lean_object* v_inst_3386_, lean_object* v_input_3387_, lean_object* v_pre_3388_, lean_object* v_post_3389_, lean_object* v_usedLetOnly_3390_, lean_object* v_skipConstInApp_3391_){
_start:
{
uint8_t v_usedLetOnly_boxed_3392_; uint8_t v_skipConstInApp_boxed_3393_; lean_object* v_res_3394_; 
v_usedLetOnly_boxed_3392_ = lean_unbox(v_usedLetOnly_3390_);
v_skipConstInApp_boxed_3393_ = lean_unbox(v_skipConstInApp_3391_);
v_res_3394_ = l_Lean_Meta_transform___redArg(v_inst_3384_, v_inst_3385_, v_inst_3386_, v_input_3387_, v_pre_3388_, v_post_3389_, v_usedLetOnly_boxed_3392_, v_skipConstInApp_boxed_3393_);
return v_res_3394_;
}
}
lean_object* l_Lean_Meta_transform(lean_object* v_m_3395_, lean_object* v_inst_3396_, lean_object* v_inst_3397_, lean_object* v_inst_3398_, lean_object* v_input_3399_, lean_object* v_pre_3400_, lean_object* v_post_3401_, uint8_t v_usedLetOnly_3402_, uint8_t v_skipConstInApp_3403_){
_start:
{
lean_object* v___x_3404_; 
v___x_3404_ = l_Lean_Meta_transform___redArg(v_inst_3396_, v_inst_3397_, v_inst_3398_, v_input_3399_, v_pre_3400_, v_post_3401_, v_usedLetOnly_3402_, v_skipConstInApp_3403_);
return v___x_3404_;
}
}
LEAN_EXPORT void l_Lean_Meta_transform_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_3396_ = stack[1].m_obj;
lean_object* v_inst_3397_ = stack[2].m_obj;
lean_object* v_inst_3398_ = stack[3].m_obj;
lean_object* v_input_3399_ = stack[4].m_obj;
lean_object* v_pre_3400_ = stack[5].m_obj;
lean_object* v_post_3401_ = stack[6].m_obj;
uint8_t v_usedLetOnly_3402_ = stack[7].m_num;
uint8_t v_skipConstInApp_3403_ = stack[8].m_num;
lean_object* v_res_3405_;
v_res_3405_ = l_Lean_Meta_transform(lean_box(0), v_inst_3396_, v_inst_3397_, v_inst_3398_, v_input_3399_, v_pre_3400_, v_post_3401_, v_usedLetOnly_3402_, v_skipConstInApp_3403_);
stack->m_obj
 = v_res_3405_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___boxed(lean_object* v_m_3406_, lean_object* v_inst_3407_, lean_object* v_inst_3408_, lean_object* v_inst_3409_, lean_object* v_input_3410_, lean_object* v_pre_3411_, lean_object* v_post_3412_, lean_object* v_usedLetOnly_3413_, lean_object* v_skipConstInApp_3414_){
_start:
{
uint8_t v_usedLetOnly_boxed_3415_; uint8_t v_skipConstInApp_boxed_3416_; lean_object* v_res_3417_; 
v_usedLetOnly_boxed_3415_ = lean_unbox(v_usedLetOnly_3413_);
v_skipConstInApp_boxed_3416_ = lean_unbox(v_skipConstInApp_3414_);
v_res_3417_ = l_Lean_Meta_transform(v_m_3406_, v_inst_3407_, v_inst_3408_, v_inst_3409_, v_input_3410_, v_pre_3411_, v_post_3412_, v_usedLetOnly_boxed_3415_, v_skipConstInApp_boxed_3416_);
return v_res_3417_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(lean_object* v_e_3418_, lean_object* v___y_3419_){
_start:
{
uint8_t v___x_3421_; 
v___x_3421_ = l_Lean_Expr_hasMVar(v_e_3418_);
if (v___x_3421_ == 0)
{
lean_object* v___x_3422_; 
v___x_3422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3422_, 0, v_e_3418_);
return v___x_3422_;
}
else
{
lean_object* v___x_3423_; lean_object* v_mctx_3424_; lean_object* v___x_3425_; lean_object* v_fst_3426_; lean_object* v_snd_3427_; lean_object* v___x_3428_; lean_object* v_cache_3429_; lean_object* v_zetaDeltaFVarIds_3430_; lean_object* v_postponed_3431_; lean_object* v_diag_3432_; lean_object* v___x_3434_; uint8_t v_isShared_3435_; uint8_t v_isSharedCheck_3441_; 
v___x_3423_ = lean_st_ref_get(v___y_3419_);
v_mctx_3424_ = lean_ctor_get(v___x_3423_, 0);
lean_inc_ref(v_mctx_3424_);
lean_dec(v___x_3423_);
v___x_3425_ = l_Lean_instantiateMVarsCore(v_mctx_3424_, v_e_3418_);
v_fst_3426_ = lean_ctor_get(v___x_3425_, 0);
lean_inc(v_fst_3426_);
v_snd_3427_ = lean_ctor_get(v___x_3425_, 1);
lean_inc(v_snd_3427_);
lean_dec_ref(v___x_3425_);
v___x_3428_ = lean_st_ref_take(v___y_3419_);
v_cache_3429_ = lean_ctor_get(v___x_3428_, 1);
v_zetaDeltaFVarIds_3430_ = lean_ctor_get(v___x_3428_, 2);
v_postponed_3431_ = lean_ctor_get(v___x_3428_, 3);
v_diag_3432_ = lean_ctor_get(v___x_3428_, 4);
v_isSharedCheck_3441_ = !lean_is_exclusive(v___x_3428_);
if (v_isSharedCheck_3441_ == 0)
{
lean_object* v_unused_3442_; 
v_unused_3442_ = lean_ctor_get(v___x_3428_, 0);
lean_dec(v_unused_3442_);
v___x_3434_ = v___x_3428_;
v_isShared_3435_ = v_isSharedCheck_3441_;
goto v_resetjp_3433_;
}
else
{
lean_inc(v_diag_3432_);
lean_inc(v_postponed_3431_);
lean_inc(v_zetaDeltaFVarIds_3430_);
lean_inc(v_cache_3429_);
lean_dec(v___x_3428_);
v___x_3434_ = lean_box(0);
v_isShared_3435_ = v_isSharedCheck_3441_;
goto v_resetjp_3433_;
}
v_resetjp_3433_:
{
lean_object* v___x_3437_; 
if (v_isShared_3435_ == 0)
{
lean_ctor_set(v___x_3434_, 0, v_snd_3427_);
v___x_3437_ = v___x_3434_;
goto v_reusejp_3436_;
}
else
{
lean_object* v_reuseFailAlloc_3440_; 
v_reuseFailAlloc_3440_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3440_, 0, v_snd_3427_);
lean_ctor_set(v_reuseFailAlloc_3440_, 1, v_cache_3429_);
lean_ctor_set(v_reuseFailAlloc_3440_, 2, v_zetaDeltaFVarIds_3430_);
lean_ctor_set(v_reuseFailAlloc_3440_, 3, v_postponed_3431_);
lean_ctor_set(v_reuseFailAlloc_3440_, 4, v_diag_3432_);
v___x_3437_ = v_reuseFailAlloc_3440_;
goto v_reusejp_3436_;
}
v_reusejp_3436_:
{
lean_object* v___x_3438_; lean_object* v___x_3439_; 
v___x_3438_ = lean_st_ref_put(v___y_3419_, v___x_3437_);
v___x_3439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3439_, 0, v_fst_3426_);
return v___x_3439_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3418_ = stack[0].m_obj;
lean_object* v___y_3419_ = stack[1].m_obj;
lean_object* v_res_3443_;
v_res_3443_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(v_e_3418_, v___y_3419_);
stack->m_obj
 = v_res_3443_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg___boxed(lean_object* v_e_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_){
_start:
{
lean_object* v_res_3447_; 
v_res_3447_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(v_e_3444_, v___y_3445_);
lean_dec(v___y_3445_);
return v_res_3447_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0(lean_object* v_e_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_){
_start:
{
lean_object* v___x_3454_; 
v___x_3454_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(v_e_3448_, v___y_3450_);
return v___x_3454_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3448_ = stack[0].m_obj;
lean_object* v___y_3449_ = stack[1].m_obj;
lean_object* v___y_3450_ = stack[2].m_obj;
lean_object* v___y_3451_ = stack[3].m_obj;
lean_object* v___y_3452_ = stack[4].m_obj;
lean_object* v_res_3455_;
v_res_3455_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0(v_e_3448_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_);
stack->m_obj
 = v_res_3455_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___boxed(lean_object* v_e_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_){
_start:
{
lean_object* v_res_3462_; 
v_res_3462_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0(v_e_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_);
lean_dec(v___y_3460_);
lean_dec_ref(v___y_3459_);
lean_dec(v___y_3458_);
lean_dec_ref(v___y_3457_);
return v_res_3462_;
}
}
lean_object* l_Lean_Meta_zetaReduce___lam__0(uint8_t v_zetaHave_3463_, lean_object* v___x_3464_, uint8_t v_zetaDelta_3465_, lean_object* v_fvarId_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_){
_start:
{
lean_object* v___x_3472_; 
v___x_3472_ = l_Lean_FVarId_findDecl_x3f___redArg(v_fvarId_3466_, v___y_3467_);
if (lean_obj_tag(v___x_3472_) == 0)
{
lean_object* v_a_3473_; lean_object* v___x_3475_; uint8_t v_isShared_3476_; uint8_t v_isSharedCheck_3501_; 
v_a_3473_ = lean_ctor_get(v___x_3472_, 0);
v_isSharedCheck_3501_ = !lean_is_exclusive(v___x_3472_);
if (v_isSharedCheck_3501_ == 0)
{
v___x_3475_ = v___x_3472_;
v_isShared_3476_ = v_isSharedCheck_3501_;
goto v_resetjp_3474_;
}
else
{
lean_inc(v_a_3473_);
lean_dec(v___x_3472_);
v___x_3475_ = lean_box(0);
v_isShared_3476_ = v_isSharedCheck_3501_;
goto v_resetjp_3474_;
}
v_resetjp_3474_:
{
if (lean_obj_tag(v_a_3473_) == 1)
{
lean_object* v_val_3477_; lean_object* v___x_3479_; uint8_t v_isShared_3480_; uint8_t v_isSharedCheck_3496_; 
v_val_3477_ = lean_ctor_get(v_a_3473_, 0);
v_isSharedCheck_3496_ = !lean_is_exclusive(v_a_3473_);
if (v_isSharedCheck_3496_ == 0)
{
v___x_3479_ = v_a_3473_;
v_isShared_3480_ = v_isSharedCheck_3496_;
goto v_resetjp_3478_;
}
else
{
lean_inc(v_val_3477_);
lean_dec(v_a_3473_);
v___x_3479_ = lean_box(0);
v_isShared_3480_ = v_isSharedCheck_3496_;
goto v_resetjp_3478_;
}
v_resetjp_3478_:
{
uint8_t v___y_3482_; 
if (v_zetaDelta_3465_ == 0)
{
lean_object* v___x_3490_; uint8_t v___x_3491_; 
v___x_3490_ = l_Lean_LocalDecl_index(v_val_3477_);
v___x_3491_ = lean_nat_dec_lt(v___x_3490_, v___x_3464_);
lean_dec(v___x_3490_);
if (v___x_3491_ == 0)
{
lean_del_object(v___x_3479_);
goto v___jp_3487_;
}
else
{
lean_object* v___x_3492_; lean_object* v___x_3494_; 
lean_dec(v_val_3477_);
lean_del_object(v___x_3475_);
v___x_3492_ = lean_box(0);
if (v_isShared_3480_ == 0)
{
lean_ctor_set_tag(v___x_3479_, 0);
lean_ctor_set(v___x_3479_, 0, v___x_3492_);
v___x_3494_ = v___x_3479_;
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
else
{
lean_del_object(v___x_3479_);
goto v___jp_3487_;
}
v___jp_3481_:
{
lean_object* v___x_3483_; lean_object* v___x_3485_; 
v___x_3483_ = l_Lean_LocalDecl_value_x3f(v_val_3477_, v___y_3482_);
lean_dec(v_val_3477_);
if (v_isShared_3476_ == 0)
{
lean_ctor_set(v___x_3475_, 0, v___x_3483_);
v___x_3485_ = v___x_3475_;
goto v_reusejp_3484_;
}
else
{
lean_object* v_reuseFailAlloc_3486_; 
v_reuseFailAlloc_3486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3486_, 0, v___x_3483_);
v___x_3485_ = v_reuseFailAlloc_3486_;
goto v_reusejp_3484_;
}
v_reusejp_3484_:
{
return v___x_3485_;
}
}
v___jp_3487_:
{
if (v_zetaHave_3463_ == 0)
{
v___y_3482_ = v_zetaHave_3463_;
goto v___jp_3481_;
}
else
{
lean_object* v___x_3488_; uint8_t v___x_3489_; 
v___x_3488_ = l_Lean_LocalDecl_index(v_val_3477_);
v___x_3489_ = lean_nat_dec_le(v___x_3464_, v___x_3488_);
lean_dec(v___x_3488_);
v___y_3482_ = v___x_3489_;
goto v___jp_3481_;
}
}
}
}
else
{
lean_object* v___x_3497_; lean_object* v___x_3499_; 
lean_dec(v_a_3473_);
v___x_3497_ = lean_box(0);
if (v_isShared_3476_ == 0)
{
lean_ctor_set(v___x_3475_, 0, v___x_3497_);
v___x_3499_ = v___x_3475_;
goto v_reusejp_3498_;
}
else
{
lean_object* v_reuseFailAlloc_3500_; 
v_reuseFailAlloc_3500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3500_, 0, v___x_3497_);
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
lean_object* v_a_3502_; lean_object* v___x_3504_; uint8_t v_isShared_3505_; uint8_t v_isSharedCheck_3509_; 
v_a_3502_ = lean_ctor_get(v___x_3472_, 0);
v_isSharedCheck_3509_ = !lean_is_exclusive(v___x_3472_);
if (v_isSharedCheck_3509_ == 0)
{
v___x_3504_ = v___x_3472_;
v_isShared_3505_ = v_isSharedCheck_3509_;
goto v_resetjp_3503_;
}
else
{
lean_inc(v_a_3502_);
lean_dec(v___x_3472_);
v___x_3504_ = lean_box(0);
v_isShared_3505_ = v_isSharedCheck_3509_;
goto v_resetjp_3503_;
}
v_resetjp_3503_:
{
lean_object* v___x_3507_; 
if (v_isShared_3505_ == 0)
{
v___x_3507_ = v___x_3504_;
goto v_reusejp_3506_;
}
else
{
lean_object* v_reuseFailAlloc_3508_; 
v_reuseFailAlloc_3508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3508_, 0, v_a_3502_);
v___x_3507_ = v_reuseFailAlloc_3508_;
goto v_reusejp_3506_;
}
v_reusejp_3506_:
{
return v___x_3507_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_zetaReduce___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_zetaHave_3463_ = stack[0].m_num;
lean_object* v___x_3464_ = stack[1].m_obj;
uint8_t v_zetaDelta_3465_ = stack[2].m_num;
lean_object* v_fvarId_3466_ = stack[3].m_obj;
lean_object* v___y_3467_ = stack[4].m_obj;
lean_object* v___y_3468_ = stack[5].m_obj;
lean_object* v___y_3469_ = stack[6].m_obj;
lean_object* v___y_3470_ = stack[7].m_obj;
lean_object* v_res_3510_;
v_res_3510_ = l_Lean_Meta_zetaReduce___lam__0(v_zetaHave_3463_, v___x_3464_, v_zetaDelta_3465_, v_fvarId_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_);
stack->m_obj
 = v_res_3510_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__0___boxed(lean_object* v_zetaHave_3511_, lean_object* v___x_3512_, lean_object* v_zetaDelta_3513_, lean_object* v_fvarId_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_){
_start:
{
uint8_t v_zetaHave_boxed_3520_; uint8_t v_zetaDelta_boxed_3521_; lean_object* v_res_3522_; 
v_zetaHave_boxed_3520_ = lean_unbox(v_zetaHave_3511_);
v_zetaDelta_boxed_3521_ = lean_unbox(v_zetaDelta_3513_);
v_res_3522_ = l_Lean_Meta_zetaReduce___lam__0(v_zetaHave_boxed_3520_, v___x_3512_, v_zetaDelta_boxed_3521_, v_fvarId_3514_, v___y_3515_, v___y_3516_, v___y_3517_, v___y_3518_);
lean_dec(v___y_3518_);
lean_dec_ref(v___y_3517_);
lean_dec(v___y_3516_);
lean_dec_ref(v___y_3515_);
lean_dec(v___x_3512_);
return v_res_3522_;
}
}
lean_object* l_Lean_Meta_zetaReduce___lam__1(lean_object* v_e_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_){
_start:
{
lean_object* v___x_3529_; lean_object* v___x_3530_; 
v___x_3529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3529_, 0, v_e_3523_);
v___x_3530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3530_, 0, v___x_3529_);
return v___x_3530_;
}
}
LEAN_EXPORT void l_Lean_Meta_zetaReduce___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3523_ = stack[0].m_obj;
lean_object* v___y_3524_ = stack[1].m_obj;
lean_object* v___y_3525_ = stack[2].m_obj;
lean_object* v___y_3526_ = stack[3].m_obj;
lean_object* v___y_3527_ = stack[4].m_obj;
lean_object* v_res_3531_;
v_res_3531_ = l_Lean_Meta_zetaReduce___lam__1(v_e_3523_, v___y_3524_, v___y_3525_, v___y_3526_, v___y_3527_);
stack->m_obj
 = v_res_3531_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__1___boxed(lean_object* v_e_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_){
_start:
{
lean_object* v_res_3538_; 
v_res_3538_ = l_Lean_Meta_zetaReduce___lam__1(v_e_3532_, v___y_3533_, v___y_3534_, v___y_3535_, v___y_3536_);
lean_dec(v___y_3536_);
lean_dec_ref(v___y_3535_);
lean_dec(v___y_3534_);
lean_dec_ref(v___y_3533_);
return v_res_3538_;
}
}
lean_object* l_Lean_Meta_zetaReduce___lam__2(lean_object* v___f_3539_, lean_object* v_e_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_){
_start:
{
if (lean_obj_tag(v_e_3540_) == 1)
{
lean_object* v_fvarId_3546_; lean_object* v___x_3547_; 
v_fvarId_3546_ = lean_ctor_get(v_e_3540_, 0);
lean_inc(v___y_3544_);
lean_inc_ref(v___y_3543_);
lean_inc(v___y_3542_);
lean_inc_ref(v___y_3541_);
lean_inc(v_fvarId_3546_);
v___x_3547_ = lean_apply_6(v___f_3539_, v_fvarId_3546_, v___y_3541_, v___y_3542_, v___y_3543_, v___y_3544_, lean_box(0));
if (lean_obj_tag(v___x_3547_) == 0)
{
lean_object* v_a_3548_; lean_object* v___x_3550_; uint8_t v_isShared_3551_; uint8_t v_isSharedCheck_3573_; 
v_a_3548_ = lean_ctor_get(v___x_3547_, 0);
v_isSharedCheck_3573_ = !lean_is_exclusive(v___x_3547_);
if (v_isSharedCheck_3573_ == 0)
{
v___x_3550_ = v___x_3547_;
v_isShared_3551_ = v_isSharedCheck_3573_;
goto v_resetjp_3549_;
}
else
{
lean_inc(v_a_3548_);
lean_dec(v___x_3547_);
v___x_3550_ = lean_box(0);
v_isShared_3551_ = v_isSharedCheck_3573_;
goto v_resetjp_3549_;
}
v_resetjp_3549_:
{
if (lean_obj_tag(v_a_3548_) == 1)
{
lean_object* v_val_3552_; lean_object* v___x_3554_; uint8_t v_isShared_3555_; uint8_t v_isSharedCheck_3568_; 
lean_del_object(v___x_3550_);
lean_dec_ref_known(v_e_3540_, 1);
v_val_3552_ = lean_ctor_get(v_a_3548_, 0);
v_isSharedCheck_3568_ = !lean_is_exclusive(v_a_3548_);
if (v_isSharedCheck_3568_ == 0)
{
v___x_3554_ = v_a_3548_;
v_isShared_3555_ = v_isSharedCheck_3568_;
goto v_resetjp_3553_;
}
else
{
lean_inc(v_val_3552_);
lean_dec(v_a_3548_);
v___x_3554_ = lean_box(0);
v_isShared_3555_ = v_isSharedCheck_3568_;
goto v_resetjp_3553_;
}
v_resetjp_3553_:
{
lean_object* v___x_3556_; lean_object* v_a_3557_; lean_object* v___x_3559_; uint8_t v_isShared_3560_; uint8_t v_isSharedCheck_3567_; 
v___x_3556_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(v_val_3552_, v___y_3542_);
v_a_3557_ = lean_ctor_get(v___x_3556_, 0);
v_isSharedCheck_3567_ = !lean_is_exclusive(v___x_3556_);
if (v_isSharedCheck_3567_ == 0)
{
v___x_3559_ = v___x_3556_;
v_isShared_3560_ = v_isSharedCheck_3567_;
goto v_resetjp_3558_;
}
else
{
lean_inc(v_a_3557_);
lean_dec(v___x_3556_);
v___x_3559_ = lean_box(0);
v_isShared_3560_ = v_isSharedCheck_3567_;
goto v_resetjp_3558_;
}
v_resetjp_3558_:
{
lean_object* v___x_3562_; 
if (v_isShared_3555_ == 0)
{
lean_ctor_set(v___x_3554_, 0, v_a_3557_);
v___x_3562_ = v___x_3554_;
goto v_reusejp_3561_;
}
else
{
lean_object* v_reuseFailAlloc_3566_; 
v_reuseFailAlloc_3566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3566_, 0, v_a_3557_);
v___x_3562_ = v_reuseFailAlloc_3566_;
goto v_reusejp_3561_;
}
v_reusejp_3561_:
{
lean_object* v___x_3564_; 
if (v_isShared_3560_ == 0)
{
lean_ctor_set(v___x_3559_, 0, v___x_3562_);
v___x_3564_ = v___x_3559_;
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
}
else
{
lean_object* v___x_3569_; lean_object* v___x_3571_; 
lean_dec(v_a_3548_);
v___x_3569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3569_, 0, v_e_3540_);
if (v_isShared_3551_ == 0)
{
lean_ctor_set(v___x_3550_, 0, v___x_3569_);
v___x_3571_ = v___x_3550_;
goto v_reusejp_3570_;
}
else
{
lean_object* v_reuseFailAlloc_3572_; 
v_reuseFailAlloc_3572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3572_, 0, v___x_3569_);
v___x_3571_ = v_reuseFailAlloc_3572_;
goto v_reusejp_3570_;
}
v_reusejp_3570_:
{
return v___x_3571_;
}
}
}
}
else
{
lean_object* v_a_3574_; lean_object* v___x_3576_; uint8_t v_isShared_3577_; uint8_t v_isSharedCheck_3581_; 
lean_dec_ref_known(v_e_3540_, 1);
v_a_3574_ = lean_ctor_get(v___x_3547_, 0);
v_isSharedCheck_3581_ = !lean_is_exclusive(v___x_3547_);
if (v_isSharedCheck_3581_ == 0)
{
v___x_3576_ = v___x_3547_;
v_isShared_3577_ = v_isSharedCheck_3581_;
goto v_resetjp_3575_;
}
else
{
lean_inc(v_a_3574_);
lean_dec(v___x_3547_);
v___x_3576_ = lean_box(0);
v_isShared_3577_ = v_isSharedCheck_3581_;
goto v_resetjp_3575_;
}
v_resetjp_3575_:
{
lean_object* v___x_3579_; 
if (v_isShared_3577_ == 0)
{
v___x_3579_ = v___x_3576_;
goto v_reusejp_3578_;
}
else
{
lean_object* v_reuseFailAlloc_3580_; 
v_reuseFailAlloc_3580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3580_, 0, v_a_3574_);
v___x_3579_ = v_reuseFailAlloc_3580_;
goto v_reusejp_3578_;
}
v_reusejp_3578_:
{
return v___x_3579_;
}
}
}
}
else
{
lean_object* v___x_3582_; lean_object* v___x_3583_; 
lean_dec_ref(v_e_3540_);
lean_dec_ref(v___f_3539_);
v___x_3582_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_3583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3583_, 0, v___x_3582_);
return v___x_3583_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_zetaReduce___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_3539_ = stack[0].m_obj;
lean_object* v_e_3540_ = stack[1].m_obj;
lean_object* v___y_3541_ = stack[2].m_obj;
lean_object* v___y_3542_ = stack[3].m_obj;
lean_object* v___y_3543_ = stack[4].m_obj;
lean_object* v___y_3544_ = stack[5].m_obj;
lean_object* v_res_3584_;
v_res_3584_ = l_Lean_Meta_zetaReduce___lam__2(v___f_3539_, v_e_3540_, v___y_3541_, v___y_3542_, v___y_3543_, v___y_3544_);
stack->m_obj
 = v_res_3584_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__2___boxed(lean_object* v___f_3585_, lean_object* v_e_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_){
_start:
{
lean_object* v_res_3592_; 
v_res_3592_ = l_Lean_Meta_zetaReduce___lam__2(v___f_3585_, v_e_3586_, v___y_3587_, v___y_3588_, v___y_3589_, v___y_3590_);
lean_dec(v___y_3590_);
lean_dec_ref(v___y_3589_);
lean_dec(v___y_3588_);
lean_dec_ref(v___y_3587_);
return v_res_3592_;
}
}
lean_object* l_Lean_Meta_zetaReduce___lam__4(lean_object* v___f_3593_, lean_object* v_e_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_){
_start:
{
lean_object* v___x_3600_; 
v___x_3600_ = l_Lean_Expr_getAppFn(v_e_3594_);
if (lean_obj_tag(v___x_3600_) == 1)
{
lean_object* v_fvarId_3601_; lean_object* v___x_3602_; 
v_fvarId_3601_ = lean_ctor_get(v___x_3600_, 0);
lean_inc(v_fvarId_3601_);
lean_dec_ref_known(v___x_3600_, 1);
lean_inc(v___y_3598_);
lean_inc_ref(v___y_3597_);
lean_inc(v___y_3596_);
lean_inc_ref(v___y_3595_);
v___x_3602_ = lean_apply_6(v___f_3593_, v_fvarId_3601_, v___y_3595_, v___y_3596_, v___y_3597_, v___y_3598_, lean_box(0));
if (lean_obj_tag(v___x_3602_) == 0)
{
lean_object* v_a_3603_; lean_object* v___x_3605_; uint8_t v_isShared_3606_; uint8_t v_isSharedCheck_3635_; 
v_a_3603_ = lean_ctor_get(v___x_3602_, 0);
v_isSharedCheck_3635_ = !lean_is_exclusive(v___x_3602_);
if (v_isSharedCheck_3635_ == 0)
{
v___x_3605_ = v___x_3602_;
v_isShared_3606_ = v_isSharedCheck_3635_;
goto v_resetjp_3604_;
}
else
{
lean_inc(v_a_3603_);
lean_dec(v___x_3602_);
v___x_3605_ = lean_box(0);
v_isShared_3606_ = v_isSharedCheck_3635_;
goto v_resetjp_3604_;
}
v_resetjp_3604_:
{
if (lean_obj_tag(v_a_3603_) == 1)
{
lean_object* v_val_3607_; lean_object* v___x_3609_; uint8_t v_isShared_3610_; uint8_t v_isSharedCheck_3630_; 
lean_del_object(v___x_3605_);
v_val_3607_ = lean_ctor_get(v_a_3603_, 0);
v_isSharedCheck_3630_ = !lean_is_exclusive(v_a_3603_);
if (v_isSharedCheck_3630_ == 0)
{
v___x_3609_ = v_a_3603_;
v_isShared_3610_ = v_isSharedCheck_3630_;
goto v_resetjp_3608_;
}
else
{
lean_inc(v_val_3607_);
lean_dec(v_a_3603_);
v___x_3609_ = lean_box(0);
v_isShared_3610_ = v_isSharedCheck_3630_;
goto v_resetjp_3608_;
}
v_resetjp_3608_:
{
lean_object* v___x_3611_; lean_object* v_a_3612_; lean_object* v___x_3614_; uint8_t v_isShared_3615_; uint8_t v_isSharedCheck_3629_; 
v___x_3611_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(v_val_3607_, v___y_3596_);
v_a_3612_ = lean_ctor_get(v___x_3611_, 0);
v_isSharedCheck_3629_ = !lean_is_exclusive(v___x_3611_);
if (v_isSharedCheck_3629_ == 0)
{
v___x_3614_ = v___x_3611_;
v_isShared_3615_ = v_isSharedCheck_3629_;
goto v_resetjp_3613_;
}
else
{
lean_inc(v_a_3612_);
lean_dec(v___x_3611_);
v___x_3614_ = lean_box(0);
v_isShared_3615_ = v_isSharedCheck_3629_;
goto v_resetjp_3613_;
}
v_resetjp_3613_:
{
lean_object* v_dummy_3616_; lean_object* v_nargs_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3624_; 
v_dummy_3616_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_3617_ = l_Lean_Expr_getAppNumArgs(v_e_3594_);
lean_inc(v_nargs_3617_);
v___x_3618_ = lean_mk_array(v_nargs_3617_, v_dummy_3616_);
v___x_3619_ = lean_unsigned_to_nat(1u);
v___x_3620_ = lean_nat_sub(v_nargs_3617_, v___x_3619_);
lean_dec(v_nargs_3617_);
v___x_3621_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3594_, v___x_3618_, v___x_3620_);
v___x_3622_ = l_Lean_Expr_beta(v_a_3612_, v___x_3621_);
if (v_isShared_3610_ == 0)
{
lean_ctor_set(v___x_3609_, 0, v___x_3622_);
v___x_3624_ = v___x_3609_;
goto v_reusejp_3623_;
}
else
{
lean_object* v_reuseFailAlloc_3628_; 
v_reuseFailAlloc_3628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3628_, 0, v___x_3622_);
v___x_3624_ = v_reuseFailAlloc_3628_;
goto v_reusejp_3623_;
}
v_reusejp_3623_:
{
lean_object* v___x_3626_; 
if (v_isShared_3615_ == 0)
{
lean_ctor_set(v___x_3614_, 0, v___x_3624_);
v___x_3626_ = v___x_3614_;
goto v_reusejp_3625_;
}
else
{
lean_object* v_reuseFailAlloc_3627_; 
v_reuseFailAlloc_3627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3627_, 0, v___x_3624_);
v___x_3626_ = v_reuseFailAlloc_3627_;
goto v_reusejp_3625_;
}
v_reusejp_3625_:
{
return v___x_3626_;
}
}
}
}
}
else
{
lean_object* v___x_3631_; lean_object* v___x_3633_; 
lean_dec(v_a_3603_);
lean_dec_ref(v_e_3594_);
v___x_3631_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
if (v_isShared_3606_ == 0)
{
lean_ctor_set(v___x_3605_, 0, v___x_3631_);
v___x_3633_ = v___x_3605_;
goto v_reusejp_3632_;
}
else
{
lean_object* v_reuseFailAlloc_3634_; 
v_reuseFailAlloc_3634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3634_, 0, v___x_3631_);
v___x_3633_ = v_reuseFailAlloc_3634_;
goto v_reusejp_3632_;
}
v_reusejp_3632_:
{
return v___x_3633_;
}
}
}
}
else
{
lean_object* v_a_3636_; lean_object* v___x_3638_; uint8_t v_isShared_3639_; uint8_t v_isSharedCheck_3643_; 
lean_dec_ref(v_e_3594_);
v_a_3636_ = lean_ctor_get(v___x_3602_, 0);
v_isSharedCheck_3643_ = !lean_is_exclusive(v___x_3602_);
if (v_isSharedCheck_3643_ == 0)
{
v___x_3638_ = v___x_3602_;
v_isShared_3639_ = v_isSharedCheck_3643_;
goto v_resetjp_3637_;
}
else
{
lean_inc(v_a_3636_);
lean_dec(v___x_3602_);
v___x_3638_ = lean_box(0);
v_isShared_3639_ = v_isSharedCheck_3643_;
goto v_resetjp_3637_;
}
v_resetjp_3637_:
{
lean_object* v___x_3641_; 
if (v_isShared_3639_ == 0)
{
v___x_3641_ = v___x_3638_;
goto v_reusejp_3640_;
}
else
{
lean_object* v_reuseFailAlloc_3642_; 
v_reuseFailAlloc_3642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3642_, 0, v_a_3636_);
v___x_3641_ = v_reuseFailAlloc_3642_;
goto v_reusejp_3640_;
}
v_reusejp_3640_:
{
return v___x_3641_;
}
}
}
}
else
{
lean_object* v___x_3644_; lean_object* v___x_3645_; 
lean_dec_ref(v___x_3600_);
lean_dec_ref(v_e_3594_);
lean_dec_ref(v___f_3593_);
v___x_3644_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_3645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3645_, 0, v___x_3644_);
return v___x_3645_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_zetaReduce___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_3593_ = stack[0].m_obj;
lean_object* v_e_3594_ = stack[1].m_obj;
lean_object* v___y_3595_ = stack[2].m_obj;
lean_object* v___y_3596_ = stack[3].m_obj;
lean_object* v___y_3597_ = stack[4].m_obj;
lean_object* v___y_3598_ = stack[5].m_obj;
lean_object* v_res_3646_;
v_res_3646_ = l_Lean_Meta_zetaReduce___lam__4(v___f_3593_, v_e_3594_, v___y_3595_, v___y_3596_, v___y_3597_, v___y_3598_);
stack->m_obj
 = v_res_3646_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__4___boxed(lean_object* v___f_3647_, lean_object* v_e_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_){
_start:
{
lean_object* v_res_3654_; 
v_res_3654_ = l_Lean_Meta_zetaReduce___lam__4(v___f_3647_, v_e_3648_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_);
lean_dec(v___y_3652_);
lean_dec_ref(v___y_3651_);
lean_dec(v___y_3650_);
lean_dec_ref(v___y_3649_);
return v_res_3654_;
}
}
lean_object* l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0(lean_object* v_00_u03b1_3655_, lean_object* v_x_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_){
_start:
{
lean_object* v___x_3662_; lean_object* v___x_3663_; 
v___x_3662_ = lean_apply_1(v_x_3656_, lean_box(0));
v___x_3663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3663_, 0, v___x_3662_);
return v___x_3663_;
}
}
LEAN_EXPORT void l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3656_ = stack[1].m_obj;
lean_object* v___y_3657_ = stack[2].m_obj;
lean_object* v___y_3658_ = stack[3].m_obj;
lean_object* v___y_3659_ = stack[4].m_obj;
lean_object* v___y_3660_ = stack[5].m_obj;
lean_object* v_res_3664_;
v_res_3664_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0(lean_box(0), v_x_3656_, v___y_3657_, v___y_3658_, v___y_3659_, v___y_3660_);
stack->m_obj
 = v_res_3664_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0___boxed(lean_object* v_00_u03b1_3665_, lean_object* v_x_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_){
_start:
{
lean_object* v_res_3672_; 
v_res_3672_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0(v_00_u03b1_3665_, v_x_3666_, v___y_3667_, v___y_3668_, v___y_3669_, v___y_3670_);
lean_dec(v___y_3670_);
lean_dec_ref(v___y_3669_);
lean_dec(v___y_3668_);
lean_dec_ref(v___y_3667_);
return v_res_3672_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__2(lean_object* v___x_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_){
_start:
{
lean_object* v___x_3679_; 
v___x_3679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3679_, 0, v___x_3673_);
return v___x_3679_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3673_ = stack[0].m_obj;
lean_object* v___y_3674_ = stack[1].m_obj;
lean_object* v___y_3675_ = stack[2].m_obj;
lean_object* v___y_3676_ = stack[3].m_obj;
lean_object* v___y_3677_ = stack[4].m_obj;
lean_object* v_res_3680_;
v_res_3680_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__2(v___x_3673_, v___y_3674_, v___y_3675_, v___y_3676_, v___y_3677_);
stack->m_obj
 = v_res_3680_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__2___boxed(lean_object* v___x_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_){
_start:
{
lean_object* v_res_3687_; 
v_res_3687_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__2(v___x_3681_, v___y_3682_, v___y_3683_, v___y_3684_, v___y_3685_);
lean_dec(v___y_3685_);
lean_dec_ref(v___y_3684_);
lean_dec(v___y_3683_);
lean_dec_ref(v___y_3682_);
return v_res_3687_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0(lean_object* v_k_3688_, lean_object* v___y_3689_, lean_object* v_b_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_){
_start:
{
lean_object* v___x_3696_; 
lean_inc(v___y_3694_);
lean_inc_ref(v___y_3693_);
lean_inc(v___y_3692_);
lean_inc_ref(v___y_3691_);
lean_inc(v___y_3689_);
v___x_3696_ = lean_apply_7(v_k_3688_, v_b_3690_, v___y_3689_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_, lean_box(0));
return v___x_3696_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_3688_ = stack[0].m_obj;
lean_object* v___y_3689_ = stack[1].m_obj;
lean_object* v_b_3690_ = stack[2].m_obj;
lean_object* v___y_3691_ = stack[3].m_obj;
lean_object* v___y_3692_ = stack[4].m_obj;
lean_object* v___y_3693_ = stack[5].m_obj;
lean_object* v___y_3694_ = stack[6].m_obj;
lean_object* v_res_3697_;
v_res_3697_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0(v_k_3688_, v___y_3689_, v_b_3690_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_);
stack->m_obj
 = v_res_3697_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0___boxed(lean_object* v_k_3698_, lean_object* v___y_3699_, lean_object* v_b_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_){
_start:
{
lean_object* v_res_3706_; 
v_res_3706_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0(v_k_3698_, v___y_3699_, v_b_3700_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_);
lean_dec(v___y_3704_);
lean_dec_ref(v___y_3703_);
lean_dec(v___y_3702_);
lean_dec_ref(v___y_3701_);
lean_dec(v___y_3699_);
return v_res_3706_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(lean_object* v_name_3707_, uint8_t v_bi_3708_, lean_object* v_type_3709_, lean_object* v_k_3710_, uint8_t v_kind_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_){
_start:
{
lean_object* v___f_3718_; lean_object* v___x_3719_; 
lean_inc(v___y_3712_);
v___f_3718_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3718_, 0, v_k_3710_);
lean_closure_set(v___f_3718_, 1, v___y_3712_);
v___x_3719_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3707_, v_bi_3708_, v_type_3709_, v___f_3718_, v_kind_3711_, v___y_3713_, v___y_3714_, v___y_3715_, v___y_3716_);
if (lean_obj_tag(v___x_3719_) == 0)
{
return v___x_3719_;
}
else
{
lean_object* v_a_3720_; lean_object* v___x_3722_; uint8_t v_isShared_3723_; uint8_t v_isSharedCheck_3727_; 
v_a_3720_ = lean_ctor_get(v___x_3719_, 0);
v_isSharedCheck_3727_ = !lean_is_exclusive(v___x_3719_);
if (v_isSharedCheck_3727_ == 0)
{
v___x_3722_ = v___x_3719_;
v_isShared_3723_ = v_isSharedCheck_3727_;
goto v_resetjp_3721_;
}
else
{
lean_inc(v_a_3720_);
lean_dec(v___x_3719_);
v___x_3722_ = lean_box(0);
v_isShared_3723_ = v_isSharedCheck_3727_;
goto v_resetjp_3721_;
}
v_resetjp_3721_:
{
lean_object* v___x_3725_; 
if (v_isShared_3723_ == 0)
{
v___x_3725_ = v___x_3722_;
goto v_reusejp_3724_;
}
else
{
lean_object* v_reuseFailAlloc_3726_; 
v_reuseFailAlloc_3726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3726_, 0, v_a_3720_);
v___x_3725_ = v_reuseFailAlloc_3726_;
goto v_reusejp_3724_;
}
v_reusejp_3724_:
{
return v___x_3725_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_3707_ = stack[0].m_obj;
uint8_t v_bi_3708_ = stack[1].m_num;
lean_object* v_type_3709_ = stack[2].m_obj;
lean_object* v_k_3710_ = stack[3].m_obj;
uint8_t v_kind_3711_ = stack[4].m_num;
lean_object* v___y_3712_ = stack[5].m_obj;
lean_object* v___y_3713_ = stack[6].m_obj;
lean_object* v___y_3714_ = stack[7].m_obj;
lean_object* v___y_3715_ = stack[8].m_obj;
lean_object* v___y_3716_ = stack[9].m_obj;
lean_object* v_res_3728_;
v_res_3728_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_name_3707_, v_bi_3708_, v_type_3709_, v_k_3710_, v_kind_3711_, v___y_3712_, v___y_3713_, v___y_3714_, v___y_3715_, v___y_3716_);
stack->m_obj
 = v_res_3728_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___boxed(lean_object* v_name_3729_, lean_object* v_bi_3730_, lean_object* v_type_3731_, lean_object* v_k_3732_, lean_object* v_kind_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_){
_start:
{
uint8_t v_bi_boxed_3740_; uint8_t v_kind_boxed_3741_; lean_object* v_res_3742_; 
v_bi_boxed_3740_ = lean_unbox(v_bi_3730_);
v_kind_boxed_3741_ = lean_unbox(v_kind_3733_);
v_res_3742_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_name_3729_, v_bi_boxed_3740_, v_type_3731_, v_k_3732_, v_kind_boxed_3741_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_, v___y_3738_);
lean_dec(v___y_3738_);
lean_dec_ref(v___y_3737_);
lean_dec(v___y_3736_);
lean_dec_ref(v___y_3735_);
lean_dec(v___y_3734_);
return v_res_3742_;
}
}
lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg(lean_object* v_name_3743_, lean_object* v_type_3744_, lean_object* v_val_3745_, lean_object* v_k_3746_, uint8_t v_nondep_3747_, uint8_t v_kind_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_){
_start:
{
lean_object* v___f_3755_; lean_object* v___x_3756_; 
lean_inc(v___y_3749_);
v___f_3755_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3755_, 0, v_k_3746_);
lean_closure_set(v___f_3755_, 1, v___y_3749_);
v___x_3756_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_3743_, v_type_3744_, v_val_3745_, v___f_3755_, v_nondep_3747_, v_kind_3748_, v___y_3750_, v___y_3751_, v___y_3752_, v___y_3753_);
if (lean_obj_tag(v___x_3756_) == 0)
{
return v___x_3756_;
}
else
{
lean_object* v_a_3757_; lean_object* v___x_3759_; uint8_t v_isShared_3760_; uint8_t v_isSharedCheck_3764_; 
v_a_3757_ = lean_ctor_get(v___x_3756_, 0);
v_isSharedCheck_3764_ = !lean_is_exclusive(v___x_3756_);
if (v_isSharedCheck_3764_ == 0)
{
v___x_3759_ = v___x_3756_;
v_isShared_3760_ = v_isSharedCheck_3764_;
goto v_resetjp_3758_;
}
else
{
lean_inc(v_a_3757_);
lean_dec(v___x_3756_);
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
}
LEAN_EXPORT void l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_3743_ = stack[0].m_obj;
lean_object* v_type_3744_ = stack[1].m_obj;
lean_object* v_val_3745_ = stack[2].m_obj;
lean_object* v_k_3746_ = stack[3].m_obj;
uint8_t v_nondep_3747_ = stack[4].m_num;
uint8_t v_kind_3748_ = stack[5].m_num;
lean_object* v___y_3749_ = stack[6].m_obj;
lean_object* v___y_3750_ = stack[7].m_obj;
lean_object* v___y_3751_ = stack[8].m_obj;
lean_object* v___y_3752_ = stack[9].m_obj;
lean_object* v___y_3753_ = stack[10].m_obj;
lean_object* v_res_3765_;
v_res_3765_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg(v_name_3743_, v_type_3744_, v_val_3745_, v_k_3746_, v_nondep_3747_, v_kind_3748_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_, v___y_3753_);
stack->m_obj
 = v_res_3765_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg___boxed(lean_object* v_name_3766_, lean_object* v_type_3767_, lean_object* v_val_3768_, lean_object* v_k_3769_, lean_object* v_nondep_3770_, lean_object* v_kind_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_){
_start:
{
uint8_t v_nondep_boxed_3778_; uint8_t v_kind_boxed_3779_; lean_object* v_res_3780_; 
v_nondep_boxed_3778_ = lean_unbox(v_nondep_3770_);
v_kind_boxed_3779_ = lean_unbox(v_kind_3771_);
v_res_3780_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg(v_name_3766_, v_type_3767_, v_val_3768_, v_k_3769_, v_nondep_boxed_3778_, v_kind_boxed_3779_, v___y_3772_, v___y_3773_, v___y_3774_, v___y_3775_, v___y_3776_);
lean_dec(v___y_3776_);
lean_dec_ref(v___y_3775_);
lean_dec(v___y_3774_);
lean_dec_ref(v___y_3773_);
lean_dec(v___y_3772_);
return v_res_3780_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0(lean_object* v_00_u03b1_3781_, lean_object* v_x_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_){
_start:
{
lean_object* v___x_3788_; lean_object* v___x_3789_; 
v___x_3788_ = lean_apply_1(v_x_3782_, lean_box(0));
v___x_3789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3789_, 0, v___x_3788_);
return v___x_3789_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3782_ = stack[1].m_obj;
lean_object* v___y_3783_ = stack[2].m_obj;
lean_object* v___y_3784_ = stack[3].m_obj;
lean_object* v___y_3785_ = stack[4].m_obj;
lean_object* v___y_3786_ = stack[5].m_obj;
lean_object* v_res_3790_;
v_res_3790_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0(lean_box(0), v_x_3782_, v___y_3783_, v___y_3784_, v___y_3785_, v___y_3786_);
stack->m_obj
 = v_res_3790_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0___boxed(lean_object* v_00_u03b1_3791_, lean_object* v_x_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_){
_start:
{
lean_object* v_res_3798_; 
v_res_3798_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0(v_00_u03b1_3791_, v_x_3792_, v___y_3793_, v___y_3794_, v___y_3795_, v___y_3796_);
lean_dec(v___y_3796_);
lean_dec_ref(v___y_3795_);
lean_dec(v___y_3794_);
lean_dec_ref(v___y_3793_);
return v_res_3798_;
}
}
lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg(lean_object* v_ref_3799_){
_start:
{
lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; 
v___x_3801_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5);
v___x_3802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3802_, 0, v_ref_3799_);
lean_ctor_set(v___x_3802_, 1, v___x_3801_);
v___x_3803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3803_, 0, v___x_3802_);
return v___x_3803_;
}
}
LEAN_EXPORT void l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_3799_ = stack[0].m_obj;
lean_object* v_res_3804_;
v_res_3804_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg(v_ref_3799_);
stack->m_obj
 = v_res_3804_;
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg___boxed(lean_object* v_ref_3805_, lean_object* v___y_3806_){
_start:
{
lean_object* v_res_3807_; 
v_res_3807_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg(v_ref_3805_);
return v_res_3807_;
}
}
lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg(lean_object* v_x_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_){
_start:
{
lean_object* v___y_3816_; lean_object* v_toCold_3825_; lean_object* v_currRecDepth_3826_; lean_object* v_ref_3827_; uint16_t v_optionFlags_3828_; uint8_t v_suppressElabErrors_3829_; uint8_t v_isRecordingDeps_3830_; lean_object* v_maxRecDepth_3836_; lean_object* v___x_3837_; uint8_t v___x_3838_; 
v_toCold_3825_ = lean_ctor_get(v___y_3812_, 0);
v_currRecDepth_3826_ = lean_ctor_get(v___y_3812_, 1);
v_ref_3827_ = lean_ctor_get(v___y_3812_, 2);
v_optionFlags_3828_ = lean_ctor_get_uint16(v___y_3812_, sizeof(void*)*3);
v_suppressElabErrors_3829_ = lean_ctor_get_uint8(v___y_3812_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3830_ = lean_ctor_get_uint8(v___y_3812_, sizeof(void*)*3 + 3);
v_maxRecDepth_3836_ = lean_ctor_get(v_toCold_3825_, 3);
v___x_3837_ = lean_unsigned_to_nat(0u);
v___x_3838_ = lean_nat_dec_eq(v_maxRecDepth_3836_, v___x_3837_);
if (v___x_3838_ == 0)
{
uint8_t v___x_3839_; 
v___x_3839_ = lean_nat_dec_eq(v_currRecDepth_3826_, v_maxRecDepth_3836_);
if (v___x_3839_ == 0)
{
goto v___jp_3831_;
}
else
{
lean_object* v___x_3840_; 
lean_dec_ref(v_x_3808_);
lean_inc(v_ref_3827_);
v___x_3840_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg(v_ref_3827_);
v___y_3816_ = v___x_3840_;
goto v___jp_3815_;
}
}
else
{
goto v___jp_3831_;
}
v___jp_3815_:
{
if (lean_obj_tag(v___y_3816_) == 0)
{
return v___y_3816_;
}
else
{
lean_object* v_a_3817_; lean_object* v___x_3819_; uint8_t v_isShared_3820_; uint8_t v_isSharedCheck_3824_; 
v_a_3817_ = lean_ctor_get(v___y_3816_, 0);
v_isSharedCheck_3824_ = !lean_is_exclusive(v___y_3816_);
if (v_isSharedCheck_3824_ == 0)
{
v___x_3819_ = v___y_3816_;
v_isShared_3820_ = v_isSharedCheck_3824_;
goto v_resetjp_3818_;
}
else
{
lean_inc(v_a_3817_);
lean_dec(v___y_3816_);
v___x_3819_ = lean_box(0);
v_isShared_3820_ = v_isSharedCheck_3824_;
goto v_resetjp_3818_;
}
v_resetjp_3818_:
{
lean_object* v___x_3822_; 
if (v_isShared_3820_ == 0)
{
v___x_3822_ = v___x_3819_;
goto v_reusejp_3821_;
}
else
{
lean_object* v_reuseFailAlloc_3823_; 
v_reuseFailAlloc_3823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3823_, 0, v_a_3817_);
v___x_3822_ = v_reuseFailAlloc_3823_;
goto v_reusejp_3821_;
}
v_reusejp_3821_:
{
return v___x_3822_;
}
}
}
}
v___jp_3831_:
{
lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; lean_object* v___x_3835_; 
v___x_3832_ = lean_unsigned_to_nat(1u);
v___x_3833_ = lean_nat_add(v_currRecDepth_3826_, v___x_3832_);
lean_inc(v_ref_3827_);
lean_inc_ref(v_toCold_3825_);
v___x_3834_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3834_, 0, v_toCold_3825_);
lean_ctor_set(v___x_3834_, 1, v___x_3833_);
lean_ctor_set(v___x_3834_, 2, v_ref_3827_);
lean_ctor_set_uint16(v___x_3834_, sizeof(void*)*3, v_optionFlags_3828_);
lean_ctor_set_uint8(v___x_3834_, sizeof(void*)*3 + 2, v_suppressElabErrors_3829_);
lean_ctor_set_uint8(v___x_3834_, sizeof(void*)*3 + 3, v_isRecordingDeps_3830_);
lean_inc(v___y_3813_);
lean_inc(v___y_3811_);
lean_inc_ref(v___y_3810_);
lean_inc(v___y_3809_);
v___x_3835_ = lean_apply_6(v_x_3808_, v___y_3809_, v___y_3810_, v___y_3811_, v___x_3834_, v___y_3813_, lean_box(0));
v___y_3816_ = v___x_3835_;
goto v___jp_3815_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3808_ = stack[0].m_obj;
lean_object* v___y_3809_ = stack[1].m_obj;
lean_object* v___y_3810_ = stack[2].m_obj;
lean_object* v___y_3811_ = stack[3].m_obj;
lean_object* v___y_3812_ = stack[4].m_obj;
lean_object* v___y_3813_ = stack[5].m_obj;
lean_object* v_res_3841_;
v_res_3841_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg(v_x_3808_, v___y_3809_, v___y_3810_, v___y_3811_, v___y_3812_, v___y_3813_);
stack->m_obj
 = v_res_3841_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg___boxed(lean_object* v_x_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_){
_start:
{
lean_object* v_res_3849_; 
v_res_3849_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg(v_x_3842_, v___y_3843_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_);
lean_dec(v___y_3847_);
lean_dec_ref(v___y_3846_);
lean_dec(v___y_3845_);
lean_dec_ref(v___y_3844_);
lean_dec(v___y_3843_);
return v_res_3849_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___lam__0___boxed(lean_object* v_fvars_3850_, lean_object* v_pre_3851_, lean_object* v_post_3852_, lean_object* v_usedLetOnly_3853_, lean_object* v_skipConstInApp_3854_, lean_object* v_skipInstances_3855_, lean_object* v_body_3856_, lean_object* v_x_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_){
_start:
{
uint8_t v_usedLetOnly_boxed_3864_; uint8_t v_skipConstInApp_boxed_3865_; uint8_t v_skipInstances_boxed_3866_; lean_object* v_res_3867_; 
v_usedLetOnly_boxed_3864_ = lean_unbox(v_usedLetOnly_3853_);
v_skipConstInApp_boxed_3865_ = lean_unbox(v_skipConstInApp_3854_);
v_skipInstances_boxed_3866_ = lean_unbox(v_skipInstances_3855_);
v_res_3867_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___lam__0(v_fvars_3850_, v_pre_3851_, v_post_3852_, v_usedLetOnly_boxed_3864_, v_skipConstInApp_boxed_3865_, v_skipInstances_boxed_3866_, v_body_3856_, v_x_3857_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_, v___y_3862_);
lean_dec(v___y_3862_);
lean_dec_ref(v___y_3861_);
lean_dec(v___y_3860_);
lean_dec_ref(v___y_3859_);
lean_dec(v___y_3858_);
return v_res_3867_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___lam__0(lean_object* v_fvars_3868_, lean_object* v_pre_3869_, lean_object* v_post_3870_, uint8_t v_usedLetOnly_3871_, uint8_t v_skipConstInApp_3872_, uint8_t v_skipInstances_3873_, lean_object* v_body_3874_, lean_object* v_x_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_){
_start:
{
lean_object* v___x_3882_; lean_object* v___x_3883_; 
v___x_3882_ = lean_array_push(v_fvars_3868_, v_x_3875_);
v___x_3883_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6(v_pre_3869_, v_post_3870_, v_usedLetOnly_3871_, v_skipConstInApp_3872_, v_skipInstances_3873_, v___x_3882_, v_body_3874_, v___y_3876_, v___y_3877_, v___y_3878_, v___y_3879_, v___y_3880_);
return v___x_3883_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_3868_ = stack[0].m_obj;
lean_object* v_pre_3869_ = stack[1].m_obj;
lean_object* v_post_3870_ = stack[2].m_obj;
uint8_t v_usedLetOnly_3871_ = stack[3].m_num;
uint8_t v_skipConstInApp_3872_ = stack[4].m_num;
uint8_t v_skipInstances_3873_ = stack[5].m_num;
lean_object* v_body_3874_ = stack[6].m_obj;
lean_object* v_x_3875_ = stack[7].m_obj;
lean_object* v___y_3876_ = stack[8].m_obj;
lean_object* v___y_3877_ = stack[9].m_obj;
lean_object* v___y_3878_ = stack[10].m_obj;
lean_object* v___y_3879_ = stack[11].m_obj;
lean_object* v___y_3880_ = stack[12].m_obj;
lean_object* v_res_3884_;
v_res_3884_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___lam__0(v_fvars_3868_, v_pre_3869_, v_post_3870_, v_usedLetOnly_3871_, v_skipConstInApp_3872_, v_skipInstances_3873_, v_body_3874_, v_x_3875_, v___y_3876_, v___y_3877_, v___y_3878_, v___y_3879_, v___y_3880_);
stack->m_obj
 = v_res_3884_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___lam__0___boxed(lean_object* v_fvars_3885_, lean_object* v_pre_3886_, lean_object* v_post_3887_, lean_object* v_usedLetOnly_3888_, lean_object* v_skipConstInApp_3889_, lean_object* v_skipInstances_3890_, lean_object* v_body_3891_, lean_object* v_x_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_){
_start:
{
uint8_t v_usedLetOnly_boxed_3899_; uint8_t v_skipConstInApp_boxed_3900_; uint8_t v_skipInstances_boxed_3901_; lean_object* v_res_3902_; 
v_usedLetOnly_boxed_3899_ = lean_unbox(v_usedLetOnly_3888_);
v_skipConstInApp_boxed_3900_ = lean_unbox(v_skipConstInApp_3889_);
v_skipInstances_boxed_3901_ = lean_unbox(v_skipInstances_3890_);
v_res_3902_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___lam__0(v_fvars_3885_, v_pre_3886_, v_post_3887_, v_usedLetOnly_boxed_3899_, v_skipConstInApp_boxed_3900_, v_skipInstances_boxed_3901_, v_body_3891_, v_x_3892_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_);
lean_dec(v___y_3897_);
lean_dec_ref(v___y_3896_);
lean_dec(v___y_3895_);
lean_dec_ref(v___y_3894_);
lean_dec(v___y_3893_);
return v_res_3902_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(lean_object* v_pre_3903_, lean_object* v_post_3904_, uint8_t v_usedLetOnly_3905_, uint8_t v_skipConstInApp_3906_, uint8_t v_skipInstances_3907_, lean_object* v_e_3908_, lean_object* v_a_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_){
_start:
{
lean_object* v___x_3915_; 
lean_inc_ref(v_post_3904_);
lean_inc(v___y_3913_);
lean_inc_ref(v___y_3912_);
lean_inc(v___y_3911_);
lean_inc_ref(v___y_3910_);
lean_inc_ref(v_e_3908_);
v___x_3915_ = lean_apply_6(v_post_3904_, v_e_3908_, v___y_3910_, v___y_3911_, v___y_3912_, v___y_3913_, lean_box(0));
if (lean_obj_tag(v___x_3915_) == 0)
{
lean_object* v_a_3916_; lean_object* v___x_3918_; uint8_t v_isShared_3919_; uint8_t v_isSharedCheck_3934_; 
v_a_3916_ = lean_ctor_get(v___x_3915_, 0);
v_isSharedCheck_3934_ = !lean_is_exclusive(v___x_3915_);
if (v_isSharedCheck_3934_ == 0)
{
v___x_3918_ = v___x_3915_;
v_isShared_3919_ = v_isSharedCheck_3934_;
goto v_resetjp_3917_;
}
else
{
lean_inc(v_a_3916_);
lean_dec(v___x_3915_);
v___x_3918_ = lean_box(0);
v_isShared_3919_ = v_isSharedCheck_3934_;
goto v_resetjp_3917_;
}
v_resetjp_3917_:
{
switch(lean_obj_tag(v_a_3916_))
{
case 0:
{
lean_object* v_e_3920_; lean_object* v___x_3922_; 
lean_dec_ref(v_e_3908_);
lean_dec_ref(v_post_3904_);
lean_dec_ref(v_pre_3903_);
v_e_3920_ = lean_ctor_get(v_a_3916_, 0);
lean_inc_ref(v_e_3920_);
lean_dec_ref_known(v_a_3916_, 1);
if (v_isShared_3919_ == 0)
{
lean_ctor_set(v___x_3918_, 0, v_e_3920_);
v___x_3922_ = v___x_3918_;
goto v_reusejp_3921_;
}
else
{
lean_object* v_reuseFailAlloc_3923_; 
v_reuseFailAlloc_3923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3923_, 0, v_e_3920_);
v___x_3922_ = v_reuseFailAlloc_3923_;
goto v_reusejp_3921_;
}
v_reusejp_3921_:
{
return v___x_3922_;
}
}
case 1:
{
lean_object* v_e_3924_; lean_object* v___x_3925_; 
lean_del_object(v___x_3918_);
lean_dec_ref(v_e_3908_);
v_e_3924_ = lean_ctor_get(v_a_3916_, 0);
lean_inc_ref(v_e_3924_);
lean_dec_ref_known(v_a_3916_, 1);
v___x_3925_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3903_, v_post_3904_, v_usedLetOnly_3905_, v_skipConstInApp_3906_, v_skipInstances_3907_, v_e_3924_, v_a_3909_, v___y_3910_, v___y_3911_, v___y_3912_, v___y_3913_);
return v___x_3925_;
}
default: 
{
lean_object* v_e_x3f_3926_; 
lean_dec_ref(v_post_3904_);
lean_dec_ref(v_pre_3903_);
v_e_x3f_3926_ = lean_ctor_get(v_a_3916_, 0);
lean_inc(v_e_x3f_3926_);
lean_dec_ref_known(v_a_3916_, 1);
if (lean_obj_tag(v_e_x3f_3926_) == 0)
{
lean_object* v___x_3928_; 
if (v_isShared_3919_ == 0)
{
lean_ctor_set(v___x_3918_, 0, v_e_3908_);
v___x_3928_ = v___x_3918_;
goto v_reusejp_3927_;
}
else
{
lean_object* v_reuseFailAlloc_3929_; 
v_reuseFailAlloc_3929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3929_, 0, v_e_3908_);
v___x_3928_ = v_reuseFailAlloc_3929_;
goto v_reusejp_3927_;
}
v_reusejp_3927_:
{
return v___x_3928_;
}
}
else
{
lean_object* v_val_3930_; lean_object* v___x_3932_; 
lean_dec_ref(v_e_3908_);
v_val_3930_ = lean_ctor_get(v_e_x3f_3926_, 0);
lean_inc(v_val_3930_);
lean_dec_ref_known(v_e_x3f_3926_, 1);
if (v_isShared_3919_ == 0)
{
lean_ctor_set(v___x_3918_, 0, v_val_3930_);
v___x_3932_ = v___x_3918_;
goto v_reusejp_3931_;
}
else
{
lean_object* v_reuseFailAlloc_3933_; 
v_reuseFailAlloc_3933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3933_, 0, v_val_3930_);
v___x_3932_ = v_reuseFailAlloc_3933_;
goto v_reusejp_3931_;
}
v_reusejp_3931_:
{
return v___x_3932_;
}
}
}
}
}
}
else
{
lean_object* v_a_3935_; lean_object* v___x_3937_; uint8_t v_isShared_3938_; uint8_t v_isSharedCheck_3942_; 
lean_dec_ref(v_e_3908_);
lean_dec_ref(v_post_3904_);
lean_dec_ref(v_pre_3903_);
v_a_3935_ = lean_ctor_get(v___x_3915_, 0);
v_isSharedCheck_3942_ = !lean_is_exclusive(v___x_3915_);
if (v_isSharedCheck_3942_ == 0)
{
v___x_3937_ = v___x_3915_;
v_isShared_3938_ = v_isSharedCheck_3942_;
goto v_resetjp_3936_;
}
else
{
lean_inc(v_a_3935_);
lean_dec(v___x_3915_);
v___x_3937_ = lean_box(0);
v_isShared_3938_ = v_isSharedCheck_3942_;
goto v_resetjp_3936_;
}
v_resetjp_3936_:
{
lean_object* v___x_3940_; 
if (v_isShared_3938_ == 0)
{
v___x_3940_ = v___x_3937_;
goto v_reusejp_3939_;
}
else
{
lean_object* v_reuseFailAlloc_3941_; 
v_reuseFailAlloc_3941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3941_, 0, v_a_3935_);
v___x_3940_ = v_reuseFailAlloc_3941_;
goto v_reusejp_3939_;
}
v_reusejp_3939_:
{
return v___x_3940_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_3903_ = stack[0].m_obj;
lean_object* v_post_3904_ = stack[1].m_obj;
uint8_t v_usedLetOnly_3905_ = stack[2].m_num;
uint8_t v_skipConstInApp_3906_ = stack[3].m_num;
uint8_t v_skipInstances_3907_ = stack[4].m_num;
lean_object* v_e_3908_ = stack[5].m_obj;
lean_object* v_a_3909_ = stack[6].m_obj;
lean_object* v___y_3910_ = stack[7].m_obj;
lean_object* v___y_3911_ = stack[8].m_obj;
lean_object* v___y_3912_ = stack[9].m_obj;
lean_object* v___y_3913_ = stack[10].m_obj;
lean_object* v_res_3943_;
v_res_3943_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_3903_, v_post_3904_, v_usedLetOnly_3905_, v_skipConstInApp_3906_, v_skipInstances_3907_, v_e_3908_, v_a_3909_, v___y_3910_, v___y_3911_, v___y_3912_, v___y_3913_);
stack->m_obj
 = v_res_3943_;
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6(lean_object* v_pre_3944_, lean_object* v_post_3945_, uint8_t v_usedLetOnly_3946_, uint8_t v_skipConstInApp_3947_, uint8_t v_skipInstances_3948_, lean_object* v_fvars_3949_, lean_object* v_e_3950_, lean_object* v_a_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_){
_start:
{
if (lean_obj_tag(v_e_3950_) == 6)
{
lean_object* v_binderName_3957_; lean_object* v_binderType_3958_; lean_object* v_body_3959_; uint8_t v_binderInfo_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___f_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; 
v_binderName_3957_ = lean_ctor_get(v_e_3950_, 0);
lean_inc(v_binderName_3957_);
v_binderType_3958_ = lean_ctor_get(v_e_3950_, 1);
lean_inc_ref(v_binderType_3958_);
v_body_3959_ = lean_ctor_get(v_e_3950_, 2);
lean_inc_ref(v_body_3959_);
v_binderInfo_3960_ = lean_ctor_get_uint8(v_e_3950_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_3950_, 3);
v___x_3961_ = lean_box(v_usedLetOnly_3946_);
v___x_3962_ = lean_box(v_skipConstInApp_3947_);
v___x_3963_ = lean_box(v_skipInstances_3948_);
lean_inc_ref(v_post_3945_);
lean_inc_ref(v_pre_3944_);
lean_inc_ref(v_fvars_3949_);
v___f_3964_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___lam__0___boxed), 14, 7);
lean_closure_set(v___f_3964_, 0, v_fvars_3949_);
lean_closure_set(v___f_3964_, 1, v_pre_3944_);
lean_closure_set(v___f_3964_, 2, v_post_3945_);
lean_closure_set(v___f_3964_, 3, v___x_3961_);
lean_closure_set(v___f_3964_, 4, v___x_3962_);
lean_closure_set(v___f_3964_, 5, v___x_3963_);
lean_closure_set(v___f_3964_, 6, v_body_3959_);
v___x_3965_ = lean_expr_instantiate_rev(v_binderType_3958_, v_fvars_3949_);
lean_dec_ref(v_fvars_3949_);
lean_dec_ref(v_binderType_3958_);
v___x_3966_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3944_, v_post_3945_, v_usedLetOnly_3946_, v_skipConstInApp_3947_, v_skipInstances_3948_, v___x_3965_, v_a_3951_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_);
if (lean_obj_tag(v___x_3966_) == 0)
{
lean_object* v_a_3967_; uint8_t v___x_3968_; lean_object* v___x_3969_; 
v_a_3967_ = lean_ctor_get(v___x_3966_, 0);
lean_inc(v_a_3967_);
lean_dec_ref_known(v___x_3966_, 1);
v___x_3968_ = 0;
v___x_3969_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_binderName_3957_, v_binderInfo_3960_, v_a_3967_, v___f_3964_, v___x_3968_, v_a_3951_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_);
return v___x_3969_;
}
else
{
lean_dec_ref(v___f_3964_);
lean_dec(v_binderName_3957_);
return v___x_3966_;
}
}
else
{
lean_object* v___x_3970_; lean_object* v___x_3971_; 
v___x_3970_ = lean_expr_instantiate_rev(v_e_3950_, v_fvars_3949_);
lean_dec_ref(v_e_3950_);
lean_inc_ref(v_post_3945_);
lean_inc_ref(v_pre_3944_);
v___x_3971_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3944_, v_post_3945_, v_usedLetOnly_3946_, v_skipConstInApp_3947_, v_skipInstances_3948_, v___x_3970_, v_a_3951_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_);
if (lean_obj_tag(v___x_3971_) == 0)
{
lean_object* v_a_3972_; uint8_t v___x_3973_; uint8_t v___x_3974_; uint8_t v___x_3975_; lean_object* v___x_3976_; 
v_a_3972_ = lean_ctor_get(v___x_3971_, 0);
lean_inc(v_a_3972_);
lean_dec_ref_known(v___x_3971_, 1);
v___x_3973_ = 0;
v___x_3974_ = 1;
v___x_3975_ = 1;
v___x_3976_ = l_Lean_Meta_mkLambdaFVars(v_fvars_3949_, v_a_3972_, v___x_3973_, v_usedLetOnly_3946_, v___x_3973_, v___x_3974_, v___x_3975_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_);
lean_dec_ref(v_fvars_3949_);
if (lean_obj_tag(v___x_3976_) == 0)
{
lean_object* v_a_3977_; lean_object* v___x_3978_; 
v_a_3977_ = lean_ctor_get(v___x_3976_, 0);
lean_inc(v_a_3977_);
lean_dec_ref_known(v___x_3976_, 1);
v___x_3978_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_3944_, v_post_3945_, v_usedLetOnly_3946_, v_skipConstInApp_3947_, v_skipInstances_3948_, v_a_3977_, v_a_3951_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_);
return v___x_3978_;
}
else
{
lean_dec_ref(v_post_3945_);
lean_dec_ref(v_pre_3944_);
return v___x_3976_;
}
}
else
{
lean_dec_ref(v_fvars_3949_);
lean_dec_ref(v_post_3945_);
lean_dec_ref(v_pre_3944_);
return v___x_3971_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_3944_ = stack[0].m_obj;
lean_object* v_post_3945_ = stack[1].m_obj;
uint8_t v_usedLetOnly_3946_ = stack[2].m_num;
uint8_t v_skipConstInApp_3947_ = stack[3].m_num;
uint8_t v_skipInstances_3948_ = stack[4].m_num;
lean_object* v_fvars_3949_ = stack[5].m_obj;
lean_object* v_e_3950_ = stack[6].m_obj;
lean_object* v_a_3951_ = stack[7].m_obj;
lean_object* v___y_3952_ = stack[8].m_obj;
lean_object* v___y_3953_ = stack[9].m_obj;
lean_object* v___y_3954_ = stack[10].m_obj;
lean_object* v___y_3955_ = stack[11].m_obj;
lean_object* v_res_3979_;
v_res_3979_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6(v_pre_3944_, v_post_3945_, v_usedLetOnly_3946_, v_skipConstInApp_3947_, v_skipInstances_3948_, v_fvars_3949_, v_e_3950_, v_a_3951_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_);
stack->m_obj
 = v_res_3979_;
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___lam__0(lean_object* v_fvars_3980_, lean_object* v_pre_3981_, lean_object* v_post_3982_, uint8_t v_usedLetOnly_3983_, uint8_t v_skipConstInApp_3984_, uint8_t v_skipInstances_3985_, lean_object* v_body_3986_, lean_object* v_x_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_){
_start:
{
lean_object* v___x_3994_; lean_object* v___x_3995_; 
v___x_3994_ = lean_array_push(v_fvars_3980_, v_x_3987_);
v___x_3995_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7(v_pre_3981_, v_post_3982_, v_usedLetOnly_3983_, v_skipConstInApp_3984_, v_skipInstances_3985_, v___x_3994_, v_body_3986_, v___y_3988_, v___y_3989_, v___y_3990_, v___y_3991_, v___y_3992_);
return v___x_3995_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_3980_ = stack[0].m_obj;
lean_object* v_pre_3981_ = stack[1].m_obj;
lean_object* v_post_3982_ = stack[2].m_obj;
uint8_t v_usedLetOnly_3983_ = stack[3].m_num;
uint8_t v_skipConstInApp_3984_ = stack[4].m_num;
uint8_t v_skipInstances_3985_ = stack[5].m_num;
lean_object* v_body_3986_ = stack[6].m_obj;
lean_object* v_x_3987_ = stack[7].m_obj;
lean_object* v___y_3988_ = stack[8].m_obj;
lean_object* v___y_3989_ = stack[9].m_obj;
lean_object* v___y_3990_ = stack[10].m_obj;
lean_object* v___y_3991_ = stack[11].m_obj;
lean_object* v___y_3992_ = stack[12].m_obj;
lean_object* v_res_3996_;
v_res_3996_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___lam__0(v_fvars_3980_, v_pre_3981_, v_post_3982_, v_usedLetOnly_3983_, v_skipConstInApp_3984_, v_skipInstances_3985_, v_body_3986_, v_x_3987_, v___y_3988_, v___y_3989_, v___y_3990_, v___y_3991_, v___y_3992_);
stack->m_obj
 = v_res_3996_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___lam__0___boxed(lean_object* v_fvars_3997_, lean_object* v_pre_3998_, lean_object* v_post_3999_, lean_object* v_usedLetOnly_4000_, lean_object* v_skipConstInApp_4001_, lean_object* v_skipInstances_4002_, lean_object* v_body_4003_, lean_object* v_x_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_){
_start:
{
uint8_t v_usedLetOnly_boxed_4011_; uint8_t v_skipConstInApp_boxed_4012_; uint8_t v_skipInstances_boxed_4013_; lean_object* v_res_4014_; 
v_usedLetOnly_boxed_4011_ = lean_unbox(v_usedLetOnly_4000_);
v_skipConstInApp_boxed_4012_ = lean_unbox(v_skipConstInApp_4001_);
v_skipInstances_boxed_4013_ = lean_unbox(v_skipInstances_4002_);
v_res_4014_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___lam__0(v_fvars_3997_, v_pre_3998_, v_post_3999_, v_usedLetOnly_boxed_4011_, v_skipConstInApp_boxed_4012_, v_skipInstances_boxed_4013_, v_body_4003_, v_x_4004_, v___y_4005_, v___y_4006_, v___y_4007_, v___y_4008_, v___y_4009_);
lean_dec(v___y_4009_);
lean_dec_ref(v___y_4008_);
lean_dec(v___y_4007_);
lean_dec_ref(v___y_4006_);
lean_dec(v___y_4005_);
return v_res_4014_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7(lean_object* v_pre_4015_, lean_object* v_post_4016_, uint8_t v_usedLetOnly_4017_, uint8_t v_skipConstInApp_4018_, uint8_t v_skipInstances_4019_, lean_object* v_fvars_4020_, lean_object* v_e_4021_, lean_object* v_a_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_){
_start:
{
if (lean_obj_tag(v_e_4021_) == 8)
{
lean_object* v_declName_4028_; lean_object* v_type_4029_; lean_object* v_value_4030_; lean_object* v_body_4031_; uint8_t v_nondep_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___f_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; 
v_declName_4028_ = lean_ctor_get(v_e_4021_, 0);
lean_inc(v_declName_4028_);
v_type_4029_ = lean_ctor_get(v_e_4021_, 1);
lean_inc_ref(v_type_4029_);
v_value_4030_ = lean_ctor_get(v_e_4021_, 2);
lean_inc_ref(v_value_4030_);
v_body_4031_ = lean_ctor_get(v_e_4021_, 3);
lean_inc_ref(v_body_4031_);
v_nondep_4032_ = lean_ctor_get_uint8(v_e_4021_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_4021_, 4);
v___x_4033_ = lean_box(v_usedLetOnly_4017_);
v___x_4034_ = lean_box(v_skipConstInApp_4018_);
v___x_4035_ = lean_box(v_skipInstances_4019_);
lean_inc_ref_n(v_post_4016_, 2);
lean_inc_ref_n(v_pre_4015_, 2);
lean_inc_ref(v_fvars_4020_);
v___f_4036_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___lam__0___boxed), 14, 7);
lean_closure_set(v___f_4036_, 0, v_fvars_4020_);
lean_closure_set(v___f_4036_, 1, v_pre_4015_);
lean_closure_set(v___f_4036_, 2, v_post_4016_);
lean_closure_set(v___f_4036_, 3, v___x_4033_);
lean_closure_set(v___f_4036_, 4, v___x_4034_);
lean_closure_set(v___f_4036_, 5, v___x_4035_);
lean_closure_set(v___f_4036_, 6, v_body_4031_);
v___x_4037_ = lean_expr_instantiate_rev(v_type_4029_, v_fvars_4020_);
lean_dec_ref(v_type_4029_);
v___x_4038_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4015_, v_post_4016_, v_usedLetOnly_4017_, v_skipConstInApp_4018_, v_skipInstances_4019_, v___x_4037_, v_a_4022_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_);
if (lean_obj_tag(v___x_4038_) == 0)
{
lean_object* v_a_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; 
v_a_4039_ = lean_ctor_get(v___x_4038_, 0);
lean_inc(v_a_4039_);
lean_dec_ref_known(v___x_4038_, 1);
v___x_4040_ = lean_expr_instantiate_rev(v_value_4030_, v_fvars_4020_);
lean_dec_ref(v_fvars_4020_);
lean_dec_ref(v_value_4030_);
v___x_4041_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4015_, v_post_4016_, v_usedLetOnly_4017_, v_skipConstInApp_4018_, v_skipInstances_4019_, v___x_4040_, v_a_4022_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_);
if (lean_obj_tag(v___x_4041_) == 0)
{
lean_object* v_a_4042_; uint8_t v___x_4043_; lean_object* v___x_4044_; 
v_a_4042_ = lean_ctor_get(v___x_4041_, 0);
lean_inc(v_a_4042_);
lean_dec_ref_known(v___x_4041_, 1);
v___x_4043_ = 0;
v___x_4044_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg(v_declName_4028_, v_a_4039_, v_a_4042_, v___f_4036_, v_nondep_4032_, v___x_4043_, v_a_4022_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_);
return v___x_4044_;
}
else
{
lean_dec(v_a_4039_);
lean_dec_ref(v___f_4036_);
lean_dec(v_declName_4028_);
return v___x_4041_;
}
}
else
{
lean_dec_ref(v___f_4036_);
lean_dec_ref(v_value_4030_);
lean_dec(v_declName_4028_);
lean_dec_ref(v_fvars_4020_);
lean_dec_ref(v_post_4016_);
lean_dec_ref(v_pre_4015_);
return v___x_4038_;
}
}
else
{
lean_object* v___x_4045_; lean_object* v___x_4046_; 
v___x_4045_ = lean_expr_instantiate_rev(v_e_4021_, v_fvars_4020_);
lean_dec_ref(v_e_4021_);
lean_inc_ref(v_post_4016_);
lean_inc_ref(v_pre_4015_);
v___x_4046_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4015_, v_post_4016_, v_usedLetOnly_4017_, v_skipConstInApp_4018_, v_skipInstances_4019_, v___x_4045_, v_a_4022_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_);
if (lean_obj_tag(v___x_4046_) == 0)
{
lean_object* v_a_4047_; uint8_t v___x_4048_; uint8_t v___x_4049_; lean_object* v___x_4050_; 
v_a_4047_ = lean_ctor_get(v___x_4046_, 0);
lean_inc(v_a_4047_);
lean_dec_ref_known(v___x_4046_, 1);
v___x_4048_ = 0;
v___x_4049_ = 1;
v___x_4050_ = l_Lean_Meta_mkLetFVars(v_fvars_4020_, v_a_4047_, v_usedLetOnly_4017_, v___x_4048_, v___x_4049_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_);
lean_dec_ref(v_fvars_4020_);
if (lean_obj_tag(v___x_4050_) == 0)
{
lean_object* v_a_4051_; lean_object* v___x_4052_; 
v_a_4051_ = lean_ctor_get(v___x_4050_, 0);
lean_inc(v_a_4051_);
lean_dec_ref_known(v___x_4050_, 1);
v___x_4052_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4015_, v_post_4016_, v_usedLetOnly_4017_, v_skipConstInApp_4018_, v_skipInstances_4019_, v_a_4051_, v_a_4022_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_);
return v___x_4052_;
}
else
{
lean_dec_ref(v_post_4016_);
lean_dec_ref(v_pre_4015_);
return v___x_4050_;
}
}
else
{
lean_dec_ref(v_fvars_4020_);
lean_dec_ref(v_post_4016_);
lean_dec_ref(v_pre_4015_);
return v___x_4046_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_4015_ = stack[0].m_obj;
lean_object* v_post_4016_ = stack[1].m_obj;
uint8_t v_usedLetOnly_4017_ = stack[2].m_num;
uint8_t v_skipConstInApp_4018_ = stack[3].m_num;
uint8_t v_skipInstances_4019_ = stack[4].m_num;
lean_object* v_fvars_4020_ = stack[5].m_obj;
lean_object* v_e_4021_ = stack[6].m_obj;
lean_object* v_a_4022_ = stack[7].m_obj;
lean_object* v___y_4023_ = stack[8].m_obj;
lean_object* v___y_4024_ = stack[9].m_obj;
lean_object* v___y_4025_ = stack[10].m_obj;
lean_object* v___y_4026_ = stack[11].m_obj;
lean_object* v_res_4053_;
v_res_4053_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7(v_pre_4015_, v_post_4016_, v_usedLetOnly_4017_, v_skipConstInApp_4018_, v_skipInstances_4019_, v_fvars_4020_, v_e_4021_, v_a_4022_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_);
stack->m_obj
 = v_res_4053_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__2(lean_object* v_pre_4054_, lean_object* v_post_4055_, uint8_t v_usedLetOnly_4056_, uint8_t v_skipConstInApp_4057_, uint8_t v_skipInstances_4058_, size_t v_sz_4059_, size_t v_i_4060_, lean_object* v_bs_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_){
_start:
{
uint8_t v___x_4068_; 
v___x_4068_ = lean_usize_dec_lt(v_i_4060_, v_sz_4059_);
if (v___x_4068_ == 0)
{
lean_object* v___x_4069_; 
lean_dec_ref(v_post_4055_);
lean_dec_ref(v_pre_4054_);
v___x_4069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4069_, 0, v_bs_4061_);
return v___x_4069_;
}
else
{
lean_object* v_v_4070_; lean_object* v___x_4071_; lean_object* v_bs_x27_4072_; lean_object* v___x_4073_; 
v_v_4070_ = lean_array_uget(v_bs_4061_, v_i_4060_);
v___x_4071_ = lean_unsigned_to_nat(0u);
v_bs_x27_4072_ = lean_array_uset(v_bs_4061_, v_i_4060_, v___x_4071_);
lean_inc_ref(v_post_4055_);
lean_inc_ref(v_pre_4054_);
v___x_4073_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4054_, v_post_4055_, v_usedLetOnly_4056_, v_skipConstInApp_4057_, v_skipInstances_4058_, v_v_4070_, v___y_4062_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_);
if (lean_obj_tag(v___x_4073_) == 0)
{
lean_object* v_a_4074_; size_t v___x_4075_; size_t v___x_4076_; lean_object* v___x_4077_; 
v_a_4074_ = lean_ctor_get(v___x_4073_, 0);
lean_inc(v_a_4074_);
lean_dec_ref_known(v___x_4073_, 1);
v___x_4075_ = ((size_t)1ULL);
v___x_4076_ = lean_usize_add(v_i_4060_, v___x_4075_);
v___x_4077_ = lean_array_uset(v_bs_x27_4072_, v_i_4060_, v_a_4074_);
v_i_4060_ = v___x_4076_;
v_bs_4061_ = v___x_4077_;
goto _start;
}
else
{
lean_object* v_a_4079_; lean_object* v___x_4081_; uint8_t v_isShared_4082_; uint8_t v_isSharedCheck_4086_; 
lean_dec_ref(v_bs_x27_4072_);
lean_dec_ref(v_post_4055_);
lean_dec_ref(v_pre_4054_);
v_a_4079_ = lean_ctor_get(v___x_4073_, 0);
v_isSharedCheck_4086_ = !lean_is_exclusive(v___x_4073_);
if (v_isSharedCheck_4086_ == 0)
{
v___x_4081_ = v___x_4073_;
v_isShared_4082_ = v_isSharedCheck_4086_;
goto v_resetjp_4080_;
}
else
{
lean_inc(v_a_4079_);
lean_dec(v___x_4073_);
v___x_4081_ = lean_box(0);
v_isShared_4082_ = v_isSharedCheck_4086_;
goto v_resetjp_4080_;
}
v_resetjp_4080_:
{
lean_object* v___x_4084_; 
if (v_isShared_4082_ == 0)
{
v___x_4084_ = v___x_4081_;
goto v_reusejp_4083_;
}
else
{
lean_object* v_reuseFailAlloc_4085_; 
v_reuseFailAlloc_4085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4085_, 0, v_a_4079_);
v___x_4084_ = v_reuseFailAlloc_4085_;
goto v_reusejp_4083_;
}
v_reusejp_4083_:
{
return v___x_4084_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_4054_ = stack[0].m_obj;
lean_object* v_post_4055_ = stack[1].m_obj;
uint8_t v_usedLetOnly_4056_ = stack[2].m_num;
uint8_t v_skipConstInApp_4057_ = stack[3].m_num;
uint8_t v_skipInstances_4058_ = stack[4].m_num;
size_t v_sz_4059_ = stack[5].m_num;
size_t v_i_4060_ = stack[6].m_num;
lean_object* v_bs_4061_ = stack[7].m_obj;
lean_object* v___y_4062_ = stack[8].m_obj;
lean_object* v___y_4063_ = stack[9].m_obj;
lean_object* v___y_4064_ = stack[10].m_obj;
lean_object* v___y_4065_ = stack[11].m_obj;
lean_object* v___y_4066_ = stack[12].m_obj;
lean_object* v_res_4087_;
v_res_4087_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__2(v_pre_4054_, v_post_4055_, v_usedLetOnly_4056_, v_skipConstInApp_4057_, v_skipInstances_4058_, v_sz_4059_, v_i_4060_, v_bs_4061_, v___y_4062_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_);
stack->m_obj
 = v_res_4087_;
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0(lean_object* v_pre_4088_, lean_object* v_post_4089_, uint8_t v_usedLetOnly_4090_, uint8_t v_skipConstInApp_4091_, uint8_t v_skipInstances_4092_, lean_object* v___x_4093_, lean_object* v___y_4094_, lean_object* v_b_4095_, lean_object* v_a_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_){
_start:
{
lean_object* v___x_4102_; 
v___x_4102_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4088_, v_post_4089_, v_usedLetOnly_4090_, v_skipConstInApp_4091_, v_skipInstances_4092_, v___x_4093_, v___y_4094_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_);
if (lean_obj_tag(v___x_4102_) == 0)
{
lean_object* v_a_4103_; lean_object* v___x_4105_; uint8_t v_isShared_4106_; uint8_t v_isSharedCheck_4112_; 
v_a_4103_ = lean_ctor_get(v___x_4102_, 0);
v_isSharedCheck_4112_ = !lean_is_exclusive(v___x_4102_);
if (v_isSharedCheck_4112_ == 0)
{
v___x_4105_ = v___x_4102_;
v_isShared_4106_ = v_isSharedCheck_4112_;
goto v_resetjp_4104_;
}
else
{
lean_inc(v_a_4103_);
lean_dec(v___x_4102_);
v___x_4105_ = lean_box(0);
v_isShared_4106_ = v_isSharedCheck_4112_;
goto v_resetjp_4104_;
}
v_resetjp_4104_:
{
lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4110_; 
v___x_4107_ = lean_array_fset(v_b_4095_, v_a_4096_, v_a_4103_);
v___x_4108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4108_, 0, v___x_4107_);
if (v_isShared_4106_ == 0)
{
lean_ctor_set(v___x_4105_, 0, v___x_4108_);
v___x_4110_ = v___x_4105_;
goto v_reusejp_4109_;
}
else
{
lean_object* v_reuseFailAlloc_4111_; 
v_reuseFailAlloc_4111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4111_, 0, v___x_4108_);
v___x_4110_ = v_reuseFailAlloc_4111_;
goto v_reusejp_4109_;
}
v_reusejp_4109_:
{
return v___x_4110_;
}
}
}
else
{
lean_object* v_a_4113_; lean_object* v___x_4115_; uint8_t v_isShared_4116_; uint8_t v_isSharedCheck_4120_; 
lean_dec_ref(v_b_4095_);
v_a_4113_ = lean_ctor_get(v___x_4102_, 0);
v_isSharedCheck_4120_ = !lean_is_exclusive(v___x_4102_);
if (v_isSharedCheck_4120_ == 0)
{
v___x_4115_ = v___x_4102_;
v_isShared_4116_ = v_isSharedCheck_4120_;
goto v_resetjp_4114_;
}
else
{
lean_inc(v_a_4113_);
lean_dec(v___x_4102_);
v___x_4115_ = lean_box(0);
v_isShared_4116_ = v_isSharedCheck_4120_;
goto v_resetjp_4114_;
}
v_resetjp_4114_:
{
lean_object* v___x_4118_; 
if (v_isShared_4116_ == 0)
{
v___x_4118_ = v___x_4115_;
goto v_reusejp_4117_;
}
else
{
lean_object* v_reuseFailAlloc_4119_; 
v_reuseFailAlloc_4119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4119_, 0, v_a_4113_);
v___x_4118_ = v_reuseFailAlloc_4119_;
goto v_reusejp_4117_;
}
v_reusejp_4117_:
{
return v___x_4118_;
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_4088_ = stack[0].m_obj;
lean_object* v_post_4089_ = stack[1].m_obj;
uint8_t v_usedLetOnly_4090_ = stack[2].m_num;
uint8_t v_skipConstInApp_4091_ = stack[3].m_num;
uint8_t v_skipInstances_4092_ = stack[4].m_num;
lean_object* v___x_4093_ = stack[5].m_obj;
lean_object* v___y_4094_ = stack[6].m_obj;
lean_object* v_b_4095_ = stack[7].m_obj;
lean_object* v_a_4096_ = stack[8].m_obj;
lean_object* v___y_4097_ = stack[9].m_obj;
lean_object* v___y_4098_ = stack[10].m_obj;
lean_object* v___y_4099_ = stack[11].m_obj;
lean_object* v___y_4100_ = stack[12].m_obj;
lean_object* v_res_4121_;
v_res_4121_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0(v_pre_4088_, v_post_4089_, v_usedLetOnly_4090_, v_skipConstInApp_4091_, v_skipInstances_4092_, v___x_4093_, v___y_4094_, v_b_4095_, v_a_4096_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_);
stack->m_obj
 = v_res_4121_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed(lean_object* v_pre_4122_, lean_object* v_post_4123_, lean_object* v_usedLetOnly_4124_, lean_object* v_skipConstInApp_4125_, lean_object* v_skipInstances_4126_, lean_object* v___x_4127_, lean_object* v___y_4128_, lean_object* v_b_4129_, lean_object* v_a_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_){
_start:
{
uint8_t v_usedLetOnly_boxed_4136_; uint8_t v_skipConstInApp_boxed_4137_; uint8_t v_skipInstances_boxed_4138_; lean_object* v_res_4139_; 
v_usedLetOnly_boxed_4136_ = lean_unbox(v_usedLetOnly_4124_);
v_skipConstInApp_boxed_4137_ = lean_unbox(v_skipConstInApp_4125_);
v_skipInstances_boxed_4138_ = lean_unbox(v_skipInstances_4126_);
v_res_4139_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0(v_pre_4122_, v_post_4123_, v_usedLetOnly_boxed_4136_, v_skipConstInApp_boxed_4137_, v_skipInstances_boxed_4138_, v___x_4127_, v___y_4128_, v_b_4129_, v_a_4130_, v___y_4131_, v___y_4132_, v___y_4133_, v___y_4134_);
lean_dec(v___y_4134_);
lean_dec_ref(v___y_4133_);
lean_dec(v___y_4132_);
lean_dec_ref(v___y_4131_);
lean_dec(v_a_4130_);
lean_dec(v___y_4128_);
return v_res_4139_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg(lean_object* v_upperBound_4140_, lean_object* v___x_4141_, lean_object* v_pre_4142_, lean_object* v_post_4143_, uint8_t v_usedLetOnly_4144_, uint8_t v_skipConstInApp_4145_, uint8_t v_skipInstances_4146_, lean_object* v_a_4147_, lean_object* v_b_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_){
_start:
{
lean_object* v___y_4156_; uint8_t v___x_4179_; 
v___x_4179_ = lean_nat_dec_lt(v_a_4147_, v_upperBound_4140_);
if (v___x_4179_ == 0)
{
lean_object* v___x_4180_; 
lean_dec(v_a_4147_);
lean_dec_ref(v_post_4143_);
lean_dec_ref(v_pre_4142_);
v___x_4180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4180_, 0, v_b_4148_);
return v___x_4180_;
}
else
{
lean_object* v___x_4181_; lean_object* v___x_4182_; uint8_t v___x_4183_; 
v___x_4181_ = lean_array_fget_borrowed(v_b_4148_, v_a_4147_);
v___x_4182_ = lean_array_get_size(v___x_4141_);
v___x_4183_ = lean_nat_dec_lt(v_a_4147_, v___x_4182_);
if (v___x_4183_ == 0)
{
lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___f_4187_; 
lean_inc(v___x_4181_);
v___x_4184_ = lean_box(v_usedLetOnly_4144_);
v___x_4185_ = lean_box(v_skipConstInApp_4145_);
v___x_4186_ = lean_box(v_skipInstances_4146_);
lean_inc(v_a_4147_);
lean_inc(v___y_4149_);
lean_inc_ref(v_post_4143_);
lean_inc_ref(v_pre_4142_);
v___f_4187_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_4187_, 0, v_pre_4142_);
lean_closure_set(v___f_4187_, 1, v_post_4143_);
lean_closure_set(v___f_4187_, 2, v___x_4184_);
lean_closure_set(v___f_4187_, 3, v___x_4185_);
lean_closure_set(v___f_4187_, 4, v___x_4186_);
lean_closure_set(v___f_4187_, 5, v___x_4181_);
lean_closure_set(v___f_4187_, 6, v___y_4149_);
lean_closure_set(v___f_4187_, 7, v_b_4148_);
lean_closure_set(v___f_4187_, 8, v_a_4147_);
v___y_4156_ = v___f_4187_;
goto v___jp_4155_;
}
else
{
lean_object* v___x_4188_; uint8_t v_isInstance_4189_; 
v___x_4188_ = lean_array_fget_borrowed(v___x_4141_, v_a_4147_);
v_isInstance_4189_ = lean_ctor_get_uint8(v___x_4188_, sizeof(void*)*1 + 4);
if (v_isInstance_4189_ == 0)
{
lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___f_4193_; 
lean_inc(v___x_4181_);
v___x_4190_ = lean_box(v_usedLetOnly_4144_);
v___x_4191_ = lean_box(v_skipConstInApp_4145_);
v___x_4192_ = lean_box(v_skipInstances_4146_);
lean_inc(v_a_4147_);
lean_inc(v___y_4149_);
lean_inc_ref(v_post_4143_);
lean_inc_ref(v_pre_4142_);
v___f_4193_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_4193_, 0, v_pre_4142_);
lean_closure_set(v___f_4193_, 1, v_post_4143_);
lean_closure_set(v___f_4193_, 2, v___x_4190_);
lean_closure_set(v___f_4193_, 3, v___x_4191_);
lean_closure_set(v___f_4193_, 4, v___x_4192_);
lean_closure_set(v___f_4193_, 5, v___x_4181_);
lean_closure_set(v___f_4193_, 6, v___y_4149_);
lean_closure_set(v___f_4193_, 7, v_b_4148_);
lean_closure_set(v___f_4193_, 8, v_a_4147_);
v___y_4156_ = v___f_4193_;
goto v___jp_4155_;
}
else
{
lean_object* v___x_4194_; lean_object* v___f_4195_; 
v___x_4194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4194_, 0, v_b_4148_);
v___f_4195_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_4195_, 0, v___x_4194_);
v___y_4156_ = v___f_4195_;
goto v___jp_4155_;
}
}
}
v___jp_4155_:
{
lean_object* v___x_4157_; 
lean_inc(v___y_4153_);
lean_inc_ref(v___y_4152_);
lean_inc(v___y_4151_);
lean_inc_ref(v___y_4150_);
v___x_4157_ = lean_apply_5(v___y_4156_, v___y_4150_, v___y_4151_, v___y_4152_, v___y_4153_, lean_box(0));
if (lean_obj_tag(v___x_4157_) == 0)
{
lean_object* v_a_4158_; lean_object* v___x_4160_; uint8_t v_isShared_4161_; uint8_t v_isSharedCheck_4170_; 
v_a_4158_ = lean_ctor_get(v___x_4157_, 0);
v_isSharedCheck_4170_ = !lean_is_exclusive(v___x_4157_);
if (v_isSharedCheck_4170_ == 0)
{
v___x_4160_ = v___x_4157_;
v_isShared_4161_ = v_isSharedCheck_4170_;
goto v_resetjp_4159_;
}
else
{
lean_inc(v_a_4158_);
lean_dec(v___x_4157_);
v___x_4160_ = lean_box(0);
v_isShared_4161_ = v_isSharedCheck_4170_;
goto v_resetjp_4159_;
}
v_resetjp_4159_:
{
if (lean_obj_tag(v_a_4158_) == 0)
{
lean_object* v_a_4162_; lean_object* v___x_4164_; 
lean_dec(v_a_4147_);
lean_dec_ref(v_post_4143_);
lean_dec_ref(v_pre_4142_);
v_a_4162_ = lean_ctor_get(v_a_4158_, 0);
lean_inc(v_a_4162_);
lean_dec_ref_known(v_a_4158_, 1);
if (v_isShared_4161_ == 0)
{
lean_ctor_set(v___x_4160_, 0, v_a_4162_);
v___x_4164_ = v___x_4160_;
goto v_reusejp_4163_;
}
else
{
lean_object* v_reuseFailAlloc_4165_; 
v_reuseFailAlloc_4165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4165_, 0, v_a_4162_);
v___x_4164_ = v_reuseFailAlloc_4165_;
goto v_reusejp_4163_;
}
v_reusejp_4163_:
{
return v___x_4164_;
}
}
else
{
lean_object* v_a_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; 
lean_del_object(v___x_4160_);
v_a_4166_ = lean_ctor_get(v_a_4158_, 0);
lean_inc(v_a_4166_);
lean_dec_ref_known(v_a_4158_, 1);
v___x_4167_ = lean_unsigned_to_nat(1u);
v___x_4168_ = lean_nat_add(v_a_4147_, v___x_4167_);
lean_dec(v_a_4147_);
v_a_4147_ = v___x_4168_;
v_b_4148_ = v_a_4166_;
goto _start;
}
}
}
else
{
lean_object* v_a_4171_; lean_object* v___x_4173_; uint8_t v_isShared_4174_; uint8_t v_isSharedCheck_4178_; 
lean_dec(v_a_4147_);
lean_dec_ref(v_post_4143_);
lean_dec_ref(v_pre_4142_);
v_a_4171_ = lean_ctor_get(v___x_4157_, 0);
v_isSharedCheck_4178_ = !lean_is_exclusive(v___x_4157_);
if (v_isSharedCheck_4178_ == 0)
{
v___x_4173_ = v___x_4157_;
v_isShared_4174_ = v_isSharedCheck_4178_;
goto v_resetjp_4172_;
}
else
{
lean_inc(v_a_4171_);
lean_dec(v___x_4157_);
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
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_4140_ = stack[0].m_obj;
lean_object* v___x_4141_ = stack[1].m_obj;
lean_object* v_pre_4142_ = stack[2].m_obj;
lean_object* v_post_4143_ = stack[3].m_obj;
uint8_t v_usedLetOnly_4144_ = stack[4].m_num;
uint8_t v_skipConstInApp_4145_ = stack[5].m_num;
uint8_t v_skipInstances_4146_ = stack[6].m_num;
lean_object* v_a_4147_ = stack[7].m_obj;
lean_object* v_b_4148_ = stack[8].m_obj;
lean_object* v___y_4149_ = stack[9].m_obj;
lean_object* v___y_4150_ = stack[10].m_obj;
lean_object* v___y_4151_ = stack[11].m_obj;
lean_object* v___y_4152_ = stack[12].m_obj;
lean_object* v___y_4153_ = stack[13].m_obj;
lean_object* v_res_4196_;
v_res_4196_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg(v_upperBound_4140_, v___x_4141_, v_pre_4142_, v_post_4143_, v_usedLetOnly_4144_, v_skipConstInApp_4145_, v_skipInstances_4146_, v_a_4147_, v_b_4148_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_, v___y_4153_);
stack->m_obj
 = v_res_4196_;
}
lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__8(uint8_t v_skipInstances_4197_, lean_object* v_pre_4198_, lean_object* v_post_4199_, uint8_t v_usedLetOnly_4200_, uint8_t v_skipConstInApp_4201_, lean_object* v_x_4202_, lean_object* v_x_4203_, lean_object* v_x_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_){
_start:
{
lean_object* v_f_4212_; lean_object* v___y_4213_; lean_object* v___y_4214_; lean_object* v___y_4215_; lean_object* v___y_4216_; lean_object* v___y_4217_; 
if (lean_obj_tag(v_x_4202_) == 5)
{
lean_object* v_fn_4260_; lean_object* v_arg_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; 
v_fn_4260_ = lean_ctor_get(v_x_4202_, 0);
lean_inc_ref(v_fn_4260_);
v_arg_4261_ = lean_ctor_get(v_x_4202_, 1);
lean_inc_ref(v_arg_4261_);
lean_dec_ref_known(v_x_4202_, 2);
v___x_4262_ = lean_array_set(v_x_4203_, v_x_4204_, v_arg_4261_);
v___x_4263_ = lean_unsigned_to_nat(1u);
v___x_4264_ = lean_nat_sub(v_x_4204_, v___x_4263_);
lean_dec(v_x_4204_);
v_x_4202_ = v_fn_4260_;
v_x_4203_ = v___x_4262_;
v_x_4204_ = v___x_4264_;
goto _start;
}
else
{
lean_dec(v_x_4204_);
if (v_skipConstInApp_4201_ == 0)
{
goto v___jp_4257_;
}
else
{
uint8_t v___x_4266_; 
v___x_4266_ = l_Lean_Expr_isConst(v_x_4202_);
if (v___x_4266_ == 0)
{
goto v___jp_4257_;
}
else
{
v_f_4212_ = v_x_4202_;
v___y_4213_ = v___y_4205_;
v___y_4214_ = v___y_4206_;
v___y_4215_ = v___y_4207_;
v___y_4216_ = v___y_4208_;
v___y_4217_ = v___y_4209_;
goto v___jp_4211_;
}
}
}
v___jp_4211_:
{
if (v_skipInstances_4197_ == 0)
{
size_t v_sz_4218_; size_t v___x_4219_; lean_object* v___x_4220_; 
v_sz_4218_ = lean_array_size(v_x_4203_);
v___x_4219_ = ((size_t)0ULL);
lean_inc_ref(v_post_4199_);
lean_inc_ref(v_pre_4198_);
v___x_4220_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__2(v_pre_4198_, v_post_4199_, v_usedLetOnly_4200_, v_skipConstInApp_4201_, v_skipInstances_4197_, v_sz_4218_, v___x_4219_, v_x_4203_, v___y_4213_, v___y_4214_, v___y_4215_, v___y_4216_, v___y_4217_);
if (lean_obj_tag(v___x_4220_) == 0)
{
lean_object* v_a_4221_; lean_object* v___x_4222_; lean_object* v___x_4223_; 
v_a_4221_ = lean_ctor_get(v___x_4220_, 0);
lean_inc(v_a_4221_);
lean_dec_ref_known(v___x_4220_, 1);
v___x_4222_ = l_Lean_mkAppN(v_f_4212_, v_a_4221_);
lean_dec(v_a_4221_);
v___x_4223_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4198_, v_post_4199_, v_usedLetOnly_4200_, v_skipConstInApp_4201_, v_skipInstances_4197_, v___x_4222_, v___y_4213_, v___y_4214_, v___y_4215_, v___y_4216_, v___y_4217_);
return v___x_4223_;
}
else
{
lean_object* v_a_4224_; lean_object* v___x_4226_; uint8_t v_isShared_4227_; uint8_t v_isSharedCheck_4231_; 
lean_dec_ref(v_f_4212_);
lean_dec_ref(v_post_4199_);
lean_dec_ref(v_pre_4198_);
v_a_4224_ = lean_ctor_get(v___x_4220_, 0);
v_isSharedCheck_4231_ = !lean_is_exclusive(v___x_4220_);
if (v_isSharedCheck_4231_ == 0)
{
v___x_4226_ = v___x_4220_;
v_isShared_4227_ = v_isSharedCheck_4231_;
goto v_resetjp_4225_;
}
else
{
lean_inc(v_a_4224_);
lean_dec(v___x_4220_);
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
lean_object* v___x_4232_; lean_object* v___x_4233_; 
v___x_4232_ = lean_array_get_size(v_x_4203_);
lean_inc_ref(v_f_4212_);
v___x_4233_ = l_Lean_Meta_getFunInfoNArgs(v_f_4212_, v___x_4232_, v___y_4214_, v___y_4215_, v___y_4216_, v___y_4217_);
if (lean_obj_tag(v___x_4233_) == 0)
{
lean_object* v_a_4234_; lean_object* v_paramInfo_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; 
v_a_4234_ = lean_ctor_get(v___x_4233_, 0);
lean_inc(v_a_4234_);
lean_dec_ref_known(v___x_4233_, 1);
v_paramInfo_4235_ = lean_ctor_get(v_a_4234_, 0);
lean_inc_ref(v_paramInfo_4235_);
lean_dec(v_a_4234_);
v___x_4236_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_4199_);
lean_inc_ref(v_pre_4198_);
v___x_4237_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg(v___x_4232_, v_paramInfo_4235_, v_pre_4198_, v_post_4199_, v_usedLetOnly_4200_, v_skipConstInApp_4201_, v_skipInstances_4197_, v___x_4236_, v_x_4203_, v___y_4213_, v___y_4214_, v___y_4215_, v___y_4216_, v___y_4217_);
lean_dec_ref(v_paramInfo_4235_);
if (lean_obj_tag(v___x_4237_) == 0)
{
lean_object* v_a_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; 
v_a_4238_ = lean_ctor_get(v___x_4237_, 0);
lean_inc(v_a_4238_);
lean_dec_ref_known(v___x_4237_, 1);
v___x_4239_ = l_Lean_mkAppN(v_f_4212_, v_a_4238_);
lean_dec(v_a_4238_);
v___x_4240_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4198_, v_post_4199_, v_usedLetOnly_4200_, v_skipConstInApp_4201_, v_skipInstances_4197_, v___x_4239_, v___y_4213_, v___y_4214_, v___y_4215_, v___y_4216_, v___y_4217_);
return v___x_4240_;
}
else
{
lean_object* v_a_4241_; lean_object* v___x_4243_; uint8_t v_isShared_4244_; uint8_t v_isSharedCheck_4248_; 
lean_dec_ref(v_f_4212_);
lean_dec_ref(v_post_4199_);
lean_dec_ref(v_pre_4198_);
v_a_4241_ = lean_ctor_get(v___x_4237_, 0);
v_isSharedCheck_4248_ = !lean_is_exclusive(v___x_4237_);
if (v_isSharedCheck_4248_ == 0)
{
v___x_4243_ = v___x_4237_;
v_isShared_4244_ = v_isSharedCheck_4248_;
goto v_resetjp_4242_;
}
else
{
lean_inc(v_a_4241_);
lean_dec(v___x_4237_);
v___x_4243_ = lean_box(0);
v_isShared_4244_ = v_isSharedCheck_4248_;
goto v_resetjp_4242_;
}
v_resetjp_4242_:
{
lean_object* v___x_4246_; 
if (v_isShared_4244_ == 0)
{
v___x_4246_ = v___x_4243_;
goto v_reusejp_4245_;
}
else
{
lean_object* v_reuseFailAlloc_4247_; 
v_reuseFailAlloc_4247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4247_, 0, v_a_4241_);
v___x_4246_ = v_reuseFailAlloc_4247_;
goto v_reusejp_4245_;
}
v_reusejp_4245_:
{
return v___x_4246_;
}
}
}
}
else
{
lean_object* v_a_4249_; lean_object* v___x_4251_; uint8_t v_isShared_4252_; uint8_t v_isSharedCheck_4256_; 
lean_dec_ref(v_f_4212_);
lean_dec_ref(v_x_4203_);
lean_dec_ref(v_post_4199_);
lean_dec_ref(v_pre_4198_);
v_a_4249_ = lean_ctor_get(v___x_4233_, 0);
v_isSharedCheck_4256_ = !lean_is_exclusive(v___x_4233_);
if (v_isSharedCheck_4256_ == 0)
{
v___x_4251_ = v___x_4233_;
v_isShared_4252_ = v_isSharedCheck_4256_;
goto v_resetjp_4250_;
}
else
{
lean_inc(v_a_4249_);
lean_dec(v___x_4233_);
v___x_4251_ = lean_box(0);
v_isShared_4252_ = v_isSharedCheck_4256_;
goto v_resetjp_4250_;
}
v_resetjp_4250_:
{
lean_object* v___x_4254_; 
if (v_isShared_4252_ == 0)
{
v___x_4254_ = v___x_4251_;
goto v_reusejp_4253_;
}
else
{
lean_object* v_reuseFailAlloc_4255_; 
v_reuseFailAlloc_4255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4255_, 0, v_a_4249_);
v___x_4254_ = v_reuseFailAlloc_4255_;
goto v_reusejp_4253_;
}
v_reusejp_4253_:
{
return v___x_4254_;
}
}
}
}
}
v___jp_4257_:
{
lean_object* v___x_4258_; 
lean_inc_ref(v_post_4199_);
lean_inc_ref(v_pre_4198_);
v___x_4258_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4198_, v_post_4199_, v_usedLetOnly_4200_, v_skipConstInApp_4201_, v_skipInstances_4197_, v_x_4202_, v___y_4205_, v___y_4206_, v___y_4207_, v___y_4208_, v___y_4209_);
if (lean_obj_tag(v___x_4258_) == 0)
{
lean_object* v_a_4259_; 
v_a_4259_ = lean_ctor_get(v___x_4258_, 0);
lean_inc(v_a_4259_);
lean_dec_ref_known(v___x_4258_, 1);
v_f_4212_ = v_a_4259_;
v___y_4213_ = v___y_4205_;
v___y_4214_ = v___y_4206_;
v___y_4215_ = v___y_4207_;
v___y_4216_ = v___y_4208_;
v___y_4217_ = v___y_4209_;
goto v___jp_4211_;
}
else
{
lean_dec_ref(v_x_4203_);
lean_dec_ref(v_post_4199_);
lean_dec_ref(v_pre_4198_);
return v___x_4258_;
}
}
}
}
LEAN_EXPORT void l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__8_0interp(lean_interpreter_value* stack)
{
uint8_t v_skipInstances_4197_ = stack[0].m_num;
lean_object* v_pre_4198_ = stack[1].m_obj;
lean_object* v_post_4199_ = stack[2].m_obj;
uint8_t v_usedLetOnly_4200_ = stack[3].m_num;
uint8_t v_skipConstInApp_4201_ = stack[4].m_num;
lean_object* v_x_4202_ = stack[5].m_obj;
lean_object* v_x_4203_ = stack[6].m_obj;
lean_object* v_x_4204_ = stack[7].m_obj;
lean_object* v___y_4205_ = stack[8].m_obj;
lean_object* v___y_4206_ = stack[9].m_obj;
lean_object* v___y_4207_ = stack[10].m_obj;
lean_object* v___y_4208_ = stack[11].m_obj;
lean_object* v___y_4209_ = stack[12].m_obj;
lean_object* v_res_4267_;
v_res_4267_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__8(v_skipInstances_4197_, v_pre_4198_, v_post_4199_, v_usedLetOnly_4200_, v_skipConstInApp_4201_, v_x_4202_, v_x_4203_, v_x_4204_, v___y_4205_, v___y_4206_, v___y_4207_, v___y_4208_, v___y_4209_);
stack->m_obj
 = v_res_4267_;
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1(lean_object* v___x_4268_, lean_object* v_pre_4269_, lean_object* v_e_4270_, lean_object* v_post_4271_, uint8_t v_usedLetOnly_4272_, uint8_t v_skipConstInApp_4273_, uint8_t v_skipInstances_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_, lean_object* v___y_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_){
_start:
{
lean_object* v___x_4281_; 
v___x_4281_ = l_Lean_Core_checkSystem(v___x_4268_, v___y_4278_, v___y_4279_);
if (lean_obj_tag(v___x_4281_) == 0)
{
lean_object* v___x_4282_; 
lean_dec_ref_known(v___x_4281_, 1);
lean_inc_ref(v_pre_4269_);
lean_inc(v___y_4279_);
lean_inc_ref(v___y_4278_);
lean_inc(v___y_4277_);
lean_inc_ref(v___y_4276_);
lean_inc_ref(v_e_4270_);
v___x_4282_ = lean_apply_6(v_pre_4269_, v_e_4270_, v___y_4276_, v___y_4277_, v___y_4278_, v___y_4279_, lean_box(0));
if (lean_obj_tag(v___x_4282_) == 0)
{
lean_object* v_a_4283_; lean_object* v___x_4285_; uint8_t v_isShared_4286_; uint8_t v_isSharedCheck_4331_; 
v_a_4283_ = lean_ctor_get(v___x_4282_, 0);
v_isSharedCheck_4331_ = !lean_is_exclusive(v___x_4282_);
if (v_isSharedCheck_4331_ == 0)
{
v___x_4285_ = v___x_4282_;
v_isShared_4286_ = v_isSharedCheck_4331_;
goto v_resetjp_4284_;
}
else
{
lean_inc(v_a_4283_);
lean_dec(v___x_4282_);
v___x_4285_ = lean_box(0);
v_isShared_4286_ = v_isSharedCheck_4331_;
goto v_resetjp_4284_;
}
v_resetjp_4284_:
{
lean_object* v___y_4288_; 
switch(lean_obj_tag(v_a_4283_))
{
case 0:
{
lean_object* v_e_4323_; lean_object* v___x_4325_; 
lean_dec_ref(v_post_4271_);
lean_dec_ref(v_e_4270_);
lean_dec_ref(v_pre_4269_);
v_e_4323_ = lean_ctor_get(v_a_4283_, 0);
lean_inc_ref(v_e_4323_);
lean_dec_ref_known(v_a_4283_, 1);
if (v_isShared_4286_ == 0)
{
lean_ctor_set(v___x_4285_, 0, v_e_4323_);
v___x_4325_ = v___x_4285_;
goto v_reusejp_4324_;
}
else
{
lean_object* v_reuseFailAlloc_4326_; 
v_reuseFailAlloc_4326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4326_, 0, v_e_4323_);
v___x_4325_ = v_reuseFailAlloc_4326_;
goto v_reusejp_4324_;
}
v_reusejp_4324_:
{
return v___x_4325_;
}
}
case 1:
{
lean_object* v_e_4327_; lean_object* v___x_4328_; 
lean_del_object(v___x_4285_);
lean_dec_ref(v_e_4270_);
v_e_4327_ = lean_ctor_get(v_a_4283_, 0);
lean_inc_ref(v_e_4327_);
lean_dec_ref_known(v_a_4283_, 1);
v___x_4328_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4269_, v_post_4271_, v_usedLetOnly_4272_, v_skipConstInApp_4273_, v_skipInstances_4274_, v_e_4327_, v___y_4275_, v___y_4276_, v___y_4277_, v___y_4278_, v___y_4279_);
return v___x_4328_;
}
default: 
{
lean_object* v_e_x3f_4329_; 
lean_del_object(v___x_4285_);
v_e_x3f_4329_ = lean_ctor_get(v_a_4283_, 0);
lean_inc(v_e_x3f_4329_);
lean_dec_ref_known(v_a_4283_, 1);
if (lean_obj_tag(v_e_x3f_4329_) == 0)
{
v___y_4288_ = v_e_4270_;
goto v___jp_4287_;
}
else
{
lean_object* v_val_4330_; 
lean_dec_ref(v_e_4270_);
v_val_4330_ = lean_ctor_get(v_e_x3f_4329_, 0);
lean_inc(v_val_4330_);
lean_dec_ref_known(v_e_x3f_4329_, 1);
v___y_4288_ = v_val_4330_;
goto v___jp_4287_;
}
}
}
v___jp_4287_:
{
switch(lean_obj_tag(v___y_4288_))
{
case 7:
{
lean_object* v___x_4289_; lean_object* v___x_4290_; 
v___x_4289_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_4290_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5(v_pre_4269_, v_post_4271_, v_usedLetOnly_4272_, v_skipConstInApp_4273_, v_skipInstances_4274_, v___x_4289_, v___y_4288_, v___y_4275_, v___y_4276_, v___y_4277_, v___y_4278_, v___y_4279_);
return v___x_4290_;
}
case 6:
{
lean_object* v___x_4291_; lean_object* v___x_4292_; 
v___x_4291_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_4292_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6(v_pre_4269_, v_post_4271_, v_usedLetOnly_4272_, v_skipConstInApp_4273_, v_skipInstances_4274_, v___x_4291_, v___y_4288_, v___y_4275_, v___y_4276_, v___y_4277_, v___y_4278_, v___y_4279_);
return v___x_4292_;
}
case 8:
{
lean_object* v___x_4293_; lean_object* v___x_4294_; 
v___x_4293_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_4294_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7(v_pre_4269_, v_post_4271_, v_usedLetOnly_4272_, v_skipConstInApp_4273_, v_skipInstances_4274_, v___x_4293_, v___y_4288_, v___y_4275_, v___y_4276_, v___y_4277_, v___y_4278_, v___y_4279_);
return v___x_4294_;
}
case 5:
{
lean_object* v_dummy_4295_; lean_object* v_nargs_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; 
v_dummy_4295_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_4296_ = l_Lean_Expr_getAppNumArgs(v___y_4288_);
lean_inc(v_nargs_4296_);
v___x_4297_ = lean_mk_array(v_nargs_4296_, v_dummy_4295_);
v___x_4298_ = lean_unsigned_to_nat(1u);
v___x_4299_ = lean_nat_sub(v_nargs_4296_, v___x_4298_);
lean_dec(v_nargs_4296_);
v___x_4300_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__8(v_skipInstances_4274_, v_pre_4269_, v_post_4271_, v_usedLetOnly_4272_, v_skipConstInApp_4273_, v___y_4288_, v___x_4297_, v___x_4299_, v___y_4275_, v___y_4276_, v___y_4277_, v___y_4278_, v___y_4279_);
return v___x_4300_;
}
case 10:
{
lean_object* v_data_4301_; lean_object* v_expr_4302_; lean_object* v___x_4303_; 
v_data_4301_ = lean_ctor_get(v___y_4288_, 0);
v_expr_4302_ = lean_ctor_get(v___y_4288_, 1);
lean_inc_ref(v_expr_4302_);
lean_inc_ref(v_post_4271_);
lean_inc_ref(v_pre_4269_);
v___x_4303_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4269_, v_post_4271_, v_usedLetOnly_4272_, v_skipConstInApp_4273_, v_skipInstances_4274_, v_expr_4302_, v___y_4275_, v___y_4276_, v___y_4277_, v___y_4278_, v___y_4279_);
if (lean_obj_tag(v___x_4303_) == 0)
{
lean_object* v_a_4304_; size_t v___x_4305_; size_t v___x_4306_; uint8_t v___x_4307_; 
v_a_4304_ = lean_ctor_get(v___x_4303_, 0);
lean_inc(v_a_4304_);
lean_dec_ref_known(v___x_4303_, 1);
v___x_4305_ = lean_ptr_addr(v_expr_4302_);
v___x_4306_ = lean_ptr_addr(v_a_4304_);
v___x_4307_ = lean_usize_dec_eq(v___x_4305_, v___x_4306_);
if (v___x_4307_ == 0)
{
lean_object* v___x_4308_; lean_object* v___x_4309_; 
lean_inc(v_data_4301_);
lean_dec_ref_known(v___y_4288_, 2);
v___x_4308_ = l_Lean_Expr_mdata___override(v_data_4301_, v_a_4304_);
v___x_4309_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4269_, v_post_4271_, v_usedLetOnly_4272_, v_skipConstInApp_4273_, v_skipInstances_4274_, v___x_4308_, v___y_4275_, v___y_4276_, v___y_4277_, v___y_4278_, v___y_4279_);
return v___x_4309_;
}
else
{
lean_object* v___x_4310_; 
lean_dec(v_a_4304_);
v___x_4310_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4269_, v_post_4271_, v_usedLetOnly_4272_, v_skipConstInApp_4273_, v_skipInstances_4274_, v___y_4288_, v___y_4275_, v___y_4276_, v___y_4277_, v___y_4278_, v___y_4279_);
return v___x_4310_;
}
}
else
{
lean_dec_ref_known(v___y_4288_, 2);
lean_dec_ref(v_post_4271_);
lean_dec_ref(v_pre_4269_);
return v___x_4303_;
}
}
case 11:
{
lean_object* v_typeName_4311_; lean_object* v_idx_4312_; lean_object* v_struct_4313_; lean_object* v___x_4314_; 
v_typeName_4311_ = lean_ctor_get(v___y_4288_, 0);
v_idx_4312_ = lean_ctor_get(v___y_4288_, 1);
v_struct_4313_ = lean_ctor_get(v___y_4288_, 2);
lean_inc_ref(v_struct_4313_);
lean_inc_ref(v_post_4271_);
lean_inc_ref(v_pre_4269_);
v___x_4314_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4269_, v_post_4271_, v_usedLetOnly_4272_, v_skipConstInApp_4273_, v_skipInstances_4274_, v_struct_4313_, v___y_4275_, v___y_4276_, v___y_4277_, v___y_4278_, v___y_4279_);
if (lean_obj_tag(v___x_4314_) == 0)
{
lean_object* v_a_4315_; size_t v___x_4316_; size_t v___x_4317_; uint8_t v___x_4318_; 
v_a_4315_ = lean_ctor_get(v___x_4314_, 0);
lean_inc(v_a_4315_);
lean_dec_ref_known(v___x_4314_, 1);
v___x_4316_ = lean_ptr_addr(v_struct_4313_);
v___x_4317_ = lean_ptr_addr(v_a_4315_);
v___x_4318_ = lean_usize_dec_eq(v___x_4316_, v___x_4317_);
if (v___x_4318_ == 0)
{
lean_object* v___x_4319_; lean_object* v___x_4320_; 
lean_inc(v_idx_4312_);
lean_inc(v_typeName_4311_);
lean_dec_ref_known(v___y_4288_, 3);
v___x_4319_ = l_Lean_Expr_proj___override(v_typeName_4311_, v_idx_4312_, v_a_4315_);
v___x_4320_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4269_, v_post_4271_, v_usedLetOnly_4272_, v_skipConstInApp_4273_, v_skipInstances_4274_, v___x_4319_, v___y_4275_, v___y_4276_, v___y_4277_, v___y_4278_, v___y_4279_);
return v___x_4320_;
}
else
{
lean_object* v___x_4321_; 
lean_dec(v_a_4315_);
v___x_4321_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4269_, v_post_4271_, v_usedLetOnly_4272_, v_skipConstInApp_4273_, v_skipInstances_4274_, v___y_4288_, v___y_4275_, v___y_4276_, v___y_4277_, v___y_4278_, v___y_4279_);
return v___x_4321_;
}
}
else
{
lean_dec_ref_known(v___y_4288_, 3);
lean_dec_ref(v_post_4271_);
lean_dec_ref(v_pre_4269_);
return v___x_4314_;
}
}
default: 
{
lean_object* v___x_4322_; 
v___x_4322_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4269_, v_post_4271_, v_usedLetOnly_4272_, v_skipConstInApp_4273_, v_skipInstances_4274_, v___y_4288_, v___y_4275_, v___y_4276_, v___y_4277_, v___y_4278_, v___y_4279_);
return v___x_4322_;
}
}
}
}
}
else
{
lean_object* v_a_4332_; lean_object* v___x_4334_; uint8_t v_isShared_4335_; uint8_t v_isSharedCheck_4339_; 
lean_dec_ref(v_post_4271_);
lean_dec_ref(v_e_4270_);
lean_dec_ref(v_pre_4269_);
v_a_4332_ = lean_ctor_get(v___x_4282_, 0);
v_isSharedCheck_4339_ = !lean_is_exclusive(v___x_4282_);
if (v_isSharedCheck_4339_ == 0)
{
v___x_4334_ = v___x_4282_;
v_isShared_4335_ = v_isSharedCheck_4339_;
goto v_resetjp_4333_;
}
else
{
lean_inc(v_a_4332_);
lean_dec(v___x_4282_);
v___x_4334_ = lean_box(0);
v_isShared_4335_ = v_isSharedCheck_4339_;
goto v_resetjp_4333_;
}
v_resetjp_4333_:
{
lean_object* v___x_4337_; 
if (v_isShared_4335_ == 0)
{
v___x_4337_ = v___x_4334_;
goto v_reusejp_4336_;
}
else
{
lean_object* v_reuseFailAlloc_4338_; 
v_reuseFailAlloc_4338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4338_, 0, v_a_4332_);
v___x_4337_ = v_reuseFailAlloc_4338_;
goto v_reusejp_4336_;
}
v_reusejp_4336_:
{
return v___x_4337_;
}
}
}
}
else
{
lean_object* v_a_4340_; lean_object* v___x_4342_; uint8_t v_isShared_4343_; uint8_t v_isSharedCheck_4347_; 
lean_dec_ref(v_post_4271_);
lean_dec_ref(v_e_4270_);
lean_dec_ref(v_pre_4269_);
v_a_4340_ = lean_ctor_get(v___x_4281_, 0);
v_isSharedCheck_4347_ = !lean_is_exclusive(v___x_4281_);
if (v_isSharedCheck_4347_ == 0)
{
v___x_4342_ = v___x_4281_;
v_isShared_4343_ = v_isSharedCheck_4347_;
goto v_resetjp_4341_;
}
else
{
lean_inc(v_a_4340_);
lean_dec(v___x_4281_);
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
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_4268_ = stack[0].m_obj;
lean_object* v_pre_4269_ = stack[1].m_obj;
lean_object* v_e_4270_ = stack[2].m_obj;
lean_object* v_post_4271_ = stack[3].m_obj;
uint8_t v_usedLetOnly_4272_ = stack[4].m_num;
uint8_t v_skipConstInApp_4273_ = stack[5].m_num;
uint8_t v_skipInstances_4274_ = stack[6].m_num;
lean_object* v___y_4275_ = stack[7].m_obj;
lean_object* v___y_4276_ = stack[8].m_obj;
lean_object* v___y_4277_ = stack[9].m_obj;
lean_object* v___y_4278_ = stack[10].m_obj;
lean_object* v___y_4279_ = stack[11].m_obj;
lean_object* v_res_4348_;
v_res_4348_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1(v___x_4268_, v_pre_4269_, v_e_4270_, v_post_4271_, v_usedLetOnly_4272_, v_skipConstInApp_4273_, v_skipInstances_4274_, v___y_4275_, v___y_4276_, v___y_4277_, v___y_4278_, v___y_4279_);
stack->m_obj
 = v_res_4348_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1___boxed(lean_object* v___x_4349_, lean_object* v_pre_4350_, lean_object* v_e_4351_, lean_object* v_post_4352_, lean_object* v_usedLetOnly_4353_, lean_object* v_skipConstInApp_4354_, lean_object* v_skipInstances_4355_, lean_object* v___y_4356_, lean_object* v___y_4357_, lean_object* v___y_4358_, lean_object* v___y_4359_, lean_object* v___y_4360_, lean_object* v___y_4361_){
_start:
{
uint8_t v_usedLetOnly_boxed_4362_; uint8_t v_skipConstInApp_boxed_4363_; uint8_t v_skipInstances_boxed_4364_; lean_object* v_res_4365_; 
v_usedLetOnly_boxed_4362_ = lean_unbox(v_usedLetOnly_4353_);
v_skipConstInApp_boxed_4363_ = lean_unbox(v_skipConstInApp_4354_);
v_skipInstances_boxed_4364_ = lean_unbox(v_skipInstances_4355_);
v_res_4365_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1(v___x_4349_, v_pre_4350_, v_e_4351_, v_post_4352_, v_usedLetOnly_boxed_4362_, v_skipConstInApp_boxed_4363_, v_skipInstances_boxed_4364_, v___y_4356_, v___y_4357_, v___y_4358_, v___y_4359_, v___y_4360_);
lean_dec(v___y_4360_);
lean_dec_ref(v___y_4359_);
lean_dec(v___y_4358_);
lean_dec_ref(v___y_4357_);
lean_dec(v___y_4356_);
return v_res_4365_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(lean_object* v_pre_4366_, lean_object* v_post_4367_, uint8_t v_usedLetOnly_4368_, uint8_t v_skipConstInApp_4369_, uint8_t v_skipInstances_4370_, lean_object* v_e_4371_, lean_object* v_a_4372_, lean_object* v___y_4373_, lean_object* v___y_4374_, lean_object* v___y_4375_, lean_object* v___y_4376_){
_start:
{
lean_object* v___x_4378_; lean_object* v___x_4379_; 
lean_inc(v_a_4372_);
v___x_4378_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_4378_, 0, lean_box(0));
lean_closure_set(v___x_4378_, 1, lean_box(0));
lean_closure_set(v___x_4378_, 2, v_a_4372_);
v___x_4379_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0(lean_box(0), v___x_4378_, v___y_4373_, v___y_4374_, v___y_4375_, v___y_4376_);
if (lean_obj_tag(v___x_4379_) == 0)
{
lean_object* v_a_4380_; lean_object* v___x_4382_; uint8_t v_isShared_4383_; uint8_t v_isSharedCheck_4414_; 
v_a_4380_ = lean_ctor_get(v___x_4379_, 0);
v_isSharedCheck_4414_ = !lean_is_exclusive(v___x_4379_);
if (v_isSharedCheck_4414_ == 0)
{
v___x_4382_ = v___x_4379_;
v_isShared_4383_ = v_isSharedCheck_4414_;
goto v_resetjp_4381_;
}
else
{
lean_inc(v_a_4380_);
lean_dec(v___x_4379_);
v___x_4382_ = lean_box(0);
v_isShared_4383_ = v_isSharedCheck_4414_;
goto v_resetjp_4381_;
}
v_resetjp_4381_:
{
lean_object* v___x_4384_; 
v___x_4384_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___redArg(v_a_4380_, v_e_4371_);
lean_dec(v_a_4380_);
if (lean_obj_tag(v___x_4384_) == 0)
{
lean_object* v___x_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; lean_object* v___f_4389_; lean_object* v___x_4390_; 
lean_del_object(v___x_4382_);
v___x_4385_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__19___closed__0));
v___x_4386_ = lean_box(v_usedLetOnly_4368_);
v___x_4387_ = lean_box(v_skipConstInApp_4369_);
v___x_4388_ = lean_box(v_skipInstances_4370_);
lean_inc_ref(v_e_4371_);
v___f_4389_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1___boxed), 13, 7);
lean_closure_set(v___f_4389_, 0, v___x_4385_);
lean_closure_set(v___f_4389_, 1, v_pre_4366_);
lean_closure_set(v___f_4389_, 2, v_e_4371_);
lean_closure_set(v___f_4389_, 3, v_post_4367_);
lean_closure_set(v___f_4389_, 4, v___x_4386_);
lean_closure_set(v___f_4389_, 5, v___x_4387_);
lean_closure_set(v___f_4389_, 6, v___x_4388_);
v___x_4390_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg(v___f_4389_, v_a_4372_, v___y_4373_, v___y_4374_, v___y_4375_, v___y_4376_);
if (lean_obj_tag(v___x_4390_) == 0)
{
lean_object* v_a_4391_; lean_object* v___f_4392_; lean_object* v___x_4393_; 
v_a_4391_ = lean_ctor_get(v___x_4390_, 0);
lean_inc_n(v_a_4391_, 2);
lean_dec_ref_known(v___x_4390_, 1);
lean_inc(v_a_4372_);
v___f_4392_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_4392_, 0, v_a_4372_);
lean_closure_set(v___f_4392_, 1, v_e_4371_);
lean_closure_set(v___f_4392_, 2, v_a_4391_);
v___x_4393_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0(lean_box(0), v___f_4392_, v___y_4373_, v___y_4374_, v___y_4375_, v___y_4376_);
if (lean_obj_tag(v___x_4393_) == 0)
{
lean_object* v___x_4395_; uint8_t v_isShared_4396_; uint8_t v_isSharedCheck_4400_; 
v_isSharedCheck_4400_ = !lean_is_exclusive(v___x_4393_);
if (v_isSharedCheck_4400_ == 0)
{
lean_object* v_unused_4401_; 
v_unused_4401_ = lean_ctor_get(v___x_4393_, 0);
lean_dec(v_unused_4401_);
v___x_4395_ = v___x_4393_;
v_isShared_4396_ = v_isSharedCheck_4400_;
goto v_resetjp_4394_;
}
else
{
lean_dec(v___x_4393_);
v___x_4395_ = lean_box(0);
v_isShared_4396_ = v_isSharedCheck_4400_;
goto v_resetjp_4394_;
}
v_resetjp_4394_:
{
lean_object* v___x_4398_; 
if (v_isShared_4396_ == 0)
{
lean_ctor_set(v___x_4395_, 0, v_a_4391_);
v___x_4398_ = v___x_4395_;
goto v_reusejp_4397_;
}
else
{
lean_object* v_reuseFailAlloc_4399_; 
v_reuseFailAlloc_4399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4399_, 0, v_a_4391_);
v___x_4398_ = v_reuseFailAlloc_4399_;
goto v_reusejp_4397_;
}
v_reusejp_4397_:
{
return v___x_4398_;
}
}
}
else
{
lean_object* v_a_4402_; lean_object* v___x_4404_; uint8_t v_isShared_4405_; uint8_t v_isSharedCheck_4409_; 
lean_dec(v_a_4391_);
v_a_4402_ = lean_ctor_get(v___x_4393_, 0);
v_isSharedCheck_4409_ = !lean_is_exclusive(v___x_4393_);
if (v_isSharedCheck_4409_ == 0)
{
v___x_4404_ = v___x_4393_;
v_isShared_4405_ = v_isSharedCheck_4409_;
goto v_resetjp_4403_;
}
else
{
lean_inc(v_a_4402_);
lean_dec(v___x_4393_);
v___x_4404_ = lean_box(0);
v_isShared_4405_ = v_isSharedCheck_4409_;
goto v_resetjp_4403_;
}
v_resetjp_4403_:
{
lean_object* v___x_4407_; 
if (v_isShared_4405_ == 0)
{
v___x_4407_ = v___x_4404_;
goto v_reusejp_4406_;
}
else
{
lean_object* v_reuseFailAlloc_4408_; 
v_reuseFailAlloc_4408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4408_, 0, v_a_4402_);
v___x_4407_ = v_reuseFailAlloc_4408_;
goto v_reusejp_4406_;
}
v_reusejp_4406_:
{
return v___x_4407_;
}
}
}
}
else
{
lean_dec_ref(v_e_4371_);
return v___x_4390_;
}
}
else
{
lean_object* v_val_4410_; lean_object* v___x_4412_; 
lean_dec_ref(v_e_4371_);
lean_dec_ref(v_post_4367_);
lean_dec_ref(v_pre_4366_);
v_val_4410_ = lean_ctor_get(v___x_4384_, 0);
lean_inc(v_val_4410_);
lean_dec_ref_known(v___x_4384_, 1);
if (v_isShared_4383_ == 0)
{
lean_ctor_set(v___x_4382_, 0, v_val_4410_);
v___x_4412_ = v___x_4382_;
goto v_reusejp_4411_;
}
else
{
lean_object* v_reuseFailAlloc_4413_; 
v_reuseFailAlloc_4413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4413_, 0, v_val_4410_);
v___x_4412_ = v_reuseFailAlloc_4413_;
goto v_reusejp_4411_;
}
v_reusejp_4411_:
{
return v___x_4412_;
}
}
}
}
else
{
lean_object* v_a_4415_; lean_object* v___x_4417_; uint8_t v_isShared_4418_; uint8_t v_isSharedCheck_4422_; 
lean_dec_ref(v_e_4371_);
lean_dec_ref(v_post_4367_);
lean_dec_ref(v_pre_4366_);
v_a_4415_ = lean_ctor_get(v___x_4379_, 0);
v_isSharedCheck_4422_ = !lean_is_exclusive(v___x_4379_);
if (v_isSharedCheck_4422_ == 0)
{
v___x_4417_ = v___x_4379_;
v_isShared_4418_ = v_isSharedCheck_4422_;
goto v_resetjp_4416_;
}
else
{
lean_inc(v_a_4415_);
lean_dec(v___x_4379_);
v___x_4417_ = lean_box(0);
v_isShared_4418_ = v_isSharedCheck_4422_;
goto v_resetjp_4416_;
}
v_resetjp_4416_:
{
lean_object* v___x_4420_; 
if (v_isShared_4418_ == 0)
{
v___x_4420_ = v___x_4417_;
goto v_reusejp_4419_;
}
else
{
lean_object* v_reuseFailAlloc_4421_; 
v_reuseFailAlloc_4421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4421_, 0, v_a_4415_);
v___x_4420_ = v_reuseFailAlloc_4421_;
goto v_reusejp_4419_;
}
v_reusejp_4419_:
{
return v___x_4420_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_4366_ = stack[0].m_obj;
lean_object* v_post_4367_ = stack[1].m_obj;
uint8_t v_usedLetOnly_4368_ = stack[2].m_num;
uint8_t v_skipConstInApp_4369_ = stack[3].m_num;
uint8_t v_skipInstances_4370_ = stack[4].m_num;
lean_object* v_e_4371_ = stack[5].m_obj;
lean_object* v_a_4372_ = stack[6].m_obj;
lean_object* v___y_4373_ = stack[7].m_obj;
lean_object* v___y_4374_ = stack[8].m_obj;
lean_object* v___y_4375_ = stack[9].m_obj;
lean_object* v___y_4376_ = stack[10].m_obj;
lean_object* v_res_4423_;
v_res_4423_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4366_, v_post_4367_, v_usedLetOnly_4368_, v_skipConstInApp_4369_, v_skipInstances_4370_, v_e_4371_, v_a_4372_, v___y_4373_, v___y_4374_, v___y_4375_, v___y_4376_);
stack->m_obj
 = v_res_4423_;
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5(lean_object* v_pre_4424_, lean_object* v_post_4425_, uint8_t v_usedLetOnly_4426_, uint8_t v_skipConstInApp_4427_, uint8_t v_skipInstances_4428_, lean_object* v_fvars_4429_, lean_object* v_e_4430_, lean_object* v_a_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_){
_start:
{
if (lean_obj_tag(v_e_4430_) == 7)
{
lean_object* v_binderName_4437_; lean_object* v_binderType_4438_; lean_object* v_body_4439_; uint8_t v_binderInfo_4440_; lean_object* v___x_4441_; lean_object* v___x_4442_; lean_object* v___x_4443_; lean_object* v___f_4444_; lean_object* v___x_4445_; lean_object* v___x_4446_; 
v_binderName_4437_ = lean_ctor_get(v_e_4430_, 0);
lean_inc(v_binderName_4437_);
v_binderType_4438_ = lean_ctor_get(v_e_4430_, 1);
lean_inc_ref(v_binderType_4438_);
v_body_4439_ = lean_ctor_get(v_e_4430_, 2);
lean_inc_ref(v_body_4439_);
v_binderInfo_4440_ = lean_ctor_get_uint8(v_e_4430_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_4430_, 3);
v___x_4441_ = lean_box(v_usedLetOnly_4426_);
v___x_4442_ = lean_box(v_skipConstInApp_4427_);
v___x_4443_ = lean_box(v_skipInstances_4428_);
lean_inc_ref(v_post_4425_);
lean_inc_ref(v_pre_4424_);
lean_inc_ref(v_fvars_4429_);
v___f_4444_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___lam__0___boxed), 14, 7);
lean_closure_set(v___f_4444_, 0, v_fvars_4429_);
lean_closure_set(v___f_4444_, 1, v_pre_4424_);
lean_closure_set(v___f_4444_, 2, v_post_4425_);
lean_closure_set(v___f_4444_, 3, v___x_4441_);
lean_closure_set(v___f_4444_, 4, v___x_4442_);
lean_closure_set(v___f_4444_, 5, v___x_4443_);
lean_closure_set(v___f_4444_, 6, v_body_4439_);
v___x_4445_ = lean_expr_instantiate_rev(v_binderType_4438_, v_fvars_4429_);
lean_dec_ref(v_fvars_4429_);
lean_dec_ref(v_binderType_4438_);
v___x_4446_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4424_, v_post_4425_, v_usedLetOnly_4426_, v_skipConstInApp_4427_, v_skipInstances_4428_, v___x_4445_, v_a_4431_, v___y_4432_, v___y_4433_, v___y_4434_, v___y_4435_);
if (lean_obj_tag(v___x_4446_) == 0)
{
lean_object* v_a_4447_; uint8_t v___x_4448_; lean_object* v___x_4449_; 
v_a_4447_ = lean_ctor_get(v___x_4446_, 0);
lean_inc(v_a_4447_);
lean_dec_ref_known(v___x_4446_, 1);
v___x_4448_ = 0;
v___x_4449_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_binderName_4437_, v_binderInfo_4440_, v_a_4447_, v___f_4444_, v___x_4448_, v_a_4431_, v___y_4432_, v___y_4433_, v___y_4434_, v___y_4435_);
return v___x_4449_;
}
else
{
lean_dec_ref(v___f_4444_);
lean_dec(v_binderName_4437_);
return v___x_4446_;
}
}
else
{
lean_object* v___x_4450_; lean_object* v___x_4451_; 
v___x_4450_ = lean_expr_instantiate_rev(v_e_4430_, v_fvars_4429_);
lean_dec_ref(v_e_4430_);
lean_inc_ref(v_post_4425_);
lean_inc_ref(v_pre_4424_);
v___x_4451_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4424_, v_post_4425_, v_usedLetOnly_4426_, v_skipConstInApp_4427_, v_skipInstances_4428_, v___x_4450_, v_a_4431_, v___y_4432_, v___y_4433_, v___y_4434_, v___y_4435_);
if (lean_obj_tag(v___x_4451_) == 0)
{
lean_object* v_a_4452_; uint8_t v___x_4453_; uint8_t v___x_4454_; uint8_t v___x_4455_; lean_object* v___x_4456_; 
v_a_4452_ = lean_ctor_get(v___x_4451_, 0);
lean_inc(v_a_4452_);
lean_dec_ref_known(v___x_4451_, 1);
v___x_4453_ = 0;
v___x_4454_ = 1;
v___x_4455_ = 1;
v___x_4456_ = l_Lean_Meta_mkForallFVars(v_fvars_4429_, v_a_4452_, v___x_4453_, v_usedLetOnly_4426_, v___x_4454_, v___x_4455_, v___y_4432_, v___y_4433_, v___y_4434_, v___y_4435_);
lean_dec_ref(v_fvars_4429_);
if (lean_obj_tag(v___x_4456_) == 0)
{
lean_object* v_a_4457_; lean_object* v___x_4458_; 
v_a_4457_ = lean_ctor_get(v___x_4456_, 0);
lean_inc(v_a_4457_);
lean_dec_ref_known(v___x_4456_, 1);
v___x_4458_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4424_, v_post_4425_, v_usedLetOnly_4426_, v_skipConstInApp_4427_, v_skipInstances_4428_, v_a_4457_, v_a_4431_, v___y_4432_, v___y_4433_, v___y_4434_, v___y_4435_);
return v___x_4458_;
}
else
{
lean_dec_ref(v_post_4425_);
lean_dec_ref(v_pre_4424_);
return v___x_4456_;
}
}
else
{
lean_dec_ref(v_fvars_4429_);
lean_dec_ref(v_post_4425_);
lean_dec_ref(v_pre_4424_);
return v___x_4451_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_4424_ = stack[0].m_obj;
lean_object* v_post_4425_ = stack[1].m_obj;
uint8_t v_usedLetOnly_4426_ = stack[2].m_num;
uint8_t v_skipConstInApp_4427_ = stack[3].m_num;
uint8_t v_skipInstances_4428_ = stack[4].m_num;
lean_object* v_fvars_4429_ = stack[5].m_obj;
lean_object* v_e_4430_ = stack[6].m_obj;
lean_object* v_a_4431_ = stack[7].m_obj;
lean_object* v___y_4432_ = stack[8].m_obj;
lean_object* v___y_4433_ = stack[9].m_obj;
lean_object* v___y_4434_ = stack[10].m_obj;
lean_object* v___y_4435_ = stack[11].m_obj;
lean_object* v_res_4459_;
v_res_4459_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5(v_pre_4424_, v_post_4425_, v_usedLetOnly_4426_, v_skipConstInApp_4427_, v_skipInstances_4428_, v_fvars_4429_, v_e_4430_, v_a_4431_, v___y_4432_, v___y_4433_, v___y_4434_, v___y_4435_);
stack->m_obj
 = v_res_4459_;
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___lam__0(lean_object* v_fvars_4460_, lean_object* v_pre_4461_, lean_object* v_post_4462_, uint8_t v_usedLetOnly_4463_, uint8_t v_skipConstInApp_4464_, uint8_t v_skipInstances_4465_, lean_object* v_body_4466_, lean_object* v_x_4467_, lean_object* v___y_4468_, lean_object* v___y_4469_, lean_object* v___y_4470_, lean_object* v___y_4471_, lean_object* v___y_4472_){
_start:
{
lean_object* v___x_4474_; lean_object* v___x_4475_; 
v___x_4474_ = lean_array_push(v_fvars_4460_, v_x_4467_);
v___x_4475_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5(v_pre_4461_, v_post_4462_, v_usedLetOnly_4463_, v_skipConstInApp_4464_, v_skipInstances_4465_, v___x_4474_, v_body_4466_, v___y_4468_, v___y_4469_, v___y_4470_, v___y_4471_, v___y_4472_);
return v___x_4475_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_4460_ = stack[0].m_obj;
lean_object* v_pre_4461_ = stack[1].m_obj;
lean_object* v_post_4462_ = stack[2].m_obj;
uint8_t v_usedLetOnly_4463_ = stack[3].m_num;
uint8_t v_skipConstInApp_4464_ = stack[4].m_num;
uint8_t v_skipInstances_4465_ = stack[5].m_num;
lean_object* v_body_4466_ = stack[6].m_obj;
lean_object* v_x_4467_ = stack[7].m_obj;
lean_object* v___y_4468_ = stack[8].m_obj;
lean_object* v___y_4469_ = stack[9].m_obj;
lean_object* v___y_4470_ = stack[10].m_obj;
lean_object* v___y_4471_ = stack[11].m_obj;
lean_object* v___y_4472_ = stack[12].m_obj;
lean_object* v_res_4476_;
v_res_4476_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___lam__0(v_fvars_4460_, v_pre_4461_, v_post_4462_, v_usedLetOnly_4463_, v_skipConstInApp_4464_, v_skipInstances_4465_, v_body_4466_, v_x_4467_, v___y_4468_, v___y_4469_, v___y_4470_, v___y_4471_, v___y_4472_);
stack->m_obj
 = v_res_4476_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3___boxed(lean_object* v_pre_4477_, lean_object* v_post_4478_, lean_object* v_usedLetOnly_4479_, lean_object* v_skipConstInApp_4480_, lean_object* v_skipInstances_4481_, lean_object* v_e_4482_, lean_object* v_a_4483_, lean_object* v___y_4484_, lean_object* v___y_4485_, lean_object* v___y_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_){
_start:
{
uint8_t v_usedLetOnly_boxed_4489_; uint8_t v_skipConstInApp_boxed_4490_; uint8_t v_skipInstances_boxed_4491_; lean_object* v_res_4492_; 
v_usedLetOnly_boxed_4489_ = lean_unbox(v_usedLetOnly_4479_);
v_skipConstInApp_boxed_4490_ = lean_unbox(v_skipConstInApp_4480_);
v_skipInstances_boxed_4491_ = lean_unbox(v_skipInstances_4481_);
v_res_4492_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4477_, v_post_4478_, v_usedLetOnly_boxed_4489_, v_skipConstInApp_boxed_4490_, v_skipInstances_boxed_4491_, v_e_4482_, v_a_4483_, v___y_4484_, v___y_4485_, v___y_4486_, v___y_4487_);
lean_dec(v___y_4487_);
lean_dec_ref(v___y_4486_);
lean_dec(v___y_4485_);
lean_dec_ref(v___y_4484_);
lean_dec(v_a_4483_);
return v_res_4492_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__2___boxed(lean_object* v_pre_4493_, lean_object* v_post_4494_, lean_object* v_usedLetOnly_4495_, lean_object* v_skipConstInApp_4496_, lean_object* v_skipInstances_4497_, lean_object* v_sz_4498_, lean_object* v_i_4499_, lean_object* v_bs_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_, lean_object* v___y_4503_, lean_object* v___y_4504_, lean_object* v___y_4505_, lean_object* v___y_4506_){
_start:
{
uint8_t v_usedLetOnly_boxed_4507_; uint8_t v_skipConstInApp_boxed_4508_; uint8_t v_skipInstances_boxed_4509_; size_t v_sz_boxed_4510_; size_t v_i_boxed_4511_; lean_object* v_res_4512_; 
v_usedLetOnly_boxed_4507_ = lean_unbox(v_usedLetOnly_4495_);
v_skipConstInApp_boxed_4508_ = lean_unbox(v_skipConstInApp_4496_);
v_skipInstances_boxed_4509_ = lean_unbox(v_skipInstances_4497_);
v_sz_boxed_4510_ = lean_unbox_usize(v_sz_4498_);
lean_dec(v_sz_4498_);
v_i_boxed_4511_ = lean_unbox_usize(v_i_4499_);
lean_dec(v_i_4499_);
v_res_4512_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__2(v_pre_4493_, v_post_4494_, v_usedLetOnly_boxed_4507_, v_skipConstInApp_boxed_4508_, v_skipInstances_boxed_4509_, v_sz_boxed_4510_, v_i_boxed_4511_, v_bs_4500_, v___y_4501_, v___y_4502_, v___y_4503_, v___y_4504_, v___y_4505_);
lean_dec(v___y_4505_);
lean_dec_ref(v___y_4504_);
lean_dec(v___y_4503_);
lean_dec_ref(v___y_4502_);
lean_dec(v___y_4501_);
return v_res_4512_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___boxed(lean_object* v_pre_4513_, lean_object* v_post_4514_, lean_object* v_usedLetOnly_4515_, lean_object* v_skipConstInApp_4516_, lean_object* v_skipInstances_4517_, lean_object* v_e_4518_, lean_object* v_a_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_, lean_object* v___y_4524_){
_start:
{
uint8_t v_usedLetOnly_boxed_4525_; uint8_t v_skipConstInApp_boxed_4526_; uint8_t v_skipInstances_boxed_4527_; lean_object* v_res_4528_; 
v_usedLetOnly_boxed_4525_ = lean_unbox(v_usedLetOnly_4515_);
v_skipConstInApp_boxed_4526_ = lean_unbox(v_skipConstInApp_4516_);
v_skipInstances_boxed_4527_ = lean_unbox(v_skipInstances_4517_);
v_res_4528_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4513_, v_post_4514_, v_usedLetOnly_boxed_4525_, v_skipConstInApp_boxed_4526_, v_skipInstances_boxed_4527_, v_e_4518_, v_a_4519_, v___y_4520_, v___y_4521_, v___y_4522_, v___y_4523_);
lean_dec(v___y_4523_);
lean_dec_ref(v___y_4522_);
lean_dec(v___y_4521_);
lean_dec_ref(v___y_4520_);
lean_dec(v_a_4519_);
return v_res_4528_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___boxed(lean_object* v_pre_4529_, lean_object* v_post_4530_, lean_object* v_usedLetOnly_4531_, lean_object* v_skipConstInApp_4532_, lean_object* v_skipInstances_4533_, lean_object* v_fvars_4534_, lean_object* v_e_4535_, lean_object* v_a_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_, lean_object* v___y_4539_, lean_object* v___y_4540_, lean_object* v___y_4541_){
_start:
{
uint8_t v_usedLetOnly_boxed_4542_; uint8_t v_skipConstInApp_boxed_4543_; uint8_t v_skipInstances_boxed_4544_; lean_object* v_res_4545_; 
v_usedLetOnly_boxed_4542_ = lean_unbox(v_usedLetOnly_4531_);
v_skipConstInApp_boxed_4543_ = lean_unbox(v_skipConstInApp_4532_);
v_skipInstances_boxed_4544_ = lean_unbox(v_skipInstances_4533_);
v_res_4545_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5(v_pre_4529_, v_post_4530_, v_usedLetOnly_boxed_4542_, v_skipConstInApp_boxed_4543_, v_skipInstances_boxed_4544_, v_fvars_4534_, v_e_4535_, v_a_4536_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_);
lean_dec(v___y_4540_);
lean_dec_ref(v___y_4539_);
lean_dec(v___y_4538_);
lean_dec_ref(v___y_4537_);
lean_dec(v_a_4536_);
return v_res_4545_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___boxed(lean_object* v_pre_4546_, lean_object* v_post_4547_, lean_object* v_usedLetOnly_4548_, lean_object* v_skipConstInApp_4549_, lean_object* v_skipInstances_4550_, lean_object* v_fvars_4551_, lean_object* v_e_4552_, lean_object* v_a_4553_, lean_object* v___y_4554_, lean_object* v___y_4555_, lean_object* v___y_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_){
_start:
{
uint8_t v_usedLetOnly_boxed_4559_; uint8_t v_skipConstInApp_boxed_4560_; uint8_t v_skipInstances_boxed_4561_; lean_object* v_res_4562_; 
v_usedLetOnly_boxed_4559_ = lean_unbox(v_usedLetOnly_4548_);
v_skipConstInApp_boxed_4560_ = lean_unbox(v_skipConstInApp_4549_);
v_skipInstances_boxed_4561_ = lean_unbox(v_skipInstances_4550_);
v_res_4562_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6(v_pre_4546_, v_post_4547_, v_usedLetOnly_boxed_4559_, v_skipConstInApp_boxed_4560_, v_skipInstances_boxed_4561_, v_fvars_4551_, v_e_4552_, v_a_4553_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_);
lean_dec(v___y_4557_);
lean_dec_ref(v___y_4556_);
lean_dec(v___y_4555_);
lean_dec_ref(v___y_4554_);
lean_dec(v_a_4553_);
return v_res_4562_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___boxed(lean_object* v_pre_4563_, lean_object* v_post_4564_, lean_object* v_usedLetOnly_4565_, lean_object* v_skipConstInApp_4566_, lean_object* v_skipInstances_4567_, lean_object* v_fvars_4568_, lean_object* v_e_4569_, lean_object* v_a_4570_, lean_object* v___y_4571_, lean_object* v___y_4572_, lean_object* v___y_4573_, lean_object* v___y_4574_, lean_object* v___y_4575_){
_start:
{
uint8_t v_usedLetOnly_boxed_4576_; uint8_t v_skipConstInApp_boxed_4577_; uint8_t v_skipInstances_boxed_4578_; lean_object* v_res_4579_; 
v_usedLetOnly_boxed_4576_ = lean_unbox(v_usedLetOnly_4565_);
v_skipConstInApp_boxed_4577_ = lean_unbox(v_skipConstInApp_4566_);
v_skipInstances_boxed_4578_ = lean_unbox(v_skipInstances_4567_);
v_res_4579_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7(v_pre_4563_, v_post_4564_, v_usedLetOnly_boxed_4576_, v_skipConstInApp_boxed_4577_, v_skipInstances_boxed_4578_, v_fvars_4568_, v_e_4569_, v_a_4570_, v___y_4571_, v___y_4572_, v___y_4573_, v___y_4574_);
lean_dec(v___y_4574_);
lean_dec_ref(v___y_4573_);
lean_dec(v___y_4572_);
lean_dec_ref(v___y_4571_);
lean_dec(v_a_4570_);
return v_res_4579_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_upperBound_4580_, lean_object* v___x_4581_, lean_object* v_pre_4582_, lean_object* v_post_4583_, lean_object* v_usedLetOnly_4584_, lean_object* v_skipConstInApp_4585_, lean_object* v_skipInstances_4586_, lean_object* v_a_4587_, lean_object* v_b_4588_, lean_object* v___y_4589_, lean_object* v___y_4590_, lean_object* v___y_4591_, lean_object* v___y_4592_, lean_object* v___y_4593_, lean_object* v___y_4594_){
_start:
{
uint8_t v_usedLetOnly_boxed_4595_; uint8_t v_skipConstInApp_boxed_4596_; uint8_t v_skipInstances_boxed_4597_; lean_object* v_res_4598_; 
v_usedLetOnly_boxed_4595_ = lean_unbox(v_usedLetOnly_4584_);
v_skipConstInApp_boxed_4596_ = lean_unbox(v_skipConstInApp_4585_);
v_skipInstances_boxed_4597_ = lean_unbox(v_skipInstances_4586_);
v_res_4598_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg(v_upperBound_4580_, v___x_4581_, v_pre_4582_, v_post_4583_, v_usedLetOnly_boxed_4595_, v_skipConstInApp_boxed_4596_, v_skipInstances_boxed_4597_, v_a_4587_, v_b_4588_, v___y_4589_, v___y_4590_, v___y_4591_, v___y_4592_, v___y_4593_);
lean_dec(v___y_4593_);
lean_dec_ref(v___y_4592_);
lean_dec(v___y_4591_);
lean_dec_ref(v___y_4590_);
lean_dec(v___y_4589_);
lean_dec_ref(v___x_4581_);
lean_dec(v_upperBound_4580_);
return v_res_4598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__8___boxed(lean_object* v_skipInstances_4599_, lean_object* v_pre_4600_, lean_object* v_post_4601_, lean_object* v_usedLetOnly_4602_, lean_object* v_skipConstInApp_4603_, lean_object* v_x_4604_, lean_object* v_x_4605_, lean_object* v_x_4606_, lean_object* v___y_4607_, lean_object* v___y_4608_, lean_object* v___y_4609_, lean_object* v___y_4610_, lean_object* v___y_4611_, lean_object* v___y_4612_){
_start:
{
uint8_t v_skipInstances_boxed_4613_; uint8_t v_usedLetOnly_boxed_4614_; uint8_t v_skipConstInApp_boxed_4615_; lean_object* v_res_4616_; 
v_skipInstances_boxed_4613_ = lean_unbox(v_skipInstances_4599_);
v_usedLetOnly_boxed_4614_ = lean_unbox(v_usedLetOnly_4602_);
v_skipConstInApp_boxed_4615_ = lean_unbox(v_skipConstInApp_4603_);
v_res_4616_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__8(v_skipInstances_boxed_4613_, v_pre_4600_, v_post_4601_, v_usedLetOnly_boxed_4614_, v_skipConstInApp_boxed_4615_, v_x_4604_, v_x_4605_, v_x_4606_, v___y_4607_, v___y_4608_, v___y_4609_, v___y_4610_, v___y_4611_);
lean_dec(v___y_4611_);
lean_dec_ref(v___y_4610_);
lean_dec(v___y_4609_);
lean_dec_ref(v___y_4608_);
lean_dec(v___y_4607_);
return v_res_4616_;
}
}
lean_object* l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(lean_object* v_input_4617_, lean_object* v_pre_4618_, lean_object* v_post_4619_, uint8_t v_usedLetOnly_4620_, uint8_t v_skipConstInApp_4621_, lean_object* v___y_4622_, lean_object* v___y_4623_, lean_object* v___y_4624_, lean_object* v___y_4625_){
_start:
{
uint8_t v___x_4627_; lean_object* v___x_4628_; lean_object* v___x_4629_; lean_object* v_a_4630_; lean_object* v___x_4631_; 
v___x_4627_ = 0;
v___x_4628_ = lean_obj_once(&l_Lean_Core_transform___redArg___closed__2, &l_Lean_Core_transform___redArg___closed__2_once, _init_l_Lean_Core_transform___redArg___closed__2);
v___x_4629_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0(lean_box(0), v___x_4628_, v___y_4622_, v___y_4623_, v___y_4624_, v___y_4625_);
v_a_4630_ = lean_ctor_get(v___x_4629_, 0);
lean_inc(v_a_4630_);
lean_dec_ref(v___x_4629_);
v___x_4631_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4618_, v_post_4619_, v_usedLetOnly_4620_, v_skipConstInApp_4621_, v___x_4627_, v_input_4617_, v_a_4630_, v___y_4622_, v___y_4623_, v___y_4624_, v___y_4625_);
if (lean_obj_tag(v___x_4631_) == 0)
{
lean_object* v_a_4632_; lean_object* v___x_4633_; lean_object* v___x_4634_; lean_object* v___x_4636_; uint8_t v_isShared_4637_; uint8_t v_isSharedCheck_4641_; 
v_a_4632_ = lean_ctor_get(v___x_4631_, 0);
lean_inc(v_a_4632_);
lean_dec_ref_known(v___x_4631_, 1);
v___x_4633_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_4633_, 0, lean_box(0));
lean_closure_set(v___x_4633_, 1, lean_box(0));
lean_closure_set(v___x_4633_, 2, v_a_4630_);
v___x_4634_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0(lean_box(0), v___x_4633_, v___y_4622_, v___y_4623_, v___y_4624_, v___y_4625_);
v_isSharedCheck_4641_ = !lean_is_exclusive(v___x_4634_);
if (v_isSharedCheck_4641_ == 0)
{
lean_object* v_unused_4642_; 
v_unused_4642_ = lean_ctor_get(v___x_4634_, 0);
lean_dec(v_unused_4642_);
v___x_4636_ = v___x_4634_;
v_isShared_4637_ = v_isSharedCheck_4641_;
goto v_resetjp_4635_;
}
else
{
lean_dec(v___x_4634_);
v___x_4636_ = lean_box(0);
v_isShared_4637_ = v_isSharedCheck_4641_;
goto v_resetjp_4635_;
}
v_resetjp_4635_:
{
lean_object* v___x_4639_; 
if (v_isShared_4637_ == 0)
{
lean_ctor_set(v___x_4636_, 0, v_a_4632_);
v___x_4639_ = v___x_4636_;
goto v_reusejp_4638_;
}
else
{
lean_object* v_reuseFailAlloc_4640_; 
v_reuseFailAlloc_4640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4640_, 0, v_a_4632_);
v___x_4639_ = v_reuseFailAlloc_4640_;
goto v_reusejp_4638_;
}
v_reusejp_4638_:
{
return v___x_4639_;
}
}
}
else
{
lean_dec(v_a_4630_);
return v___x_4631_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_input_4617_ = stack[0].m_obj;
lean_object* v_pre_4618_ = stack[1].m_obj;
lean_object* v_post_4619_ = stack[2].m_obj;
uint8_t v_usedLetOnly_4620_ = stack[3].m_num;
uint8_t v_skipConstInApp_4621_ = stack[4].m_num;
lean_object* v___y_4622_ = stack[5].m_obj;
lean_object* v___y_4623_ = stack[6].m_obj;
lean_object* v___y_4624_ = stack[7].m_obj;
lean_object* v___y_4625_ = stack[8].m_obj;
lean_object* v_res_4643_;
v_res_4643_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(v_input_4617_, v_pre_4618_, v_post_4619_, v_usedLetOnly_4620_, v_skipConstInApp_4621_, v___y_4622_, v___y_4623_, v___y_4624_, v___y_4625_);
stack->m_obj
 = v_res_4643_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___boxed(lean_object* v_input_4644_, lean_object* v_pre_4645_, lean_object* v_post_4646_, lean_object* v_usedLetOnly_4647_, lean_object* v_skipConstInApp_4648_, lean_object* v___y_4649_, lean_object* v___y_4650_, lean_object* v___y_4651_, lean_object* v___y_4652_, lean_object* v___y_4653_){
_start:
{
uint8_t v_usedLetOnly_boxed_4654_; uint8_t v_skipConstInApp_boxed_4655_; lean_object* v_res_4656_; 
v_usedLetOnly_boxed_4654_ = lean_unbox(v_usedLetOnly_4647_);
v_skipConstInApp_boxed_4655_ = lean_unbox(v_skipConstInApp_4648_);
v_res_4656_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(v_input_4644_, v_pre_4645_, v_post_4646_, v_usedLetOnly_boxed_4654_, v_skipConstInApp_boxed_4655_, v___y_4649_, v___y_4650_, v___y_4651_, v___y_4652_);
lean_dec(v___y_4652_);
lean_dec_ref(v___y_4651_);
lean_dec(v___y_4650_);
lean_dec_ref(v___y_4649_);
return v_res_4656_;
}
}
lean_object* l_Lean_Meta_zetaReduce(lean_object* v_e_4658_, uint8_t v_zetaDelta_4659_, uint8_t v_zetaHave_4660_, uint8_t v_beta_4661_, lean_object* v_a_4662_, lean_object* v_a_4663_, lean_object* v_a_4664_, lean_object* v_a_4665_){
_start:
{
lean_object* v_lctx_4667_; lean_object* v___x_4668_; lean_object* v___x_4669_; lean_object* v___x_4670_; lean_object* v___f_4671_; uint8_t v___x_4672_; 
v_lctx_4667_ = lean_ctor_get(v_a_4662_, 2);
lean_inc_ref(v_lctx_4667_);
v___x_4668_ = lean_local_ctx_num_indices(v_lctx_4667_);
v___x_4669_ = lean_box(v_zetaHave_4660_);
v___x_4670_ = lean_box(v_zetaDelta_4659_);
v___f_4671_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaReduce___lam__0___boxed), 9, 3);
lean_closure_set(v___f_4671_, 0, v___x_4669_);
lean_closure_set(v___f_4671_, 1, v___x_4668_);
lean_closure_set(v___f_4671_, 2, v___x_4670_);
v___x_4672_ = 1;
if (v_beta_4661_ == 0)
{
lean_object* v___f_4673_; lean_object* v___f_4674_; lean_object* v___x_4675_; 
v___f_4673_ = ((lean_object*)(l_Lean_Meta_zetaReduce___closed__0));
v___f_4674_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaReduce___lam__2___boxed), 7, 1);
lean_closure_set(v___f_4674_, 0, v___f_4671_);
v___x_4675_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(v_e_4658_, v___f_4674_, v___f_4673_, v___x_4672_, v_beta_4661_, v_a_4662_, v_a_4663_, v_a_4664_, v_a_4665_);
return v___x_4675_;
}
else
{
lean_object* v___f_4676_; lean_object* v___f_4677_; uint8_t v___x_4678_; lean_object* v___x_4679_; 
v___f_4676_ = ((lean_object*)(l_Lean_Meta_zetaReduce___closed__0));
v___f_4677_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaReduce___lam__4___boxed), 7, 1);
lean_closure_set(v___f_4677_, 0, v___f_4671_);
v___x_4678_ = 0;
v___x_4679_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(v_e_4658_, v___f_4677_, v___f_4676_, v___x_4672_, v___x_4678_, v_a_4662_, v_a_4663_, v_a_4664_, v_a_4665_);
return v___x_4679_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_zetaReduce_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4658_ = stack[0].m_obj;
uint8_t v_zetaDelta_4659_ = stack[1].m_num;
uint8_t v_zetaHave_4660_ = stack[2].m_num;
uint8_t v_beta_4661_ = stack[3].m_num;
lean_object* v_a_4662_ = stack[4].m_obj;
lean_object* v_a_4663_ = stack[5].m_obj;
lean_object* v_a_4664_ = stack[6].m_obj;
lean_object* v_a_4665_ = stack[7].m_obj;
lean_object* v_res_4680_;
v_res_4680_ = l_Lean_Meta_zetaReduce(v_e_4658_, v_zetaDelta_4659_, v_zetaHave_4660_, v_beta_4661_, v_a_4662_, v_a_4663_, v_a_4664_, v_a_4665_);
stack->m_obj
 = v_res_4680_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___boxed(lean_object* v_e_4681_, lean_object* v_zetaDelta_4682_, lean_object* v_zetaHave_4683_, lean_object* v_beta_4684_, lean_object* v_a_4685_, lean_object* v_a_4686_, lean_object* v_a_4687_, lean_object* v_a_4688_, lean_object* v_a_4689_){
_start:
{
uint8_t v_zetaDelta_boxed_4690_; uint8_t v_zetaHave_boxed_4691_; uint8_t v_beta_boxed_4692_; lean_object* v_res_4693_; 
v_zetaDelta_boxed_4690_ = lean_unbox(v_zetaDelta_4682_);
v_zetaHave_boxed_4691_ = lean_unbox(v_zetaHave_4683_);
v_beta_boxed_4692_ = lean_unbox(v_beta_4684_);
v_res_4693_ = l_Lean_Meta_zetaReduce(v_e_4681_, v_zetaDelta_boxed_4690_, v_zetaHave_boxed_4691_, v_beta_boxed_4692_, v_a_4685_, v_a_4686_, v_a_4687_, v_a_4688_);
lean_dec(v_a_4688_);
lean_dec_ref(v_a_4687_);
lean_dec(v_a_4686_);
lean_dec_ref(v_a_4685_);
return v_res_4693_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4(lean_object* v_upperBound_4694_, lean_object* v___x_4695_, lean_object* v_pre_4696_, lean_object* v_post_4697_, uint8_t v_usedLetOnly_4698_, uint8_t v_skipConstInApp_4699_, uint8_t v_skipInstances_4700_, lean_object* v___x_4701_, lean_object* v_inst_4702_, lean_object* v_R_4703_, lean_object* v_a_4704_, lean_object* v_b_4705_, lean_object* v_c_4706_, lean_object* v___y_4707_, lean_object* v___y_4708_, lean_object* v___y_4709_, lean_object* v___y_4710_, lean_object* v___y_4711_){
_start:
{
lean_object* v___x_4713_; 
v___x_4713_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg(v_upperBound_4694_, v___x_4695_, v_pre_4696_, v_post_4697_, v_usedLetOnly_4698_, v_skipConstInApp_4699_, v_skipInstances_4700_, v_a_4704_, v_b_4705_, v___y_4707_, v___y_4708_, v___y_4709_, v___y_4710_, v___y_4711_);
return v___x_4713_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_4694_ = stack[0].m_obj;
lean_object* v___x_4695_ = stack[1].m_obj;
lean_object* v_pre_4696_ = stack[2].m_obj;
lean_object* v_post_4697_ = stack[3].m_obj;
uint8_t v_usedLetOnly_4698_ = stack[4].m_num;
uint8_t v_skipConstInApp_4699_ = stack[5].m_num;
uint8_t v_skipInstances_4700_ = stack[6].m_num;
lean_object* v___x_4701_ = stack[7].m_obj;
lean_object* v_a_4704_ = stack[10].m_obj;
lean_object* v_b_4705_ = stack[11].m_obj;
lean_object* v___y_4707_ = stack[13].m_obj;
lean_object* v___y_4708_ = stack[14].m_obj;
lean_object* v___y_4709_ = stack[15].m_obj;
lean_object* v___y_4710_ = stack[16].m_obj;
lean_object* v___y_4711_ = stack[17].m_obj;
lean_object* v_res_4714_;
v_res_4714_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4(v_upperBound_4694_, v___x_4695_, v_pre_4696_, v_post_4697_, v_usedLetOnly_4698_, v_skipConstInApp_4699_, v_skipInstances_4700_, v___x_4701_, lean_box(0), lean_box(0), v_a_4704_, v_b_4705_, lean_box(0), v___y_4707_, v___y_4708_, v___y_4709_, v___y_4710_, v___y_4711_);
stack->m_obj
 = v_res_4714_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___boxed(lean_object** _args){
lean_object* v_upperBound_4715_ = _args[0];
lean_object* v___x_4716_ = _args[1];
lean_object* v_pre_4717_ = _args[2];
lean_object* v_post_4718_ = _args[3];
lean_object* v_usedLetOnly_4719_ = _args[4];
lean_object* v_skipConstInApp_4720_ = _args[5];
lean_object* v_skipInstances_4721_ = _args[6];
lean_object* v___x_4722_ = _args[7];
lean_object* v_inst_4723_ = _args[8];
lean_object* v_R_4724_ = _args[9];
lean_object* v_a_4725_ = _args[10];
lean_object* v_b_4726_ = _args[11];
lean_object* v_c_4727_ = _args[12];
lean_object* v___y_4728_ = _args[13];
lean_object* v___y_4729_ = _args[14];
lean_object* v___y_4730_ = _args[15];
lean_object* v___y_4731_ = _args[16];
lean_object* v___y_4732_ = _args[17];
lean_object* v___y_4733_ = _args[18];
_start:
{
uint8_t v_usedLetOnly_boxed_4734_; uint8_t v_skipConstInApp_boxed_4735_; uint8_t v_skipInstances_boxed_4736_; lean_object* v_res_4737_; 
v_usedLetOnly_boxed_4734_ = lean_unbox(v_usedLetOnly_4719_);
v_skipConstInApp_boxed_4735_ = lean_unbox(v_skipConstInApp_4720_);
v_skipInstances_boxed_4736_ = lean_unbox(v_skipInstances_4721_);
v_res_4737_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4(v_upperBound_4715_, v___x_4716_, v_pre_4717_, v_post_4718_, v_usedLetOnly_boxed_4734_, v_skipConstInApp_boxed_4735_, v_skipInstances_boxed_4736_, v___x_4722_, v_inst_4723_, v_R_4724_, v_a_4725_, v_b_4726_, v_c_4727_, v___y_4728_, v___y_4729_, v___y_4730_, v___y_4731_, v___y_4732_);
lean_dec(v___y_4732_);
lean_dec_ref(v___y_4731_);
lean_dec(v___y_4730_);
lean_dec_ref(v___y_4729_);
lean_dec(v___y_4728_);
lean_dec(v___x_4722_);
lean_dec_ref(v___x_4716_);
lean_dec(v_upperBound_4715_);
return v_res_4737_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6(lean_object* v_00_u03b1_4738_, lean_object* v_name_4739_, uint8_t v_bi_4740_, lean_object* v_type_4741_, lean_object* v_k_4742_, uint8_t v_kind_4743_, lean_object* v___y_4744_, lean_object* v___y_4745_, lean_object* v___y_4746_, lean_object* v___y_4747_, lean_object* v___y_4748_){
_start:
{
lean_object* v___x_4750_; 
v___x_4750_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_name_4739_, v_bi_4740_, v_type_4741_, v_k_4742_, v_kind_4743_, v___y_4744_, v___y_4745_, v___y_4746_, v___y_4747_, v___y_4748_);
return v___x_4750_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_4739_ = stack[1].m_obj;
uint8_t v_bi_4740_ = stack[2].m_num;
lean_object* v_type_4741_ = stack[3].m_obj;
lean_object* v_k_4742_ = stack[4].m_obj;
uint8_t v_kind_4743_ = stack[5].m_num;
lean_object* v___y_4744_ = stack[6].m_obj;
lean_object* v___y_4745_ = stack[7].m_obj;
lean_object* v___y_4746_ = stack[8].m_obj;
lean_object* v___y_4747_ = stack[9].m_obj;
lean_object* v___y_4748_ = stack[10].m_obj;
lean_object* v_res_4751_;
v_res_4751_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6(lean_box(0), v_name_4739_, v_bi_4740_, v_type_4741_, v_k_4742_, v_kind_4743_, v___y_4744_, v___y_4745_, v___y_4746_, v___y_4747_, v___y_4748_);
stack->m_obj
 = v_res_4751_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___boxed(lean_object* v_00_u03b1_4752_, lean_object* v_name_4753_, lean_object* v_bi_4754_, lean_object* v_type_4755_, lean_object* v_k_4756_, lean_object* v_kind_4757_, lean_object* v___y_4758_, lean_object* v___y_4759_, lean_object* v___y_4760_, lean_object* v___y_4761_, lean_object* v___y_4762_, lean_object* v___y_4763_){
_start:
{
uint8_t v_bi_boxed_4764_; uint8_t v_kind_boxed_4765_; lean_object* v_res_4766_; 
v_bi_boxed_4764_ = lean_unbox(v_bi_4754_);
v_kind_boxed_4765_ = lean_unbox(v_kind_4757_);
v_res_4766_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6(v_00_u03b1_4752_, v_name_4753_, v_bi_boxed_4764_, v_type_4755_, v_k_4756_, v_kind_boxed_4765_, v___y_4758_, v___y_4759_, v___y_4760_, v___y_4761_, v___y_4762_);
lean_dec(v___y_4762_);
lean_dec_ref(v___y_4761_);
lean_dec(v___y_4760_);
lean_dec_ref(v___y_4759_);
lean_dec(v___y_4758_);
return v_res_4766_;
}
}
lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9(lean_object* v_00_u03b1_4767_, lean_object* v_name_4768_, lean_object* v_type_4769_, lean_object* v_val_4770_, lean_object* v_k_4771_, uint8_t v_nondep_4772_, uint8_t v_kind_4773_, lean_object* v___y_4774_, lean_object* v___y_4775_, lean_object* v___y_4776_, lean_object* v___y_4777_, lean_object* v___y_4778_){
_start:
{
lean_object* v___x_4780_; 
v___x_4780_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg(v_name_4768_, v_type_4769_, v_val_4770_, v_k_4771_, v_nondep_4772_, v_kind_4773_, v___y_4774_, v___y_4775_, v___y_4776_, v___y_4777_, v___y_4778_);
return v___x_4780_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_4768_ = stack[1].m_obj;
lean_object* v_type_4769_ = stack[2].m_obj;
lean_object* v_val_4770_ = stack[3].m_obj;
lean_object* v_k_4771_ = stack[4].m_obj;
uint8_t v_nondep_4772_ = stack[5].m_num;
uint8_t v_kind_4773_ = stack[6].m_num;
lean_object* v___y_4774_ = stack[7].m_obj;
lean_object* v___y_4775_ = stack[8].m_obj;
lean_object* v___y_4776_ = stack[9].m_obj;
lean_object* v___y_4777_ = stack[10].m_obj;
lean_object* v___y_4778_ = stack[11].m_obj;
lean_object* v_res_4781_;
v_res_4781_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9(lean_box(0), v_name_4768_, v_type_4769_, v_val_4770_, v_k_4771_, v_nondep_4772_, v_kind_4773_, v___y_4774_, v___y_4775_, v___y_4776_, v___y_4777_, v___y_4778_);
stack->m_obj
 = v_res_4781_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___boxed(lean_object* v_00_u03b1_4782_, lean_object* v_name_4783_, lean_object* v_type_4784_, lean_object* v_val_4785_, lean_object* v_k_4786_, lean_object* v_nondep_4787_, lean_object* v_kind_4788_, lean_object* v___y_4789_, lean_object* v___y_4790_, lean_object* v___y_4791_, lean_object* v___y_4792_, lean_object* v___y_4793_, lean_object* v___y_4794_){
_start:
{
uint8_t v_nondep_boxed_4795_; uint8_t v_kind_boxed_4796_; lean_object* v_res_4797_; 
v_nondep_boxed_4795_ = lean_unbox(v_nondep_4787_);
v_kind_boxed_4796_ = lean_unbox(v_kind_4788_);
v_res_4797_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9(v_00_u03b1_4782_, v_name_4783_, v_type_4784_, v_val_4785_, v_k_4786_, v_nondep_boxed_4795_, v_kind_boxed_4796_, v___y_4789_, v___y_4790_, v___y_4791_, v___y_4792_, v___y_4793_);
lean_dec(v___y_4793_);
lean_dec_ref(v___y_4792_);
lean_dec(v___y_4791_);
lean_dec_ref(v___y_4790_);
lean_dec(v___y_4789_);
return v_res_4797_;
}
}
lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12(lean_object* v_00_u03b1_4798_, lean_object* v_ref_4799_, lean_object* v___y_4800_, lean_object* v___y_4801_, lean_object* v___y_4802_, lean_object* v___y_4803_){
_start:
{
lean_object* v___x_4805_; 
v___x_4805_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg(v_ref_4799_);
return v___x_4805_;
}
}
LEAN_EXPORT void l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_4799_ = stack[1].m_obj;
lean_object* v___y_4800_ = stack[2].m_obj;
lean_object* v___y_4801_ = stack[3].m_obj;
lean_object* v___y_4802_ = stack[4].m_obj;
lean_object* v___y_4803_ = stack[5].m_obj;
lean_object* v_res_4806_;
v_res_4806_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12(lean_box(0), v_ref_4799_, v___y_4800_, v___y_4801_, v___y_4802_, v___y_4803_);
stack->m_obj
 = v_res_4806_;
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___boxed(lean_object* v_00_u03b1_4807_, lean_object* v_ref_4808_, lean_object* v___y_4809_, lean_object* v___y_4810_, lean_object* v___y_4811_, lean_object* v___y_4812_, lean_object* v___y_4813_){
_start:
{
lean_object* v_res_4814_; 
v_res_4814_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12(v_00_u03b1_4807_, v_ref_4808_, v___y_4809_, v___y_4810_, v___y_4811_, v___y_4812_);
lean_dec(v___y_4812_);
lean_dec_ref(v___y_4811_);
lean_dec(v___y_4810_);
lean_dec_ref(v___y_4809_);
return v_res_4814_;
}
}
lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9(lean_object* v_00_u03b1_4815_, lean_object* v_x_4816_, lean_object* v___y_4817_, lean_object* v___y_4818_, lean_object* v___y_4819_, lean_object* v___y_4820_, lean_object* v___y_4821_){
_start:
{
lean_object* v___x_4823_; 
v___x_4823_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg(v_x_4816_, v___y_4817_, v___y_4818_, v___y_4819_, v___y_4820_, v___y_4821_);
return v___x_4823_;
}
}
LEAN_EXPORT void l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4816_ = stack[1].m_obj;
lean_object* v___y_4817_ = stack[2].m_obj;
lean_object* v___y_4818_ = stack[3].m_obj;
lean_object* v___y_4819_ = stack[4].m_obj;
lean_object* v___y_4820_ = stack[5].m_obj;
lean_object* v___y_4821_ = stack[6].m_obj;
lean_object* v_res_4824_;
v_res_4824_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9(lean_box(0), v_x_4816_, v___y_4817_, v___y_4818_, v___y_4819_, v___y_4820_, v___y_4821_);
stack->m_obj
 = v_res_4824_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___boxed(lean_object* v_00_u03b1_4825_, lean_object* v_x_4826_, lean_object* v___y_4827_, lean_object* v___y_4828_, lean_object* v___y_4829_, lean_object* v___y_4830_, lean_object* v___y_4831_, lean_object* v___y_4832_){
_start:
{
lean_object* v_res_4833_; 
v_res_4833_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9(v_00_u03b1_4825_, v_x_4826_, v___y_4827_, v___y_4828_, v___y_4829_, v___y_4830_, v___y_4831_);
lean_dec(v___y_4831_);
lean_dec_ref(v___y_4830_);
lean_dec(v___y_4829_);
lean_dec_ref(v___y_4828_);
lean_dec(v___y_4827_);
return v_res_4833_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0_spec__0(lean_object* v_a_4834_, lean_object* v_as_4835_, size_t v_i_4836_, size_t v_stop_4837_){
_start:
{
uint8_t v___x_4838_; 
v___x_4838_ = lean_usize_dec_eq(v_i_4836_, v_stop_4837_);
if (v___x_4838_ == 0)
{
lean_object* v___x_4839_; uint8_t v___x_4840_; 
v___x_4839_ = lean_array_uget_borrowed(v_as_4835_, v_i_4836_);
v___x_4840_ = l_Lean_instBEqFVarId_beq(v_a_4834_, v___x_4839_);
if (v___x_4840_ == 0)
{
size_t v___x_4841_; size_t v___x_4842_; 
v___x_4841_ = ((size_t)1ULL);
v___x_4842_ = lean_usize_add(v_i_4836_, v___x_4841_);
v_i_4836_ = v___x_4842_;
goto _start;
}
else
{
return v___x_4840_;
}
}
else
{
uint8_t v___x_4844_; 
v___x_4844_ = 0;
return v___x_4844_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_4834_ = stack[0].m_obj;
lean_object* v_as_4835_ = stack[1].m_obj;
size_t v_i_4836_ = stack[2].m_num;
size_t v_stop_4837_ = stack[3].m_num;
uint8_t v_res_4845_;
v_res_4845_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0_spec__0(v_a_4834_, v_as_4835_, v_i_4836_, v_stop_4837_);
stack->m_num = v_res_4845_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0_spec__0___boxed(lean_object* v_a_4846_, lean_object* v_as_4847_, lean_object* v_i_4848_, lean_object* v_stop_4849_){
_start:
{
size_t v_i_boxed_4850_; size_t v_stop_boxed_4851_; uint8_t v_res_4852_; lean_object* v_r_4853_; 
v_i_boxed_4850_ = lean_unbox_usize(v_i_4848_);
lean_dec(v_i_4848_);
v_stop_boxed_4851_ = lean_unbox_usize(v_stop_4849_);
lean_dec(v_stop_4849_);
v_res_4852_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0_spec__0(v_a_4846_, v_as_4847_, v_i_boxed_4850_, v_stop_boxed_4851_);
lean_dec_ref(v_as_4847_);
lean_dec(v_a_4846_);
v_r_4853_ = lean_box(v_res_4852_);
return v_r_4853_;
}
}
uint8_t l_Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0(lean_object* v_as_4854_, lean_object* v_a_4855_){
_start:
{
lean_object* v___x_4856_; lean_object* v___x_4857_; uint8_t v___x_4858_; 
v___x_4856_ = lean_unsigned_to_nat(0u);
v___x_4857_ = lean_array_get_size(v_as_4854_);
v___x_4858_ = lean_nat_dec_lt(v___x_4856_, v___x_4857_);
if (v___x_4858_ == 0)
{
return v___x_4858_;
}
else
{
if (v___x_4858_ == 0)
{
return v___x_4858_;
}
else
{
size_t v___x_4859_; size_t v___x_4860_; uint8_t v___x_4861_; 
v___x_4859_ = ((size_t)0ULL);
v___x_4860_ = lean_usize_of_nat(v___x_4857_);
v___x_4861_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0_spec__0(v_a_4855_, v_as_4854_, v___x_4859_, v___x_4860_);
return v___x_4861_;
}
}
}
}
LEAN_EXPORT void l_Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_4854_ = stack[0].m_obj;
lean_object* v_a_4855_ = stack[1].m_obj;
uint8_t v_res_4862_;
v_res_4862_ = l_Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0(v_as_4854_, v_a_4855_);
stack->m_num = v_res_4862_;
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0___boxed(lean_object* v_as_4863_, lean_object* v_a_4864_){
_start:
{
uint8_t v_res_4865_; lean_object* v_r_4866_; 
v_res_4865_ = l_Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0(v_as_4863_, v_a_4864_);
lean_dec(v_a_4864_);
lean_dec_ref(v_as_4863_);
v_r_4866_ = lean_box(v_res_4865_);
return v_r_4866_;
}
}
lean_object* l_Lean_Meta_zetaDeltaFVars___lam__1(lean_object* v_fvars_4867_, lean_object* v_e_4868_, lean_object* v___y_4869_, lean_object* v___y_4870_, lean_object* v___y_4871_, lean_object* v___y_4872_){
_start:
{
lean_object* v___x_4877_; 
v___x_4877_ = l_Lean_Expr_getAppFn(v_e_4868_);
if (lean_obj_tag(v___x_4877_) == 1)
{
lean_object* v_fvarId_4878_; uint8_t v___x_4879_; 
v_fvarId_4878_ = lean_ctor_get(v___x_4877_, 0);
lean_inc(v_fvarId_4878_);
lean_dec_ref_known(v___x_4877_, 1);
v___x_4879_ = l_Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0(v_fvars_4867_, v_fvarId_4878_);
if (v___x_4879_ == 0)
{
lean_dec(v_fvarId_4878_);
lean_dec_ref(v_e_4868_);
goto v___jp_4874_;
}
else
{
uint8_t v___x_4880_; lean_object* v___x_4881_; 
v___x_4880_ = 0;
v___x_4881_ = l_Lean_FVarId_getValue_x3f___redArg(v_fvarId_4878_, v___x_4880_, v___y_4869_, v___y_4871_, v___y_4872_);
if (lean_obj_tag(v___x_4881_) == 0)
{
lean_object* v_a_4882_; 
v_a_4882_ = lean_ctor_get(v___x_4881_, 0);
lean_inc(v_a_4882_);
lean_dec_ref_known(v___x_4881_, 1);
if (lean_obj_tag(v_a_4882_) == 1)
{
lean_object* v_val_4883_; lean_object* v___x_4885_; uint8_t v_isShared_4886_; uint8_t v_isSharedCheck_4906_; 
v_val_4883_ = lean_ctor_get(v_a_4882_, 0);
v_isSharedCheck_4906_ = !lean_is_exclusive(v_a_4882_);
if (v_isSharedCheck_4906_ == 0)
{
v___x_4885_ = v_a_4882_;
v_isShared_4886_ = v_isSharedCheck_4906_;
goto v_resetjp_4884_;
}
else
{
lean_inc(v_val_4883_);
lean_dec(v_a_4882_);
v___x_4885_ = lean_box(0);
v_isShared_4886_ = v_isSharedCheck_4906_;
goto v_resetjp_4884_;
}
v_resetjp_4884_:
{
lean_object* v___x_4887_; lean_object* v_a_4888_; lean_object* v___x_4890_; uint8_t v_isShared_4891_; uint8_t v_isSharedCheck_4905_; 
v___x_4887_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(v_val_4883_, v___y_4870_);
v_a_4888_ = lean_ctor_get(v___x_4887_, 0);
v_isSharedCheck_4905_ = !lean_is_exclusive(v___x_4887_);
if (v_isSharedCheck_4905_ == 0)
{
v___x_4890_ = v___x_4887_;
v_isShared_4891_ = v_isSharedCheck_4905_;
goto v_resetjp_4889_;
}
else
{
lean_inc(v_a_4888_);
lean_dec(v___x_4887_);
v___x_4890_ = lean_box(0);
v_isShared_4891_ = v_isSharedCheck_4905_;
goto v_resetjp_4889_;
}
v_resetjp_4889_:
{
lean_object* v_dummy_4892_; lean_object* v_nargs_4893_; lean_object* v___x_4894_; lean_object* v___x_4895_; lean_object* v___x_4896_; lean_object* v___x_4897_; lean_object* v___x_4898_; lean_object* v___x_4900_; 
v_dummy_4892_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_4893_ = l_Lean_Expr_getAppNumArgs(v_e_4868_);
lean_inc(v_nargs_4893_);
v___x_4894_ = lean_mk_array(v_nargs_4893_, v_dummy_4892_);
v___x_4895_ = lean_unsigned_to_nat(1u);
v___x_4896_ = lean_nat_sub(v_nargs_4893_, v___x_4895_);
lean_dec(v_nargs_4893_);
v___x_4897_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_4868_, v___x_4894_, v___x_4896_);
v___x_4898_ = l_Lean_Expr_beta(v_a_4888_, v___x_4897_);
if (v_isShared_4886_ == 0)
{
lean_ctor_set(v___x_4885_, 0, v___x_4898_);
v___x_4900_ = v___x_4885_;
goto v_reusejp_4899_;
}
else
{
lean_object* v_reuseFailAlloc_4904_; 
v_reuseFailAlloc_4904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4904_, 0, v___x_4898_);
v___x_4900_ = v_reuseFailAlloc_4904_;
goto v_reusejp_4899_;
}
v_reusejp_4899_:
{
lean_object* v___x_4902_; 
if (v_isShared_4891_ == 0)
{
lean_ctor_set(v___x_4890_, 0, v___x_4900_);
v___x_4902_ = v___x_4890_;
goto v_reusejp_4901_;
}
else
{
lean_object* v_reuseFailAlloc_4903_; 
v_reuseFailAlloc_4903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4903_, 0, v___x_4900_);
v___x_4902_ = v_reuseFailAlloc_4903_;
goto v_reusejp_4901_;
}
v_reusejp_4901_:
{
return v___x_4902_;
}
}
}
}
}
else
{
lean_dec(v_a_4882_);
lean_dec_ref(v_e_4868_);
goto v___jp_4874_;
}
}
else
{
lean_object* v_a_4907_; lean_object* v___x_4909_; uint8_t v_isShared_4910_; uint8_t v_isSharedCheck_4914_; 
lean_dec_ref(v_e_4868_);
v_a_4907_ = lean_ctor_get(v___x_4881_, 0);
v_isSharedCheck_4914_ = !lean_is_exclusive(v___x_4881_);
if (v_isSharedCheck_4914_ == 0)
{
v___x_4909_ = v___x_4881_;
v_isShared_4910_ = v_isSharedCheck_4914_;
goto v_resetjp_4908_;
}
else
{
lean_inc(v_a_4907_);
lean_dec(v___x_4881_);
v___x_4909_ = lean_box(0);
v_isShared_4910_ = v_isSharedCheck_4914_;
goto v_resetjp_4908_;
}
v_resetjp_4908_:
{
lean_object* v___x_4912_; 
if (v_isShared_4910_ == 0)
{
v___x_4912_ = v___x_4909_;
goto v_reusejp_4911_;
}
else
{
lean_object* v_reuseFailAlloc_4913_; 
v_reuseFailAlloc_4913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4913_, 0, v_a_4907_);
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
}
else
{
lean_object* v___x_4915_; lean_object* v___x_4916_; 
lean_dec_ref(v___x_4877_);
lean_dec_ref(v_e_4868_);
v___x_4915_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_4916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4916_, 0, v___x_4915_);
return v___x_4916_;
}
v___jp_4874_:
{
lean_object* v___x_4875_; lean_object* v___x_4876_; 
v___x_4875_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_4876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4876_, 0, v___x_4875_);
return v___x_4876_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_zetaDeltaFVars___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_4867_ = stack[0].m_obj;
lean_object* v_e_4868_ = stack[1].m_obj;
lean_object* v___y_4869_ = stack[2].m_obj;
lean_object* v___y_4870_ = stack[3].m_obj;
lean_object* v___y_4871_ = stack[4].m_obj;
lean_object* v___y_4872_ = stack[5].m_obj;
lean_object* v_res_4917_;
v_res_4917_ = l_Lean_Meta_zetaDeltaFVars___lam__1(v_fvars_4867_, v_e_4868_, v___y_4869_, v___y_4870_, v___y_4871_, v___y_4872_);
stack->m_obj
 = v_res_4917_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaFVars___lam__1___boxed(lean_object* v_fvars_4918_, lean_object* v_e_4919_, lean_object* v___y_4920_, lean_object* v___y_4921_, lean_object* v___y_4922_, lean_object* v___y_4923_, lean_object* v___y_4924_){
_start:
{
lean_object* v_res_4925_; 
v_res_4925_ = l_Lean_Meta_zetaDeltaFVars___lam__1(v_fvars_4918_, v_e_4919_, v___y_4920_, v___y_4921_, v___y_4922_, v___y_4923_);
lean_dec(v___y_4923_);
lean_dec_ref(v___y_4922_);
lean_dec(v___y_4921_);
lean_dec_ref(v___y_4920_);
lean_dec_ref(v_fvars_4918_);
return v_res_4925_;
}
}
lean_object* l_Lean_Meta_zetaDeltaFVars(lean_object* v_e_4926_, lean_object* v_fvars_4927_, lean_object* v_a_4928_, lean_object* v_a_4929_, lean_object* v_a_4930_, lean_object* v_a_4931_){
_start:
{
lean_object* v___f_4933_; lean_object* v_pre_4934_; uint8_t v___x_4935_; lean_object* v___x_4936_; 
v___f_4933_ = ((lean_object*)(l_Lean_Meta_zetaReduce___closed__0));
v_pre_4934_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaDeltaFVars___lam__1___boxed), 7, 1);
lean_closure_set(v_pre_4934_, 0, v_fvars_4927_);
v___x_4935_ = 0;
v___x_4936_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(v_e_4926_, v_pre_4934_, v___f_4933_, v___x_4935_, v___x_4935_, v_a_4928_, v_a_4929_, v_a_4930_, v_a_4931_);
return v___x_4936_;
}
}
LEAN_EXPORT void l_Lean_Meta_zetaDeltaFVars_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4926_ = stack[0].m_obj;
lean_object* v_fvars_4927_ = stack[1].m_obj;
lean_object* v_a_4928_ = stack[2].m_obj;
lean_object* v_a_4929_ = stack[3].m_obj;
lean_object* v_a_4930_ = stack[4].m_obj;
lean_object* v_a_4931_ = stack[5].m_obj;
lean_object* v_res_4937_;
v_res_4937_ = l_Lean_Meta_zetaDeltaFVars(v_e_4926_, v_fvars_4927_, v_a_4928_, v_a_4929_, v_a_4930_, v_a_4931_);
stack->m_obj
 = v_res_4937_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaFVars___boxed(lean_object* v_e_4938_, lean_object* v_fvars_4939_, lean_object* v_a_4940_, lean_object* v_a_4941_, lean_object* v_a_4942_, lean_object* v_a_4943_, lean_object* v_a_4944_){
_start:
{
lean_object* v_res_4945_; 
v_res_4945_ = l_Lean_Meta_zetaDeltaFVars(v_e_4938_, v_fvars_4939_, v_a_4940_, v_a_4941_, v_a_4942_, v_a_4943_);
lean_dec(v_a_4943_);
lean_dec_ref(v_a_4942_);
lean_dec(v_a_4941_);
lean_dec_ref(v_a_4940_);
return v_res_4945_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_4946_; 
v___x_4946_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_4946_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_4947_; lean_object* v___x_4948_; 
v___x_4947_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__0, &l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__0);
v___x_4948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4948_, 0, v___x_4947_);
return v___x_4948_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_4949_; lean_object* v___x_4950_; 
v___x_4949_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__1, &l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__1);
v___x_4950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4950_, 0, v___x_4949_);
lean_ctor_set(v___x_4950_, 1, v___x_4949_);
return v___x_4950_;
}
}
lean_object* l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(lean_object* v_env_4951_, lean_object* v___y_4952_){
_start:
{
lean_object* v___x_4954_; lean_object* v_nextMacroScope_4955_; lean_object* v_ngen_4956_; lean_object* v_auxDeclNGen_4957_; lean_object* v_traceState_4958_; lean_object* v_recordedDeps_4959_; lean_object* v_messages_4960_; lean_object* v_infoState_4961_; lean_object* v_snapshotTasks_4962_; lean_object* v___x_4964_; uint8_t v_isShared_4965_; uint8_t v_isSharedCheck_4973_; 
v___x_4954_ = lean_st_ref_take(v___y_4952_);
v_nextMacroScope_4955_ = lean_ctor_get(v___x_4954_, 1);
v_ngen_4956_ = lean_ctor_get(v___x_4954_, 2);
v_auxDeclNGen_4957_ = lean_ctor_get(v___x_4954_, 3);
v_traceState_4958_ = lean_ctor_get(v___x_4954_, 4);
v_recordedDeps_4959_ = lean_ctor_get(v___x_4954_, 6);
v_messages_4960_ = lean_ctor_get(v___x_4954_, 7);
v_infoState_4961_ = lean_ctor_get(v___x_4954_, 8);
v_snapshotTasks_4962_ = lean_ctor_get(v___x_4954_, 9);
v_isSharedCheck_4973_ = !lean_is_exclusive(v___x_4954_);
if (v_isSharedCheck_4973_ == 0)
{
lean_object* v_unused_4974_; lean_object* v_unused_4975_; 
v_unused_4974_ = lean_ctor_get(v___x_4954_, 5);
lean_dec(v_unused_4974_);
v_unused_4975_ = lean_ctor_get(v___x_4954_, 0);
lean_dec(v_unused_4975_);
v___x_4964_ = v___x_4954_;
v_isShared_4965_ = v_isSharedCheck_4973_;
goto v_resetjp_4963_;
}
else
{
lean_inc(v_snapshotTasks_4962_);
lean_inc(v_infoState_4961_);
lean_inc(v_messages_4960_);
lean_inc(v_recordedDeps_4959_);
lean_inc(v_traceState_4958_);
lean_inc(v_auxDeclNGen_4957_);
lean_inc(v_ngen_4956_);
lean_inc(v_nextMacroScope_4955_);
lean_dec(v___x_4954_);
v___x_4964_ = lean_box(0);
v_isShared_4965_ = v_isSharedCheck_4973_;
goto v_resetjp_4963_;
}
v_resetjp_4963_:
{
lean_object* v___x_4966_; lean_object* v___x_4967_; lean_object* v___x_4969_; 
v___x_4966_ = lean_box(0);
v___x_4967_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2, &l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2);
if (v_isShared_4965_ == 0)
{
lean_ctor_set(v___x_4964_, 5, v___x_4967_);
lean_ctor_set(v___x_4964_, 0, v_env_4951_);
v___x_4969_ = v___x_4964_;
goto v_reusejp_4968_;
}
else
{
lean_object* v_reuseFailAlloc_4972_; 
v_reuseFailAlloc_4972_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4972_, 0, v_env_4951_);
lean_ctor_set(v_reuseFailAlloc_4972_, 1, v_nextMacroScope_4955_);
lean_ctor_set(v_reuseFailAlloc_4972_, 2, v_ngen_4956_);
lean_ctor_set(v_reuseFailAlloc_4972_, 3, v_auxDeclNGen_4957_);
lean_ctor_set(v_reuseFailAlloc_4972_, 4, v_traceState_4958_);
lean_ctor_set(v_reuseFailAlloc_4972_, 5, v___x_4967_);
lean_ctor_set(v_reuseFailAlloc_4972_, 6, v_recordedDeps_4959_);
lean_ctor_set(v_reuseFailAlloc_4972_, 7, v_messages_4960_);
lean_ctor_set(v_reuseFailAlloc_4972_, 8, v_infoState_4961_);
lean_ctor_set(v_reuseFailAlloc_4972_, 9, v_snapshotTasks_4962_);
v___x_4969_ = v_reuseFailAlloc_4972_;
goto v_reusejp_4968_;
}
v_reusejp_4968_:
{
lean_object* v___x_4970_; lean_object* v___x_4971_; 
v___x_4970_ = lean_st_ref_put(v___y_4952_, v___x_4969_);
v___x_4971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4971_, 0, v___x_4966_);
return v___x_4971_;
}
}
}
}
LEAN_EXPORT void l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_4951_ = stack[0].m_obj;
lean_object* v___y_4952_ = stack[1].m_obj;
lean_object* v_res_4976_;
v_res_4976_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_4951_, v___y_4952_);
stack->m_obj
 = v_res_4976_;
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___boxed(lean_object* v_env_4977_, lean_object* v___y_4978_, lean_object* v___y_4979_){
_start:
{
lean_object* v_res_4980_; 
v_res_4980_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_4977_, v___y_4978_);
lean_dec(v___y_4978_);
return v_res_4980_;
}
}
lean_object* l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0(lean_object* v_env_4981_, lean_object* v___y_4982_, lean_object* v___y_4983_){
_start:
{
lean_object* v___x_4985_; 
v___x_4985_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_4981_, v___y_4983_);
return v___x_4985_;
}
}
LEAN_EXPORT void l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_4981_ = stack[0].m_obj;
lean_object* v___y_4982_ = stack[1].m_obj;
lean_object* v___y_4983_ = stack[2].m_obj;
lean_object* v_res_4986_;
v_res_4986_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0(v_env_4981_, v___y_4982_, v___y_4983_);
stack->m_obj
 = v_res_4986_;
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___boxed(lean_object* v_env_4987_, lean_object* v___y_4988_, lean_object* v___y_4989_, lean_object* v___y_4990_){
_start:
{
lean_object* v_res_4991_; 
v_res_4991_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0(v_env_4987_, v___y_4988_, v___y_4989_);
lean_dec(v___y_4989_);
lean_dec_ref(v___y_4988_);
return v_res_4991_;
}
}
lean_object* l_Lean_Meta_unfoldDeclsFrom___lam__1(lean_object* v_env_4992_, lean_object* v___x_4993_, uint8_t v___x_4994_, lean_object* v_e_4995_, lean_object* v___y_4996_, lean_object* v___y_4997_){
_start:
{
if (lean_obj_tag(v_e_4995_) == 4)
{
lean_object* v_declName_4999_; lean_object* v_us_5000_; uint8_t v___x_5001_; uint8_t v___x_5002_; 
v_declName_4999_ = lean_ctor_get(v_e_4995_, 0);
v_us_5000_ = lean_ctor_get(v_e_4995_, 1);
v___x_5001_ = 1;
lean_inc(v_declName_4999_);
v___x_5002_ = l_Lean_Environment_contains(v_env_4992_, v_declName_4999_, v___x_5001_);
if (v___x_5002_ == 0)
{
lean_object* v___x_5003_; 
lean_inc(v_declName_4999_);
v___x_5003_ = l_Lean_Environment_find_x3f(v___x_4993_, v_declName_4999_, v___x_4994_);
if (lean_obj_tag(v___x_5003_) == 1)
{
lean_object* v_val_5004_; lean_object* v___x_5006_; uint8_t v_isShared_5007_; uint8_t v_isSharedCheck_5033_; 
v_val_5004_ = lean_ctor_get(v___x_5003_, 0);
v_isSharedCheck_5033_ = !lean_is_exclusive(v___x_5003_);
if (v_isSharedCheck_5033_ == 0)
{
v___x_5006_ = v___x_5003_;
v_isShared_5007_ = v_isSharedCheck_5033_;
goto v_resetjp_5005_;
}
else
{
lean_inc(v_val_5004_);
lean_dec(v___x_5003_);
v___x_5006_ = lean_box(0);
v_isShared_5007_ = v_isSharedCheck_5033_;
goto v_resetjp_5005_;
}
v_resetjp_5005_:
{
uint8_t v___x_5008_; 
v___x_5008_ = l_Lean_ConstantInfo_hasValue(v_val_5004_, v___x_5001_);
if (v___x_5008_ == 0)
{
lean_object* v___x_5010_; 
lean_dec(v_val_5004_);
if (v_isShared_5007_ == 0)
{
lean_ctor_set_tag(v___x_5006_, 0);
lean_ctor_set(v___x_5006_, 0, v_e_4995_);
v___x_5010_ = v___x_5006_;
goto v_reusejp_5009_;
}
else
{
lean_object* v_reuseFailAlloc_5012_; 
v_reuseFailAlloc_5012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5012_, 0, v_e_4995_);
v___x_5010_ = v_reuseFailAlloc_5012_;
goto v_reusejp_5009_;
}
v_reusejp_5009_:
{
lean_object* v___x_5011_; 
v___x_5011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5011_, 0, v___x_5010_);
return v___x_5011_;
}
}
else
{
lean_object* v___x_5013_; 
lean_inc(v_us_5000_);
lean_dec_ref_known(v_e_4995_, 2);
v___x_5013_ = l_Lean_Core_instantiateValueLevelParams(v_val_5004_, v_us_5000_, v___x_5001_, v___y_4996_, v___y_4997_);
lean_dec(v_val_5004_);
if (lean_obj_tag(v___x_5013_) == 0)
{
lean_object* v_a_5014_; lean_object* v___x_5016_; uint8_t v_isShared_5017_; uint8_t v_isSharedCheck_5024_; 
v_a_5014_ = lean_ctor_get(v___x_5013_, 0);
v_isSharedCheck_5024_ = !lean_is_exclusive(v___x_5013_);
if (v_isSharedCheck_5024_ == 0)
{
v___x_5016_ = v___x_5013_;
v_isShared_5017_ = v_isSharedCheck_5024_;
goto v_resetjp_5015_;
}
else
{
lean_inc(v_a_5014_);
lean_dec(v___x_5013_);
v___x_5016_ = lean_box(0);
v_isShared_5017_ = v_isSharedCheck_5024_;
goto v_resetjp_5015_;
}
v_resetjp_5015_:
{
lean_object* v___x_5019_; 
if (v_isShared_5007_ == 0)
{
lean_ctor_set(v___x_5006_, 0, v_a_5014_);
v___x_5019_ = v___x_5006_;
goto v_reusejp_5018_;
}
else
{
lean_object* v_reuseFailAlloc_5023_; 
v_reuseFailAlloc_5023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5023_, 0, v_a_5014_);
v___x_5019_ = v_reuseFailAlloc_5023_;
goto v_reusejp_5018_;
}
v_reusejp_5018_:
{
lean_object* v___x_5021_; 
if (v_isShared_5017_ == 0)
{
lean_ctor_set(v___x_5016_, 0, v___x_5019_);
v___x_5021_ = v___x_5016_;
goto v_reusejp_5020_;
}
else
{
lean_object* v_reuseFailAlloc_5022_; 
v_reuseFailAlloc_5022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5022_, 0, v___x_5019_);
v___x_5021_ = v_reuseFailAlloc_5022_;
goto v_reusejp_5020_;
}
v_reusejp_5020_:
{
return v___x_5021_;
}
}
}
}
else
{
lean_object* v_a_5025_; lean_object* v___x_5027_; uint8_t v_isShared_5028_; uint8_t v_isSharedCheck_5032_; 
lean_del_object(v___x_5006_);
v_a_5025_ = lean_ctor_get(v___x_5013_, 0);
v_isSharedCheck_5032_ = !lean_is_exclusive(v___x_5013_);
if (v_isSharedCheck_5032_ == 0)
{
v___x_5027_ = v___x_5013_;
v_isShared_5028_ = v_isSharedCheck_5032_;
goto v_resetjp_5026_;
}
else
{
lean_inc(v_a_5025_);
lean_dec(v___x_5013_);
v___x_5027_ = lean_box(0);
v_isShared_5028_ = v_isSharedCheck_5032_;
goto v_resetjp_5026_;
}
v_resetjp_5026_:
{
lean_object* v___x_5030_; 
if (v_isShared_5028_ == 0)
{
v___x_5030_ = v___x_5027_;
goto v_reusejp_5029_;
}
else
{
lean_object* v_reuseFailAlloc_5031_; 
v_reuseFailAlloc_5031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5031_, 0, v_a_5025_);
v___x_5030_ = v_reuseFailAlloc_5031_;
goto v_reusejp_5029_;
}
v_reusejp_5029_:
{
return v___x_5030_;
}
}
}
}
}
}
else
{
lean_object* v___x_5034_; lean_object* v___x_5035_; 
lean_dec(v___x_5003_);
v___x_5034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5034_, 0, v_e_4995_);
v___x_5035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5035_, 0, v___x_5034_);
return v___x_5035_;
}
}
else
{
lean_object* v___x_5036_; lean_object* v___x_5037_; 
lean_dec_ref(v___x_4993_);
v___x_5036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5036_, 0, v_e_4995_);
v___x_5037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5037_, 0, v___x_5036_);
return v___x_5037_;
}
}
else
{
lean_object* v___x_5038_; lean_object* v___x_5039_; 
lean_dec_ref(v_e_4995_);
lean_dec_ref(v___x_4993_);
lean_dec_ref(v_env_4992_);
v___x_5038_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_5039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5039_, 0, v___x_5038_);
return v___x_5039_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_unfoldDeclsFrom___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_4992_ = stack[0].m_obj;
lean_object* v___x_4993_ = stack[1].m_obj;
uint8_t v___x_4994_ = stack[2].m_num;
lean_object* v_e_4995_ = stack[3].m_obj;
lean_object* v___y_4996_ = stack[4].m_obj;
lean_object* v___y_4997_ = stack[5].m_obj;
lean_object* v_res_5040_;
v_res_5040_ = l_Lean_Meta_unfoldDeclsFrom___lam__1(v_env_4992_, v___x_4993_, v___x_4994_, v_e_4995_, v___y_4996_, v___y_4997_);
stack->m_obj
 = v_res_5040_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___lam__1___boxed(lean_object* v_env_5041_, lean_object* v___x_5042_, lean_object* v___x_5043_, lean_object* v_e_5044_, lean_object* v___y_5045_, lean_object* v___y_5046_, lean_object* v___y_5047_){
_start:
{
uint8_t v___x_2029__boxed_5048_; lean_object* v_res_5049_; 
v___x_2029__boxed_5048_ = lean_unbox(v___x_5043_);
v_res_5049_ = l_Lean_Meta_unfoldDeclsFrom___lam__1(v_env_5041_, v___x_5042_, v___x_2029__boxed_5048_, v_e_5044_, v___y_5045_, v___y_5046_);
lean_dec(v___y_5046_);
lean_dec_ref(v___y_5045_);
return v_res_5049_;
}
}
lean_object* l_Lean_Meta_unfoldDeclsFrom___lam__0(lean_object* v_biggerEnv_5050_, lean_object* v_e_5051_, lean_object* v___f_5052_, lean_object* v___y_5053_, lean_object* v___y_5054_){
_start:
{
lean_object* v___x_5056_; lean_object* v_env_5057_; uint8_t v___x_5058_; lean_object* v___x_5059_; lean_object* v___x_5060_; lean_object* v___f_5061_; lean_object* v___x_5062_; lean_object* v___x_5063_; 
v___x_5056_ = lean_st_ref_get(v___y_5054_);
v_env_5057_ = lean_ctor_get(v___x_5056_, 0);
lean_inc_ref(v_env_5057_);
lean_dec(v___x_5056_);
v___x_5058_ = 0;
v___x_5059_ = l_Lean_Environment_setExporting(v_biggerEnv_5050_, v___x_5058_);
v___x_5060_ = lean_box(v___x_5058_);
lean_inc_ref(v___x_5059_);
v___f_5061_ = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDeclsFrom___lam__1___boxed), 7, 3);
lean_closure_set(v___f_5061_, 0, v_env_5057_);
lean_closure_set(v___f_5061_, 1, v___x_5059_);
lean_closure_set(v___f_5061_, 2, v___x_5060_);
v___x_5062_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v___x_5059_, v___y_5054_);
lean_dec_ref(v___x_5062_);
v___x_5063_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_5051_, v___f_5061_, v___f_5052_, v___y_5053_, v___y_5054_);
return v___x_5063_;
}
}
LEAN_EXPORT void l_Lean_Meta_unfoldDeclsFrom___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_biggerEnv_5050_ = stack[0].m_obj;
lean_object* v_e_5051_ = stack[1].m_obj;
lean_object* v___f_5052_ = stack[2].m_obj;
lean_object* v___y_5053_ = stack[3].m_obj;
lean_object* v___y_5054_ = stack[4].m_obj;
lean_object* v_res_5064_;
v_res_5064_ = l_Lean_Meta_unfoldDeclsFrom___lam__0(v_biggerEnv_5050_, v_e_5051_, v___f_5052_, v___y_5053_, v___y_5054_);
stack->m_obj
 = v_res_5064_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___lam__0___boxed(lean_object* v_biggerEnv_5065_, lean_object* v_e_5066_, lean_object* v___f_5067_, lean_object* v___y_5068_, lean_object* v___y_5069_, lean_object* v___y_5070_){
_start:
{
lean_object* v_res_5071_; 
v_res_5071_ = l_Lean_Meta_unfoldDeclsFrom___lam__0(v_biggerEnv_5065_, v_e_5066_, v___f_5067_, v___y_5068_, v___y_5069_);
lean_dec(v___y_5069_);
lean_dec_ref(v___y_5068_);
return v_res_5071_;
}
}
lean_object* l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg(lean_object* v_env_5072_, lean_object* v_x_5073_, lean_object* v___y_5074_, lean_object* v___y_5075_){
_start:
{
lean_object* v___x_5077_; lean_object* v_env_5078_; lean_object* v_a_5080_; lean_object* v___x_5090_; lean_object* v___x_5091_; 
v___x_5077_ = lean_st_ref_get(v___y_5075_);
v_env_5078_ = lean_ctor_get(v___x_5077_, 0);
lean_inc_ref(v_env_5078_);
lean_dec(v___x_5077_);
v___x_5090_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_5072_, v___y_5075_);
lean_dec_ref(v___x_5090_);
lean_inc(v___y_5075_);
lean_inc_ref(v___y_5074_);
v___x_5091_ = lean_apply_3(v_x_5073_, v___y_5074_, v___y_5075_, lean_box(0));
if (lean_obj_tag(v___x_5091_) == 0)
{
lean_object* v_a_5092_; lean_object* v___x_5093_; lean_object* v___x_5095_; uint8_t v_isShared_5096_; uint8_t v_isSharedCheck_5100_; 
v_a_5092_ = lean_ctor_get(v___x_5091_, 0);
lean_inc(v_a_5092_);
lean_dec_ref_known(v___x_5091_, 1);
v___x_5093_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_5078_, v___y_5075_);
v_isSharedCheck_5100_ = !lean_is_exclusive(v___x_5093_);
if (v_isSharedCheck_5100_ == 0)
{
lean_object* v_unused_5101_; 
v_unused_5101_ = lean_ctor_get(v___x_5093_, 0);
lean_dec(v_unused_5101_);
v___x_5095_ = v___x_5093_;
v_isShared_5096_ = v_isSharedCheck_5100_;
goto v_resetjp_5094_;
}
else
{
lean_dec(v___x_5093_);
v___x_5095_ = lean_box(0);
v_isShared_5096_ = v_isSharedCheck_5100_;
goto v_resetjp_5094_;
}
v_resetjp_5094_:
{
lean_object* v___x_5098_; 
if (v_isShared_5096_ == 0)
{
lean_ctor_set(v___x_5095_, 0, v_a_5092_);
v___x_5098_ = v___x_5095_;
goto v_reusejp_5097_;
}
else
{
lean_object* v_reuseFailAlloc_5099_; 
v_reuseFailAlloc_5099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5099_, 0, v_a_5092_);
v___x_5098_ = v_reuseFailAlloc_5099_;
goto v_reusejp_5097_;
}
v_reusejp_5097_:
{
return v___x_5098_;
}
}
}
else
{
lean_object* v_a_5102_; 
v_a_5102_ = lean_ctor_get(v___x_5091_, 0);
lean_inc(v_a_5102_);
lean_dec_ref_known(v___x_5091_, 1);
v_a_5080_ = v_a_5102_;
goto v___jp_5079_;
}
v___jp_5079_:
{
lean_object* v___x_5081_; lean_object* v___x_5083_; uint8_t v_isShared_5084_; uint8_t v_isSharedCheck_5088_; 
v___x_5081_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_5078_, v___y_5075_);
v_isSharedCheck_5088_ = !lean_is_exclusive(v___x_5081_);
if (v_isSharedCheck_5088_ == 0)
{
lean_object* v_unused_5089_; 
v_unused_5089_ = lean_ctor_get(v___x_5081_, 0);
lean_dec(v_unused_5089_);
v___x_5083_ = v___x_5081_;
v_isShared_5084_ = v_isSharedCheck_5088_;
goto v_resetjp_5082_;
}
else
{
lean_dec(v___x_5081_);
v___x_5083_ = lean_box(0);
v_isShared_5084_ = v_isSharedCheck_5088_;
goto v_resetjp_5082_;
}
v_resetjp_5082_:
{
lean_object* v___x_5086_; 
if (v_isShared_5084_ == 0)
{
lean_ctor_set_tag(v___x_5083_, 1);
lean_ctor_set(v___x_5083_, 0, v_a_5080_);
v___x_5086_ = v___x_5083_;
goto v_reusejp_5085_;
}
else
{
lean_object* v_reuseFailAlloc_5087_; 
v_reuseFailAlloc_5087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5087_, 0, v_a_5080_);
v___x_5086_ = v_reuseFailAlloc_5087_;
goto v_reusejp_5085_;
}
v_reusejp_5085_:
{
return v___x_5086_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_5072_ = stack[0].m_obj;
lean_object* v_x_5073_ = stack[1].m_obj;
lean_object* v___y_5074_ = stack[2].m_obj;
lean_object* v___y_5075_ = stack[3].m_obj;
lean_object* v_res_5103_;
v_res_5103_ = l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg(v_env_5072_, v_x_5073_, v___y_5074_, v___y_5075_);
stack->m_obj
 = v_res_5103_;
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg___boxed(lean_object* v_env_5104_, lean_object* v_x_5105_, lean_object* v___y_5106_, lean_object* v___y_5107_, lean_object* v___y_5108_){
_start:
{
lean_object* v_res_5109_; 
v_res_5109_ = l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg(v_env_5104_, v_x_5105_, v___y_5106_, v___y_5107_);
lean_dec(v___y_5107_);
lean_dec_ref(v___y_5106_);
return v_res_5109_;
}
}
lean_object* l_Lean_Meta_unfoldDeclsFrom(lean_object* v_biggerEnv_5110_, lean_object* v_e_5111_, lean_object* v_a_5112_, lean_object* v_a_5113_){
_start:
{
lean_object* v___f_5115_; lean_object* v___f_5116_; lean_object* v___x_5117_; lean_object* v_env_5118_; lean_object* v___x_5119_; lean_object* v___x_5120_; 
v___f_5115_ = ((lean_object*)(l_Lean_Core_betaReduce___closed__1));
v___f_5116_ = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDeclsFrom___lam__0___boxed), 6, 3);
lean_closure_set(v___f_5116_, 0, v_biggerEnv_5110_);
lean_closure_set(v___f_5116_, 1, v_e_5111_);
lean_closure_set(v___f_5116_, 2, v___f_5115_);
v___x_5117_ = lean_st_ref_get(v_a_5113_);
v_env_5118_ = lean_ctor_get(v___x_5117_, 0);
lean_inc_ref(v_env_5118_);
lean_dec(v___x_5117_);
v___x_5119_ = l_Lean_Environment_unlockAsync(v_env_5118_);
v___x_5120_ = l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg(v___x_5119_, v___f_5116_, v_a_5112_, v_a_5113_);
return v___x_5120_;
}
}
LEAN_EXPORT void l_Lean_Meta_unfoldDeclsFrom_0interp(lean_interpreter_value* stack)
{
lean_object* v_biggerEnv_5110_ = stack[0].m_obj;
lean_object* v_e_5111_ = stack[1].m_obj;
lean_object* v_a_5112_ = stack[2].m_obj;
lean_object* v_a_5113_ = stack[3].m_obj;
lean_object* v_res_5121_;
v_res_5121_ = l_Lean_Meta_unfoldDeclsFrom(v_biggerEnv_5110_, v_e_5111_, v_a_5112_, v_a_5113_);
stack->m_obj
 = v_res_5121_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___boxed(lean_object* v_biggerEnv_5122_, lean_object* v_e_5123_, lean_object* v_a_5124_, lean_object* v_a_5125_, lean_object* v_a_5126_){
_start:
{
lean_object* v_res_5127_; 
v_res_5127_ = l_Lean_Meta_unfoldDeclsFrom(v_biggerEnv_5122_, v_e_5123_, v_a_5124_, v_a_5125_);
lean_dec(v_a_5125_);
lean_dec_ref(v_a_5124_);
return v_res_5127_;
}
}
lean_object* l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1(lean_object* v_00_u03b1_5128_, lean_object* v_env_5129_, lean_object* v_x_5130_, lean_object* v___y_5131_, lean_object* v___y_5132_){
_start:
{
lean_object* v___x_5134_; 
v___x_5134_ = l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg(v_env_5129_, v_x_5130_, v___y_5131_, v___y_5132_);
return v___x_5134_;
}
}
LEAN_EXPORT void l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_5129_ = stack[1].m_obj;
lean_object* v_x_5130_ = stack[2].m_obj;
lean_object* v___y_5131_ = stack[3].m_obj;
lean_object* v___y_5132_ = stack[4].m_obj;
lean_object* v_res_5135_;
v_res_5135_ = l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1(lean_box(0), v_env_5129_, v_x_5130_, v___y_5131_, v___y_5132_);
stack->m_obj
 = v_res_5135_;
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___boxed(lean_object* v_00_u03b1_5136_, lean_object* v_env_5137_, lean_object* v_x_5138_, lean_object* v___y_5139_, lean_object* v___y_5140_, lean_object* v___y_5141_){
_start:
{
lean_object* v_res_5142_; 
v_res_5142_ = l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1(v_00_u03b1_5136_, v_env_5137_, v_x_5138_, v___y_5139_, v___y_5140_);
lean_dec(v___y_5140_);
lean_dec_ref(v___y_5139_);
return v_res_5142_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0(lean_object* v_af_5143_, lean_object* v_axs_5144_, lean_object* v_numSectionVars_5145_, lean_object* v_as_5146_, size_t v_i_5147_, size_t v_stop_5148_){
_start:
{
uint8_t v___x_5149_; 
v___x_5149_ = lean_usize_dec_eq(v_i_5147_, v_stop_5148_);
if (v___x_5149_ == 0)
{
uint8_t v___x_5150_; uint8_t v___y_5152_; lean_object* v___x_5156_; lean_object* v___x_5157_; uint8_t v___x_5158_; 
v___x_5150_ = 1;
v___x_5156_ = lean_array_uget_borrowed(v_as_5146_, v_i_5147_);
v___x_5157_ = l_Lean_Expr_constName_x21(v_af_5143_);
v___x_5158_ = lean_name_eq(v___x_5157_, v___x_5156_);
lean_dec(v___x_5157_);
if (v___x_5158_ == 0)
{
v___y_5152_ = v___x_5158_;
goto v___jp_5151_;
}
else
{
lean_object* v___x_5159_; uint8_t v___x_5160_; 
v___x_5159_ = lean_array_get_size(v_axs_5144_);
v___x_5160_ = lean_nat_dec_le(v___x_5159_, v_numSectionVars_5145_);
v___y_5152_ = v___x_5160_;
goto v___jp_5151_;
}
v___jp_5151_:
{
if (v___y_5152_ == 0)
{
size_t v___x_5153_; size_t v___x_5154_; 
v___x_5153_ = ((size_t)1ULL);
v___x_5154_ = lean_usize_add(v_i_5147_, v___x_5153_);
v_i_5147_ = v___x_5154_;
goto _start;
}
else
{
return v___x_5150_;
}
}
}
else
{
uint8_t v___x_5161_; 
v___x_5161_ = 0;
return v___x_5161_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_af_5143_ = stack[0].m_obj;
lean_object* v_axs_5144_ = stack[1].m_obj;
lean_object* v_numSectionVars_5145_ = stack[2].m_obj;
lean_object* v_as_5146_ = stack[3].m_obj;
size_t v_i_5147_ = stack[4].m_num;
size_t v_stop_5148_ = stack[5].m_num;
uint8_t v_res_5162_;
v_res_5162_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0(v_af_5143_, v_axs_5144_, v_numSectionVars_5145_, v_as_5146_, v_i_5147_, v_stop_5148_);
stack->m_num = v_res_5162_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0___boxed(lean_object* v_af_5163_, lean_object* v_axs_5164_, lean_object* v_numSectionVars_5165_, lean_object* v_as_5166_, lean_object* v_i_5167_, lean_object* v_stop_5168_){
_start:
{
size_t v_i_boxed_5169_; size_t v_stop_boxed_5170_; uint8_t v_res_5171_; lean_object* v_r_5172_; 
v_i_boxed_5169_ = lean_unbox_usize(v_i_5167_);
lean_dec(v_i_5167_);
v_stop_boxed_5170_ = lean_unbox_usize(v_stop_5168_);
lean_dec(v_stop_5168_);
v_res_5171_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0(v_af_5163_, v_axs_5164_, v_numSectionVars_5165_, v_as_5166_, v_i_boxed_5169_, v_stop_boxed_5170_);
lean_dec_ref(v_as_5166_);
lean_dec(v_numSectionVars_5165_);
lean_dec_ref(v_axs_5164_);
lean_dec_ref(v_af_5163_);
v_r_5172_ = lean_box(v_res_5171_);
return v_r_5172_;
}
}
uint8_t l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1_spec__1(lean_object* v_fnNames_5173_, lean_object* v_numSectionVars_5174_, lean_object* v_x_5175_, lean_object* v_x_5176_, lean_object* v_x_5177_){
_start:
{
if (lean_obj_tag(v_x_5175_) == 5)
{
lean_object* v_fn_5178_; lean_object* v_arg_5179_; lean_object* v___x_5180_; lean_object* v___x_5181_; lean_object* v___x_5182_; 
v_fn_5178_ = lean_ctor_get(v_x_5175_, 0);
lean_inc_ref(v_fn_5178_);
v_arg_5179_ = lean_ctor_get(v_x_5175_, 1);
lean_inc_ref(v_arg_5179_);
lean_dec_ref_known(v_x_5175_, 2);
v___x_5180_ = lean_array_set(v_x_5176_, v_x_5177_, v_arg_5179_);
v___x_5181_ = lean_unsigned_to_nat(1u);
v___x_5182_ = lean_nat_sub(v_x_5177_, v___x_5181_);
lean_dec(v_x_5177_);
v_x_5175_ = v_fn_5178_;
v_x_5176_ = v___x_5180_;
v_x_5177_ = v___x_5182_;
goto _start;
}
else
{
uint8_t v___x_5184_; 
lean_dec(v_x_5177_);
v___x_5184_ = l_Lean_Expr_isConst(v_x_5175_);
if (v___x_5184_ == 0)
{
lean_dec_ref(v_x_5176_);
lean_dec_ref(v_x_5175_);
return v___x_5184_;
}
else
{
lean_object* v___x_5185_; lean_object* v___x_5186_; uint8_t v___x_5187_; 
v___x_5185_ = lean_unsigned_to_nat(0u);
v___x_5186_ = lean_array_get_size(v_fnNames_5173_);
v___x_5187_ = lean_nat_dec_lt(v___x_5185_, v___x_5186_);
if (v___x_5187_ == 0)
{
lean_dec_ref(v_x_5176_);
lean_dec_ref(v_x_5175_);
return v___x_5187_;
}
else
{
if (v___x_5187_ == 0)
{
lean_dec_ref(v_x_5176_);
lean_dec_ref(v_x_5175_);
return v___x_5187_;
}
else
{
size_t v___x_5188_; size_t v___x_5189_; uint8_t v___x_5190_; 
v___x_5188_ = ((size_t)0ULL);
v___x_5189_ = lean_usize_of_nat(v___x_5186_);
v___x_5190_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0(v_x_5175_, v_x_5176_, v_numSectionVars_5174_, v_fnNames_5173_, v___x_5188_, v___x_5189_);
lean_dec_ref(v_x_5176_);
lean_dec_ref(v_x_5175_);
return v___x_5190_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_fnNames_5173_ = stack[0].m_obj;
lean_object* v_numSectionVars_5174_ = stack[1].m_obj;
lean_object* v_x_5175_ = stack[2].m_obj;
lean_object* v_x_5176_ = stack[3].m_obj;
lean_object* v_x_5177_ = stack[4].m_obj;
uint8_t v_res_5191_;
v_res_5191_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1_spec__1(v_fnNames_5173_, v_numSectionVars_5174_, v_x_5175_, v_x_5176_, v_x_5177_);
stack->m_num = v_res_5191_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1_spec__1___boxed(lean_object* v_fnNames_5192_, lean_object* v_numSectionVars_5193_, lean_object* v_x_5194_, lean_object* v_x_5195_, lean_object* v_x_5196_){
_start:
{
uint8_t v_res_5197_; lean_object* v_r_5198_; 
v_res_5197_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1_spec__1(v_fnNames_5192_, v_numSectionVars_5193_, v_x_5194_, v_x_5195_, v_x_5196_);
lean_dec(v_numSectionVars_5193_);
lean_dec_ref(v_fnNames_5192_);
v_r_5198_ = lean_box(v_res_5197_);
return v_r_5198_;
}
}
uint8_t l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1(lean_object* v_numSectionVars_5199_, lean_object* v_fnNames_5200_, lean_object* v_x_5201_, lean_object* v_x_5202_, lean_object* v_x_5203_){
_start:
{
if (lean_obj_tag(v_x_5201_) == 5)
{
lean_object* v_fn_5204_; lean_object* v_arg_5205_; lean_object* v___x_5206_; lean_object* v___x_5207_; lean_object* v___x_5208_; uint8_t v___x_5209_; 
v_fn_5204_ = lean_ctor_get(v_x_5201_, 0);
lean_inc_ref(v_fn_5204_);
v_arg_5205_ = lean_ctor_get(v_x_5201_, 1);
lean_inc_ref(v_arg_5205_);
lean_dec_ref_known(v_x_5201_, 2);
v___x_5206_ = lean_array_set(v_x_5202_, v_x_5203_, v_arg_5205_);
v___x_5207_ = lean_unsigned_to_nat(1u);
v___x_5208_ = lean_nat_sub(v_x_5203_, v___x_5207_);
v___x_5209_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1_spec__1(v_fnNames_5200_, v_numSectionVars_5199_, v_fn_5204_, v___x_5206_, v___x_5208_);
return v___x_5209_;
}
else
{
uint8_t v___x_5210_; 
v___x_5210_ = l_Lean_Expr_isConst(v_x_5201_);
if (v___x_5210_ == 0)
{
lean_dec_ref(v_x_5202_);
lean_dec_ref(v_x_5201_);
return v___x_5210_;
}
else
{
lean_object* v___x_5211_; lean_object* v___x_5212_; uint8_t v___x_5213_; 
v___x_5211_ = lean_unsigned_to_nat(0u);
v___x_5212_ = lean_array_get_size(v_fnNames_5200_);
v___x_5213_ = lean_nat_dec_lt(v___x_5211_, v___x_5212_);
if (v___x_5213_ == 0)
{
lean_dec_ref(v_x_5202_);
lean_dec_ref(v_x_5201_);
return v___x_5213_;
}
else
{
if (v___x_5213_ == 0)
{
lean_dec_ref(v_x_5202_);
lean_dec_ref(v_x_5201_);
return v___x_5213_;
}
else
{
size_t v___x_5214_; size_t v___x_5215_; uint8_t v___x_5216_; 
v___x_5214_ = ((size_t)0ULL);
v___x_5215_ = lean_usize_of_nat(v___x_5212_);
v___x_5216_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0(v_x_5201_, v_x_5202_, v_numSectionVars_5199_, v_fnNames_5200_, v___x_5214_, v___x_5215_);
lean_dec_ref(v_x_5202_);
lean_dec_ref(v_x_5201_);
return v___x_5216_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_numSectionVars_5199_ = stack[0].m_obj;
lean_object* v_fnNames_5200_ = stack[1].m_obj;
lean_object* v_x_5201_ = stack[2].m_obj;
lean_object* v_x_5202_ = stack[3].m_obj;
lean_object* v_x_5203_ = stack[4].m_obj;
uint8_t v_res_5217_;
v_res_5217_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1(v_numSectionVars_5199_, v_fnNames_5200_, v_x_5201_, v_x_5202_, v_x_5203_);
stack->m_num = v_res_5217_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1___boxed(lean_object* v_numSectionVars_5218_, lean_object* v_fnNames_5219_, lean_object* v_x_5220_, lean_object* v_x_5221_, lean_object* v_x_5222_){
_start:
{
uint8_t v_res_5223_; lean_object* v_r_5224_; 
v_res_5223_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1(v_numSectionVars_5218_, v_fnNames_5219_, v_x_5220_, v_x_5221_, v_x_5222_);
lean_dec(v_x_5222_);
lean_dec_ref(v_fnNames_5219_);
lean_dec(v_numSectionVars_5218_);
v_r_5224_ = lean_box(v_res_5223_);
return v_r_5224_;
}
}
uint8_t l___private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg(lean_object* v_fnNames_5225_, lean_object* v_numSectionVars_5226_, lean_object* v_a_5227_){
_start:
{
lean_object* v_dummy_5228_; lean_object* v_nargs_5229_; lean_object* v___x_5230_; lean_object* v___x_5231_; lean_object* v___x_5232_; uint8_t v___x_5233_; 
v_dummy_5228_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___closed__0);
v_nargs_5229_ = l_Lean_Expr_getAppNumArgs(v_a_5227_);
lean_inc(v_nargs_5229_);
v___x_5230_ = lean_mk_array(v_nargs_5229_, v_dummy_5228_);
v___x_5231_ = lean_unsigned_to_nat(1u);
v___x_5232_ = lean_nat_sub(v_nargs_5229_, v___x_5231_);
lean_dec(v_nargs_5229_);
v___x_5233_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1(v_numSectionVars_5226_, v_fnNames_5225_, v_a_5227_, v___x_5230_, v___x_5232_);
lean_dec(v___x_5232_);
return v___x_5233_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_fnNames_5225_ = stack[0].m_obj;
lean_object* v_numSectionVars_5226_ = stack[1].m_obj;
lean_object* v_a_5227_ = stack[2].m_obj;
uint8_t v_res_5234_;
v_res_5234_ = l___private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg(v_fnNames_5225_, v_numSectionVars_5226_, v_a_5227_);
stack->m_num = v_res_5234_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg___boxed(lean_object* v_fnNames_5235_, lean_object* v_numSectionVars_5236_, lean_object* v_a_5237_){
_start:
{
uint8_t v_res_5238_; lean_object* v_r_5239_; 
v_res_5238_ = l___private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg(v_fnNames_5235_, v_numSectionVars_5236_, v_a_5237_);
lean_dec(v_numSectionVars_5236_);
lean_dec_ref(v_fnNames_5235_);
v_r_5239_ = lean_box(v_res_5238_);
return v_r_5239_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__0(lean_object* v_fnNames_5240_, lean_object* v_numSectionVars_5241_, lean_object* v_as_5242_, size_t v_i_5243_, size_t v_stop_5244_){
_start:
{
uint8_t v___x_5245_; 
v___x_5245_ = lean_usize_dec_eq(v_i_5243_, v_stop_5244_);
if (v___x_5245_ == 0)
{
lean_object* v___x_5246_; uint8_t v___x_5247_; 
v___x_5246_ = lean_array_uget_borrowed(v_as_5242_, v_i_5243_);
lean_inc(v___x_5246_);
v___x_5247_ = l___private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg(v_fnNames_5240_, v_numSectionVars_5241_, v___x_5246_);
if (v___x_5247_ == 0)
{
size_t v___x_5248_; size_t v___x_5249_; 
v___x_5248_ = ((size_t)1ULL);
v___x_5249_ = lean_usize_add(v_i_5243_, v___x_5248_);
v_i_5243_ = v___x_5249_;
goto _start;
}
else
{
return v___x_5247_;
}
}
else
{
uint8_t v___x_5251_; 
v___x_5251_ = 0;
return v___x_5251_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fnNames_5240_ = stack[0].m_obj;
lean_object* v_numSectionVars_5241_ = stack[1].m_obj;
lean_object* v_as_5242_ = stack[2].m_obj;
size_t v_i_5243_ = stack[3].m_num;
size_t v_stop_5244_ = stack[4].m_num;
uint8_t v_res_5252_;
v_res_5252_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__0(v_fnNames_5240_, v_numSectionVars_5241_, v_as_5242_, v_i_5243_, v_stop_5244_);
stack->m_num = v_res_5252_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__0___boxed(lean_object* v_fnNames_5253_, lean_object* v_numSectionVars_5254_, lean_object* v_as_5255_, lean_object* v_i_5256_, lean_object* v_stop_5257_){
_start:
{
size_t v_i_boxed_5258_; size_t v_stop_boxed_5259_; uint8_t v_res_5260_; lean_object* v_r_5261_; 
v_i_boxed_5258_ = lean_unbox_usize(v_i_5256_);
lean_dec(v_i_5256_);
v_stop_boxed_5259_ = lean_unbox_usize(v_stop_5257_);
lean_dec(v_stop_5257_);
v_res_5260_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__0(v_fnNames_5253_, v_numSectionVars_5254_, v_as_5255_, v_i_boxed_5258_, v_stop_boxed_5259_);
lean_dec_ref(v_as_5255_);
lean_dec(v_numSectionVars_5254_);
lean_dec_ref(v_fnNames_5253_);
v_r_5261_ = lean_box(v_res_5260_);
return v_r_5261_;
}
}
lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__1(lean_object* v_fnNames_5262_, lean_object* v_numSectionVars_5263_, lean_object* v___x_5264_, lean_object* v_x_5265_, lean_object* v_x_5266_, lean_object* v___y_5267_, lean_object* v___y_5268_){
_start:
{
if (lean_obj_tag(v_x_5265_) == 5)
{
lean_object* v_fn_5273_; lean_object* v_arg_5274_; lean_object* v___x_5275_; 
v_fn_5273_ = lean_ctor_get(v_x_5265_, 0);
lean_inc_ref(v_fn_5273_);
v_arg_5274_ = lean_ctor_get(v_x_5265_, 1);
lean_inc_ref(v_arg_5274_);
lean_dec_ref_known(v_x_5265_, 2);
v___x_5275_ = lean_array_push(v_x_5266_, v_arg_5274_);
v_x_5265_ = v_fn_5273_;
v_x_5266_ = v___x_5275_;
goto _start;
}
else
{
uint8_t v___x_5277_; 
v___x_5277_ = l_Lean_Expr_isConst(v_x_5265_);
if (v___x_5277_ == 0)
{
lean_dec_ref(v_x_5266_);
lean_dec_ref(v_x_5265_);
lean_dec_ref(v___x_5264_);
goto v___jp_5270_;
}
else
{
lean_object* v___x_5278_; lean_object* v___x_5279_; uint8_t v___x_5280_; 
v___x_5278_ = lean_unsigned_to_nat(0u);
v___x_5279_ = lean_array_get_size(v_x_5266_);
v___x_5280_ = lean_nat_dec_lt(v___x_5278_, v___x_5279_);
if (v___x_5280_ == 0)
{
lean_dec_ref(v_x_5266_);
lean_dec_ref(v_x_5265_);
lean_dec_ref(v___x_5264_);
goto v___jp_5270_;
}
else
{
if (v___x_5280_ == 0)
{
lean_dec_ref(v_x_5266_);
lean_dec_ref(v_x_5265_);
lean_dec_ref(v___x_5264_);
goto v___jp_5270_;
}
else
{
size_t v___x_5281_; size_t v___x_5282_; uint8_t v___x_5283_; 
v___x_5281_ = ((size_t)0ULL);
v___x_5282_ = lean_usize_of_nat(v___x_5279_);
v___x_5283_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__0(v_fnNames_5262_, v_numSectionVars_5263_, v_x_5266_, v___x_5281_, v___x_5282_);
if (v___x_5283_ == 0)
{
lean_dec_ref(v_x_5266_);
lean_dec_ref(v_x_5265_);
lean_dec_ref(v___x_5264_);
goto v___jp_5270_;
}
else
{
lean_object* v___x_5284_; uint8_t v___x_5285_; lean_object* v___x_5286_; 
v___x_5284_ = l_Lean_Expr_constName_x21(v_x_5265_);
v___x_5285_ = 0;
v___x_5286_ = l_Lean_Environment_find_x3f(v___x_5264_, v___x_5284_, v___x_5285_);
if (lean_obj_tag(v___x_5286_) == 1)
{
lean_object* v_val_5287_; 
v_val_5287_ = lean_ctor_get(v___x_5286_, 0);
lean_inc(v_val_5287_);
lean_dec_ref_known(v___x_5286_, 1);
if (lean_obj_tag(v_val_5287_) == 2)
{
lean_object* v___x_5288_; lean_object* v___x_5289_; lean_object* v___x_5291_; uint8_t v_isShared_5292_; uint8_t v_isSharedCheck_5313_; 
v___x_5288_ = l_Lean_Expr_constLevels_x21(v_x_5265_);
lean_dec_ref(v_x_5265_);
v___x_5289_ = l_Lean_Core_instantiateValueLevelParams(v_val_5287_, v___x_5288_, v___x_5280_, v___y_5267_, v___y_5268_);
v_isSharedCheck_5313_ = !lean_is_exclusive(v_val_5287_);
if (v_isSharedCheck_5313_ == 0)
{
lean_object* v_unused_5314_; 
v_unused_5314_ = lean_ctor_get(v_val_5287_, 0);
lean_dec(v_unused_5314_);
v___x_5291_ = v_val_5287_;
v_isShared_5292_ = v_isSharedCheck_5313_;
goto v_resetjp_5290_;
}
else
{
lean_dec(v_val_5287_);
v___x_5291_ = lean_box(0);
v_isShared_5292_ = v_isSharedCheck_5313_;
goto v_resetjp_5290_;
}
v_resetjp_5290_:
{
if (lean_obj_tag(v___x_5289_) == 0)
{
lean_object* v_a_5293_; lean_object* v___x_5295_; uint8_t v_isShared_5296_; uint8_t v_isSharedCheck_5304_; 
v_a_5293_ = lean_ctor_get(v___x_5289_, 0);
v_isSharedCheck_5304_ = !lean_is_exclusive(v___x_5289_);
if (v_isSharedCheck_5304_ == 0)
{
v___x_5295_ = v___x_5289_;
v_isShared_5296_ = v_isSharedCheck_5304_;
goto v_resetjp_5294_;
}
else
{
lean_inc(v_a_5293_);
lean_dec(v___x_5289_);
v___x_5295_ = lean_box(0);
v_isShared_5296_ = v_isSharedCheck_5304_;
goto v_resetjp_5294_;
}
v_resetjp_5294_:
{
lean_object* v___x_5297_; lean_object* v___x_5299_; 
v___x_5297_ = l_Lean_Expr_betaRev(v_a_5293_, v_x_5266_, v___x_5285_, v___x_5285_);
lean_dec_ref(v_x_5266_);
if (v_isShared_5292_ == 0)
{
lean_ctor_set_tag(v___x_5291_, 1);
lean_ctor_set(v___x_5291_, 0, v___x_5297_);
v___x_5299_ = v___x_5291_;
goto v_reusejp_5298_;
}
else
{
lean_object* v_reuseFailAlloc_5303_; 
v_reuseFailAlloc_5303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5303_, 0, v___x_5297_);
v___x_5299_ = v_reuseFailAlloc_5303_;
goto v_reusejp_5298_;
}
v_reusejp_5298_:
{
lean_object* v___x_5301_; 
if (v_isShared_5296_ == 0)
{
lean_ctor_set(v___x_5295_, 0, v___x_5299_);
v___x_5301_ = v___x_5295_;
goto v_reusejp_5300_;
}
else
{
lean_object* v_reuseFailAlloc_5302_; 
v_reuseFailAlloc_5302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5302_, 0, v___x_5299_);
v___x_5301_ = v_reuseFailAlloc_5302_;
goto v_reusejp_5300_;
}
v_reusejp_5300_:
{
return v___x_5301_;
}
}
}
}
else
{
lean_object* v_a_5305_; lean_object* v___x_5307_; uint8_t v_isShared_5308_; uint8_t v_isSharedCheck_5312_; 
lean_del_object(v___x_5291_);
lean_dec_ref(v_x_5266_);
v_a_5305_ = lean_ctor_get(v___x_5289_, 0);
v_isSharedCheck_5312_ = !lean_is_exclusive(v___x_5289_);
if (v_isSharedCheck_5312_ == 0)
{
v___x_5307_ = v___x_5289_;
v_isShared_5308_ = v_isSharedCheck_5312_;
goto v_resetjp_5306_;
}
else
{
lean_inc(v_a_5305_);
lean_dec(v___x_5289_);
v___x_5307_ = lean_box(0);
v_isShared_5308_ = v_isSharedCheck_5312_;
goto v_resetjp_5306_;
}
v_resetjp_5306_:
{
lean_object* v___x_5310_; 
if (v_isShared_5308_ == 0)
{
v___x_5310_ = v___x_5307_;
goto v_reusejp_5309_;
}
else
{
lean_object* v_reuseFailAlloc_5311_; 
v_reuseFailAlloc_5311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5311_, 0, v_a_5305_);
v___x_5310_ = v_reuseFailAlloc_5311_;
goto v_reusejp_5309_;
}
v_reusejp_5309_:
{
return v___x_5310_;
}
}
}
}
}
else
{
lean_dec(v_val_5287_);
lean_dec_ref(v_x_5266_);
lean_dec_ref(v_x_5265_);
goto v___jp_5270_;
}
}
else
{
lean_dec(v___x_5286_);
lean_dec_ref(v_x_5266_);
lean_dec_ref(v_x_5265_);
goto v___jp_5270_;
}
}
}
}
}
}
v___jp_5270_:
{
lean_object* v___x_5271_; lean_object* v___x_5272_; 
v___x_5271_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_5272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5272_, 0, v___x_5271_);
return v___x_5272_;
}
}
}
LEAN_EXPORT void l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_fnNames_5262_ = stack[0].m_obj;
lean_object* v_numSectionVars_5263_ = stack[1].m_obj;
lean_object* v___x_5264_ = stack[2].m_obj;
lean_object* v_x_5265_ = stack[3].m_obj;
lean_object* v_x_5266_ = stack[4].m_obj;
lean_object* v___y_5267_ = stack[5].m_obj;
lean_object* v___y_5268_ = stack[6].m_obj;
lean_object* v_res_5315_;
v_res_5315_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__1(v_fnNames_5262_, v_numSectionVars_5263_, v___x_5264_, v_x_5265_, v_x_5266_, v___y_5267_, v___y_5268_);
stack->m_obj
 = v_res_5315_;
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__1___boxed(lean_object* v_fnNames_5316_, lean_object* v_numSectionVars_5317_, lean_object* v___x_5318_, lean_object* v_x_5319_, lean_object* v_x_5320_, lean_object* v___y_5321_, lean_object* v___y_5322_, lean_object* v___y_5323_){
_start:
{
lean_object* v_res_5324_; 
v_res_5324_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__1(v_fnNames_5316_, v_numSectionVars_5317_, v___x_5318_, v_x_5319_, v_x_5320_, v___y_5321_, v___y_5322_);
lean_dec(v___y_5322_);
lean_dec_ref(v___y_5321_);
lean_dec(v_numSectionVars_5317_);
lean_dec_ref(v_fnNames_5316_);
return v_res_5324_;
}
}
lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___lam__1(lean_object* v_fnNames_5325_, lean_object* v_numSectionVars_5326_, lean_object* v_env_5327_, lean_object* v_e_5328_, lean_object* v___y_5329_, lean_object* v___y_5330_){
_start:
{
lean_object* v___x_5332_; lean_object* v___x_5333_; lean_object* v___x_5334_; 
v___x_5332_ = l_Lean_Expr_getAppNumArgs(v_e_5328_);
v___x_5333_ = lean_mk_empty_array_with_capacity(v___x_5332_);
lean_dec(v___x_5332_);
v___x_5334_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__1(v_fnNames_5325_, v_numSectionVars_5326_, v_env_5327_, v_e_5328_, v___x_5333_, v___y_5329_, v___y_5330_);
return v___x_5334_;
}
}
LEAN_EXPORT void l_Lean_Meta_unfoldIfArgIsAppOf___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_fnNames_5325_ = stack[0].m_obj;
lean_object* v_numSectionVars_5326_ = stack[1].m_obj;
lean_object* v_env_5327_ = stack[2].m_obj;
lean_object* v_e_5328_ = stack[3].m_obj;
lean_object* v___y_5329_ = stack[4].m_obj;
lean_object* v___y_5330_ = stack[5].m_obj;
lean_object* v_res_5335_;
v_res_5335_ = l_Lean_Meta_unfoldIfArgIsAppOf___lam__1(v_fnNames_5325_, v_numSectionVars_5326_, v_env_5327_, v_e_5328_, v___y_5329_, v___y_5330_);
stack->m_obj
 = v_res_5335_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___lam__1___boxed(lean_object* v_fnNames_5336_, lean_object* v_numSectionVars_5337_, lean_object* v_env_5338_, lean_object* v_e_5339_, lean_object* v___y_5340_, lean_object* v___y_5341_, lean_object* v___y_5342_){
_start:
{
lean_object* v_res_5343_; 
v_res_5343_ = l_Lean_Meta_unfoldIfArgIsAppOf___lam__1(v_fnNames_5336_, v_numSectionVars_5337_, v_env_5338_, v_e_5339_, v___y_5340_, v___y_5341_);
lean_dec(v___y_5341_);
lean_dec_ref(v___y_5340_);
lean_dec(v_numSectionVars_5337_);
lean_dec_ref(v_fnNames_5336_);
return v_res_5343_;
}
}
lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___lam__0(lean_object* v_fnNames_5344_, lean_object* v_numSectionVars_5345_, lean_object* v_e_5346_, lean_object* v___f_5347_, lean_object* v___y_5348_, lean_object* v___y_5349_){
_start:
{
lean_object* v___x_5351_; lean_object* v_env_5352_; lean_object* v___f_5353_; lean_object* v___x_5354_; 
v___x_5351_ = lean_st_ref_get(v___y_5349_);
v_env_5352_ = lean_ctor_get(v___x_5351_, 0);
lean_inc_ref(v_env_5352_);
lean_dec(v___x_5351_);
v___f_5353_ = lean_alloc_closure((void*)(l_Lean_Meta_unfoldIfArgIsAppOf___lam__1___boxed), 7, 3);
lean_closure_set(v___f_5353_, 0, v_fnNames_5344_);
lean_closure_set(v___f_5353_, 1, v_numSectionVars_5345_);
lean_closure_set(v___f_5353_, 2, v_env_5352_);
v___x_5354_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_5346_, v___f_5353_, v___f_5347_, v___y_5348_, v___y_5349_);
return v___x_5354_;
}
}
LEAN_EXPORT void l_Lean_Meta_unfoldIfArgIsAppOf___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fnNames_5344_ = stack[0].m_obj;
lean_object* v_numSectionVars_5345_ = stack[1].m_obj;
lean_object* v_e_5346_ = stack[2].m_obj;
lean_object* v___f_5347_ = stack[3].m_obj;
lean_object* v___y_5348_ = stack[4].m_obj;
lean_object* v___y_5349_ = stack[5].m_obj;
lean_object* v_res_5355_;
v_res_5355_ = l_Lean_Meta_unfoldIfArgIsAppOf___lam__0(v_fnNames_5344_, v_numSectionVars_5345_, v_e_5346_, v___f_5347_, v___y_5348_, v___y_5349_);
stack->m_obj
 = v_res_5355_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___lam__0___boxed(lean_object* v_fnNames_5356_, lean_object* v_numSectionVars_5357_, lean_object* v_e_5358_, lean_object* v___f_5359_, lean_object* v___y_5360_, lean_object* v___y_5361_, lean_object* v___y_5362_){
_start:
{
lean_object* v_res_5363_; 
v_res_5363_ = l_Lean_Meta_unfoldIfArgIsAppOf___lam__0(v_fnNames_5356_, v_numSectionVars_5357_, v_e_5358_, v___f_5359_, v___y_5360_, v___y_5361_);
lean_dec(v___y_5361_);
lean_dec_ref(v___y_5360_);
return v_res_5363_;
}
}
lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0(lean_object* v___y_5364_, uint8_t v_isExporting_5365_, lean_object* v___x_5366_, lean_object* v_a_x3f_5367_){
_start:
{
lean_object* v___x_5369_; lean_object* v_env_5370_; lean_object* v_nextMacroScope_5371_; lean_object* v_ngen_5372_; lean_object* v_auxDeclNGen_5373_; lean_object* v_traceState_5374_; lean_object* v_recordedDeps_5375_; lean_object* v_messages_5376_; lean_object* v_infoState_5377_; lean_object* v_snapshotTasks_5378_; lean_object* v___x_5380_; uint8_t v_isShared_5381_; uint8_t v_isSharedCheck_5389_; 
v___x_5369_ = lean_st_ref_take(v___y_5364_);
v_env_5370_ = lean_ctor_get(v___x_5369_, 0);
v_nextMacroScope_5371_ = lean_ctor_get(v___x_5369_, 1);
v_ngen_5372_ = lean_ctor_get(v___x_5369_, 2);
v_auxDeclNGen_5373_ = lean_ctor_get(v___x_5369_, 3);
v_traceState_5374_ = lean_ctor_get(v___x_5369_, 4);
v_recordedDeps_5375_ = lean_ctor_get(v___x_5369_, 6);
v_messages_5376_ = lean_ctor_get(v___x_5369_, 7);
v_infoState_5377_ = lean_ctor_get(v___x_5369_, 8);
v_snapshotTasks_5378_ = lean_ctor_get(v___x_5369_, 9);
v_isSharedCheck_5389_ = !lean_is_exclusive(v___x_5369_);
if (v_isSharedCheck_5389_ == 0)
{
lean_object* v_unused_5390_; 
v_unused_5390_ = lean_ctor_get(v___x_5369_, 5);
lean_dec(v_unused_5390_);
v___x_5380_ = v___x_5369_;
v_isShared_5381_ = v_isSharedCheck_5389_;
goto v_resetjp_5379_;
}
else
{
lean_inc(v_snapshotTasks_5378_);
lean_inc(v_infoState_5377_);
lean_inc(v_messages_5376_);
lean_inc(v_recordedDeps_5375_);
lean_inc(v_traceState_5374_);
lean_inc(v_auxDeclNGen_5373_);
lean_inc(v_ngen_5372_);
lean_inc(v_nextMacroScope_5371_);
lean_inc(v_env_5370_);
lean_dec(v___x_5369_);
v___x_5380_ = lean_box(0);
v_isShared_5381_ = v_isSharedCheck_5389_;
goto v_resetjp_5379_;
}
v_resetjp_5379_:
{
lean_object* v___x_5382_; lean_object* v___x_5383_; lean_object* v___x_5385_; 
v___x_5382_ = lean_box(0);
v___x_5383_ = l_Lean_Environment_setExporting(v_env_5370_, v_isExporting_5365_);
if (v_isShared_5381_ == 0)
{
lean_ctor_set(v___x_5380_, 5, v___x_5366_);
lean_ctor_set(v___x_5380_, 0, v___x_5383_);
v___x_5385_ = v___x_5380_;
goto v_reusejp_5384_;
}
else
{
lean_object* v_reuseFailAlloc_5388_; 
v_reuseFailAlloc_5388_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5388_, 0, v___x_5383_);
lean_ctor_set(v_reuseFailAlloc_5388_, 1, v_nextMacroScope_5371_);
lean_ctor_set(v_reuseFailAlloc_5388_, 2, v_ngen_5372_);
lean_ctor_set(v_reuseFailAlloc_5388_, 3, v_auxDeclNGen_5373_);
lean_ctor_set(v_reuseFailAlloc_5388_, 4, v_traceState_5374_);
lean_ctor_set(v_reuseFailAlloc_5388_, 5, v___x_5366_);
lean_ctor_set(v_reuseFailAlloc_5388_, 6, v_recordedDeps_5375_);
lean_ctor_set(v_reuseFailAlloc_5388_, 7, v_messages_5376_);
lean_ctor_set(v_reuseFailAlloc_5388_, 8, v_infoState_5377_);
lean_ctor_set(v_reuseFailAlloc_5388_, 9, v_snapshotTasks_5378_);
v___x_5385_ = v_reuseFailAlloc_5388_;
goto v_reusejp_5384_;
}
v_reusejp_5384_:
{
lean_object* v___x_5386_; lean_object* v___x_5387_; 
v___x_5386_ = lean_st_ref_put(v___y_5364_, v___x_5385_);
v___x_5387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5387_, 0, v___x_5382_);
return v___x_5387_;
}
}
}
}
LEAN_EXPORT void l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_5364_ = stack[0].m_obj;
uint8_t v_isExporting_5365_ = stack[1].m_num;
lean_object* v___x_5366_ = stack[2].m_obj;
lean_object* v_a_x3f_5367_ = stack[3].m_obj;
lean_object* v_res_5391_;
v_res_5391_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0(v___y_5364_, v_isExporting_5365_, v___x_5366_, v_a_x3f_5367_);
stack->m_obj
 = v_res_5391_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0___boxed(lean_object* v___y_5392_, lean_object* v_isExporting_5393_, lean_object* v___x_5394_, lean_object* v_a_x3f_5395_, lean_object* v___y_5396_){
_start:
{
uint8_t v_isExporting_boxed_5397_; lean_object* v_res_5398_; 
v_isExporting_boxed_5397_ = lean_unbox(v_isExporting_5393_);
v_res_5398_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0(v___y_5392_, v_isExporting_boxed_5397_, v___x_5394_, v_a_x3f_5395_);
lean_dec(v_a_x3f_5395_);
lean_dec(v___y_5392_);
return v_res_5398_;
}
}
lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg(lean_object* v_x_5399_, uint8_t v_isExporting_5400_, lean_object* v___y_5401_, lean_object* v___y_5402_){
_start:
{
lean_object* v___x_5404_; lean_object* v_env_5405_; lean_object* v___x_5406_; uint8_t v_isModule_5407_; 
v___x_5404_ = lean_st_ref_get(v___y_5402_);
v_env_5405_ = lean_ctor_get(v___x_5404_, 0);
lean_inc_ref(v_env_5405_);
lean_dec(v___x_5404_);
v___x_5406_ = l_Lean_Environment_header(v_env_5405_);
v_isModule_5407_ = lean_ctor_get_uint8(v___x_5406_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_5406_);
if (v_isModule_5407_ == 0)
{
lean_object* v___x_5408_; 
lean_dec_ref(v_env_5405_);
lean_inc(v___y_5402_);
lean_inc_ref(v___y_5401_);
v___x_5408_ = lean_apply_3(v_x_5399_, v___y_5401_, v___y_5402_, lean_box(0));
return v___x_5408_;
}
else
{
uint8_t v_isExporting_5409_; 
v_isExporting_5409_ = lean_ctor_get_uint8(v_env_5405_, sizeof(void*)*13);
lean_dec_ref(v_env_5405_);
if (v_isExporting_5400_ == 0)
{
if (v_isExporting_5409_ == 0)
{
lean_object* v___x_5461_; 
lean_inc(v___y_5402_);
lean_inc_ref(v___y_5401_);
v___x_5461_ = lean_apply_3(v_x_5399_, v___y_5401_, v___y_5402_, lean_box(0));
return v___x_5461_;
}
else
{
goto v___jp_5410_;
}
}
else
{
if (v_isExporting_5409_ == 0)
{
goto v___jp_5410_;
}
else
{
lean_object* v___x_5462_; 
lean_inc(v___y_5402_);
lean_inc_ref(v___y_5401_);
v___x_5462_ = lean_apply_3(v_x_5399_, v___y_5401_, v___y_5402_, lean_box(0));
return v___x_5462_;
}
}
v___jp_5410_:
{
lean_object* v___x_5411_; lean_object* v_env_5412_; lean_object* v_nextMacroScope_5413_; lean_object* v_ngen_5414_; lean_object* v_auxDeclNGen_5415_; lean_object* v_traceState_5416_; lean_object* v_recordedDeps_5417_; lean_object* v_messages_5418_; lean_object* v_infoState_5419_; lean_object* v_snapshotTasks_5420_; lean_object* v___x_5422_; uint8_t v_isShared_5423_; uint8_t v_isSharedCheck_5459_; 
v___x_5411_ = lean_st_ref_take(v___y_5402_);
v_env_5412_ = lean_ctor_get(v___x_5411_, 0);
v_nextMacroScope_5413_ = lean_ctor_get(v___x_5411_, 1);
v_ngen_5414_ = lean_ctor_get(v___x_5411_, 2);
v_auxDeclNGen_5415_ = lean_ctor_get(v___x_5411_, 3);
v_traceState_5416_ = lean_ctor_get(v___x_5411_, 4);
v_recordedDeps_5417_ = lean_ctor_get(v___x_5411_, 6);
v_messages_5418_ = lean_ctor_get(v___x_5411_, 7);
v_infoState_5419_ = lean_ctor_get(v___x_5411_, 8);
v_snapshotTasks_5420_ = lean_ctor_get(v___x_5411_, 9);
v_isSharedCheck_5459_ = !lean_is_exclusive(v___x_5411_);
if (v_isSharedCheck_5459_ == 0)
{
lean_object* v_unused_5460_; 
v_unused_5460_ = lean_ctor_get(v___x_5411_, 5);
lean_dec(v_unused_5460_);
v___x_5422_ = v___x_5411_;
v_isShared_5423_ = v_isSharedCheck_5459_;
goto v_resetjp_5421_;
}
else
{
lean_inc(v_snapshotTasks_5420_);
lean_inc(v_infoState_5419_);
lean_inc(v_messages_5418_);
lean_inc(v_recordedDeps_5417_);
lean_inc(v_traceState_5416_);
lean_inc(v_auxDeclNGen_5415_);
lean_inc(v_ngen_5414_);
lean_inc(v_nextMacroScope_5413_);
lean_inc(v_env_5412_);
lean_dec(v___x_5411_);
v___x_5422_ = lean_box(0);
v_isShared_5423_ = v_isSharedCheck_5459_;
goto v_resetjp_5421_;
}
v_resetjp_5421_:
{
lean_object* v___x_5424_; lean_object* v___x_5425_; lean_object* v___x_5427_; 
v___x_5424_ = l_Lean_Environment_setExporting(v_env_5412_, v_isExporting_5400_);
v___x_5425_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2, &l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2);
if (v_isShared_5423_ == 0)
{
lean_ctor_set(v___x_5422_, 5, v___x_5425_);
lean_ctor_set(v___x_5422_, 0, v___x_5424_);
v___x_5427_ = v___x_5422_;
goto v_reusejp_5426_;
}
else
{
lean_object* v_reuseFailAlloc_5458_; 
v_reuseFailAlloc_5458_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5458_, 0, v___x_5424_);
lean_ctor_set(v_reuseFailAlloc_5458_, 1, v_nextMacroScope_5413_);
lean_ctor_set(v_reuseFailAlloc_5458_, 2, v_ngen_5414_);
lean_ctor_set(v_reuseFailAlloc_5458_, 3, v_auxDeclNGen_5415_);
lean_ctor_set(v_reuseFailAlloc_5458_, 4, v_traceState_5416_);
lean_ctor_set(v_reuseFailAlloc_5458_, 5, v___x_5425_);
lean_ctor_set(v_reuseFailAlloc_5458_, 6, v_recordedDeps_5417_);
lean_ctor_set(v_reuseFailAlloc_5458_, 7, v_messages_5418_);
lean_ctor_set(v_reuseFailAlloc_5458_, 8, v_infoState_5419_);
lean_ctor_set(v_reuseFailAlloc_5458_, 9, v_snapshotTasks_5420_);
v___x_5427_ = v_reuseFailAlloc_5458_;
goto v_reusejp_5426_;
}
v_reusejp_5426_:
{
lean_object* v___x_5428_; lean_object* v_r_5429_; 
v___x_5428_ = lean_st_ref_put(v___y_5402_, v___x_5427_);
lean_inc(v___y_5402_);
lean_inc_ref(v___y_5401_);
v_r_5429_ = lean_apply_3(v_x_5399_, v___y_5401_, v___y_5402_, lean_box(0));
if (lean_obj_tag(v_r_5429_) == 0)
{
lean_object* v_a_5430_; lean_object* v___x_5432_; uint8_t v_isShared_5433_; uint8_t v_isSharedCheck_5446_; 
v_a_5430_ = lean_ctor_get(v_r_5429_, 0);
v_isSharedCheck_5446_ = !lean_is_exclusive(v_r_5429_);
if (v_isSharedCheck_5446_ == 0)
{
v___x_5432_ = v_r_5429_;
v_isShared_5433_ = v_isSharedCheck_5446_;
goto v_resetjp_5431_;
}
else
{
lean_inc(v_a_5430_);
lean_dec(v_r_5429_);
v___x_5432_ = lean_box(0);
v_isShared_5433_ = v_isSharedCheck_5446_;
goto v_resetjp_5431_;
}
v_resetjp_5431_:
{
lean_object* v___x_5435_; 
lean_inc(v_a_5430_);
if (v_isShared_5433_ == 0)
{
lean_ctor_set_tag(v___x_5432_, 1);
v___x_5435_ = v___x_5432_;
goto v_reusejp_5434_;
}
else
{
lean_object* v_reuseFailAlloc_5445_; 
v_reuseFailAlloc_5445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5445_, 0, v_a_5430_);
v___x_5435_ = v_reuseFailAlloc_5445_;
goto v_reusejp_5434_;
}
v_reusejp_5434_:
{
lean_object* v___x_5436_; lean_object* v___x_5438_; uint8_t v_isShared_5439_; uint8_t v_isSharedCheck_5443_; 
v___x_5436_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0(v___y_5402_, v_isExporting_5409_, v___x_5425_, v___x_5435_);
lean_dec_ref(v___x_5435_);
v_isSharedCheck_5443_ = !lean_is_exclusive(v___x_5436_);
if (v_isSharedCheck_5443_ == 0)
{
lean_object* v_unused_5444_; 
v_unused_5444_ = lean_ctor_get(v___x_5436_, 0);
lean_dec(v_unused_5444_);
v___x_5438_ = v___x_5436_;
v_isShared_5439_ = v_isSharedCheck_5443_;
goto v_resetjp_5437_;
}
else
{
lean_dec(v___x_5436_);
v___x_5438_ = lean_box(0);
v_isShared_5439_ = v_isSharedCheck_5443_;
goto v_resetjp_5437_;
}
v_resetjp_5437_:
{
lean_object* v___x_5441_; 
if (v_isShared_5439_ == 0)
{
lean_ctor_set(v___x_5438_, 0, v_a_5430_);
v___x_5441_ = v___x_5438_;
goto v_reusejp_5440_;
}
else
{
lean_object* v_reuseFailAlloc_5442_; 
v_reuseFailAlloc_5442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5442_, 0, v_a_5430_);
v___x_5441_ = v_reuseFailAlloc_5442_;
goto v_reusejp_5440_;
}
v_reusejp_5440_:
{
return v___x_5441_;
}
}
}
}
}
else
{
lean_object* v_a_5447_; lean_object* v___x_5448_; lean_object* v___x_5449_; lean_object* v___x_5451_; uint8_t v_isShared_5452_; uint8_t v_isSharedCheck_5456_; 
v_a_5447_ = lean_ctor_get(v_r_5429_, 0);
lean_inc(v_a_5447_);
lean_dec_ref_known(v_r_5429_, 1);
v___x_5448_ = lean_box(0);
v___x_5449_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0(v___y_5402_, v_isExporting_5409_, v___x_5425_, v___x_5448_);
v_isSharedCheck_5456_ = !lean_is_exclusive(v___x_5449_);
if (v_isSharedCheck_5456_ == 0)
{
lean_object* v_unused_5457_; 
v_unused_5457_ = lean_ctor_get(v___x_5449_, 0);
lean_dec(v_unused_5457_);
v___x_5451_ = v___x_5449_;
v_isShared_5452_ = v_isSharedCheck_5456_;
goto v_resetjp_5450_;
}
else
{
lean_dec(v___x_5449_);
v___x_5451_ = lean_box(0);
v_isShared_5452_ = v_isSharedCheck_5456_;
goto v_resetjp_5450_;
}
v_resetjp_5450_:
{
lean_object* v___x_5454_; 
if (v_isShared_5452_ == 0)
{
lean_ctor_set_tag(v___x_5451_, 1);
lean_ctor_set(v___x_5451_, 0, v_a_5447_);
v___x_5454_ = v___x_5451_;
goto v_reusejp_5453_;
}
else
{
lean_object* v_reuseFailAlloc_5455_; 
v_reuseFailAlloc_5455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5455_, 0, v_a_5447_);
v___x_5454_ = v_reuseFailAlloc_5455_;
goto v_reusejp_5453_;
}
v_reusejp_5453_:
{
return v___x_5454_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_5399_ = stack[0].m_obj;
uint8_t v_isExporting_5400_ = stack[1].m_num;
lean_object* v___y_5401_ = stack[2].m_obj;
lean_object* v___y_5402_ = stack[3].m_obj;
lean_object* v_res_5463_;
v_res_5463_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg(v_x_5399_, v_isExporting_5400_, v___y_5401_, v___y_5402_);
stack->m_obj
 = v_res_5463_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___boxed(lean_object* v_x_5464_, lean_object* v_isExporting_5465_, lean_object* v___y_5466_, lean_object* v___y_5467_, lean_object* v___y_5468_){
_start:
{
uint8_t v_isExporting_boxed_5469_; lean_object* v_res_5470_; 
v_isExporting_boxed_5469_ = lean_unbox(v_isExporting_5465_);
v_res_5470_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg(v_x_5464_, v_isExporting_boxed_5469_, v___y_5466_, v___y_5467_);
lean_dec(v___y_5467_);
lean_dec_ref(v___y_5466_);
return v_res_5470_;
}
}
lean_object* l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg(lean_object* v_x_5471_, uint8_t v_when_5472_, lean_object* v___y_5473_, lean_object* v___y_5474_){
_start:
{
if (v_when_5472_ == 0)
{
lean_object* v___x_5476_; 
lean_inc(v___y_5474_);
lean_inc_ref(v___y_5473_);
v___x_5476_ = lean_apply_3(v_x_5471_, v___y_5473_, v___y_5474_, lean_box(0));
return v___x_5476_;
}
else
{
uint8_t v___x_5477_; lean_object* v___x_5478_; 
v___x_5477_ = 0;
v___x_5478_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg(v_x_5471_, v___x_5477_, v___y_5473_, v___y_5474_);
return v___x_5478_;
}
}
}
LEAN_EXPORT void l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_5471_ = stack[0].m_obj;
uint8_t v_when_5472_ = stack[1].m_num;
lean_object* v___y_5473_ = stack[2].m_obj;
lean_object* v___y_5474_ = stack[3].m_obj;
lean_object* v_res_5479_;
v_res_5479_ = l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg(v_x_5471_, v_when_5472_, v___y_5473_, v___y_5474_);
stack->m_obj
 = v_res_5479_;
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg___boxed(lean_object* v_x_5480_, lean_object* v_when_5481_, lean_object* v___y_5482_, lean_object* v___y_5483_, lean_object* v___y_5484_){
_start:
{
uint8_t v_when_boxed_5485_; lean_object* v_res_5486_; 
v_when_boxed_5485_ = lean_unbox(v_when_5481_);
v_res_5486_ = l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg(v_x_5480_, v_when_boxed_5485_, v___y_5482_, v___y_5483_);
lean_dec(v___y_5483_);
lean_dec_ref(v___y_5482_);
return v_res_5486_;
}
}
lean_object* l_Lean_Meta_unfoldIfArgIsAppOf(lean_object* v_fnNames_5487_, lean_object* v_numSectionVars_5488_, lean_object* v_e_5489_, lean_object* v_a_5490_, lean_object* v_a_5491_){
_start:
{
lean_object* v___f_5493_; lean_object* v___f_5494_; uint8_t v___x_5495_; lean_object* v___x_5496_; 
v___f_5493_ = ((lean_object*)(l_Lean_Core_betaReduce___closed__1));
v___f_5494_ = lean_alloc_closure((void*)(l_Lean_Meta_unfoldIfArgIsAppOf___lam__0___boxed), 7, 4);
lean_closure_set(v___f_5494_, 0, v_fnNames_5487_);
lean_closure_set(v___f_5494_, 1, v_numSectionVars_5488_);
lean_closure_set(v___f_5494_, 2, v_e_5489_);
lean_closure_set(v___f_5494_, 3, v___f_5493_);
v___x_5495_ = 1;
v___x_5496_ = l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg(v___f_5494_, v___x_5495_, v_a_5490_, v_a_5491_);
return v___x_5496_;
}
}
LEAN_EXPORT void l_Lean_Meta_unfoldIfArgIsAppOf_0interp(lean_interpreter_value* stack)
{
lean_object* v_fnNames_5487_ = stack[0].m_obj;
lean_object* v_numSectionVars_5488_ = stack[1].m_obj;
lean_object* v_e_5489_ = stack[2].m_obj;
lean_object* v_a_5490_ = stack[3].m_obj;
lean_object* v_a_5491_ = stack[4].m_obj;
lean_object* v_res_5497_;
v_res_5497_ = l_Lean_Meta_unfoldIfArgIsAppOf(v_fnNames_5487_, v_numSectionVars_5488_, v_e_5489_, v_a_5490_, v_a_5491_);
stack->m_obj
 = v_res_5497_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___boxed(lean_object* v_fnNames_5498_, lean_object* v_numSectionVars_5499_, lean_object* v_e_5500_, lean_object* v_a_5501_, lean_object* v_a_5502_, lean_object* v_a_5503_){
_start:
{
lean_object* v_res_5504_; 
v_res_5504_ = l_Lean_Meta_unfoldIfArgIsAppOf(v_fnNames_5498_, v_numSectionVars_5499_, v_e_5500_, v_a_5501_, v_a_5502_);
lean_dec(v_a_5502_);
lean_dec_ref(v_a_5501_);
return v_res_5504_;
}
}
lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2(lean_object* v_00_u03b1_5505_, lean_object* v_x_5506_, uint8_t v_isExporting_5507_, lean_object* v___y_5508_, lean_object* v___y_5509_){
_start:
{
lean_object* v___x_5511_; 
v___x_5511_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg(v_x_5506_, v_isExporting_5507_, v___y_5508_, v___y_5509_);
return v___x_5511_;
}
}
LEAN_EXPORT void l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_5506_ = stack[1].m_obj;
uint8_t v_isExporting_5507_ = stack[2].m_num;
lean_object* v___y_5508_ = stack[3].m_obj;
lean_object* v___y_5509_ = stack[4].m_obj;
lean_object* v_res_5512_;
v_res_5512_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2(lean_box(0), v_x_5506_, v_isExporting_5507_, v___y_5508_, v___y_5509_);
stack->m_obj
 = v_res_5512_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___boxed(lean_object* v_00_u03b1_5513_, lean_object* v_x_5514_, lean_object* v_isExporting_5515_, lean_object* v___y_5516_, lean_object* v___y_5517_, lean_object* v___y_5518_){
_start:
{
uint8_t v_isExporting_boxed_5519_; lean_object* v_res_5520_; 
v_isExporting_boxed_5519_ = lean_unbox(v_isExporting_5515_);
v_res_5520_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2(v_00_u03b1_5513_, v_x_5514_, v_isExporting_boxed_5519_, v___y_5516_, v___y_5517_);
lean_dec(v___y_5517_);
lean_dec_ref(v___y_5516_);
return v_res_5520_;
}
}
lean_object* l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2(lean_object* v_00_u03b1_5521_, lean_object* v_x_5522_, uint8_t v_when_5523_, lean_object* v___y_5524_, lean_object* v___y_5525_){
_start:
{
lean_object* v___x_5527_; 
v___x_5527_ = l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg(v_x_5522_, v_when_5523_, v___y_5524_, v___y_5525_);
return v___x_5527_;
}
}
LEAN_EXPORT void l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_5522_ = stack[1].m_obj;
uint8_t v_when_5523_ = stack[2].m_num;
lean_object* v___y_5524_ = stack[3].m_obj;
lean_object* v___y_5525_ = stack[4].m_obj;
lean_object* v_res_5528_;
v_res_5528_ = l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2(lean_box(0), v_x_5522_, v_when_5523_, v___y_5524_, v___y_5525_);
stack->m_obj
 = v_res_5528_;
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___boxed(lean_object* v_00_u03b1_5529_, lean_object* v_x_5530_, lean_object* v_when_5531_, lean_object* v___y_5532_, lean_object* v___y_5533_, lean_object* v___y_5534_){
_start:
{
uint8_t v_when_boxed_5535_; lean_object* v_res_5536_; 
v_when_boxed_5535_ = lean_unbox(v_when_5531_);
v_res_5536_ = l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2(v_00_u03b1_5529_, v_x_5530_, v_when_boxed_5535_, v___y_5532_, v___y_5533_);
lean_dec(v___y_5533_);
lean_dec_ref(v___y_5532_);
return v_res_5536_;
}
}
lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___lam__0(lean_object* v_x_5537_, lean_object* v___y_5538_, lean_object* v___y_5539_){
_start:
{
lean_object* v___x_5541_; lean_object* v___x_5542_; 
v___x_5541_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_5542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5542_, 0, v___x_5541_);
return v___x_5542_;
}
}
LEAN_EXPORT void l_Lean_Meta_eraseInaccessibleAnnotations___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_5537_ = stack[0].m_obj;
lean_object* v___y_5538_ = stack[1].m_obj;
lean_object* v___y_5539_ = stack[2].m_obj;
lean_object* v_res_5543_;
v_res_5543_ = l_Lean_Meta_eraseInaccessibleAnnotations___lam__0(v_x_5537_, v___y_5538_, v___y_5539_);
stack->m_obj
 = v_res_5543_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___lam__0___boxed(lean_object* v_x_5544_, lean_object* v___y_5545_, lean_object* v___y_5546_, lean_object* v___y_5547_){
_start:
{
lean_object* v_res_5548_; 
v_res_5548_ = l_Lean_Meta_eraseInaccessibleAnnotations___lam__0(v_x_5544_, v___y_5545_, v___y_5546_);
lean_dec(v___y_5546_);
lean_dec_ref(v___y_5545_);
lean_dec_ref(v_x_5544_);
return v_res_5548_;
}
}
lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___lam__1(lean_object* v_e_5549_, lean_object* v___y_5550_, lean_object* v___y_5551_){
_start:
{
lean_object* v___y_5554_; lean_object* v___x_5557_; 
v___x_5557_ = l_Lean_inaccessible_x3f(v_e_5549_);
if (lean_obj_tag(v___x_5557_) == 1)
{
lean_object* v_val_5558_; 
lean_dec_ref(v_e_5549_);
v_val_5558_ = lean_ctor_get(v___x_5557_, 0);
lean_inc(v_val_5558_);
lean_dec_ref_known(v___x_5557_, 1);
v___y_5554_ = v_val_5558_;
goto v___jp_5553_;
}
else
{
lean_dec(v___x_5557_);
v___y_5554_ = v_e_5549_;
goto v___jp_5553_;
}
v___jp_5553_:
{
lean_object* v___x_5555_; lean_object* v___x_5556_; 
v___x_5555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5555_, 0, v___y_5554_);
v___x_5556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5556_, 0, v___x_5555_);
return v___x_5556_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_eraseInaccessibleAnnotations___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_5549_ = stack[0].m_obj;
lean_object* v___y_5550_ = stack[1].m_obj;
lean_object* v___y_5551_ = stack[2].m_obj;
lean_object* v_res_5559_;
v_res_5559_ = l_Lean_Meta_eraseInaccessibleAnnotations___lam__1(v_e_5549_, v___y_5550_, v___y_5551_);
stack->m_obj
 = v_res_5559_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___lam__1___boxed(lean_object* v_e_5560_, lean_object* v___y_5561_, lean_object* v___y_5562_, lean_object* v___y_5563_){
_start:
{
lean_object* v_res_5564_; 
v_res_5564_ = l_Lean_Meta_eraseInaccessibleAnnotations___lam__1(v_e_5560_, v___y_5561_, v___y_5562_);
lean_dec(v___y_5562_);
lean_dec_ref(v___y_5561_);
return v_res_5564_;
}
}
lean_object* l_Lean_Meta_eraseInaccessibleAnnotations(lean_object* v_e_5567_, lean_object* v_a_5568_, lean_object* v_a_5569_){
_start:
{
lean_object* v___f_5571_; lean_object* v___f_5572_; lean_object* v___x_5573_; 
v___f_5571_ = ((lean_object*)(l_Lean_Meta_eraseInaccessibleAnnotations___closed__0));
v___f_5572_ = ((lean_object*)(l_Lean_Meta_eraseInaccessibleAnnotations___closed__1));
v___x_5573_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_5567_, v___f_5571_, v___f_5572_, v_a_5568_, v_a_5569_);
return v___x_5573_;
}
}
LEAN_EXPORT void l_Lean_Meta_eraseInaccessibleAnnotations_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_5567_ = stack[0].m_obj;
lean_object* v_a_5568_ = stack[1].m_obj;
lean_object* v_a_5569_ = stack[2].m_obj;
lean_object* v_res_5574_;
v_res_5574_ = l_Lean_Meta_eraseInaccessibleAnnotations(v_e_5567_, v_a_5568_, v_a_5569_);
stack->m_obj
 = v_res_5574_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___boxed(lean_object* v_e_5575_, lean_object* v_a_5576_, lean_object* v_a_5577_, lean_object* v_a_5578_){
_start:
{
lean_object* v_res_5579_; 
v_res_5579_ = l_Lean_Meta_eraseInaccessibleAnnotations(v_e_5575_, v_a_5576_, v_a_5577_);
lean_dec(v_a_5577_);
lean_dec_ref(v_a_5576_);
return v_res_5579_;
}
}
lean_object* l_Lean_Meta_erasePatternRefAnnotations___lam__1(lean_object* v_e_5580_, lean_object* v___y_5581_, lean_object* v___y_5582_){
_start:
{
lean_object* v___y_5585_; lean_object* v___x_5588_; 
v___x_5588_ = l_Lean_patternWithRef_x3f(v_e_5580_);
if (lean_obj_tag(v___x_5588_) == 1)
{
lean_object* v_val_5589_; lean_object* v_snd_5590_; 
lean_dec_ref(v_e_5580_);
v_val_5589_ = lean_ctor_get(v___x_5588_, 0);
lean_inc(v_val_5589_);
lean_dec_ref_known(v___x_5588_, 1);
v_snd_5590_ = lean_ctor_get(v_val_5589_, 1);
lean_inc(v_snd_5590_);
lean_dec(v_val_5589_);
v___y_5585_ = v_snd_5590_;
goto v___jp_5584_;
}
else
{
lean_dec(v___x_5588_);
v___y_5585_ = v_e_5580_;
goto v___jp_5584_;
}
v___jp_5584_:
{
lean_object* v___x_5586_; lean_object* v___x_5587_; 
v___x_5586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5586_, 0, v___y_5585_);
v___x_5587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5587_, 0, v___x_5586_);
return v___x_5587_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_erasePatternRefAnnotations___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_5580_ = stack[0].m_obj;
lean_object* v___y_5581_ = stack[1].m_obj;
lean_object* v___y_5582_ = stack[2].m_obj;
lean_object* v_res_5591_;
v_res_5591_ = l_Lean_Meta_erasePatternRefAnnotations___lam__1(v_e_5580_, v___y_5581_, v___y_5582_);
stack->m_obj
 = v_res_5591_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_erasePatternRefAnnotations___lam__1___boxed(lean_object* v_e_5592_, lean_object* v___y_5593_, lean_object* v___y_5594_, lean_object* v___y_5595_){
_start:
{
lean_object* v_res_5596_; 
v_res_5596_ = l_Lean_Meta_erasePatternRefAnnotations___lam__1(v_e_5592_, v___y_5593_, v___y_5594_);
lean_dec(v___y_5594_);
lean_dec_ref(v___y_5593_);
return v_res_5596_;
}
}
lean_object* l_Lean_Meta_erasePatternRefAnnotations(lean_object* v_e_5598_, lean_object* v_a_5599_, lean_object* v_a_5600_){
_start:
{
lean_object* v___f_5602_; lean_object* v___f_5603_; lean_object* v___x_5604_; 
v___f_5602_ = ((lean_object*)(l_Lean_Meta_eraseInaccessibleAnnotations___closed__0));
v___f_5603_ = ((lean_object*)(l_Lean_Meta_erasePatternRefAnnotations___closed__0));
v___x_5604_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_5598_, v___f_5602_, v___f_5603_, v_a_5599_, v_a_5600_);
return v___x_5604_;
}
}
LEAN_EXPORT void l_Lean_Meta_erasePatternRefAnnotations_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_5598_ = stack[0].m_obj;
lean_object* v_a_5599_ = stack[1].m_obj;
lean_object* v_a_5600_ = stack[2].m_obj;
lean_object* v_res_5605_;
v_res_5605_ = l_Lean_Meta_erasePatternRefAnnotations(v_e_5598_, v_a_5599_, v_a_5600_);
stack->m_obj
 = v_res_5605_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_erasePatternRefAnnotations___boxed(lean_object* v_e_5606_, lean_object* v_a_5607_, lean_object* v_a_5608_, lean_object* v_a_5609_){
_start:
{
lean_object* v_res_5610_; 
v_res_5610_ = l_Lean_Meta_erasePatternRefAnnotations(v_e_5606_, v_a_5607_, v_a_5608_);
lean_dec(v_a_5608_);
lean_dec_ref(v_a_5607_);
return v_res_5610_;
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
