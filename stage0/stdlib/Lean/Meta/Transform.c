// Lean compiler output
// Module: Lean.Meta.Transform
// Imports: public import Lean.Meta.FunInfo public import Init.Data.Range.Polymorphic.RangeIterator import Init.Data.Range.Polymorphic.Iterators
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
lean_object* l_Lean_Expr_updateAppN(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_ExprStructEq_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_ExprStructEq_hash___boxed(lean_object*);
lean_object* l_Lean_MonadCacheT_instMonad___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadCacheT_instMonadControl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadControlTOfMonadControl___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadControlTOfMonadControl___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_modifyGetUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Expr_withAppAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_checkSystem___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadCacheT_instMonadLift___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadCacheT_instMonad___aux__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_withIncRecDepth___redArg(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__20___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "transform"};
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__20___closed__0 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__20___closed__0_value;
static const lean_closure_object l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__20___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_checkSystem___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__20___closed__0_value)} };
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__20___closed__1 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__20___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__13(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__12___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ExprStructEq_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0_value;
static const lean_closure_object l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ExprStructEq_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__6(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__5(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__7(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__8(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__9___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__10(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__10___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__11(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__18___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__18___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__13___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__20___closed__0_value)} };
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__0(lean_object* v_toApplicative_149_, lean_object* v___x_150_, lean_object* v___x_151_, lean_object* v_e_152_, lean_object* v_a_153_){
_start:
{
lean_object* v_toPure_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
v_toPure_154_ = lean_ctor_get(v_toApplicative_149_, 1);
lean_inc(v_toPure_154_);
lean_dec_ref(v_toApplicative_149_);
v___x_155_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___x_150_, v___x_151_, v_a_153_, v_e_152_);
v___x_156_ = lean_apply_2(v_toPure_154_, lean_box(0), v___x_155_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__0___boxed(lean_object* v_toApplicative_157_, lean_object* v___x_158_, lean_object* v___x_159_, lean_object* v_e_160_, lean_object* v_a_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__0(v_toApplicative_157_, v___x_158_, v___x_159_, v_e_160_, v_a_161_);
lean_dec_ref(v_a_161_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__1(lean_object* v_toApplicative_163_, lean_object* v_a_164_, lean_object* v_a_165_){
_start:
{
lean_object* v_toPure_166_; lean_object* v___x_167_; 
v_toPure_166_ = lean_ctor_get(v_toApplicative_163_, 1);
lean_inc(v_toPure_166_);
lean_dec_ref(v_toApplicative_163_);
v___x_167_ = lean_apply_2(v_toPure_166_, lean_box(0), v_a_164_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__2(lean_object* v___x_168_, lean_object* v___x_169_, lean_object* v_e_170_, lean_object* v_a_171_, lean_object* v_s_172_){
_start:
{
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_173_ = lean_box(0);
v___x_174_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_168_, v___x_169_, v_s_172_, v_e_170_, v_a_171_);
v___x_175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_175_, 0, v___x_173_);
lean_ctor_set(v___x_175_, 1, v___x_174_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__3(lean_object* v_toApplicative_176_, lean_object* v___x_177_, lean_object* v___x_178_, lean_object* v_e_179_, lean_object* v_a_180_, lean_object* v_x_181_, lean_object* v_toBind_182_, lean_object* v_a_183_){
_start:
{
lean_object* v___f_184_; lean_object* v___f_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
lean_inc_ref(v_a_183_);
v___f_184_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__1), 3, 2);
lean_closure_set(v___f_184_, 0, v_toApplicative_176_);
lean_closure_set(v___f_184_, 1, v_a_183_);
v___f_185_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__2), 5, 4);
lean_closure_set(v___f_185_, 0, v___x_177_);
lean_closure_set(v___f_185_, 1, v___x_178_);
lean_closure_set(v___f_185_, 2, v_e_179_);
lean_closure_set(v___f_185_, 3, v_a_183_);
lean_inc(v_a_180_);
v___x_186_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_186_, 0, lean_box(0));
lean_closure_set(v___x_186_, 1, lean_box(0));
lean_closure_set(v___x_186_, 2, lean_box(0));
lean_closure_set(v___x_186_, 3, v_a_180_);
lean_closure_set(v___x_186_, 4, v___f_185_);
v___x_187_ = lean_apply_2(v_x_181_, lean_box(0), v___x_186_);
v___x_188_ = lean_apply_4(v_toBind_182_, lean_box(0), lean_box(0), v___x_187_, v___f_184_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__3___boxed(lean_object* v_toApplicative_189_, lean_object* v___x_190_, lean_object* v___x_191_, lean_object* v_e_192_, lean_object* v_a_193_, lean_object* v_x_194_, lean_object* v_toBind_195_, lean_object* v_a_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__3(v_toApplicative_189_, v___x_190_, v___x_191_, v_e_192_, v_a_193_, v_x_194_, v_toBind_195_, v_a_196_);
lean_dec(v_a_193_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__20(lean_object* v_inst_201_, lean_object* v_x_202_, lean_object* v___x_203_, lean_object* v___x_204_, lean_object* v_inst_205_, lean_object* v___f_206_, lean_object* v___x_207_, lean_object* v___x_208_, lean_object* v_a_209_, lean_object* v_toBind_210_, lean_object* v___f_211_, lean_object* v_toApplicative_212_, lean_object* v_a_213_){
_start:
{
if (lean_obj_tag(v_a_213_) == 0)
{
lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_2753__overap_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
lean_dec_ref(v_toApplicative_212_);
v___x_214_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__20___closed__1));
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
v___x_2753__overap_218_ = l_Lean_Core_withIncRecDepth___redArg(v___x_207_, v___x_208_, v___x_217_);
lean_inc(v_a_209_);
v___x_219_ = lean_apply_1(v___x_2753__overap_218_, v_a_209_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__20___boxed(lean_object* v_inst_224_, lean_object* v_x_225_, lean_object* v___x_226_, lean_object* v___x_227_, lean_object* v_inst_228_, lean_object* v___f_229_, lean_object* v___x_230_, lean_object* v___x_231_, lean_object* v_a_232_, lean_object* v_toBind_233_, lean_object* v___f_234_, lean_object* v_toApplicative_235_, lean_object* v_a_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__20(v_inst_224_, v_x_225_, v___x_226_, v___x_227_, v_inst_228_, v___f_229_, v___x_230_, v___x_231_, v_a_232_, v_toBind_233_, v___f_234_, v_toApplicative_235_, v_a_236_);
lean_dec(v_a_232_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__13(lean_object* v_toApplicative_238_, lean_object* v_a_239_, lean_object* v_a_240_){
_start:
{
lean_object* v_toPure_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v_toPure_241_ = lean_ctor_get(v_toApplicative_238_, 1);
lean_inc(v_toPure_241_);
lean_dec_ref(v_toApplicative_238_);
v___x_242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_242_, 0, v_a_239_);
lean_ctor_set(v___x_242_, 1, v_a_240_);
v___x_243_ = lean_apply_2(v_toPure_241_, lean_box(0), v___x_242_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__12(lean_object* v_toApplicative_244_, lean_object* v___y_245_, lean_object* v_a_246_){
_start:
{
lean_object* v_fst_247_; lean_object* v_snd_248_; lean_object* v_toPure_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v_fst_247_ = lean_ctor_get(v_a_246_, 0);
lean_inc(v_fst_247_);
v_snd_248_ = lean_ctor_get(v_a_246_, 1);
lean_inc(v_snd_248_);
lean_dec_ref(v_a_246_);
v_toPure_249_ = lean_ctor_get(v_toApplicative_244_, 1);
lean_inc(v_toPure_249_);
lean_dec_ref(v_toApplicative_244_);
v___x_250_ = l_Lean_Expr_updateAppN(v___y_245_, v_fst_247_, v_snd_248_);
lean_dec(v_snd_248_);
v___x_251_ = lean_apply_2(v_toPure_249_, lean_box(0), v___x_250_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__12___boxed(lean_object* v_toApplicative_252_, lean_object* v___y_253_, lean_object* v_a_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__12(v_toApplicative_252_, v___y_253_, v_a_254_);
lean_dec_ref(v___y_253_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__4___boxed(lean_object* v_inst_258_, lean_object* v_inst_259_, lean_object* v_inst_260_, lean_object* v_pre_261_, lean_object* v_post_262_, lean_object* v_x_263_, lean_object* v_x_264_, lean_object* v___y_265_, lean_object* v_a_266_){
_start:
{
lean_object* v_res_267_; 
v_res_267_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__4(v_inst_258_, v_inst_259_, v_inst_260_, v_pre_261_, v_post_262_, v_x_263_, v_x_264_, v___y_265_, v_a_266_);
lean_dec(v___y_265_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__6(lean_object* v_binderType_268_, lean_object* v_a_269_, lean_object* v_binderName_270_, uint8_t v_binderInfo_271_, lean_object* v_inst_272_, lean_object* v_inst_273_, lean_object* v_inst_274_, lean_object* v_pre_275_, lean_object* v_post_276_, lean_object* v_x_277_, lean_object* v_x_278_, lean_object* v___y_279_, lean_object* v_body_280_, lean_object* v___y_281_, lean_object* v_a_282_){
_start:
{
size_t v___x_283_; size_t v___x_284_; uint8_t v___x_285_; 
v___x_283_ = lean_ptr_addr(v_binderType_268_);
v___x_284_ = lean_ptr_addr(v_a_269_);
v___x_285_ = lean_usize_dec_eq(v___x_283_, v___x_284_);
if (v___x_285_ == 0)
{
lean_object* v___x_286_; lean_object* v___x_287_; 
lean_dec_ref(v___y_281_);
v___x_286_ = l_Lean_Expr_forallE___override(v_binderName_270_, v_a_269_, v_a_282_, v_binderInfo_271_);
v___x_287_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_272_, v_inst_273_, v_inst_274_, v_pre_275_, v_post_276_, v_x_277_, v_x_278_, v___x_286_, v___y_279_);
return v___x_287_;
}
else
{
size_t v___x_288_; size_t v___x_289_; uint8_t v___x_290_; 
v___x_288_ = lean_ptr_addr(v_body_280_);
v___x_289_ = lean_ptr_addr(v_a_282_);
v___x_290_ = lean_usize_dec_eq(v___x_288_, v___x_289_);
if (v___x_290_ == 0)
{
lean_object* v___x_291_; lean_object* v___x_292_; 
lean_dec_ref(v___y_281_);
v___x_291_ = l_Lean_Expr_forallE___override(v_binderName_270_, v_a_269_, v_a_282_, v_binderInfo_271_);
v___x_292_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_272_, v_inst_273_, v_inst_274_, v_pre_275_, v_post_276_, v_x_277_, v_x_278_, v___x_291_, v___y_279_);
return v___x_292_;
}
else
{
uint8_t v___x_293_; 
v___x_293_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_271_, v_binderInfo_271_);
if (v___x_293_ == 0)
{
lean_object* v___x_294_; lean_object* v___x_295_; 
lean_dec_ref(v___y_281_);
v___x_294_ = l_Lean_Expr_forallE___override(v_binderName_270_, v_a_269_, v_a_282_, v_binderInfo_271_);
v___x_295_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_272_, v_inst_273_, v_inst_274_, v_pre_275_, v_post_276_, v_x_277_, v_x_278_, v___x_294_, v___y_279_);
return v___x_295_;
}
else
{
lean_object* v___x_296_; 
lean_dec_ref(v_a_282_);
lean_dec(v_binderName_270_);
lean_dec_ref(v_a_269_);
v___x_296_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_272_, v_inst_273_, v_inst_274_, v_pre_275_, v_post_276_, v_x_277_, v_x_278_, v___y_281_, v___y_279_);
return v___x_296_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__6___boxed(lean_object* v_binderType_297_, lean_object* v_a_298_, lean_object* v_binderName_299_, lean_object* v_binderInfo_300_, lean_object* v_inst_301_, lean_object* v_inst_302_, lean_object* v_inst_303_, lean_object* v_pre_304_, lean_object* v_post_305_, lean_object* v_x_306_, lean_object* v_x_307_, lean_object* v___y_308_, lean_object* v_body_309_, lean_object* v___y_310_, lean_object* v_a_311_){
_start:
{
uint8_t v_binderInfo_3060__boxed_312_; lean_object* v_res_313_; 
v_binderInfo_3060__boxed_312_ = lean_unbox(v_binderInfo_300_);
v_res_313_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__6(v_binderType_297_, v_a_298_, v_binderName_299_, v_binderInfo_3060__boxed_312_, v_inst_301_, v_inst_302_, v_inst_303_, v_pre_304_, v_post_305_, v_x_306_, v_x_307_, v___y_308_, v_body_309_, v___y_310_, v_a_311_);
lean_dec_ref(v_body_309_);
lean_dec(v___y_308_);
lean_dec_ref(v_binderType_297_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__5(lean_object* v_binderType_314_, lean_object* v_binderName_315_, uint8_t v_binderInfo_316_, lean_object* v_inst_317_, lean_object* v_inst_318_, lean_object* v_inst_319_, lean_object* v_pre_320_, lean_object* v_post_321_, lean_object* v_x_322_, lean_object* v_x_323_, lean_object* v___y_324_, lean_object* v_body_325_, lean_object* v___y_326_, lean_object* v_toBind_327_, lean_object* v_a_328_){
_start:
{
lean_object* v___x_329_; lean_object* v___f_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_329_ = lean_box(v_binderInfo_316_);
lean_inc_ref(v_body_325_);
lean_inc(v___y_324_);
lean_inc(v_x_323_);
lean_inc(v_post_321_);
lean_inc(v_pre_320_);
lean_inc_ref(v_inst_319_);
lean_inc(v_inst_318_);
lean_inc_ref(v_inst_317_);
v___f_330_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__6___boxed), 15, 14);
lean_closure_set(v___f_330_, 0, v_binderType_314_);
lean_closure_set(v___f_330_, 1, v_a_328_);
lean_closure_set(v___f_330_, 2, v_binderName_315_);
lean_closure_set(v___f_330_, 3, v___x_329_);
lean_closure_set(v___f_330_, 4, v_inst_317_);
lean_closure_set(v___f_330_, 5, v_inst_318_);
lean_closure_set(v___f_330_, 6, v_inst_319_);
lean_closure_set(v___f_330_, 7, v_pre_320_);
lean_closure_set(v___f_330_, 8, v_post_321_);
lean_closure_set(v___f_330_, 9, v_x_322_);
lean_closure_set(v___f_330_, 10, v_x_323_);
lean_closure_set(v___f_330_, 11, v___y_324_);
lean_closure_set(v___f_330_, 12, v_body_325_);
lean_closure_set(v___f_330_, 13, v___y_326_);
v___x_331_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_317_, v_inst_318_, v_inst_319_, v_pre_320_, v_post_321_, v_x_322_, v_x_323_, v_body_325_, v___y_324_);
v___x_332_ = lean_apply_4(v_toBind_327_, lean_box(0), lean_box(0), v___x_331_, v___f_330_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__5___boxed(lean_object* v_binderType_333_, lean_object* v_binderName_334_, lean_object* v_binderInfo_335_, lean_object* v_inst_336_, lean_object* v_inst_337_, lean_object* v_inst_338_, lean_object* v_pre_339_, lean_object* v_post_340_, lean_object* v_x_341_, lean_object* v_x_342_, lean_object* v___y_343_, lean_object* v_body_344_, lean_object* v___y_345_, lean_object* v_toBind_346_, lean_object* v_a_347_){
_start:
{
uint8_t v_binderInfo_2921__boxed_348_; lean_object* v_res_349_; 
v_binderInfo_2921__boxed_348_ = lean_unbox(v_binderInfo_335_);
v_res_349_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__5(v_binderType_333_, v_binderName_334_, v_binderInfo_2921__boxed_348_, v_inst_336_, v_inst_337_, v_inst_338_, v_pre_339_, v_post_340_, v_x_341_, v_x_342_, v___y_343_, v_body_344_, v___y_345_, v_toBind_346_, v_a_347_);
lean_dec(v___y_343_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__7(lean_object* v_binderType_350_, lean_object* v_a_351_, lean_object* v_binderName_352_, uint8_t v_binderInfo_353_, lean_object* v_inst_354_, lean_object* v_inst_355_, lean_object* v_inst_356_, lean_object* v_pre_357_, lean_object* v_post_358_, lean_object* v_x_359_, lean_object* v_x_360_, lean_object* v___y_361_, lean_object* v_body_362_, lean_object* v___y_363_, lean_object* v_a_364_){
_start:
{
size_t v___x_365_; size_t v___x_366_; uint8_t v___x_367_; 
v___x_365_ = lean_ptr_addr(v_binderType_350_);
v___x_366_ = lean_ptr_addr(v_a_351_);
v___x_367_ = lean_usize_dec_eq(v___x_365_, v___x_366_);
if (v___x_367_ == 0)
{
lean_object* v___x_368_; lean_object* v___x_369_; 
lean_dec_ref(v___y_363_);
v___x_368_ = l_Lean_Expr_lam___override(v_binderName_352_, v_a_351_, v_a_364_, v_binderInfo_353_);
v___x_369_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_354_, v_inst_355_, v_inst_356_, v_pre_357_, v_post_358_, v_x_359_, v_x_360_, v___x_368_, v___y_361_);
return v___x_369_;
}
else
{
size_t v___x_370_; size_t v___x_371_; uint8_t v___x_372_; 
v___x_370_ = lean_ptr_addr(v_body_362_);
v___x_371_ = lean_ptr_addr(v_a_364_);
v___x_372_ = lean_usize_dec_eq(v___x_370_, v___x_371_);
if (v___x_372_ == 0)
{
lean_object* v___x_373_; lean_object* v___x_374_; 
lean_dec_ref(v___y_363_);
v___x_373_ = l_Lean_Expr_lam___override(v_binderName_352_, v_a_351_, v_a_364_, v_binderInfo_353_);
v___x_374_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_354_, v_inst_355_, v_inst_356_, v_pre_357_, v_post_358_, v_x_359_, v_x_360_, v___x_373_, v___y_361_);
return v___x_374_;
}
else
{
uint8_t v___x_375_; 
v___x_375_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_353_, v_binderInfo_353_);
if (v___x_375_ == 0)
{
lean_object* v___x_376_; lean_object* v___x_377_; 
lean_dec_ref(v___y_363_);
v___x_376_ = l_Lean_Expr_lam___override(v_binderName_352_, v_a_351_, v_a_364_, v_binderInfo_353_);
v___x_377_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_354_, v_inst_355_, v_inst_356_, v_pre_357_, v_post_358_, v_x_359_, v_x_360_, v___x_376_, v___y_361_);
return v___x_377_;
}
else
{
lean_object* v___x_378_; 
lean_dec_ref(v_a_364_);
lean_dec(v_binderName_352_);
lean_dec_ref(v_a_351_);
v___x_378_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_354_, v_inst_355_, v_inst_356_, v_pre_357_, v_post_358_, v_x_359_, v_x_360_, v___y_363_, v___y_361_);
return v___x_378_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__7___boxed(lean_object* v_binderType_379_, lean_object* v_a_380_, lean_object* v_binderName_381_, lean_object* v_binderInfo_382_, lean_object* v_inst_383_, lean_object* v_inst_384_, lean_object* v_inst_385_, lean_object* v_pre_386_, lean_object* v_post_387_, lean_object* v_x_388_, lean_object* v_x_389_, lean_object* v___y_390_, lean_object* v_body_391_, lean_object* v___y_392_, lean_object* v_a_393_){
_start:
{
uint8_t v_binderInfo_3085__boxed_394_; lean_object* v_res_395_; 
v_binderInfo_3085__boxed_394_ = lean_unbox(v_binderInfo_382_);
v_res_395_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__7(v_binderType_379_, v_a_380_, v_binderName_381_, v_binderInfo_3085__boxed_394_, v_inst_383_, v_inst_384_, v_inst_385_, v_pre_386_, v_post_387_, v_x_388_, v_x_389_, v___y_390_, v_body_391_, v___y_392_, v_a_393_);
lean_dec_ref(v_body_391_);
lean_dec(v___y_390_);
lean_dec_ref(v_binderType_379_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__8(lean_object* v_binderType_396_, lean_object* v_binderName_397_, uint8_t v_binderInfo_398_, lean_object* v_inst_399_, lean_object* v_inst_400_, lean_object* v_inst_401_, lean_object* v_pre_402_, lean_object* v_post_403_, lean_object* v_x_404_, lean_object* v_x_405_, lean_object* v___y_406_, lean_object* v_body_407_, lean_object* v___y_408_, lean_object* v_toBind_409_, lean_object* v_a_410_){
_start:
{
lean_object* v___x_411_; lean_object* v___f_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_411_ = lean_box(v_binderInfo_398_);
lean_inc_ref(v_body_407_);
lean_inc(v___y_406_);
lean_inc(v_x_405_);
lean_inc(v_post_403_);
lean_inc(v_pre_402_);
lean_inc_ref(v_inst_401_);
lean_inc(v_inst_400_);
lean_inc_ref(v_inst_399_);
v___f_412_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__7___boxed), 15, 14);
lean_closure_set(v___f_412_, 0, v_binderType_396_);
lean_closure_set(v___f_412_, 1, v_a_410_);
lean_closure_set(v___f_412_, 2, v_binderName_397_);
lean_closure_set(v___f_412_, 3, v___x_411_);
lean_closure_set(v___f_412_, 4, v_inst_399_);
lean_closure_set(v___f_412_, 5, v_inst_400_);
lean_closure_set(v___f_412_, 6, v_inst_401_);
lean_closure_set(v___f_412_, 7, v_pre_402_);
lean_closure_set(v___f_412_, 8, v_post_403_);
lean_closure_set(v___f_412_, 9, v_x_404_);
lean_closure_set(v___f_412_, 10, v_x_405_);
lean_closure_set(v___f_412_, 11, v___y_406_);
lean_closure_set(v___f_412_, 12, v_body_407_);
lean_closure_set(v___f_412_, 13, v___y_408_);
v___x_413_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_399_, v_inst_400_, v_inst_401_, v_pre_402_, v_post_403_, v_x_404_, v_x_405_, v_body_407_, v___y_406_);
v___x_414_ = lean_apply_4(v_toBind_409_, lean_box(0), lean_box(0), v___x_413_, v___f_412_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__8___boxed(lean_object* v_binderType_415_, lean_object* v_binderName_416_, lean_object* v_binderInfo_417_, lean_object* v_inst_418_, lean_object* v_inst_419_, lean_object* v_inst_420_, lean_object* v_pre_421_, lean_object* v_post_422_, lean_object* v_x_423_, lean_object* v_x_424_, lean_object* v___y_425_, lean_object* v_body_426_, lean_object* v___y_427_, lean_object* v_toBind_428_, lean_object* v_a_429_){
_start:
{
uint8_t v_binderInfo_2935__boxed_430_; lean_object* v_res_431_; 
v_binderInfo_2935__boxed_430_ = lean_unbox(v_binderInfo_417_);
v_res_431_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__8(v_binderType_415_, v_binderName_416_, v_binderInfo_2935__boxed_430_, v_inst_418_, v_inst_419_, v_inst_420_, v_pre_421_, v_post_422_, v_x_423_, v_x_424_, v___y_425_, v_body_426_, v___y_427_, v_toBind_428_, v_a_429_);
lean_dec(v___y_425_);
return v_res_431_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__9(lean_object* v_type_432_, lean_object* v_a_433_, lean_object* v_declName_434_, lean_object* v_a_435_, uint8_t v_nondep_436_, lean_object* v_inst_437_, lean_object* v_inst_438_, lean_object* v_inst_439_, lean_object* v_pre_440_, lean_object* v_post_441_, lean_object* v_x_442_, lean_object* v_x_443_, lean_object* v___y_444_, lean_object* v_value_445_, lean_object* v_body_446_, lean_object* v___y_447_, lean_object* v_a_448_){
_start:
{
size_t v___x_449_; size_t v___x_450_; uint8_t v___x_451_; 
v___x_449_ = lean_ptr_addr(v_type_432_);
v___x_450_ = lean_ptr_addr(v_a_433_);
v___x_451_ = lean_usize_dec_eq(v___x_449_, v___x_450_);
if (v___x_451_ == 0)
{
lean_object* v___x_452_; lean_object* v___x_453_; 
lean_dec_ref(v___y_447_);
v___x_452_ = l_Lean_Expr_letE___override(v_declName_434_, v_a_433_, v_a_435_, v_a_448_, v_nondep_436_);
v___x_453_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_437_, v_inst_438_, v_inst_439_, v_pre_440_, v_post_441_, v_x_442_, v_x_443_, v___x_452_, v___y_444_);
return v___x_453_;
}
else
{
size_t v___x_454_; size_t v___x_455_; uint8_t v___x_456_; 
v___x_454_ = lean_ptr_addr(v_value_445_);
v___x_455_ = lean_ptr_addr(v_a_435_);
v___x_456_ = lean_usize_dec_eq(v___x_454_, v___x_455_);
if (v___x_456_ == 0)
{
lean_object* v___x_457_; lean_object* v___x_458_; 
lean_dec_ref(v___y_447_);
v___x_457_ = l_Lean_Expr_letE___override(v_declName_434_, v_a_433_, v_a_435_, v_a_448_, v_nondep_436_);
v___x_458_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_437_, v_inst_438_, v_inst_439_, v_pre_440_, v_post_441_, v_x_442_, v_x_443_, v___x_457_, v___y_444_);
return v___x_458_;
}
else
{
size_t v___x_459_; size_t v___x_460_; uint8_t v___x_461_; 
v___x_459_ = lean_ptr_addr(v_body_446_);
v___x_460_ = lean_ptr_addr(v_a_448_);
v___x_461_ = lean_usize_dec_eq(v___x_459_, v___x_460_);
if (v___x_461_ == 0)
{
lean_object* v___x_462_; lean_object* v___x_463_; 
lean_dec_ref(v___y_447_);
v___x_462_ = l_Lean_Expr_letE___override(v_declName_434_, v_a_433_, v_a_435_, v_a_448_, v_nondep_436_);
v___x_463_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_437_, v_inst_438_, v_inst_439_, v_pre_440_, v_post_441_, v_x_442_, v_x_443_, v___x_462_, v___y_444_);
return v___x_463_;
}
else
{
lean_object* v___x_464_; 
lean_dec_ref(v_a_448_);
lean_dec_ref(v_a_435_);
lean_dec(v_declName_434_);
lean_dec_ref(v_a_433_);
v___x_464_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_437_, v_inst_438_, v_inst_439_, v_pre_440_, v_post_441_, v_x_442_, v_x_443_, v___y_447_, v___y_444_);
return v___x_464_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__9___boxed(lean_object** _args){
lean_object* v_type_465_ = _args[0];
lean_object* v_a_466_ = _args[1];
lean_object* v_declName_467_ = _args[2];
lean_object* v_a_468_ = _args[3];
lean_object* v_nondep_469_ = _args[4];
lean_object* v_inst_470_ = _args[5];
lean_object* v_inst_471_ = _args[6];
lean_object* v_inst_472_ = _args[7];
lean_object* v_pre_473_ = _args[8];
lean_object* v_post_474_ = _args[9];
lean_object* v_x_475_ = _args[10];
lean_object* v_x_476_ = _args[11];
lean_object* v___y_477_ = _args[12];
lean_object* v_value_478_ = _args[13];
lean_object* v_body_479_ = _args[14];
lean_object* v___y_480_ = _args[15];
lean_object* v_a_481_ = _args[16];
_start:
{
uint8_t v_nondep_3110__boxed_482_; lean_object* v_res_483_; 
v_nondep_3110__boxed_482_ = lean_unbox(v_nondep_469_);
v_res_483_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__9(v_type_465_, v_a_466_, v_declName_467_, v_a_468_, v_nondep_3110__boxed_482_, v_inst_470_, v_inst_471_, v_inst_472_, v_pre_473_, v_post_474_, v_x_475_, v_x_476_, v___y_477_, v_value_478_, v_body_479_, v___y_480_, v_a_481_);
lean_dec_ref(v_body_479_);
lean_dec_ref(v_value_478_);
lean_dec(v___y_477_);
lean_dec_ref(v_type_465_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__10(lean_object* v_type_484_, lean_object* v_a_485_, lean_object* v_declName_486_, uint8_t v_nondep_487_, lean_object* v_inst_488_, lean_object* v_inst_489_, lean_object* v_inst_490_, lean_object* v_pre_491_, lean_object* v_post_492_, lean_object* v_x_493_, lean_object* v_x_494_, lean_object* v___y_495_, lean_object* v_value_496_, lean_object* v_body_497_, lean_object* v___y_498_, lean_object* v_toBind_499_, lean_object* v_a_500_){
_start:
{
lean_object* v___x_501_; lean_object* v___f_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_501_ = lean_box(v_nondep_487_);
lean_inc_ref(v_body_497_);
lean_inc(v___y_495_);
lean_inc(v_x_494_);
lean_inc(v_post_492_);
lean_inc(v_pre_491_);
lean_inc_ref(v_inst_490_);
lean_inc(v_inst_489_);
lean_inc_ref(v_inst_488_);
v___f_502_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__9___boxed), 17, 16);
lean_closure_set(v___f_502_, 0, v_type_484_);
lean_closure_set(v___f_502_, 1, v_a_485_);
lean_closure_set(v___f_502_, 2, v_declName_486_);
lean_closure_set(v___f_502_, 3, v_a_500_);
lean_closure_set(v___f_502_, 4, v___x_501_);
lean_closure_set(v___f_502_, 5, v_inst_488_);
lean_closure_set(v___f_502_, 6, v_inst_489_);
lean_closure_set(v___f_502_, 7, v_inst_490_);
lean_closure_set(v___f_502_, 8, v_pre_491_);
lean_closure_set(v___f_502_, 9, v_post_492_);
lean_closure_set(v___f_502_, 10, v_x_493_);
lean_closure_set(v___f_502_, 11, v_x_494_);
lean_closure_set(v___f_502_, 12, v___y_495_);
lean_closure_set(v___f_502_, 13, v_value_496_);
lean_closure_set(v___f_502_, 14, v_body_497_);
lean_closure_set(v___f_502_, 15, v___y_498_);
v___x_503_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_488_, v_inst_489_, v_inst_490_, v_pre_491_, v_post_492_, v_x_493_, v_x_494_, v_body_497_, v___y_495_);
v___x_504_ = lean_apply_4(v_toBind_499_, lean_box(0), lean_box(0), v___x_503_, v___f_502_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__10___boxed(lean_object** _args){
lean_object* v_type_505_ = _args[0];
lean_object* v_a_506_ = _args[1];
lean_object* v_declName_507_ = _args[2];
lean_object* v_nondep_508_ = _args[3];
lean_object* v_inst_509_ = _args[4];
lean_object* v_inst_510_ = _args[5];
lean_object* v_inst_511_ = _args[6];
lean_object* v_pre_512_ = _args[7];
lean_object* v_post_513_ = _args[8];
lean_object* v_x_514_ = _args[9];
lean_object* v_x_515_ = _args[10];
lean_object* v___y_516_ = _args[11];
lean_object* v_value_517_ = _args[12];
lean_object* v_body_518_ = _args[13];
lean_object* v___y_519_ = _args[14];
lean_object* v_toBind_520_ = _args[15];
lean_object* v_a_521_ = _args[16];
_start:
{
uint8_t v_nondep_2891__boxed_522_; lean_object* v_res_523_; 
v_nondep_2891__boxed_522_ = lean_unbox(v_nondep_508_);
v_res_523_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__10(v_type_505_, v_a_506_, v_declName_507_, v_nondep_2891__boxed_522_, v_inst_509_, v_inst_510_, v_inst_511_, v_pre_512_, v_post_513_, v_x_514_, v_x_515_, v___y_516_, v_value_517_, v_body_518_, v___y_519_, v_toBind_520_, v_a_521_);
lean_dec(v___y_516_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__11(lean_object* v_type_524_, lean_object* v_declName_525_, uint8_t v_nondep_526_, lean_object* v_inst_527_, lean_object* v_inst_528_, lean_object* v_inst_529_, lean_object* v_pre_530_, lean_object* v_post_531_, lean_object* v_x_532_, lean_object* v_x_533_, lean_object* v___y_534_, lean_object* v_value_535_, lean_object* v_body_536_, lean_object* v___y_537_, lean_object* v_toBind_538_, lean_object* v_a_539_){
_start:
{
lean_object* v___x_540_; lean_object* v___f_541_; lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_540_ = lean_box(v_nondep_526_);
lean_inc(v_toBind_538_);
lean_inc_ref(v_value_535_);
lean_inc(v___y_534_);
lean_inc(v_x_533_);
lean_inc(v_post_531_);
lean_inc(v_pre_530_);
lean_inc_ref(v_inst_529_);
lean_inc(v_inst_528_);
lean_inc_ref(v_inst_527_);
v___f_541_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__10___boxed), 17, 16);
lean_closure_set(v___f_541_, 0, v_type_524_);
lean_closure_set(v___f_541_, 1, v_a_539_);
lean_closure_set(v___f_541_, 2, v_declName_525_);
lean_closure_set(v___f_541_, 3, v___x_540_);
lean_closure_set(v___f_541_, 4, v_inst_527_);
lean_closure_set(v___f_541_, 5, v_inst_528_);
lean_closure_set(v___f_541_, 6, v_inst_529_);
lean_closure_set(v___f_541_, 7, v_pre_530_);
lean_closure_set(v___f_541_, 8, v_post_531_);
lean_closure_set(v___f_541_, 9, v_x_532_);
lean_closure_set(v___f_541_, 10, v_x_533_);
lean_closure_set(v___f_541_, 11, v___y_534_);
lean_closure_set(v___f_541_, 12, v_value_535_);
lean_closure_set(v___f_541_, 13, v_body_536_);
lean_closure_set(v___f_541_, 14, v___y_537_);
lean_closure_set(v___f_541_, 15, v_toBind_538_);
v___x_542_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_527_, v_inst_528_, v_inst_529_, v_pre_530_, v_post_531_, v_x_532_, v_x_533_, v_value_535_, v___y_534_);
v___x_543_ = lean_apply_4(v_toBind_538_, lean_box(0), lean_box(0), v___x_542_, v___f_541_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__11___boxed(lean_object* v_type_544_, lean_object* v_declName_545_, lean_object* v_nondep_546_, lean_object* v_inst_547_, lean_object* v_inst_548_, lean_object* v_inst_549_, lean_object* v_pre_550_, lean_object* v_post_551_, lean_object* v_x_552_, lean_object* v_x_553_, lean_object* v___y_554_, lean_object* v_value_555_, lean_object* v_body_556_, lean_object* v___y_557_, lean_object* v_toBind_558_, lean_object* v_a_559_){
_start:
{
uint8_t v_nondep_2906__boxed_560_; lean_object* v_res_561_; 
v_nondep_2906__boxed_560_ = lean_unbox(v_nondep_546_);
v_res_561_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__11(v_type_544_, v_declName_545_, v_nondep_2906__boxed_560_, v_inst_547_, v_inst_548_, v_inst_549_, v_pre_550_, v_post_551_, v_x_552_, v_x_553_, v___y_554_, v_value_555_, v_body_556_, v___y_557_, v_toBind_558_, v_a_559_);
lean_dec(v___y_554_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___boxed(lean_object* v_inst_562_, lean_object* v_inst_563_, lean_object* v_inst_564_, lean_object* v_pre_565_, lean_object* v_post_566_, lean_object* v_x_567_, lean_object* v_x_568_, lean_object* v_e_569_, lean_object* v_a_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_562_, v_inst_563_, v_inst_564_, v_pre_565_, v_post_566_, v_x_567_, v_x_568_, v_e_569_, v_a_570_);
lean_dec(v_a_570_);
return v_res_571_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__14(lean_object* v_toApplicative_572_, lean_object* v_inst_573_, lean_object* v_inst_574_, lean_object* v_inst_575_, lean_object* v_pre_576_, lean_object* v_post_577_, lean_object* v_x_578_, lean_object* v_x_579_, lean_object* v_args_580_, lean_object* v___x_581_, lean_object* v___y_582_, lean_object* v_toBind_583_, lean_object* v_a_584_){
_start:
{
lean_object* v___f_585_; lean_object* v___x_586_; size_t v_sz_587_; size_t v___x_588_; lean_object* v___x_2619__overap_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
v___f_585_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__13), 3, 2);
lean_closure_set(v___f_585_, 0, v_toApplicative_572_);
lean_closure_set(v___f_585_, 1, v_a_584_);
v___x_586_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___boxed), 9, 7);
lean_closure_set(v___x_586_, 0, v_inst_573_);
lean_closure_set(v___x_586_, 1, v_inst_574_);
lean_closure_set(v___x_586_, 2, v_inst_575_);
lean_closure_set(v___x_586_, 3, v_pre_576_);
lean_closure_set(v___x_586_, 4, v_post_577_);
lean_closure_set(v___x_586_, 5, v_x_578_);
lean_closure_set(v___x_586_, 6, v_x_579_);
v_sz_587_ = lean_array_size(v_args_580_);
v___x_588_ = ((size_t)0ULL);
v___x_2619__overap_589_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_581_, v___x_586_, v_sz_587_, v___x_588_, v_args_580_);
lean_inc(v___y_582_);
v___x_590_ = lean_apply_1(v___x_2619__overap_589_, v___y_582_);
v___x_591_ = lean_apply_4(v_toBind_583_, lean_box(0), lean_box(0), v___x_590_, v___f_585_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__14___boxed(lean_object* v_toApplicative_592_, lean_object* v_inst_593_, lean_object* v_inst_594_, lean_object* v_inst_595_, lean_object* v_pre_596_, lean_object* v_post_597_, lean_object* v_x_598_, lean_object* v_x_599_, lean_object* v_args_600_, lean_object* v___x_601_, lean_object* v___y_602_, lean_object* v_toBind_603_, lean_object* v_a_604_){
_start:
{
lean_object* v_res_605_; 
v_res_605_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__14(v_toApplicative_592_, v_inst_593_, v_inst_594_, v_inst_595_, v_pre_596_, v_post_597_, v_x_598_, v_x_599_, v_args_600_, v___x_601_, v___y_602_, v_toBind_603_, v_a_604_);
lean_dec(v___y_602_);
return v_res_605_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__15(lean_object* v_toApplicative_606_, lean_object* v_inst_607_, lean_object* v_inst_608_, lean_object* v_inst_609_, lean_object* v_pre_610_, lean_object* v_post_611_, lean_object* v_x_612_, lean_object* v_x_613_, lean_object* v___x_614_, lean_object* v_toBind_615_, lean_object* v___f_616_, lean_object* v_f_617_, lean_object* v_args_618_, lean_object* v___y_619_){
_start:
{
lean_object* v___f_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
lean_inc_n(v_toBind_615_, 2);
lean_inc(v___y_619_);
lean_inc(v_x_613_);
lean_inc(v_post_611_);
lean_inc(v_pre_610_);
lean_inc_ref(v_inst_609_);
lean_inc(v_inst_608_);
lean_inc_ref(v_inst_607_);
v___f_620_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__14___boxed), 13, 12);
lean_closure_set(v___f_620_, 0, v_toApplicative_606_);
lean_closure_set(v___f_620_, 1, v_inst_607_);
lean_closure_set(v___f_620_, 2, v_inst_608_);
lean_closure_set(v___f_620_, 3, v_inst_609_);
lean_closure_set(v___f_620_, 4, v_pre_610_);
lean_closure_set(v___f_620_, 5, v_post_611_);
lean_closure_set(v___f_620_, 6, v_x_612_);
lean_closure_set(v___f_620_, 7, v_x_613_);
lean_closure_set(v___f_620_, 8, v_args_618_);
lean_closure_set(v___f_620_, 9, v___x_614_);
lean_closure_set(v___f_620_, 10, v___y_619_);
lean_closure_set(v___f_620_, 11, v_toBind_615_);
v___x_621_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_607_, v_inst_608_, v_inst_609_, v_pre_610_, v_post_611_, v_x_612_, v_x_613_, v_f_617_, v___y_619_);
v___x_622_ = lean_apply_4(v_toBind_615_, lean_box(0), lean_box(0), v___x_621_, v___f_620_);
v___x_623_ = lean_apply_4(v_toBind_615_, lean_box(0), lean_box(0), v___x_622_, v___f_616_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__15___boxed(lean_object* v_toApplicative_624_, lean_object* v_inst_625_, lean_object* v_inst_626_, lean_object* v_inst_627_, lean_object* v_pre_628_, lean_object* v_post_629_, lean_object* v_x_630_, lean_object* v_x_631_, lean_object* v___x_632_, lean_object* v_toBind_633_, lean_object* v___f_634_, lean_object* v_f_635_, lean_object* v_args_636_, lean_object* v___y_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__15(v_toApplicative_624_, v_inst_625_, v_inst_626_, v_inst_627_, v_pre_628_, v_post_629_, v_x_630_, v_x_631_, v___x_632_, v_toBind_633_, v___f_634_, v_f_635_, v_args_636_, v___y_637_);
lean_dec(v___y_637_);
return v_res_638_;
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__18___closed__0(void){
_start:
{
lean_object* v___x_639_; lean_object* v_dummy_640_; 
v___x_639_ = lean_box(0);
v_dummy_640_ = l_Lean_Expr_sort___override(v___x_639_);
return v_dummy_640_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__16(lean_object* v_expr_641_, lean_object* v_data_642_, lean_object* v_inst_643_, lean_object* v_inst_644_, lean_object* v_inst_645_, lean_object* v_pre_646_, lean_object* v_post_647_, lean_object* v_x_648_, lean_object* v_x_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v_a_652_){
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__16___boxed(lean_object* v_expr_659_, lean_object* v_data_660_, lean_object* v_inst_661_, lean_object* v_inst_662_, lean_object* v_inst_663_, lean_object* v_pre_664_, lean_object* v_post_665_, lean_object* v_x_666_, lean_object* v_x_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v_a_670_){
_start:
{
lean_object* v_res_671_; 
v_res_671_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__16(v_expr_659_, v_data_660_, v_inst_661_, v_inst_662_, v_inst_663_, v_pre_664_, v_post_665_, v_x_666_, v_x_667_, v___y_668_, v___y_669_, v_a_670_);
lean_dec(v___y_668_);
lean_dec_ref(v_expr_659_);
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17(lean_object* v_struct_672_, lean_object* v_typeName_673_, lean_object* v_idx_674_, lean_object* v_inst_675_, lean_object* v_inst_676_, lean_object* v_inst_677_, lean_object* v_pre_678_, lean_object* v_post_679_, lean_object* v_x_680_, lean_object* v_x_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v_a_684_){
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___boxed(lean_object* v_struct_691_, lean_object* v_typeName_692_, lean_object* v_idx_693_, lean_object* v_inst_694_, lean_object* v_inst_695_, lean_object* v_inst_696_, lean_object* v_pre_697_, lean_object* v_post_698_, lean_object* v_x_699_, lean_object* v_x_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v_a_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17(v_struct_691_, v_typeName_692_, v_idx_693_, v_inst_694_, v_inst_695_, v_inst_696_, v_pre_697_, v_post_698_, v_x_699_, v_x_700_, v___y_701_, v___y_702_, v_a_703_);
lean_dec(v___y_701_);
lean_dec_ref(v_struct_691_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__18(lean_object* v_toApplicative_705_, lean_object* v_inst_706_, lean_object* v_inst_707_, lean_object* v_inst_708_, lean_object* v_pre_709_, lean_object* v_post_710_, lean_object* v_x_711_, lean_object* v_x_712_, lean_object* v___y_713_, lean_object* v_toBind_714_, lean_object* v___f_715_, lean_object* v___x_716_, lean_object* v___f_717_, lean_object* v_e_718_, lean_object* v_a_719_){
_start:
{
lean_object* v___y_721_; 
switch(lean_obj_tag(v_a_719_))
{
case 0:
{
lean_object* v_e_769_; lean_object* v_toPure_770_; lean_object* v___x_771_; 
lean_dec_ref(v_e_718_);
lean_dec(v___f_717_);
lean_dec_ref(v___x_716_);
lean_dec(v___f_715_);
lean_dec(v_toBind_714_);
lean_dec(v_x_712_);
lean_dec(v_post_710_);
lean_dec(v_pre_709_);
lean_dec_ref(v_inst_708_);
lean_dec(v_inst_707_);
lean_dec_ref(v_inst_706_);
v_e_769_ = lean_ctor_get(v_a_719_, 0);
lean_inc_ref(v_e_769_);
lean_dec_ref_known(v_a_719_, 1);
v_toPure_770_ = lean_ctor_get(v_toApplicative_705_, 1);
lean_inc(v_toPure_770_);
lean_dec_ref(v_toApplicative_705_);
v___x_771_ = lean_apply_2(v_toPure_770_, lean_box(0), v_e_769_);
return v___x_771_;
}
case 1:
{
lean_object* v_e_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
lean_dec_ref(v_e_718_);
lean_dec(v___f_717_);
lean_dec_ref(v___x_716_);
lean_dec_ref(v_toApplicative_705_);
v_e_772_ = lean_ctor_get(v_a_719_, 0);
lean_inc_ref(v_e_772_);
lean_dec_ref_known(v_a_719_, 1);
v___x_773_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_706_, v_inst_707_, v_inst_708_, v_pre_709_, v_post_710_, v_x_711_, v_x_712_, v_e_772_, v___y_713_);
v___x_774_ = lean_apply_4(v_toBind_714_, lean_box(0), lean_box(0), v___x_773_, v___f_715_);
return v___x_774_;
}
default: 
{
lean_object* v_e_x3f_775_; 
lean_dec(v___f_715_);
v_e_x3f_775_ = lean_ctor_get(v_a_719_, 0);
lean_inc(v_e_x3f_775_);
lean_dec_ref_known(v_a_719_, 1);
if (lean_obj_tag(v_e_x3f_775_) == 0)
{
v___y_721_ = v_e_718_;
goto v___jp_720_;
}
else
{
lean_object* v_val_776_; 
lean_dec_ref(v_e_718_);
v_val_776_ = lean_ctor_get(v_e_x3f_775_, 0);
lean_inc(v_val_776_);
lean_dec_ref_known(v_e_x3f_775_, 1);
v___y_721_ = v_val_776_;
goto v___jp_720_;
}
}
}
v___jp_720_:
{
switch(lean_obj_tag(v___y_721_))
{
case 7:
{
lean_object* v_binderName_722_; lean_object* v_binderType_723_; lean_object* v_body_724_; uint8_t v_binderInfo_725_; lean_object* v___x_726_; lean_object* v___f_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
lean_dec(v___f_717_);
lean_dec_ref(v___x_716_);
lean_dec_ref(v_toApplicative_705_);
v_binderName_722_ = lean_ctor_get(v___y_721_, 0);
lean_inc(v_binderName_722_);
v_binderType_723_ = lean_ctor_get(v___y_721_, 1);
lean_inc_ref_n(v_binderType_723_, 2);
v_body_724_ = lean_ctor_get(v___y_721_, 2);
lean_inc_ref(v_body_724_);
v_binderInfo_725_ = lean_ctor_get_uint8(v___y_721_, sizeof(void*)*3 + 8);
v___x_726_ = lean_box(v_binderInfo_725_);
lean_inc(v_toBind_714_);
lean_inc(v___y_713_);
lean_inc(v_x_712_);
lean_inc(v_post_710_);
lean_inc(v_pre_709_);
lean_inc_ref(v_inst_708_);
lean_inc(v_inst_707_);
lean_inc_ref(v_inst_706_);
v___f_727_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__5___boxed), 15, 14);
lean_closure_set(v___f_727_, 0, v_binderType_723_);
lean_closure_set(v___f_727_, 1, v_binderName_722_);
lean_closure_set(v___f_727_, 2, v___x_726_);
lean_closure_set(v___f_727_, 3, v_inst_706_);
lean_closure_set(v___f_727_, 4, v_inst_707_);
lean_closure_set(v___f_727_, 5, v_inst_708_);
lean_closure_set(v___f_727_, 6, v_pre_709_);
lean_closure_set(v___f_727_, 7, v_post_710_);
lean_closure_set(v___f_727_, 8, v_x_711_);
lean_closure_set(v___f_727_, 9, v_x_712_);
lean_closure_set(v___f_727_, 10, v___y_713_);
lean_closure_set(v___f_727_, 11, v_body_724_);
lean_closure_set(v___f_727_, 12, v___y_721_);
lean_closure_set(v___f_727_, 13, v_toBind_714_);
v___x_728_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_706_, v_inst_707_, v_inst_708_, v_pre_709_, v_post_710_, v_x_711_, v_x_712_, v_binderType_723_, v___y_713_);
v___x_729_ = lean_apply_4(v_toBind_714_, lean_box(0), lean_box(0), v___x_728_, v___f_727_);
return v___x_729_;
}
case 6:
{
lean_object* v_binderName_730_; lean_object* v_binderType_731_; lean_object* v_body_732_; uint8_t v_binderInfo_733_; lean_object* v___x_734_; lean_object* v___f_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
lean_dec(v___f_717_);
lean_dec_ref(v___x_716_);
lean_dec_ref(v_toApplicative_705_);
v_binderName_730_ = lean_ctor_get(v___y_721_, 0);
lean_inc(v_binderName_730_);
v_binderType_731_ = lean_ctor_get(v___y_721_, 1);
lean_inc_ref_n(v_binderType_731_, 2);
v_body_732_ = lean_ctor_get(v___y_721_, 2);
lean_inc_ref(v_body_732_);
v_binderInfo_733_ = lean_ctor_get_uint8(v___y_721_, sizeof(void*)*3 + 8);
v___x_734_ = lean_box(v_binderInfo_733_);
lean_inc(v_toBind_714_);
lean_inc(v___y_713_);
lean_inc(v_x_712_);
lean_inc(v_post_710_);
lean_inc(v_pre_709_);
lean_inc_ref(v_inst_708_);
lean_inc(v_inst_707_);
lean_inc_ref(v_inst_706_);
v___f_735_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__8___boxed), 15, 14);
lean_closure_set(v___f_735_, 0, v_binderType_731_);
lean_closure_set(v___f_735_, 1, v_binderName_730_);
lean_closure_set(v___f_735_, 2, v___x_734_);
lean_closure_set(v___f_735_, 3, v_inst_706_);
lean_closure_set(v___f_735_, 4, v_inst_707_);
lean_closure_set(v___f_735_, 5, v_inst_708_);
lean_closure_set(v___f_735_, 6, v_pre_709_);
lean_closure_set(v___f_735_, 7, v_post_710_);
lean_closure_set(v___f_735_, 8, v_x_711_);
lean_closure_set(v___f_735_, 9, v_x_712_);
lean_closure_set(v___f_735_, 10, v___y_713_);
lean_closure_set(v___f_735_, 11, v_body_732_);
lean_closure_set(v___f_735_, 12, v___y_721_);
lean_closure_set(v___f_735_, 13, v_toBind_714_);
v___x_736_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_706_, v_inst_707_, v_inst_708_, v_pre_709_, v_post_710_, v_x_711_, v_x_712_, v_binderType_731_, v___y_713_);
v___x_737_ = lean_apply_4(v_toBind_714_, lean_box(0), lean_box(0), v___x_736_, v___f_735_);
return v___x_737_;
}
case 8:
{
lean_object* v_declName_738_; lean_object* v_type_739_; lean_object* v_value_740_; lean_object* v_body_741_; uint8_t v_nondep_742_; lean_object* v___x_743_; lean_object* v___f_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
lean_dec(v___f_717_);
lean_dec_ref(v___x_716_);
lean_dec_ref(v_toApplicative_705_);
v_declName_738_ = lean_ctor_get(v___y_721_, 0);
lean_inc(v_declName_738_);
v_type_739_ = lean_ctor_get(v___y_721_, 1);
lean_inc_ref_n(v_type_739_, 2);
v_value_740_ = lean_ctor_get(v___y_721_, 2);
lean_inc_ref(v_value_740_);
v_body_741_ = lean_ctor_get(v___y_721_, 3);
lean_inc_ref(v_body_741_);
v_nondep_742_ = lean_ctor_get_uint8(v___y_721_, sizeof(void*)*4 + 8);
v___x_743_ = lean_box(v_nondep_742_);
lean_inc(v_toBind_714_);
lean_inc(v___y_713_);
lean_inc(v_x_712_);
lean_inc(v_post_710_);
lean_inc(v_pre_709_);
lean_inc_ref(v_inst_708_);
lean_inc(v_inst_707_);
lean_inc_ref(v_inst_706_);
v___f_744_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__11___boxed), 16, 15);
lean_closure_set(v___f_744_, 0, v_type_739_);
lean_closure_set(v___f_744_, 1, v_declName_738_);
lean_closure_set(v___f_744_, 2, v___x_743_);
lean_closure_set(v___f_744_, 3, v_inst_706_);
lean_closure_set(v___f_744_, 4, v_inst_707_);
lean_closure_set(v___f_744_, 5, v_inst_708_);
lean_closure_set(v___f_744_, 6, v_pre_709_);
lean_closure_set(v___f_744_, 7, v_post_710_);
lean_closure_set(v___f_744_, 8, v_x_711_);
lean_closure_set(v___f_744_, 9, v_x_712_);
lean_closure_set(v___f_744_, 10, v___y_713_);
lean_closure_set(v___f_744_, 11, v_value_740_);
lean_closure_set(v___f_744_, 12, v_body_741_);
lean_closure_set(v___f_744_, 13, v___y_721_);
lean_closure_set(v___f_744_, 14, v_toBind_714_);
v___x_745_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_706_, v_inst_707_, v_inst_708_, v_pre_709_, v_post_710_, v_x_711_, v_x_712_, v_type_739_, v___y_713_);
v___x_746_ = lean_apply_4(v_toBind_714_, lean_box(0), lean_box(0), v___x_745_, v___f_744_);
return v___x_746_;
}
case 5:
{
lean_object* v___f_747_; lean_object* v___f_748_; lean_object* v_dummy_749_; lean_object* v_nargs_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_2711__overap_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
lean_inc_ref(v___y_721_);
lean_inc_ref(v_toApplicative_705_);
v___f_747_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__12___boxed), 3, 2);
lean_closure_set(v___f_747_, 0, v_toApplicative_705_);
lean_closure_set(v___f_747_, 1, v___y_721_);
lean_inc(v_toBind_714_);
v___f_748_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__15___boxed), 14, 11);
lean_closure_set(v___f_748_, 0, v_toApplicative_705_);
lean_closure_set(v___f_748_, 1, v_inst_706_);
lean_closure_set(v___f_748_, 2, v_inst_707_);
lean_closure_set(v___f_748_, 3, v_inst_708_);
lean_closure_set(v___f_748_, 4, v_pre_709_);
lean_closure_set(v___f_748_, 5, v_post_710_);
lean_closure_set(v___f_748_, 6, v_x_711_);
lean_closure_set(v___f_748_, 7, v_x_712_);
lean_closure_set(v___f_748_, 8, v___x_716_);
lean_closure_set(v___f_748_, 9, v_toBind_714_);
lean_closure_set(v___f_748_, 10, v___f_747_);
v_dummy_749_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__18___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__18___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__18___closed__0);
v_nargs_750_ = l_Lean_Expr_getAppNumArgs(v___y_721_);
lean_inc(v_nargs_750_);
v___x_751_ = lean_mk_array(v_nargs_750_, v_dummy_749_);
v___x_752_ = lean_unsigned_to_nat(1u);
v___x_753_ = lean_nat_sub(v_nargs_750_, v___x_752_);
lean_dec(v_nargs_750_);
v___x_2711__overap_754_ = l_Lean_Expr_withAppAux___redArg(v___f_748_, v___y_721_, v___x_751_, v___x_753_);
lean_inc(v___y_713_);
v___x_755_ = lean_apply_1(v___x_2711__overap_754_, v___y_713_);
v___x_756_ = lean_apply_4(v_toBind_714_, lean_box(0), lean_box(0), v___x_755_, v___f_717_);
return v___x_756_;
}
case 10:
{
lean_object* v_data_757_; lean_object* v_expr_758_; lean_object* v___f_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
lean_dec(v___f_717_);
lean_dec_ref(v___x_716_);
lean_dec_ref(v_toApplicative_705_);
v_data_757_ = lean_ctor_get(v___y_721_, 0);
lean_inc(v_data_757_);
v_expr_758_ = lean_ctor_get(v___y_721_, 1);
lean_inc_ref_n(v_expr_758_, 2);
lean_inc(v___y_713_);
lean_inc(v_x_712_);
lean_inc(v_post_710_);
lean_inc(v_pre_709_);
lean_inc_ref(v_inst_708_);
lean_inc(v_inst_707_);
lean_inc_ref(v_inst_706_);
v___f_759_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__16___boxed), 12, 11);
lean_closure_set(v___f_759_, 0, v_expr_758_);
lean_closure_set(v___f_759_, 1, v_data_757_);
lean_closure_set(v___f_759_, 2, v_inst_706_);
lean_closure_set(v___f_759_, 3, v_inst_707_);
lean_closure_set(v___f_759_, 4, v_inst_708_);
lean_closure_set(v___f_759_, 5, v_pre_709_);
lean_closure_set(v___f_759_, 6, v_post_710_);
lean_closure_set(v___f_759_, 7, v_x_711_);
lean_closure_set(v___f_759_, 8, v_x_712_);
lean_closure_set(v___f_759_, 9, v___y_713_);
lean_closure_set(v___f_759_, 10, v___y_721_);
v___x_760_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_706_, v_inst_707_, v_inst_708_, v_pre_709_, v_post_710_, v_x_711_, v_x_712_, v_expr_758_, v___y_713_);
v___x_761_ = lean_apply_4(v_toBind_714_, lean_box(0), lean_box(0), v___x_760_, v___f_759_);
return v___x_761_;
}
case 11:
{
lean_object* v_typeName_762_; lean_object* v_idx_763_; lean_object* v_struct_764_; lean_object* v___f_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
lean_dec(v___f_717_);
lean_dec_ref(v___x_716_);
lean_dec_ref(v_toApplicative_705_);
v_typeName_762_ = lean_ctor_get(v___y_721_, 0);
lean_inc(v_typeName_762_);
v_idx_763_ = lean_ctor_get(v___y_721_, 1);
lean_inc(v_idx_763_);
v_struct_764_ = lean_ctor_get(v___y_721_, 2);
lean_inc_ref_n(v_struct_764_, 2);
lean_inc(v___y_713_);
lean_inc(v_x_712_);
lean_inc(v_post_710_);
lean_inc(v_pre_709_);
lean_inc_ref(v_inst_708_);
lean_inc(v_inst_707_);
lean_inc_ref(v_inst_706_);
v___f_765_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__17___boxed), 13, 12);
lean_closure_set(v___f_765_, 0, v_struct_764_);
lean_closure_set(v___f_765_, 1, v_typeName_762_);
lean_closure_set(v___f_765_, 2, v_idx_763_);
lean_closure_set(v___f_765_, 3, v_inst_706_);
lean_closure_set(v___f_765_, 4, v_inst_707_);
lean_closure_set(v___f_765_, 5, v_inst_708_);
lean_closure_set(v___f_765_, 6, v_pre_709_);
lean_closure_set(v___f_765_, 7, v_post_710_);
lean_closure_set(v___f_765_, 8, v_x_711_);
lean_closure_set(v___f_765_, 9, v_x_712_);
lean_closure_set(v___f_765_, 10, v___y_713_);
lean_closure_set(v___f_765_, 11, v___y_721_);
v___x_766_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_706_, v_inst_707_, v_inst_708_, v_pre_709_, v_post_710_, v_x_711_, v_x_712_, v_struct_764_, v___y_713_);
v___x_767_ = lean_apply_4(v_toBind_714_, lean_box(0), lean_box(0), v___x_766_, v___f_765_);
return v___x_767_;
}
default: 
{
lean_object* v___x_768_; 
lean_dec(v___f_717_);
lean_dec_ref(v___x_716_);
lean_dec(v_toBind_714_);
lean_dec_ref(v_toApplicative_705_);
v___x_768_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_706_, v_inst_707_, v_inst_708_, v_pre_709_, v_post_710_, v_x_711_, v_x_712_, v___y_721_, v___y_713_);
return v___x_768_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__18___boxed(lean_object* v_toApplicative_777_, lean_object* v_inst_778_, lean_object* v_inst_779_, lean_object* v_inst_780_, lean_object* v_pre_781_, lean_object* v_post_782_, lean_object* v_x_783_, lean_object* v_x_784_, lean_object* v___y_785_, lean_object* v_toBind_786_, lean_object* v___f_787_, lean_object* v___x_788_, lean_object* v___f_789_, lean_object* v_e_790_, lean_object* v_a_791_){
_start:
{
lean_object* v_res_792_; 
v_res_792_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__18(v_toApplicative_777_, v_inst_778_, v_inst_779_, v_inst_780_, v_pre_781_, v_post_782_, v_x_783_, v_x_784_, v___y_785_, v_toBind_786_, v___f_787_, v___x_788_, v___f_789_, v_e_790_, v_a_791_);
lean_dec(v___y_785_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__19(lean_object* v_inst_793_, lean_object* v_inst_794_, lean_object* v_inst_795_, lean_object* v_pre_796_, lean_object* v_post_797_, lean_object* v_x_798_, lean_object* v_x_799_, lean_object* v_toApplicative_800_, lean_object* v_toBind_801_, lean_object* v___x_802_, lean_object* v_e_803_, lean_object* v_____r_804_, lean_object* v___y_805_){
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
v___f_806_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__4___boxed), 9, 8);
lean_closure_set(v___f_806_, 0, v_inst_793_);
lean_closure_set(v___f_806_, 1, v_inst_794_);
lean_closure_set(v___f_806_, 2, v_inst_795_);
lean_closure_set(v___f_806_, 3, v_pre_796_);
lean_closure_set(v___f_806_, 4, v_post_797_);
lean_closure_set(v___f_806_, 5, v_x_798_);
lean_closure_set(v___f_806_, 6, v_x_799_);
lean_closure_set(v___f_806_, 7, v___y_805_);
lean_inc_ref(v_e_803_);
lean_inc_ref(v___f_806_);
lean_inc(v_toBind_801_);
v___f_807_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__18___boxed), 15, 14);
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
lean_closure_set(v___f_807_, 11, v___x_802_);
lean_closure_set(v___f_807_, 12, v___f_806_);
lean_closure_set(v___f_807_, 13, v_e_803_);
v___x_808_ = lean_apply_1(v_pre_796_, v_e_803_);
v___x_809_ = lean_apply_4(v_toBind_801_, lean_box(0), lean_box(0), v___x_808_, v___f_807_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__19___boxed(lean_object* v_inst_810_, lean_object* v_inst_811_, lean_object* v_inst_812_, lean_object* v_pre_813_, lean_object* v_post_814_, lean_object* v_x_815_, lean_object* v_x_816_, lean_object* v_toApplicative_817_, lean_object* v_toBind_818_, lean_object* v___x_819_, lean_object* v_e_820_, lean_object* v_____r_821_, lean_object* v___y_822_){
_start:
{
lean_object* v_res_823_; 
v_res_823_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__19(v_inst_810_, v_inst_811_, v_inst_812_, v_pre_813_, v_post_814_, v_x_815_, v_x_816_, v_toApplicative_817_, v_toBind_818_, v___x_819_, v_e_820_, v_____r_821_, v___y_822_);
lean_dec(v___y_822_);
return v_res_823_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(lean_object* v_inst_824_, lean_object* v_inst_825_, lean_object* v_inst_826_, lean_object* v_pre_827_, lean_object* v_post_828_, lean_object* v_x_829_, lean_object* v_x_830_, lean_object* v_e_831_, lean_object* v_a_832_){
_start:
{
lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___f_837_; lean_object* v___f_838_; lean_object* v___x_839_; lean_object* v_toApplicative_840_; lean_object* v_toBind_841_; lean_object* v___f_842_; lean_object* v___f_843_; lean_object* v___f_844_; lean_object* v___f_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_833_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0));
v___x_834_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1));
lean_inc_ref_n(v_inst_824_, 2);
v___x_835_ = l_Lean_MonadCacheT_instMonad___redArg(v_x_829_, v___x_833_, v___x_834_, v_inst_824_);
v___x_836_ = l_Lean_MonadCacheT_instMonadControl___redArg(v_x_829_, v___x_833_, v___x_834_);
lean_inc_ref_n(v_inst_826_, 2);
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
lean_inc_n(v_toBind_841_, 5);
lean_inc_ref_n(v_e_831_, 2);
v___f_842_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_842_, 0, v_toApplicative_840_);
lean_closure_set(v___f_842_, 1, v___x_833_);
lean_closure_set(v___f_842_, 2, v___x_834_);
lean_closure_set(v___f_842_, 3, v_e_831_);
lean_inc_n(v_x_830_, 2);
lean_inc_n(v_a_832_, 3);
v___f_843_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__3___boxed), 8, 7);
lean_closure_set(v___f_843_, 0, v_toApplicative_840_);
lean_closure_set(v___f_843_, 1, v___x_833_);
lean_closure_set(v___f_843_, 2, v___x_834_);
lean_closure_set(v___f_843_, 3, v_e_831_);
lean_closure_set(v___f_843_, 4, v_a_832_);
lean_closure_set(v___f_843_, 5, v_x_830_);
lean_closure_set(v___f_843_, 6, v_toBind_841_);
lean_inc_ref(v___x_835_);
lean_inc(v_inst_825_);
v___f_844_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__19___boxed), 13, 11);
lean_closure_set(v___f_844_, 0, v_inst_824_);
lean_closure_set(v___f_844_, 1, v_inst_825_);
lean_closure_set(v___f_844_, 2, v_inst_826_);
lean_closure_set(v___f_844_, 3, v_pre_827_);
lean_closure_set(v___f_844_, 4, v_post_828_);
lean_closure_set(v___f_844_, 5, v_x_829_);
lean_closure_set(v___f_844_, 6, v_x_830_);
lean_closure_set(v___f_844_, 7, v_toApplicative_840_);
lean_closure_set(v___f_844_, 8, v_toBind_841_);
lean_closure_set(v___f_844_, 9, v___x_835_);
lean_closure_set(v___f_844_, 10, v_e_831_);
v___f_845_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__20___boxed), 13, 12);
lean_closure_set(v___f_845_, 0, v_inst_825_);
lean_closure_set(v___f_845_, 1, v_x_829_);
lean_closure_set(v___f_845_, 2, v___x_833_);
lean_closure_set(v___f_845_, 3, v___x_834_);
lean_closure_set(v___f_845_, 4, v_inst_824_);
lean_closure_set(v___f_845_, 5, v___f_844_);
lean_closure_set(v___f_845_, 6, v___x_835_);
lean_closure_set(v___f_845_, 7, v___x_839_);
lean_closure_set(v___f_845_, 8, v_a_832_);
lean_closure_set(v___f_845_, 9, v_toBind_841_);
lean_closure_set(v___f_845_, 10, v___f_843_);
lean_closure_set(v___f_845_, 11, v_toApplicative_840_);
v___x_846_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_846_, 0, lean_box(0));
lean_closure_set(v___x_846_, 1, lean_box(0));
lean_closure_set(v___x_846_, 2, v_a_832_);
v___x_847_ = lean_apply_2(v_x_830_, lean_box(0), v___x_846_);
v___x_848_ = lean_apply_4(v_toBind_841_, lean_box(0), lean_box(0), v___x_847_, v___f_842_);
v___x_849_ = lean_apply_4(v_toBind_841_, lean_box(0), lean_box(0), v___x_848_, v___f_845_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg___lam__0(lean_object* v_toApplicative_850_, lean_object* v_inst_851_, lean_object* v_inst_852_, lean_object* v_inst_853_, lean_object* v_pre_854_, lean_object* v_post_855_, lean_object* v_x_856_, lean_object* v_x_857_, lean_object* v_a_858_, lean_object* v_e_859_, lean_object* v_a_860_){
_start:
{
lean_object* v___y_862_; 
switch(lean_obj_tag(v_a_860_))
{
case 0:
{
lean_object* v_e_865_; lean_object* v_toPure_866_; lean_object* v___x_867_; 
lean_dec_ref(v_e_859_);
lean_dec(v_x_857_);
lean_dec(v_post_855_);
lean_dec(v_pre_854_);
lean_dec_ref(v_inst_853_);
lean_dec(v_inst_852_);
lean_dec_ref(v_inst_851_);
v_e_865_ = lean_ctor_get(v_a_860_, 0);
lean_inc_ref(v_e_865_);
lean_dec_ref_known(v_a_860_, 1);
v_toPure_866_ = lean_ctor_get(v_toApplicative_850_, 1);
lean_inc(v_toPure_866_);
lean_dec_ref(v_toApplicative_850_);
v___x_867_ = lean_apply_2(v_toPure_866_, lean_box(0), v_e_865_);
return v___x_867_;
}
case 1:
{
lean_object* v_e_868_; lean_object* v___x_869_; 
lean_dec_ref(v_e_859_);
lean_dec_ref(v_toApplicative_850_);
v_e_868_ = lean_ctor_get(v_a_860_, 0);
lean_inc_ref(v_e_868_);
lean_dec_ref_known(v_a_860_, 1);
v___x_869_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_851_, v_inst_852_, v_inst_853_, v_pre_854_, v_post_855_, v_x_856_, v_x_857_, v_e_868_, v_a_858_);
return v___x_869_;
}
default: 
{
lean_object* v_e_x3f_870_; 
lean_dec(v_x_857_);
lean_dec(v_post_855_);
lean_dec(v_pre_854_);
lean_dec_ref(v_inst_853_);
lean_dec(v_inst_852_);
lean_dec_ref(v_inst_851_);
v_e_x3f_870_ = lean_ctor_get(v_a_860_, 0);
lean_inc(v_e_x3f_870_);
lean_dec_ref_known(v_a_860_, 1);
if (lean_obj_tag(v_e_x3f_870_) == 0)
{
v___y_862_ = v_e_859_;
goto v___jp_861_;
}
else
{
lean_object* v_val_871_; 
lean_dec_ref(v_e_859_);
v_val_871_ = lean_ctor_get(v_e_x3f_870_, 0);
lean_inc(v_val_871_);
lean_dec_ref_known(v_e_x3f_870_, 1);
v___y_862_ = v_val_871_;
goto v___jp_861_;
}
}
}
v___jp_861_:
{
lean_object* v_toPure_863_; lean_object* v___x_864_; 
v_toPure_863_ = lean_ctor_get(v_toApplicative_850_, 1);
lean_inc(v_toPure_863_);
lean_dec_ref(v_toApplicative_850_);
v___x_864_ = lean_apply_2(v_toPure_863_, lean_box(0), v___y_862_);
return v___x_864_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg___lam__0___boxed(lean_object* v_toApplicative_872_, lean_object* v_inst_873_, lean_object* v_inst_874_, lean_object* v_inst_875_, lean_object* v_pre_876_, lean_object* v_post_877_, lean_object* v_x_878_, lean_object* v_x_879_, lean_object* v_a_880_, lean_object* v_e_881_, lean_object* v_a_882_){
_start:
{
lean_object* v_res_883_; 
v_res_883_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg___lam__0(v_toApplicative_872_, v_inst_873_, v_inst_874_, v_inst_875_, v_pre_876_, v_post_877_, v_x_878_, v_x_879_, v_a_880_, v_e_881_, v_a_882_);
lean_dec(v_a_880_);
return v_res_883_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(lean_object* v_inst_884_, lean_object* v_inst_885_, lean_object* v_inst_886_, lean_object* v_pre_887_, lean_object* v_post_888_, lean_object* v_x_889_, lean_object* v_x_890_, lean_object* v_e_891_, lean_object* v_a_892_){
_start:
{
lean_object* v_toApplicative_893_; lean_object* v_toBind_894_; lean_object* v___f_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
v_toApplicative_893_ = lean_ctor_get(v_inst_884_, 0);
lean_inc_ref(v_toApplicative_893_);
v_toBind_894_ = lean_ctor_get(v_inst_884_, 1);
lean_inc(v_toBind_894_);
lean_inc_ref(v_e_891_);
lean_inc(v_a_892_);
lean_inc(v_post_888_);
v___f_895_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg___lam__0___boxed), 11, 10);
lean_closure_set(v___f_895_, 0, v_toApplicative_893_);
lean_closure_set(v___f_895_, 1, v_inst_884_);
lean_closure_set(v___f_895_, 2, v_inst_885_);
lean_closure_set(v___f_895_, 3, v_inst_886_);
lean_closure_set(v___f_895_, 4, v_pre_887_);
lean_closure_set(v___f_895_, 5, v_post_888_);
lean_closure_set(v___f_895_, 6, v_x_889_);
lean_closure_set(v___f_895_, 7, v_x_890_);
lean_closure_set(v___f_895_, 8, v_a_892_);
lean_closure_set(v___f_895_, 9, v_e_891_);
v___x_896_ = lean_apply_1(v_post_888_, v_e_891_);
v___x_897_ = lean_apply_4(v_toBind_894_, lean_box(0), lean_box(0), v___x_896_, v___f_895_);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__4(lean_object* v_inst_898_, lean_object* v_inst_899_, lean_object* v_inst_900_, lean_object* v_pre_901_, lean_object* v_post_902_, lean_object* v_x_903_, lean_object* v_x_904_, lean_object* v___y_905_, lean_object* v_a_906_){
_start:
{
lean_object* v___x_907_; 
v___x_907_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_898_, v_inst_899_, v_inst_900_, v_pre_901_, v_post_902_, v_x_903_, v_x_904_, v_a_906_, v___y_905_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg___boxed(lean_object* v_inst_908_, lean_object* v_inst_909_, lean_object* v_inst_910_, lean_object* v_pre_911_, lean_object* v_post_912_, lean_object* v_x_913_, lean_object* v_x_914_, lean_object* v_e_915_, lean_object* v_a_916_){
_start:
{
lean_object* v_res_917_; 
v_res_917_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_908_, v_inst_909_, v_inst_910_, v_pre_911_, v_post_912_, v_x_913_, v_x_914_, v_e_915_, v_a_916_);
lean_dec(v_a_916_);
return v_res_917_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit(lean_object* v_m_918_, lean_object* v_inst_919_, lean_object* v_inst_920_, lean_object* v_inst_921_, lean_object* v_pre_922_, lean_object* v_post_923_, lean_object* v_x_924_, lean_object* v_x_925_, lean_object* v_e_926_, lean_object* v_a_927_){
_start:
{
lean_object* v___x_928_; 
v___x_928_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_919_, v_inst_920_, v_inst_921_, v_pre_922_, v_post_923_, v_x_924_, v_x_925_, v_e_926_, v_a_927_);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___boxed(lean_object* v_m_929_, lean_object* v_inst_930_, lean_object* v_inst_931_, lean_object* v_inst_932_, lean_object* v_pre_933_, lean_object* v_post_934_, lean_object* v_x_935_, lean_object* v_x_936_, lean_object* v_e_937_, lean_object* v_a_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit(v_m_929_, v_inst_930_, v_inst_931_, v_inst_932_, v_pre_933_, v_post_934_, v_x_935_, v_x_936_, v_e_937_, v_a_938_);
lean_dec(v_a_938_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost(lean_object* v_m_940_, lean_object* v_inst_941_, lean_object* v_inst_942_, lean_object* v_inst_943_, lean_object* v_pre_944_, lean_object* v_post_945_, lean_object* v_x_946_, lean_object* v_x_947_, lean_object* v_e_948_, lean_object* v_a_949_){
_start:
{
lean_object* v___x_950_; 
v___x_950_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___redArg(v_inst_941_, v_inst_942_, v_inst_943_, v_pre_944_, v_post_945_, v_x_946_, v_x_947_, v_e_948_, v_a_949_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___boxed(lean_object* v_m_951_, lean_object* v_inst_952_, lean_object* v_inst_953_, lean_object* v_inst_954_, lean_object* v_pre_955_, lean_object* v_post_956_, lean_object* v_x_957_, lean_object* v_x_958_, lean_object* v_e_959_, lean_object* v_a_960_){
_start:
{
lean_object* v_res_961_; 
v_res_961_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost(v_m_951_, v_inst_952_, v_inst_953_, v_inst_954_, v_pre_955_, v_post_956_, v_x_957_, v_x_958_, v_e_959_, v_a_960_);
lean_dec(v_a_960_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___redArg___lam__0(lean_object* v_x_962_){
_start:
{
lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_964_ = lean_apply_1(v_x_962_, lean_box(0));
v___x_965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_965_, 0, v___x_964_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___redArg___lam__0___boxed(lean_object* v_x_966_, lean_object* v___y_967_){
_start:
{
lean_object* v_res_968_; 
v_res_968_ = l_Lean_Core_transform___redArg___lam__0(v_x_966_);
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___redArg___lam__1(lean_object* v_inst_969_, lean_object* v_00_u03b1_970_, lean_object* v_x_971_){
_start:
{
lean_object* v___f_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
v___f_972_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_972_, 0, v_x_971_);
v___x_973_ = lean_alloc_closure((void*)(l_Lean_Core_liftIOCore___boxed), 5, 2);
lean_closure_set(v___x_973_, 0, lean_box(0));
lean_closure_set(v___x_973_, 1, v___f_972_);
v___x_974_ = lean_apply_2(v_inst_969_, lean_box(0), v___x_973_);
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___redArg___lam__2(lean_object* v_toPure_975_, lean_object* v_____x_976_){
_start:
{
lean_object* v_fst_977_; lean_object* v___x_978_; 
v_fst_977_ = lean_ctor_get(v_____x_976_, 0);
lean_inc(v_fst_977_);
lean_dec_ref(v_____x_976_);
v___x_978_ = lean_apply_2(v_toPure_975_, lean_box(0), v_fst_977_);
return v___x_978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___redArg___lam__3(lean_object* v_a_979_, lean_object* v_toPure_980_, lean_object* v_s_981_){
_start:
{
lean_object* v___x_982_; lean_object* v___x_983_; 
v___x_982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_982_, 0, v_a_979_);
lean_ctor_set(v___x_982_, 1, v_s_981_);
v___x_983_ = lean_apply_2(v_toPure_980_, lean_box(0), v___x_982_);
return v___x_983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___redArg___lam__4(lean_object* v_toPure_984_, lean_object* v_ref_985_, lean_object* v_x_986_, lean_object* v_toBind_987_, lean_object* v_a_988_){
_start:
{
lean_object* v___f_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; 
v___f_989_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__3), 3, 2);
lean_closure_set(v___f_989_, 0, v_a_988_);
lean_closure_set(v___f_989_, 1, v_toPure_984_);
v___x_990_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_990_, 0, lean_box(0));
lean_closure_set(v___x_990_, 1, lean_box(0));
lean_closure_set(v___x_990_, 2, v_ref_985_);
v___x_991_ = lean_apply_2(v_x_986_, lean_box(0), v___x_990_);
v___x_992_ = lean_apply_4(v_toBind_987_, lean_box(0), lean_box(0), v___x_991_, v___f_989_);
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___redArg___lam__5(lean_object* v_toPure_993_, lean_object* v_x_994_, lean_object* v_toBind_995_, lean_object* v_inst_996_, lean_object* v_inst_997_, lean_object* v_inst_998_, lean_object* v_pre_999_, lean_object* v_post_1000_, lean_object* v_x_1001_, lean_object* v_input_1002_, lean_object* v_ref_1003_){
_start:
{
lean_object* v___f_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
lean_inc(v_toBind_995_);
lean_inc(v_x_994_);
lean_inc(v_ref_1003_);
v___f_1004_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__4), 5, 4);
lean_closure_set(v___f_1004_, 0, v_toPure_993_);
lean_closure_set(v___f_1004_, 1, v_ref_1003_);
lean_closure_set(v___f_1004_, 2, v_x_994_);
lean_closure_set(v___f_1004_, 3, v_toBind_995_);
v___x_1005_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg(v_inst_996_, v_inst_997_, v_inst_998_, v_pre_999_, v_post_1000_, v_x_1001_, v_x_994_, v_input_1002_, v_ref_1003_);
lean_dec(v_ref_1003_);
v___x_1006_ = lean_apply_4(v_toBind_995_, lean_box(0), lean_box(0), v___x_1005_, v___f_1004_);
return v___x_1006_;
}
}
static lean_object* _init_l_Lean_Core_transform___redArg___closed__0(void){
_start:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1007_ = lean_box(0);
v___x_1008_ = lean_unsigned_to_nat(16u);
v___x_1009_ = lean_mk_array(v___x_1008_, v___x_1007_);
return v___x_1009_;
}
}
static lean_object* _init_l_Lean_Core_transform___redArg___closed__1(void){
_start:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1010_ = lean_obj_once(&l_Lean_Core_transform___redArg___closed__0, &l_Lean_Core_transform___redArg___closed__0_once, _init_l_Lean_Core_transform___redArg___closed__0);
v___x_1011_ = lean_unsigned_to_nat(0u);
v___x_1012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1011_);
lean_ctor_set(v___x_1012_, 1, v___x_1010_);
return v___x_1012_;
}
}
static lean_object* _init_l_Lean_Core_transform___redArg___closed__2(void){
_start:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1013_ = lean_obj_once(&l_Lean_Core_transform___redArg___closed__1, &l_Lean_Core_transform___redArg___closed__1_once, _init_l_Lean_Core_transform___redArg___closed__1);
v___x_1014_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1014_, 0, lean_box(0));
lean_closure_set(v___x_1014_, 1, lean_box(0));
lean_closure_set(v___x_1014_, 2, v___x_1013_);
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___redArg(lean_object* v_inst_1015_, lean_object* v_inst_1016_, lean_object* v_inst_1017_, lean_object* v_input_1018_, lean_object* v_pre_1019_, lean_object* v_post_1020_){
_start:
{
lean_object* v_x_1021_; lean_object* v_toApplicative_1022_; lean_object* v_toBind_1023_; lean_object* v_toPure_1024_; lean_object* v_x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___f_1028_; lean_object* v___f_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; 
v_x_1021_ = lean_box(0);
v_toApplicative_1022_ = lean_ctor_get(v_inst_1015_, 0);
v_toBind_1023_ = lean_ctor_get(v_inst_1015_, 1);
lean_inc_n(v_toBind_1023_, 3);
v_toPure_1024_ = lean_ctor_get(v_toApplicative_1022_, 1);
lean_inc_n(v_toPure_1024_, 2);
lean_inc_n(v_inst_1016_, 2);
v_x_1025_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__1), 3, 1);
lean_closure_set(v_x_1025_, 0, v_inst_1016_);
v___x_1026_ = lean_obj_once(&l_Lean_Core_transform___redArg___closed__2, &l_Lean_Core_transform___redArg___closed__2_once, _init_l_Lean_Core_transform___redArg___closed__2);
v___x_1027_ = l_Lean_Core_transform___redArg___lam__1(v_inst_1016_, lean_box(0), v___x_1026_);
v___f_1028_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__2), 2, 1);
lean_closure_set(v___f_1028_, 0, v_toPure_1024_);
v___f_1029_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__5), 11, 10);
lean_closure_set(v___f_1029_, 0, v_toPure_1024_);
lean_closure_set(v___f_1029_, 1, v_x_1025_);
lean_closure_set(v___f_1029_, 2, v_toBind_1023_);
lean_closure_set(v___f_1029_, 3, v_inst_1015_);
lean_closure_set(v___f_1029_, 4, v_inst_1016_);
lean_closure_set(v___f_1029_, 5, v_inst_1017_);
lean_closure_set(v___f_1029_, 6, v_pre_1019_);
lean_closure_set(v___f_1029_, 7, v_post_1020_);
lean_closure_set(v___f_1029_, 8, v_x_1021_);
lean_closure_set(v___f_1029_, 9, v_input_1018_);
v___x_1030_ = lean_apply_4(v_toBind_1023_, lean_box(0), lean_box(0), v___x_1027_, v___f_1029_);
v___x_1031_ = lean_apply_4(v_toBind_1023_, lean_box(0), lean_box(0), v___x_1030_, v___f_1028_);
return v___x_1031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform(lean_object* v_m_1032_, lean_object* v_inst_1033_, lean_object* v_inst_1034_, lean_object* v_inst_1035_, lean_object* v_input_1036_, lean_object* v_pre_1037_, lean_object* v_post_1038_){
_start:
{
lean_object* v___x_1039_; 
v___x_1039_ = l_Lean_Core_transform___redArg(v_inst_1033_, v_inst_1034_, v_inst_1035_, v_input_1036_, v_pre_1037_, v_post_1038_);
return v___x_1039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_betaReduce___lam__0(lean_object* v_e_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_){
_start:
{
uint8_t v___x_1046_; uint8_t v___x_1047_; 
v___x_1046_ = 0;
v___x_1047_ = l_Lean_Expr_isHeadBetaTarget(v_e_1042_, v___x_1046_);
if (v___x_1047_ == 0)
{
lean_object* v___x_1048_; lean_object* v___x_1049_; 
lean_dec_ref(v_e_1042_);
v___x_1048_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_1049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1048_);
return v___x_1049_;
}
else
{
lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1050_ = l_Lean_Expr_headBeta(v_e_1042_);
v___x_1051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1050_);
v___x_1052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1051_);
return v___x_1052_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_betaReduce___lam__0___boxed(lean_object* v_e_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_){
_start:
{
lean_object* v_res_1057_; 
v_res_1057_ = l_Lean_Core_betaReduce___lam__0(v_e_1053_, v___y_1054_, v___y_1055_);
lean_dec(v___y_1055_);
lean_dec_ref(v___y_1054_);
return v_res_1057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_betaReduce___lam__1(lean_object* v_e_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_){
_start:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1062_, 0, v_e_1058_);
v___x_1063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1062_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_betaReduce___lam__1___boxed(lean_object* v_e_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_){
_start:
{
lean_object* v_res_1068_; 
v_res_1068_ = l_Lean_Core_betaReduce___lam__1(v_e_1064_, v___y_1065_, v___y_1066_);
lean_dec(v___y_1066_);
lean_dec_ref(v___y_1065_);
return v_res_1068_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; 
v___x_1069_ = lean_box(0);
v___x_1070_ = l_Lean_interruptExceptionId;
v___x_1071_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1070_);
lean_ctor_set(v___x_1071_, 1, v___x_1069_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___redArg(){
_start:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1073_ = lean_obj_once(&l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___redArg___closed__0, &l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___redArg___closed__0);
v___x_1074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1073_);
return v___x_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___redArg___boxed(lean_object* v___y_1075_){
_start:
{
lean_object* v_res_1076_; 
v_res_1076_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___redArg();
return v_res_1076_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1082_ = l_Lean_maxRecDepthErrorMessage;
v___x_1083_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1082_);
return v___x_1083_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_1084_; lean_object* v___x_1085_; 
v___x_1084_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__3);
v___x_1085_ = l_Lean_MessageData_ofFormat(v___x_1084_);
return v___x_1085_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___x_1086_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__4);
v___x_1087_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__2));
v___x_1088_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1088_, 0, v___x_1087_);
lean_ctor_set(v___x_1088_, 1, v___x_1086_);
return v___x_1088_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg(lean_object* v_ref_1089_){
_start:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1091_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5);
v___x_1092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1092_, 0, v_ref_1089_);
lean_ctor_set(v___x_1092_, 1, v___x_1091_);
v___x_1093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1092_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object* v_ref_1094_, lean_object* v___y_1095_){
_start:
{
lean_object* v_res_1096_; 
v_res_1096_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_1094_);
return v_res_1096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___redArg(lean_object* v_x_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_){
_start:
{
lean_object* v___y_1103_; uint8_t v___y_1113_; uint8_t v___y_1114_; lean_object* v___y_1115_; lean_object* v___y_1116_; uint16_t v___y_1117_; uint8_t v___y_1118_; lean_object* v___y_1119_; lean_object* v_toCold_1124_; lean_object* v_currRecDepth_1125_; lean_object* v_ref_1126_; uint16_t v_optionFlags_1127_; uint8_t v_suppressElabErrors_1128_; uint8_t v_checkDeprecated_1129_; uint8_t v_isRecordingDeps_1130_; lean_object* v_maxRecDepth_1131_; lean_object* v_cancelTk_x3f_1132_; 
v_toCold_1124_ = lean_ctor_get(v___y_1099_, 0);
v_currRecDepth_1125_ = lean_ctor_get(v___y_1099_, 1);
v_ref_1126_ = lean_ctor_get(v___y_1099_, 2);
v_optionFlags_1127_ = lean_ctor_get_uint16(v___y_1099_, sizeof(void*)*3);
v_suppressElabErrors_1128_ = lean_ctor_get_uint8(v___y_1099_, sizeof(void*)*3 + 2);
v_checkDeprecated_1129_ = lean_ctor_get_uint8(v___y_1099_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1130_ = lean_ctor_get_uint8(v___y_1099_, sizeof(void*)*3 + 4);
v_maxRecDepth_1131_ = lean_ctor_get(v_toCold_1124_, 3);
v_cancelTk_x3f_1132_ = lean_ctor_get(v_toCold_1124_, 10);
if (lean_obj_tag(v_cancelTk_x3f_1132_) == 1)
{
lean_object* v_val_1138_; uint8_t v___x_1139_; 
v_val_1138_ = lean_ctor_get(v_cancelTk_x3f_1132_, 0);
v___x_1139_ = l_IO_CancelToken_isSet(v_val_1138_);
if (v___x_1139_ == 0)
{
goto v___jp_1133_;
}
else
{
lean_object* v___x_1140_; lean_object* v_a_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1148_; 
lean_dec_ref(v_x_1097_);
v___x_1140_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___redArg();
v_a_1141_ = lean_ctor_get(v___x_1140_, 0);
v_isSharedCheck_1148_ = !lean_is_exclusive(v___x_1140_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1143_ = v___x_1140_;
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_a_1141_);
lean_dec(v___x_1140_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1146_; 
if (v_isShared_1144_ == 0)
{
v___x_1146_ = v___x_1143_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_a_1141_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
return v___x_1146_;
}
}
}
}
else
{
goto v___jp_1133_;
}
v___jp_1102_:
{
if (lean_obj_tag(v___y_1103_) == 0)
{
return v___y_1103_;
}
else
{
lean_object* v_a_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1111_; 
v_a_1104_ = lean_ctor_get(v___y_1103_, 0);
v_isSharedCheck_1111_ = !lean_is_exclusive(v___y_1103_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1106_ = v___y_1103_;
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_a_1104_);
lean_dec(v___y_1103_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1109_; 
if (v_isShared_1107_ == 0)
{
v___x_1109_ = v___x_1106_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_a_1104_);
v___x_1109_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
return v___x_1109_;
}
}
}
}
v___jp_1112_:
{
lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1120_ = lean_unsigned_to_nat(1u);
v___x_1121_ = lean_nat_add(v___y_1116_, v___x_1120_);
lean_inc_ref(v___y_1119_);
v___x_1122_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1122_, 0, v___y_1119_);
lean_ctor_set(v___x_1122_, 1, v___x_1121_);
lean_ctor_set(v___x_1122_, 2, v___y_1115_);
lean_ctor_set_uint16(v___x_1122_, sizeof(void*)*3, v___y_1117_);
lean_ctor_set_uint8(v___x_1122_, sizeof(void*)*3 + 2, v___y_1118_);
lean_ctor_set_uint8(v___x_1122_, sizeof(void*)*3 + 3, v___y_1113_);
lean_ctor_set_uint8(v___x_1122_, sizeof(void*)*3 + 4, v___y_1114_);
lean_inc(v___y_1100_);
lean_inc(v___y_1098_);
v___x_1123_ = lean_apply_4(v_x_1097_, v___y_1098_, v___x_1122_, v___y_1100_, lean_box(0));
v___y_1103_ = v___x_1123_;
goto v___jp_1102_;
}
v___jp_1133_:
{
lean_object* v___x_1134_; uint8_t v___x_1135_; 
v___x_1134_ = lean_unsigned_to_nat(0u);
v___x_1135_ = lean_nat_dec_eq(v_maxRecDepth_1131_, v___x_1134_);
if (v___x_1135_ == 0)
{
uint8_t v___x_1136_; 
v___x_1136_ = lean_nat_dec_eq(v_currRecDepth_1125_, v_maxRecDepth_1131_);
if (v___x_1136_ == 0)
{
lean_inc(v_ref_1126_);
v___y_1113_ = v_checkDeprecated_1129_;
v___y_1114_ = v_isRecordingDeps_1130_;
v___y_1115_ = v_ref_1126_;
v___y_1116_ = v_currRecDepth_1125_;
v___y_1117_ = v_optionFlags_1127_;
v___y_1118_ = v_suppressElabErrors_1128_;
v___y_1119_ = v_toCold_1124_;
goto v___jp_1112_;
}
else
{
lean_object* v___x_1137_; 
lean_dec_ref(v_x_1097_);
lean_inc(v_ref_1126_);
v___x_1137_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_1126_);
v___y_1103_ = v___x_1137_;
goto v___jp_1102_;
}
}
else
{
lean_inc(v_ref_1126_);
v___y_1113_ = v_checkDeprecated_1129_;
v___y_1114_ = v_isRecordingDeps_1130_;
v___y_1115_ = v_ref_1126_;
v___y_1116_ = v_currRecDepth_1125_;
v___y_1117_ = v_optionFlags_1127_;
v___y_1118_ = v_suppressElabErrors_1128_;
v___y_1119_ = v_toCold_1124_;
goto v___jp_1112_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___redArg___boxed(lean_object* v_x_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_){
_start:
{
lean_object* v_res_1154_; 
v_res_1154_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___redArg(v_x_1149_, v___y_1150_, v___y_1151_, v___y_1152_);
lean_dec(v___y_1152_);
lean_dec_ref(v___y_1151_);
lean_dec(v___y_1150_);
return v_res_1154_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_1155_, lean_object* v_x_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_){
_start:
{
lean_object* v___x_1160_; lean_object* v___x_1161_; 
v___x_1160_ = lean_apply_1(v_x_1156_, lean_box(0));
v___x_1161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1161_, 0, v___x_1160_);
return v___x_1161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_1162_, lean_object* v_x_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_){
_start:
{
lean_object* v_res_1167_; 
v_res_1167_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__0(v_00_u03b1_1162_, v_x_1163_, v___y_1164_, v___y_1165_);
lean_dec(v___y_1165_);
lean_dec_ref(v___y_1164_);
return v_res_1167_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___redArg(lean_object* v_a_1168_, lean_object* v_x_1169_){
_start:
{
if (lean_obj_tag(v_x_1169_) == 0)
{
uint8_t v___x_1170_; 
v___x_1170_ = 0;
return v___x_1170_;
}
else
{
lean_object* v_key_1171_; lean_object* v_tail_1172_; uint8_t v___x_1173_; 
v_key_1171_ = lean_ctor_get(v_x_1169_, 0);
v_tail_1172_ = lean_ctor_get(v_x_1169_, 2);
v___x_1173_ = l_Lean_ExprStructEq_beq(v_key_1171_, v_a_1168_);
if (v___x_1173_ == 0)
{
v_x_1169_ = v_tail_1172_;
goto _start;
}
else
{
return v___x_1173_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___redArg___boxed(lean_object* v_a_1175_, lean_object* v_x_1176_){
_start:
{
uint8_t v_res_1177_; lean_object* v_r_1178_; 
v_res_1177_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___redArg(v_a_1175_, v_x_1176_);
lean_dec(v_x_1176_);
lean_dec_ref(v_a_1175_);
v_r_1178_ = lean_box(v_res_1177_);
return v_r_1178_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(lean_object* v_x_1179_, lean_object* v_x_1180_){
_start:
{
if (lean_obj_tag(v_x_1180_) == 0)
{
return v_x_1179_;
}
else
{
lean_object* v_key_1181_; lean_object* v_value_1182_; lean_object* v_tail_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1206_; 
v_key_1181_ = lean_ctor_get(v_x_1180_, 0);
v_value_1182_ = lean_ctor_get(v_x_1180_, 1);
v_tail_1183_ = lean_ctor_get(v_x_1180_, 2);
v_isSharedCheck_1206_ = !lean_is_exclusive(v_x_1180_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1185_ = v_x_1180_;
v_isShared_1186_ = v_isSharedCheck_1206_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_tail_1183_);
lean_inc(v_value_1182_);
lean_inc(v_key_1181_);
lean_dec(v_x_1180_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1206_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v___x_1187_; uint64_t v___x_1188_; uint64_t v___x_1189_; uint64_t v___x_1190_; uint64_t v_fold_1191_; uint64_t v___x_1192_; uint64_t v___x_1193_; uint64_t v___x_1194_; size_t v___x_1195_; size_t v___x_1196_; size_t v___x_1197_; size_t v___x_1198_; size_t v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1202_; 
v___x_1187_ = lean_array_get_size(v_x_1179_);
v___x_1188_ = l_Lean_ExprStructEq_hash(v_key_1181_);
v___x_1189_ = 32ULL;
v___x_1190_ = lean_uint64_shift_right(v___x_1188_, v___x_1189_);
v_fold_1191_ = lean_uint64_xor(v___x_1188_, v___x_1190_);
v___x_1192_ = 16ULL;
v___x_1193_ = lean_uint64_shift_right(v_fold_1191_, v___x_1192_);
v___x_1194_ = lean_uint64_xor(v_fold_1191_, v___x_1193_);
v___x_1195_ = lean_uint64_to_usize(v___x_1194_);
v___x_1196_ = lean_usize_of_nat(v___x_1187_);
v___x_1197_ = ((size_t)1ULL);
v___x_1198_ = lean_usize_sub(v___x_1196_, v___x_1197_);
v___x_1199_ = lean_usize_land(v___x_1195_, v___x_1198_);
v___x_1200_ = lean_array_uget_borrowed(v_x_1179_, v___x_1199_);
lean_inc(v___x_1200_);
if (v_isShared_1186_ == 0)
{
lean_ctor_set(v___x_1185_, 2, v___x_1200_);
v___x_1202_ = v___x_1185_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v_key_1181_);
lean_ctor_set(v_reuseFailAlloc_1205_, 1, v_value_1182_);
lean_ctor_set(v_reuseFailAlloc_1205_, 2, v___x_1200_);
v___x_1202_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
lean_object* v___x_1203_; 
v___x_1203_ = lean_array_uset(v_x_1179_, v___x_1199_, v___x_1202_);
v_x_1179_ = v___x_1203_;
v_x_1180_ = v_tail_1183_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(lean_object* v_i_1207_, lean_object* v_source_1208_, lean_object* v_target_1209_){
_start:
{
lean_object* v___x_1210_; uint8_t v___x_1211_; 
v___x_1210_ = lean_array_get_size(v_source_1208_);
v___x_1211_ = lean_nat_dec_lt(v_i_1207_, v___x_1210_);
if (v___x_1211_ == 0)
{
lean_dec_ref(v_source_1208_);
lean_dec(v_i_1207_);
return v_target_1209_;
}
else
{
lean_object* v_es_1212_; lean_object* v___x_1213_; lean_object* v_source_1214_; lean_object* v_target_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; 
v_es_1212_ = lean_array_fget(v_source_1208_, v_i_1207_);
v___x_1213_ = lean_box(0);
v_source_1214_ = lean_array_fset(v_source_1208_, v_i_1207_, v___x_1213_);
v_target_1215_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_target_1209_, v_es_1212_);
v___x_1216_ = lean_unsigned_to_nat(1u);
v___x_1217_ = lean_nat_add(v_i_1207_, v___x_1216_);
lean_dec(v_i_1207_);
v_i_1207_ = v___x_1217_;
v_source_1208_ = v_source_1214_;
v_target_1209_ = v_target_1215_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11___redArg(lean_object* v_data_1219_){
_start:
{
lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v_nbuckets_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1220_ = lean_array_get_size(v_data_1219_);
v___x_1221_ = lean_unsigned_to_nat(2u);
v_nbuckets_1222_ = lean_nat_mul(v___x_1220_, v___x_1221_);
v___x_1223_ = lean_unsigned_to_nat(0u);
v___x_1224_ = lean_box(0);
v___x_1225_ = lean_mk_array(v_nbuckets_1222_, v___x_1224_);
v___x_1226_ = lean_array_propagate_mark(v_data_1219_, v___x_1225_);
v___x_1227_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v___x_1223_, v_data_1219_, v___x_1226_);
return v___x_1227_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__12___redArg(lean_object* v_a_1228_, lean_object* v_b_1229_, lean_object* v_x_1230_){
_start:
{
if (lean_obj_tag(v_x_1230_) == 0)
{
lean_dec(v_b_1229_);
lean_dec_ref(v_a_1228_);
return v_x_1230_;
}
else
{
lean_object* v_key_1231_; lean_object* v_value_1232_; lean_object* v_tail_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1245_; 
v_key_1231_ = lean_ctor_get(v_x_1230_, 0);
v_value_1232_ = lean_ctor_get(v_x_1230_, 1);
v_tail_1233_ = lean_ctor_get(v_x_1230_, 2);
v_isSharedCheck_1245_ = !lean_is_exclusive(v_x_1230_);
if (v_isSharedCheck_1245_ == 0)
{
v___x_1235_ = v_x_1230_;
v_isShared_1236_ = v_isSharedCheck_1245_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_tail_1233_);
lean_inc(v_value_1232_);
lean_inc(v_key_1231_);
lean_dec(v_x_1230_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1245_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
uint8_t v___x_1237_; 
v___x_1237_ = l_Lean_ExprStructEq_beq(v_key_1231_, v_a_1228_);
if (v___x_1237_ == 0)
{
lean_object* v___x_1238_; lean_object* v___x_1240_; 
v___x_1238_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__12___redArg(v_a_1228_, v_b_1229_, v_tail_1233_);
if (v_isShared_1236_ == 0)
{
lean_ctor_set(v___x_1235_, 2, v___x_1238_);
v___x_1240_ = v___x_1235_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v_key_1231_);
lean_ctor_set(v_reuseFailAlloc_1241_, 1, v_value_1232_);
lean_ctor_set(v_reuseFailAlloc_1241_, 2, v___x_1238_);
v___x_1240_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
return v___x_1240_;
}
}
else
{
lean_object* v___x_1243_; 
lean_dec(v_value_1232_);
lean_dec(v_key_1231_);
if (v_isShared_1236_ == 0)
{
lean_ctor_set(v___x_1235_, 1, v_b_1229_);
lean_ctor_set(v___x_1235_, 0, v_a_1228_);
v___x_1243_ = v___x_1235_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v_a_1228_);
lean_ctor_set(v_reuseFailAlloc_1244_, 1, v_b_1229_);
lean_ctor_set(v_reuseFailAlloc_1244_, 2, v_tail_1233_);
v___x_1243_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
return v___x_1243_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6___redArg(lean_object* v_m_1246_, lean_object* v_a_1247_, lean_object* v_b_1248_){
_start:
{
lean_object* v_size_1249_; lean_object* v_buckets_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1293_; 
v_size_1249_ = lean_ctor_get(v_m_1246_, 0);
v_buckets_1250_ = lean_ctor_get(v_m_1246_, 1);
v_isSharedCheck_1293_ = !lean_is_exclusive(v_m_1246_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1252_ = v_m_1246_;
v_isShared_1253_ = v_isSharedCheck_1293_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_buckets_1250_);
lean_inc(v_size_1249_);
lean_dec(v_m_1246_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1293_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v___x_1254_; uint64_t v___x_1255_; uint64_t v___x_1256_; uint64_t v___x_1257_; uint64_t v_fold_1258_; uint64_t v___x_1259_; uint64_t v___x_1260_; uint64_t v___x_1261_; size_t v___x_1262_; size_t v___x_1263_; size_t v___x_1264_; size_t v___x_1265_; size_t v___x_1266_; lean_object* v_bkt_1267_; uint8_t v___x_1268_; 
v___x_1254_ = lean_array_get_size(v_buckets_1250_);
v___x_1255_ = l_Lean_ExprStructEq_hash(v_a_1247_);
v___x_1256_ = 32ULL;
v___x_1257_ = lean_uint64_shift_right(v___x_1255_, v___x_1256_);
v_fold_1258_ = lean_uint64_xor(v___x_1255_, v___x_1257_);
v___x_1259_ = 16ULL;
v___x_1260_ = lean_uint64_shift_right(v_fold_1258_, v___x_1259_);
v___x_1261_ = lean_uint64_xor(v_fold_1258_, v___x_1260_);
v___x_1262_ = lean_uint64_to_usize(v___x_1261_);
v___x_1263_ = lean_usize_of_nat(v___x_1254_);
v___x_1264_ = ((size_t)1ULL);
v___x_1265_ = lean_usize_sub(v___x_1263_, v___x_1264_);
v___x_1266_ = lean_usize_land(v___x_1262_, v___x_1265_);
v_bkt_1267_ = lean_array_uget_borrowed(v_buckets_1250_, v___x_1266_);
v___x_1268_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___redArg(v_a_1247_, v_bkt_1267_);
if (v___x_1268_ == 0)
{
lean_object* v___x_1269_; lean_object* v_size_x27_1270_; lean_object* v___x_1271_; lean_object* v_buckets_x27_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; uint8_t v___x_1278_; 
v___x_1269_ = lean_unsigned_to_nat(1u);
v_size_x27_1270_ = lean_nat_add(v_size_1249_, v___x_1269_);
lean_dec(v_size_1249_);
lean_inc(v_bkt_1267_);
v___x_1271_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1271_, 0, v_a_1247_);
lean_ctor_set(v___x_1271_, 1, v_b_1248_);
lean_ctor_set(v___x_1271_, 2, v_bkt_1267_);
v_buckets_x27_1272_ = lean_array_uset(v_buckets_1250_, v___x_1266_, v___x_1271_);
v___x_1273_ = lean_unsigned_to_nat(4u);
v___x_1274_ = lean_nat_mul(v_size_x27_1270_, v___x_1273_);
v___x_1275_ = lean_unsigned_to_nat(3u);
v___x_1276_ = lean_nat_div(v___x_1274_, v___x_1275_);
lean_dec(v___x_1274_);
v___x_1277_ = lean_array_get_size(v_buckets_x27_1272_);
v___x_1278_ = lean_nat_dec_le(v___x_1276_, v___x_1277_);
lean_dec(v___x_1276_);
if (v___x_1278_ == 0)
{
lean_object* v_val_1279_; lean_object* v___x_1281_; 
v_val_1279_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11___redArg(v_buckets_x27_1272_);
if (v_isShared_1253_ == 0)
{
lean_ctor_set(v___x_1252_, 1, v_val_1279_);
lean_ctor_set(v___x_1252_, 0, v_size_x27_1270_);
v___x_1281_ = v___x_1252_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v_size_x27_1270_);
lean_ctor_set(v_reuseFailAlloc_1282_, 1, v_val_1279_);
v___x_1281_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
return v___x_1281_;
}
}
else
{
lean_object* v___x_1284_; 
if (v_isShared_1253_ == 0)
{
lean_ctor_set(v___x_1252_, 1, v_buckets_x27_1272_);
lean_ctor_set(v___x_1252_, 0, v_size_x27_1270_);
v___x_1284_ = v___x_1252_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v_size_x27_1270_);
lean_ctor_set(v_reuseFailAlloc_1285_, 1, v_buckets_x27_1272_);
v___x_1284_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
return v___x_1284_;
}
}
}
else
{
lean_object* v___x_1286_; lean_object* v_buckets_x27_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1291_; 
lean_inc(v_bkt_1267_);
v___x_1286_ = lean_box(0);
v_buckets_x27_1287_ = lean_array_uset(v_buckets_1250_, v___x_1266_, v___x_1286_);
v___x_1288_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__12___redArg(v_a_1247_, v_b_1248_, v_bkt_1267_);
v___x_1289_ = lean_array_uset(v_buckets_x27_1287_, v___x_1266_, v___x_1288_);
if (v_isShared_1253_ == 0)
{
lean_ctor_set(v___x_1252_, 1, v___x_1289_);
v___x_1291_ = v___x_1252_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_size_1249_);
lean_ctor_set(v_reuseFailAlloc_1292_, 1, v___x_1289_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__2(lean_object* v_a_1294_, lean_object* v_e_1295_, lean_object* v_a_1296_){
_start:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; 
v___x_1298_ = lean_st_ref_take(v_a_1294_);
v___x_1299_ = lean_box(0);
v___x_1300_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6___redArg(v___x_1298_, v_e_1295_, v_a_1296_);
v___x_1301_ = lean_st_ref_put(v_a_1294_, v___x_1300_);
return v___x_1299_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__2___boxed(lean_object* v_a_1302_, lean_object* v_e_1303_, lean_object* v_a_1304_, lean_object* v___y_1305_){
_start:
{
lean_object* v_res_1306_; 
v_res_1306_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__2(v_a_1302_, v_e_1303_, v_a_1304_);
lean_dec(v_a_1302_);
return v_res_1306_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_a_1307_, lean_object* v_x_1308_){
_start:
{
if (lean_obj_tag(v_x_1308_) == 0)
{
lean_object* v___x_1309_; 
v___x_1309_ = lean_box(0);
return v___x_1309_;
}
else
{
lean_object* v_key_1310_; lean_object* v_value_1311_; lean_object* v_tail_1312_; uint8_t v___x_1313_; 
v_key_1310_ = lean_ctor_get(v_x_1308_, 0);
v_value_1311_ = lean_ctor_get(v_x_1308_, 1);
v_tail_1312_ = lean_ctor_get(v_x_1308_, 2);
v___x_1313_ = l_Lean_ExprStructEq_beq(v_key_1310_, v_a_1307_);
if (v___x_1313_ == 0)
{
v_x_1308_ = v_tail_1312_;
goto _start;
}
else
{
lean_object* v___x_1315_; 
lean_inc(v_value_1311_);
v___x_1315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1315_, 0, v_value_1311_);
return v___x_1315_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_a_1316_, lean_object* v_x_1317_){
_start:
{
lean_object* v_res_1318_; 
v_res_1318_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1_spec__2___redArg(v_a_1316_, v_x_1317_);
lean_dec(v_x_1317_);
lean_dec_ref(v_a_1316_);
return v_res_1318_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1___redArg(lean_object* v_m_1319_, lean_object* v_a_1320_){
_start:
{
lean_object* v_buckets_1321_; lean_object* v___x_1322_; uint64_t v___x_1323_; uint64_t v___x_1324_; uint64_t v___x_1325_; uint64_t v_fold_1326_; uint64_t v___x_1327_; uint64_t v___x_1328_; uint64_t v___x_1329_; size_t v___x_1330_; size_t v___x_1331_; size_t v___x_1332_; size_t v___x_1333_; size_t v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; 
v_buckets_1321_ = lean_ctor_get(v_m_1319_, 1);
v___x_1322_ = lean_array_get_size(v_buckets_1321_);
v___x_1323_ = l_Lean_ExprStructEq_hash(v_a_1320_);
v___x_1324_ = 32ULL;
v___x_1325_ = lean_uint64_shift_right(v___x_1323_, v___x_1324_);
v_fold_1326_ = lean_uint64_xor(v___x_1323_, v___x_1325_);
v___x_1327_ = 16ULL;
v___x_1328_ = lean_uint64_shift_right(v_fold_1326_, v___x_1327_);
v___x_1329_ = lean_uint64_xor(v_fold_1326_, v___x_1328_);
v___x_1330_ = lean_uint64_to_usize(v___x_1329_);
v___x_1331_ = lean_usize_of_nat(v___x_1322_);
v___x_1332_ = ((size_t)1ULL);
v___x_1333_ = lean_usize_sub(v___x_1331_, v___x_1332_);
v___x_1334_ = lean_usize_land(v___x_1330_, v___x_1333_);
v___x_1335_ = lean_array_uget_borrowed(v_buckets_1321_, v___x_1334_);
v___x_1336_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1_spec__2___redArg(v_a_1320_, v___x_1335_);
return v___x_1336_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_m_1337_, lean_object* v_a_1338_){
_start:
{
lean_object* v_res_1339_; 
v_res_1339_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1___redArg(v_m_1337_, v_a_1338_);
lean_dec_ref(v_a_1338_);
lean_dec_ref(v_m_1337_);
return v_res_1339_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(lean_object* v_pre_1340_, lean_object* v_post_1341_, size_t v_sz_1342_, size_t v_i_1343_, lean_object* v_bs_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_){
_start:
{
uint8_t v___x_1349_; 
v___x_1349_ = lean_usize_dec_lt(v_i_1343_, v_sz_1342_);
if (v___x_1349_ == 0)
{
lean_object* v___x_1350_; 
lean_dec_ref(v_post_1341_);
lean_dec_ref(v_pre_1340_);
v___x_1350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1350_, 0, v_bs_1344_);
return v___x_1350_;
}
else
{
lean_object* v_v_1351_; lean_object* v___x_1352_; lean_object* v_bs_x27_1353_; lean_object* v___x_1354_; 
v_v_1351_ = lean_array_uget(v_bs_1344_, v_i_1343_);
v___x_1352_ = lean_unsigned_to_nat(0u);
v_bs_x27_1353_ = lean_array_uset(v_bs_1344_, v_i_1343_, v___x_1352_);
lean_inc_ref(v_post_1341_);
lean_inc_ref(v_pre_1340_);
v___x_1354_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1340_, v_post_1341_, v_v_1351_, v___y_1345_, v___y_1346_, v___y_1347_);
if (lean_obj_tag(v___x_1354_) == 0)
{
lean_object* v_a_1355_; size_t v___x_1356_; size_t v___x_1357_; lean_object* v___x_1358_; 
v_a_1355_ = lean_ctor_get(v___x_1354_, 0);
lean_inc(v_a_1355_);
lean_dec_ref_known(v___x_1354_, 1);
v___x_1356_ = ((size_t)1ULL);
v___x_1357_ = lean_usize_add(v_i_1343_, v___x_1356_);
v___x_1358_ = lean_array_uset(v_bs_x27_1353_, v_i_1343_, v_a_1355_);
v_i_1343_ = v___x_1357_;
v_bs_1344_ = v___x_1358_;
goto _start;
}
else
{
lean_object* v_a_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1367_; 
lean_dec_ref(v_bs_x27_1353_);
lean_dec_ref(v_post_1341_);
lean_dec_ref(v_pre_1340_);
v_a_1360_ = lean_ctor_get(v___x_1354_, 0);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1354_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1362_ = v___x_1354_;
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_a_1360_);
lean_dec(v___x_1354_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1365_; 
if (v_isShared_1363_ == 0)
{
v___x_1365_ = v___x_1362_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_a_1360_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
return v___x_1365_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__4(lean_object* v_pre_1368_, lean_object* v_post_1369_, lean_object* v___y_1370_, lean_object* v_x_1371_, lean_object* v_x_1372_, lean_object* v_x_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_){
_start:
{
if (lean_obj_tag(v_x_1371_) == 5)
{
lean_object* v_fn_1378_; lean_object* v_arg_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; 
v_fn_1378_ = lean_ctor_get(v_x_1371_, 0);
lean_inc_ref(v_fn_1378_);
v_arg_1379_ = lean_ctor_get(v_x_1371_, 1);
lean_inc_ref(v_arg_1379_);
lean_dec_ref_known(v_x_1371_, 2);
v___x_1380_ = lean_array_set(v_x_1372_, v_x_1373_, v_arg_1379_);
v___x_1381_ = lean_unsigned_to_nat(1u);
v___x_1382_ = lean_nat_sub(v_x_1373_, v___x_1381_);
lean_dec(v_x_1373_);
v_x_1371_ = v_fn_1378_;
v_x_1372_ = v___x_1380_;
v_x_1373_ = v___x_1382_;
goto _start;
}
else
{
lean_object* v___x_1384_; 
lean_dec(v_x_1373_);
lean_inc_ref(v_post_1369_);
lean_inc_ref(v_pre_1368_);
v___x_1384_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1368_, v_post_1369_, v_x_1371_, v___y_1374_, v___y_1375_, v___y_1376_);
if (lean_obj_tag(v___x_1384_) == 0)
{
lean_object* v_a_1385_; size_t v_sz_1386_; size_t v___x_1387_; lean_object* v___x_1388_; 
v_a_1385_ = lean_ctor_get(v___x_1384_, 0);
lean_inc(v_a_1385_);
lean_dec_ref_known(v___x_1384_, 1);
v_sz_1386_ = lean_array_size(v_x_1372_);
v___x_1387_ = ((size_t)0ULL);
v___x_1388_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1368_, v_post_1369_, v_sz_1386_, v___x_1387_, v_x_1372_, v___y_1374_, v___y_1375_, v___y_1376_);
if (lean_obj_tag(v___x_1388_) == 0)
{
lean_object* v_a_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1397_; 
v_a_1389_ = lean_ctor_get(v___x_1388_, 0);
v_isSharedCheck_1397_ = !lean_is_exclusive(v___x_1388_);
if (v_isSharedCheck_1397_ == 0)
{
v___x_1391_ = v___x_1388_;
v_isShared_1392_ = v_isSharedCheck_1397_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_a_1389_);
lean_dec(v___x_1388_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1397_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v___x_1393_; lean_object* v___x_1395_; 
v___x_1393_ = l_Lean_Expr_updateAppN(v___y_1370_, v_a_1385_, v_a_1389_);
lean_dec(v_a_1389_);
if (v_isShared_1392_ == 0)
{
lean_ctor_set(v___x_1391_, 0, v___x_1393_);
v___x_1395_ = v___x_1391_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v___x_1393_);
v___x_1395_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
return v___x_1395_;
}
}
}
else
{
lean_object* v_a_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1405_; 
lean_dec(v_a_1385_);
v_a_1398_ = lean_ctor_get(v___x_1388_, 0);
v_isSharedCheck_1405_ = !lean_is_exclusive(v___x_1388_);
if (v_isSharedCheck_1405_ == 0)
{
v___x_1400_ = v___x_1388_;
v_isShared_1401_ = v_isSharedCheck_1405_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_a_1398_);
lean_dec(v___x_1388_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1405_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v___x_1403_; 
if (v_isShared_1401_ == 0)
{
v___x_1403_ = v___x_1400_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v_a_1398_);
v___x_1403_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
return v___x_1403_;
}
}
}
}
else
{
lean_dec_ref(v_x_1372_);
lean_dec_ref(v_post_1369_);
lean_dec_ref(v_pre_1368_);
return v___x_1384_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__1(lean_object* v___x_1406_, lean_object* v_pre_1407_, lean_object* v_e_1408_, lean_object* v_post_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_){
_start:
{
lean_object* v___x_1414_; 
v___x_1414_ = l_Lean_Core_checkSystem(v___x_1406_, v___y_1411_, v___y_1412_);
if (lean_obj_tag(v___x_1414_) == 0)
{
lean_object* v___x_1415_; 
lean_dec_ref_known(v___x_1414_, 1);
lean_inc_ref(v_pre_1407_);
lean_inc(v___y_1412_);
lean_inc_ref(v___y_1411_);
lean_inc_ref(v_e_1408_);
v___x_1415_ = lean_apply_4(v_pre_1407_, v_e_1408_, v___y_1411_, v___y_1412_, lean_box(0));
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_object* v_a_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1533_; 
v_a_1416_ = lean_ctor_get(v___x_1415_, 0);
v_isSharedCheck_1533_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1533_ == 0)
{
v___x_1418_ = v___x_1415_;
v_isShared_1419_ = v_isSharedCheck_1533_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_a_1416_);
lean_dec(v___x_1415_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1533_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___y_1421_; 
switch(lean_obj_tag(v_a_1416_))
{
case 0:
{
lean_object* v_e_1523_; lean_object* v___x_1525_; 
lean_dec_ref(v_post_1409_);
lean_dec_ref(v_e_1408_);
lean_dec_ref(v_pre_1407_);
v_e_1523_ = lean_ctor_get(v_a_1416_, 0);
lean_inc_ref(v_e_1523_);
lean_dec_ref_known(v_a_1416_, 1);
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 0, v_e_1523_);
v___x_1525_ = v___x_1418_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v_e_1523_);
v___x_1525_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
return v___x_1525_;
}
}
case 1:
{
lean_object* v_e_1527_; lean_object* v___x_1528_; 
lean_del_object(v___x_1418_);
lean_dec_ref(v_e_1408_);
v_e_1527_ = lean_ctor_get(v_a_1416_, 0);
lean_inc_ref(v_e_1527_);
lean_dec_ref_known(v_a_1416_, 1);
lean_inc_ref(v_post_1409_);
lean_inc_ref(v_pre_1407_);
v___x_1528_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1407_, v_post_1409_, v_e_1527_, v___y_1410_, v___y_1411_, v___y_1412_);
if (lean_obj_tag(v___x_1528_) == 0)
{
lean_object* v_a_1529_; lean_object* v___x_1530_; 
v_a_1529_ = lean_ctor_get(v___x_1528_, 0);
lean_inc(v_a_1529_);
lean_dec_ref_known(v___x_1528_, 1);
v___x_1530_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3(v_pre_1407_, v_post_1409_, v_a_1529_, v___y_1410_, v___y_1411_, v___y_1412_);
return v___x_1530_;
}
else
{
lean_dec_ref(v_post_1409_);
lean_dec_ref(v_pre_1407_);
return v___x_1528_;
}
}
default: 
{
lean_object* v_e_x3f_1531_; 
lean_del_object(v___x_1418_);
v_e_x3f_1531_ = lean_ctor_get(v_a_1416_, 0);
lean_inc(v_e_x3f_1531_);
lean_dec_ref_known(v_a_1416_, 1);
if (lean_obj_tag(v_e_x3f_1531_) == 0)
{
v___y_1421_ = v_e_1408_;
goto v___jp_1420_;
}
else
{
lean_object* v_val_1532_; 
lean_dec_ref(v_e_1408_);
v_val_1532_ = lean_ctor_get(v_e_x3f_1531_, 0);
lean_inc(v_val_1532_);
lean_dec_ref_known(v_e_x3f_1531_, 1);
v___y_1421_ = v_val_1532_;
goto v___jp_1420_;
}
}
}
v___jp_1420_:
{
switch(lean_obj_tag(v___y_1421_))
{
case 7:
{
lean_object* v_binderName_1422_; lean_object* v_binderType_1423_; lean_object* v_body_1424_; uint8_t v_binderInfo_1425_; lean_object* v___x_1426_; 
v_binderName_1422_ = lean_ctor_get(v___y_1421_, 0);
v_binderType_1423_ = lean_ctor_get(v___y_1421_, 1);
v_body_1424_ = lean_ctor_get(v___y_1421_, 2);
v_binderInfo_1425_ = lean_ctor_get_uint8(v___y_1421_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1423_);
lean_inc_ref(v_post_1409_);
lean_inc_ref(v_pre_1407_);
v___x_1426_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1407_, v_post_1409_, v_binderType_1423_, v___y_1410_, v___y_1411_, v___y_1412_);
if (lean_obj_tag(v___x_1426_) == 0)
{
lean_object* v_a_1427_; lean_object* v___x_1428_; 
v_a_1427_ = lean_ctor_get(v___x_1426_, 0);
lean_inc(v_a_1427_);
lean_dec_ref_known(v___x_1426_, 1);
lean_inc_ref(v_body_1424_);
lean_inc_ref(v_post_1409_);
lean_inc_ref(v_pre_1407_);
v___x_1428_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1407_, v_post_1409_, v_body_1424_, v___y_1410_, v___y_1411_, v___y_1412_);
if (lean_obj_tag(v___x_1428_) == 0)
{
lean_object* v_a_1429_; size_t v___x_1430_; size_t v___x_1431_; uint8_t v___x_1432_; 
v_a_1429_ = lean_ctor_get(v___x_1428_, 0);
lean_inc(v_a_1429_);
lean_dec_ref_known(v___x_1428_, 1);
v___x_1430_ = lean_ptr_addr(v_binderType_1423_);
v___x_1431_ = lean_ptr_addr(v_a_1427_);
v___x_1432_ = lean_usize_dec_eq(v___x_1430_, v___x_1431_);
if (v___x_1432_ == 0)
{
lean_object* v___x_1433_; lean_object* v___x_1434_; 
lean_inc(v_binderName_1422_);
lean_dec_ref_known(v___y_1421_, 3);
v___x_1433_ = l_Lean_Expr_forallE___override(v_binderName_1422_, v_a_1427_, v_a_1429_, v_binderInfo_1425_);
v___x_1434_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3(v_pre_1407_, v_post_1409_, v___x_1433_, v___y_1410_, v___y_1411_, v___y_1412_);
return v___x_1434_;
}
else
{
size_t v___x_1435_; size_t v___x_1436_; uint8_t v___x_1437_; 
v___x_1435_ = lean_ptr_addr(v_body_1424_);
v___x_1436_ = lean_ptr_addr(v_a_1429_);
v___x_1437_ = lean_usize_dec_eq(v___x_1435_, v___x_1436_);
if (v___x_1437_ == 0)
{
lean_object* v___x_1438_; lean_object* v___x_1439_; 
lean_inc(v_binderName_1422_);
lean_dec_ref_known(v___y_1421_, 3);
v___x_1438_ = l_Lean_Expr_forallE___override(v_binderName_1422_, v_a_1427_, v_a_1429_, v_binderInfo_1425_);
v___x_1439_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3(v_pre_1407_, v_post_1409_, v___x_1438_, v___y_1410_, v___y_1411_, v___y_1412_);
return v___x_1439_;
}
else
{
uint8_t v___x_1440_; 
v___x_1440_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1425_, v_binderInfo_1425_);
if (v___x_1440_ == 0)
{
lean_object* v___x_1441_; lean_object* v___x_1442_; 
lean_inc(v_binderName_1422_);
lean_dec_ref_known(v___y_1421_, 3);
v___x_1441_ = l_Lean_Expr_forallE___override(v_binderName_1422_, v_a_1427_, v_a_1429_, v_binderInfo_1425_);
v___x_1442_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3(v_pre_1407_, v_post_1409_, v___x_1441_, v___y_1410_, v___y_1411_, v___y_1412_);
return v___x_1442_;
}
else
{
lean_object* v___x_1443_; 
lean_dec(v_a_1429_);
lean_dec(v_a_1427_);
v___x_1443_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3(v_pre_1407_, v_post_1409_, v___y_1421_, v___y_1410_, v___y_1411_, v___y_1412_);
return v___x_1443_;
}
}
}
}
else
{
lean_dec(v_a_1427_);
lean_dec_ref_known(v___y_1421_, 3);
lean_dec_ref(v_post_1409_);
lean_dec_ref(v_pre_1407_);
return v___x_1428_;
}
}
else
{
lean_dec_ref_known(v___y_1421_, 3);
lean_dec_ref(v_post_1409_);
lean_dec_ref(v_pre_1407_);
return v___x_1426_;
}
}
case 6:
{
lean_object* v_binderName_1444_; lean_object* v_binderType_1445_; lean_object* v_body_1446_; uint8_t v_binderInfo_1447_; lean_object* v___x_1448_; 
v_binderName_1444_ = lean_ctor_get(v___y_1421_, 0);
v_binderType_1445_ = lean_ctor_get(v___y_1421_, 1);
v_body_1446_ = lean_ctor_get(v___y_1421_, 2);
v_binderInfo_1447_ = lean_ctor_get_uint8(v___y_1421_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1445_);
lean_inc_ref(v_post_1409_);
lean_inc_ref(v_pre_1407_);
v___x_1448_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1407_, v_post_1409_, v_binderType_1445_, v___y_1410_, v___y_1411_, v___y_1412_);
if (lean_obj_tag(v___x_1448_) == 0)
{
lean_object* v_a_1449_; lean_object* v___x_1450_; 
v_a_1449_ = lean_ctor_get(v___x_1448_, 0);
lean_inc(v_a_1449_);
lean_dec_ref_known(v___x_1448_, 1);
lean_inc_ref(v_body_1446_);
lean_inc_ref(v_post_1409_);
lean_inc_ref(v_pre_1407_);
v___x_1450_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1407_, v_post_1409_, v_body_1446_, v___y_1410_, v___y_1411_, v___y_1412_);
if (lean_obj_tag(v___x_1450_) == 0)
{
lean_object* v_a_1451_; size_t v___x_1452_; size_t v___x_1453_; uint8_t v___x_1454_; 
v_a_1451_ = lean_ctor_get(v___x_1450_, 0);
lean_inc(v_a_1451_);
lean_dec_ref_known(v___x_1450_, 1);
v___x_1452_ = lean_ptr_addr(v_binderType_1445_);
v___x_1453_ = lean_ptr_addr(v_a_1449_);
v___x_1454_ = lean_usize_dec_eq(v___x_1452_, v___x_1453_);
if (v___x_1454_ == 0)
{
lean_object* v___x_1455_; lean_object* v___x_1456_; 
lean_inc(v_binderName_1444_);
lean_dec_ref_known(v___y_1421_, 3);
v___x_1455_ = l_Lean_Expr_lam___override(v_binderName_1444_, v_a_1449_, v_a_1451_, v_binderInfo_1447_);
v___x_1456_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3(v_pre_1407_, v_post_1409_, v___x_1455_, v___y_1410_, v___y_1411_, v___y_1412_);
return v___x_1456_;
}
else
{
size_t v___x_1457_; size_t v___x_1458_; uint8_t v___x_1459_; 
v___x_1457_ = lean_ptr_addr(v_body_1446_);
v___x_1458_ = lean_ptr_addr(v_a_1451_);
v___x_1459_ = lean_usize_dec_eq(v___x_1457_, v___x_1458_);
if (v___x_1459_ == 0)
{
lean_object* v___x_1460_; lean_object* v___x_1461_; 
lean_inc(v_binderName_1444_);
lean_dec_ref_known(v___y_1421_, 3);
v___x_1460_ = l_Lean_Expr_lam___override(v_binderName_1444_, v_a_1449_, v_a_1451_, v_binderInfo_1447_);
v___x_1461_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3(v_pre_1407_, v_post_1409_, v___x_1460_, v___y_1410_, v___y_1411_, v___y_1412_);
return v___x_1461_;
}
else
{
uint8_t v___x_1462_; 
v___x_1462_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1447_, v_binderInfo_1447_);
if (v___x_1462_ == 0)
{
lean_object* v___x_1463_; lean_object* v___x_1464_; 
lean_inc(v_binderName_1444_);
lean_dec_ref_known(v___y_1421_, 3);
v___x_1463_ = l_Lean_Expr_lam___override(v_binderName_1444_, v_a_1449_, v_a_1451_, v_binderInfo_1447_);
v___x_1464_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3(v_pre_1407_, v_post_1409_, v___x_1463_, v___y_1410_, v___y_1411_, v___y_1412_);
return v___x_1464_;
}
else
{
lean_object* v___x_1465_; 
lean_dec(v_a_1451_);
lean_dec(v_a_1449_);
v___x_1465_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3(v_pre_1407_, v_post_1409_, v___y_1421_, v___y_1410_, v___y_1411_, v___y_1412_);
return v___x_1465_;
}
}
}
}
else
{
lean_dec(v_a_1449_);
lean_dec_ref_known(v___y_1421_, 3);
lean_dec_ref(v_post_1409_);
lean_dec_ref(v_pre_1407_);
return v___x_1450_;
}
}
else
{
lean_dec_ref_known(v___y_1421_, 3);
lean_dec_ref(v_post_1409_);
lean_dec_ref(v_pre_1407_);
return v___x_1448_;
}
}
case 8:
{
lean_object* v_declName_1466_; lean_object* v_type_1467_; lean_object* v_value_1468_; lean_object* v_body_1469_; uint8_t v_nondep_1470_; lean_object* v___x_1471_; 
v_declName_1466_ = lean_ctor_get(v___y_1421_, 0);
v_type_1467_ = lean_ctor_get(v___y_1421_, 1);
v_value_1468_ = lean_ctor_get(v___y_1421_, 2);
v_body_1469_ = lean_ctor_get(v___y_1421_, 3);
v_nondep_1470_ = lean_ctor_get_uint8(v___y_1421_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_1467_);
lean_inc_ref(v_post_1409_);
lean_inc_ref(v_pre_1407_);
v___x_1471_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1407_, v_post_1409_, v_type_1467_, v___y_1410_, v___y_1411_, v___y_1412_);
if (lean_obj_tag(v___x_1471_) == 0)
{
lean_object* v_a_1472_; lean_object* v___x_1473_; 
v_a_1472_ = lean_ctor_get(v___x_1471_, 0);
lean_inc(v_a_1472_);
lean_dec_ref_known(v___x_1471_, 1);
lean_inc_ref(v_value_1468_);
lean_inc_ref(v_post_1409_);
lean_inc_ref(v_pre_1407_);
v___x_1473_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1407_, v_post_1409_, v_value_1468_, v___y_1410_, v___y_1411_, v___y_1412_);
if (lean_obj_tag(v___x_1473_) == 0)
{
lean_object* v_a_1474_; lean_object* v___x_1475_; 
v_a_1474_ = lean_ctor_get(v___x_1473_, 0);
lean_inc(v_a_1474_);
lean_dec_ref_known(v___x_1473_, 1);
lean_inc_ref(v_body_1469_);
lean_inc_ref(v_post_1409_);
lean_inc_ref(v_pre_1407_);
v___x_1475_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1407_, v_post_1409_, v_body_1469_, v___y_1410_, v___y_1411_, v___y_1412_);
if (lean_obj_tag(v___x_1475_) == 0)
{
lean_object* v_a_1476_; size_t v___x_1477_; size_t v___x_1478_; uint8_t v___x_1479_; 
v_a_1476_ = lean_ctor_get(v___x_1475_, 0);
lean_inc(v_a_1476_);
lean_dec_ref_known(v___x_1475_, 1);
v___x_1477_ = lean_ptr_addr(v_type_1467_);
v___x_1478_ = lean_ptr_addr(v_a_1472_);
v___x_1479_ = lean_usize_dec_eq(v___x_1477_, v___x_1478_);
if (v___x_1479_ == 0)
{
lean_object* v___x_1480_; lean_object* v___x_1481_; 
lean_inc(v_declName_1466_);
lean_dec_ref_known(v___y_1421_, 4);
v___x_1480_ = l_Lean_Expr_letE___override(v_declName_1466_, v_a_1472_, v_a_1474_, v_a_1476_, v_nondep_1470_);
v___x_1481_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3(v_pre_1407_, v_post_1409_, v___x_1480_, v___y_1410_, v___y_1411_, v___y_1412_);
return v___x_1481_;
}
else
{
size_t v___x_1482_; size_t v___x_1483_; uint8_t v___x_1484_; 
v___x_1482_ = lean_ptr_addr(v_value_1468_);
v___x_1483_ = lean_ptr_addr(v_a_1474_);
v___x_1484_ = lean_usize_dec_eq(v___x_1482_, v___x_1483_);
if (v___x_1484_ == 0)
{
lean_object* v___x_1485_; lean_object* v___x_1486_; 
lean_inc(v_declName_1466_);
lean_dec_ref_known(v___y_1421_, 4);
v___x_1485_ = l_Lean_Expr_letE___override(v_declName_1466_, v_a_1472_, v_a_1474_, v_a_1476_, v_nondep_1470_);
v___x_1486_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3(v_pre_1407_, v_post_1409_, v___x_1485_, v___y_1410_, v___y_1411_, v___y_1412_);
return v___x_1486_;
}
else
{
size_t v___x_1487_; size_t v___x_1488_; uint8_t v___x_1489_; 
v___x_1487_ = lean_ptr_addr(v_body_1469_);
v___x_1488_ = lean_ptr_addr(v_a_1476_);
v___x_1489_ = lean_usize_dec_eq(v___x_1487_, v___x_1488_);
if (v___x_1489_ == 0)
{
lean_object* v___x_1490_; lean_object* v___x_1491_; 
lean_inc(v_declName_1466_);
lean_dec_ref_known(v___y_1421_, 4);
v___x_1490_ = l_Lean_Expr_letE___override(v_declName_1466_, v_a_1472_, v_a_1474_, v_a_1476_, v_nondep_1470_);
v___x_1491_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3(v_pre_1407_, v_post_1409_, v___x_1490_, v___y_1410_, v___y_1411_, v___y_1412_);
return v___x_1491_;
}
else
{
lean_object* v___x_1492_; 
lean_dec(v_a_1476_);
lean_dec(v_a_1474_);
lean_dec(v_a_1472_);
v___x_1492_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3(v_pre_1407_, v_post_1409_, v___y_1421_, v___y_1410_, v___y_1411_, v___y_1412_);
return v___x_1492_;
}
}
}
}
else
{
lean_dec(v_a_1474_);
lean_dec(v_a_1472_);
lean_dec_ref_known(v___y_1421_, 4);
lean_dec_ref(v_post_1409_);
lean_dec_ref(v_pre_1407_);
return v___x_1475_;
}
}
else
{
lean_dec(v_a_1472_);
lean_dec_ref_known(v___y_1421_, 4);
lean_dec_ref(v_post_1409_);
lean_dec_ref(v_pre_1407_);
return v___x_1473_;
}
}
else
{
lean_dec_ref_known(v___y_1421_, 4);
lean_dec_ref(v_post_1409_);
lean_dec_ref(v_pre_1407_);
return v___x_1471_;
}
}
case 5:
{
lean_object* v_dummy_1493_; lean_object* v_nargs_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; 
v_dummy_1493_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__18___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__18___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__18___closed__0);
v_nargs_1494_ = l_Lean_Expr_getAppNumArgs(v___y_1421_);
lean_inc(v_nargs_1494_);
v___x_1495_ = lean_mk_array(v_nargs_1494_, v_dummy_1493_);
v___x_1496_ = lean_unsigned_to_nat(1u);
v___x_1497_ = lean_nat_sub(v_nargs_1494_, v___x_1496_);
lean_dec(v_nargs_1494_);
lean_inc_ref(v___y_1421_);
lean_inc_ref(v_post_1409_);
lean_inc_ref(v_pre_1407_);
v___x_1498_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__4(v_pre_1407_, v_post_1409_, v___y_1421_, v___y_1421_, v___x_1495_, v___x_1497_, v___y_1410_, v___y_1411_, v___y_1412_);
lean_dec_ref_known(v___y_1421_, 2);
if (lean_obj_tag(v___x_1498_) == 0)
{
lean_object* v_a_1499_; lean_object* v___x_1500_; 
v_a_1499_ = lean_ctor_get(v___x_1498_, 0);
lean_inc(v_a_1499_);
lean_dec_ref_known(v___x_1498_, 1);
v___x_1500_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3(v_pre_1407_, v_post_1409_, v_a_1499_, v___y_1410_, v___y_1411_, v___y_1412_);
return v___x_1500_;
}
else
{
lean_dec_ref(v_post_1409_);
lean_dec_ref(v_pre_1407_);
return v___x_1498_;
}
}
case 10:
{
lean_object* v_data_1501_; lean_object* v_expr_1502_; lean_object* v___x_1503_; 
v_data_1501_ = lean_ctor_get(v___y_1421_, 0);
v_expr_1502_ = lean_ctor_get(v___y_1421_, 1);
lean_inc_ref(v_expr_1502_);
lean_inc_ref(v_post_1409_);
lean_inc_ref(v_pre_1407_);
v___x_1503_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1407_, v_post_1409_, v_expr_1502_, v___y_1410_, v___y_1411_, v___y_1412_);
if (lean_obj_tag(v___x_1503_) == 0)
{
lean_object* v_a_1504_; size_t v___x_1505_; size_t v___x_1506_; uint8_t v___x_1507_; 
v_a_1504_ = lean_ctor_get(v___x_1503_, 0);
lean_inc(v_a_1504_);
lean_dec_ref_known(v___x_1503_, 1);
v___x_1505_ = lean_ptr_addr(v_expr_1502_);
v___x_1506_ = lean_ptr_addr(v_a_1504_);
v___x_1507_ = lean_usize_dec_eq(v___x_1505_, v___x_1506_);
if (v___x_1507_ == 0)
{
lean_object* v___x_1508_; lean_object* v___x_1509_; 
lean_inc(v_data_1501_);
lean_dec_ref_known(v___y_1421_, 2);
v___x_1508_ = l_Lean_Expr_mdata___override(v_data_1501_, v_a_1504_);
v___x_1509_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3(v_pre_1407_, v_post_1409_, v___x_1508_, v___y_1410_, v___y_1411_, v___y_1412_);
return v___x_1509_;
}
else
{
lean_object* v___x_1510_; 
lean_dec(v_a_1504_);
v___x_1510_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3(v_pre_1407_, v_post_1409_, v___y_1421_, v___y_1410_, v___y_1411_, v___y_1412_);
return v___x_1510_;
}
}
else
{
lean_dec_ref_known(v___y_1421_, 2);
lean_dec_ref(v_post_1409_);
lean_dec_ref(v_pre_1407_);
return v___x_1503_;
}
}
case 11:
{
lean_object* v_typeName_1511_; lean_object* v_idx_1512_; lean_object* v_struct_1513_; lean_object* v___x_1514_; 
v_typeName_1511_ = lean_ctor_get(v___y_1421_, 0);
v_idx_1512_ = lean_ctor_get(v___y_1421_, 1);
v_struct_1513_ = lean_ctor_get(v___y_1421_, 2);
lean_inc_ref(v_struct_1513_);
lean_inc_ref(v_post_1409_);
lean_inc_ref(v_pre_1407_);
v___x_1514_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1407_, v_post_1409_, v_struct_1513_, v___y_1410_, v___y_1411_, v___y_1412_);
if (lean_obj_tag(v___x_1514_) == 0)
{
lean_object* v_a_1515_; size_t v___x_1516_; size_t v___x_1517_; uint8_t v___x_1518_; 
v_a_1515_ = lean_ctor_get(v___x_1514_, 0);
lean_inc(v_a_1515_);
lean_dec_ref_known(v___x_1514_, 1);
v___x_1516_ = lean_ptr_addr(v_struct_1513_);
v___x_1517_ = lean_ptr_addr(v_a_1515_);
v___x_1518_ = lean_usize_dec_eq(v___x_1516_, v___x_1517_);
if (v___x_1518_ == 0)
{
lean_object* v___x_1519_; lean_object* v___x_1520_; 
lean_inc(v_idx_1512_);
lean_inc(v_typeName_1511_);
lean_dec_ref_known(v___y_1421_, 3);
v___x_1519_ = l_Lean_Expr_proj___override(v_typeName_1511_, v_idx_1512_, v_a_1515_);
v___x_1520_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3(v_pre_1407_, v_post_1409_, v___x_1519_, v___y_1410_, v___y_1411_, v___y_1412_);
return v___x_1520_;
}
else
{
lean_object* v___x_1521_; 
lean_dec(v_a_1515_);
v___x_1521_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3(v_pre_1407_, v_post_1409_, v___y_1421_, v___y_1410_, v___y_1411_, v___y_1412_);
return v___x_1521_;
}
}
else
{
lean_dec_ref_known(v___y_1421_, 3);
lean_dec_ref(v_post_1409_);
lean_dec_ref(v_pre_1407_);
return v___x_1514_;
}
}
default: 
{
lean_object* v___x_1522_; 
v___x_1522_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3(v_pre_1407_, v_post_1409_, v___y_1421_, v___y_1410_, v___y_1411_, v___y_1412_);
return v___x_1522_;
}
}
}
}
}
else
{
lean_object* v_a_1534_; lean_object* v___x_1536_; uint8_t v_isShared_1537_; uint8_t v_isSharedCheck_1541_; 
lean_dec_ref(v_post_1409_);
lean_dec_ref(v_e_1408_);
lean_dec_ref(v_pre_1407_);
v_a_1534_ = lean_ctor_get(v___x_1415_, 0);
v_isSharedCheck_1541_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1541_ == 0)
{
v___x_1536_ = v___x_1415_;
v_isShared_1537_ = v_isSharedCheck_1541_;
goto v_resetjp_1535_;
}
else
{
lean_inc(v_a_1534_);
lean_dec(v___x_1415_);
v___x_1536_ = lean_box(0);
v_isShared_1537_ = v_isSharedCheck_1541_;
goto v_resetjp_1535_;
}
v_resetjp_1535_:
{
lean_object* v___x_1539_; 
if (v_isShared_1537_ == 0)
{
v___x_1539_ = v___x_1536_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v_a_1534_);
v___x_1539_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
return v___x_1539_;
}
}
}
}
else
{
lean_object* v_a_1542_; lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1549_; 
lean_dec_ref(v_post_1409_);
lean_dec_ref(v_e_1408_);
lean_dec_ref(v_pre_1407_);
v_a_1542_ = lean_ctor_get(v___x_1414_, 0);
v_isSharedCheck_1549_ = !lean_is_exclusive(v___x_1414_);
if (v_isSharedCheck_1549_ == 0)
{
v___x_1544_ = v___x_1414_;
v_isShared_1545_ = v_isSharedCheck_1549_;
goto v_resetjp_1543_;
}
else
{
lean_inc(v_a_1542_);
lean_dec(v___x_1414_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1549_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
lean_object* v___x_1547_; 
if (v_isShared_1545_ == 0)
{
v___x_1547_ = v___x_1544_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v_a_1542_);
v___x_1547_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1546_;
}
v_reusejp_1546_:
{
return v___x_1547_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__1___boxed(lean_object* v___x_1550_, lean_object* v_pre_1551_, lean_object* v_e_1552_, lean_object* v_post_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_){
_start:
{
lean_object* v_res_1558_; 
v_res_1558_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__1(v___x_1550_, v_pre_1551_, v_e_1552_, v_post_1553_, v___y_1554_, v___y_1555_, v___y_1556_);
lean_dec(v___y_1556_);
lean_dec_ref(v___y_1555_);
lean_dec(v___y_1554_);
return v_res_1558_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(lean_object* v_pre_1559_, lean_object* v_post_1560_, lean_object* v_e_1561_, lean_object* v_a_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_){
_start:
{
lean_object* v___x_1566_; lean_object* v___x_1567_; 
lean_inc(v_a_1562_);
v___x_1566_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1566_, 0, lean_box(0));
lean_closure_set(v___x_1566_, 1, lean_box(0));
lean_closure_set(v___x_1566_, 2, v_a_1562_);
v___x_1567_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__0(lean_box(0), v___x_1566_, v___y_1563_, v___y_1564_);
if (lean_obj_tag(v___x_1567_) == 0)
{
lean_object* v_a_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1599_; 
v_a_1568_ = lean_ctor_get(v___x_1567_, 0);
v_isSharedCheck_1599_ = !lean_is_exclusive(v___x_1567_);
if (v_isSharedCheck_1599_ == 0)
{
v___x_1570_ = v___x_1567_;
v_isShared_1571_ = v_isSharedCheck_1599_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_a_1568_);
lean_dec(v___x_1567_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1599_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v___x_1572_; 
v___x_1572_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1___redArg(v_a_1568_, v_e_1561_);
lean_dec(v_a_1568_);
if (lean_obj_tag(v___x_1572_) == 0)
{
lean_object* v___x_1573_; lean_object* v___f_1574_; lean_object* v___x_1575_; 
lean_del_object(v___x_1570_);
v___x_1573_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__20___closed__0));
lean_inc_ref(v_e_1561_);
v___f_1574_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__1___boxed), 8, 4);
lean_closure_set(v___f_1574_, 0, v___x_1573_);
lean_closure_set(v___f_1574_, 1, v_pre_1559_);
lean_closure_set(v___f_1574_, 2, v_e_1561_);
lean_closure_set(v___f_1574_, 3, v_post_1560_);
v___x_1575_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___redArg(v___f_1574_, v_a_1562_, v___y_1563_, v___y_1564_);
if (lean_obj_tag(v___x_1575_) == 0)
{
lean_object* v_a_1576_; lean_object* v___f_1577_; lean_object* v___x_1578_; 
v_a_1576_ = lean_ctor_get(v___x_1575_, 0);
lean_inc_n(v_a_1576_, 2);
lean_dec_ref_known(v___x_1575_, 1);
lean_inc(v_a_1562_);
v___f_1577_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1577_, 0, v_a_1562_);
lean_closure_set(v___f_1577_, 1, v_e_1561_);
lean_closure_set(v___f_1577_, 2, v_a_1576_);
v___x_1578_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__0(lean_box(0), v___f_1577_, v___y_1563_, v___y_1564_);
if (lean_obj_tag(v___x_1578_) == 0)
{
lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1585_; 
v_isSharedCheck_1585_ = !lean_is_exclusive(v___x_1578_);
if (v_isSharedCheck_1585_ == 0)
{
lean_object* v_unused_1586_; 
v_unused_1586_ = lean_ctor_get(v___x_1578_, 0);
lean_dec(v_unused_1586_);
v___x_1580_ = v___x_1578_;
v_isShared_1581_ = v_isSharedCheck_1585_;
goto v_resetjp_1579_;
}
else
{
lean_dec(v___x_1578_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1585_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
lean_object* v___x_1583_; 
if (v_isShared_1581_ == 0)
{
lean_ctor_set(v___x_1580_, 0, v_a_1576_);
v___x_1583_ = v___x_1580_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v_a_1576_);
v___x_1583_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
return v___x_1583_;
}
}
}
else
{
lean_object* v_a_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1594_; 
lean_dec(v_a_1576_);
v_a_1587_ = lean_ctor_get(v___x_1578_, 0);
v_isSharedCheck_1594_ = !lean_is_exclusive(v___x_1578_);
if (v_isSharedCheck_1594_ == 0)
{
v___x_1589_ = v___x_1578_;
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_a_1587_);
lean_dec(v___x_1578_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
lean_object* v___x_1592_; 
if (v_isShared_1590_ == 0)
{
v___x_1592_ = v___x_1589_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v_a_1587_);
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
lean_dec_ref(v_e_1561_);
return v___x_1575_;
}
}
else
{
lean_object* v_val_1595_; lean_object* v___x_1597_; 
lean_dec_ref(v_e_1561_);
lean_dec_ref(v_post_1560_);
lean_dec_ref(v_pre_1559_);
v_val_1595_ = lean_ctor_get(v___x_1572_, 0);
lean_inc(v_val_1595_);
lean_dec_ref_known(v___x_1572_, 1);
if (v_isShared_1571_ == 0)
{
lean_ctor_set(v___x_1570_, 0, v_val_1595_);
v___x_1597_ = v___x_1570_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v_val_1595_);
v___x_1597_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
return v___x_1597_;
}
}
}
}
else
{
lean_object* v_a_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1607_; 
lean_dec_ref(v_e_1561_);
lean_dec_ref(v_post_1560_);
lean_dec_ref(v_pre_1559_);
v_a_1600_ = lean_ctor_get(v___x_1567_, 0);
v_isSharedCheck_1607_ = !lean_is_exclusive(v___x_1567_);
if (v_isSharedCheck_1607_ == 0)
{
v___x_1602_ = v___x_1567_;
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_a_1600_);
lean_dec(v___x_1567_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1605_; 
if (v_isShared_1603_ == 0)
{
v___x_1605_ = v___x_1602_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_a_1600_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
return v___x_1605_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3(lean_object* v_pre_1608_, lean_object* v_post_1609_, lean_object* v_e_1610_, lean_object* v_a_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_){
_start:
{
lean_object* v___x_1615_; 
lean_inc_ref(v_post_1609_);
lean_inc(v___y_1613_);
lean_inc_ref(v___y_1612_);
lean_inc_ref(v_e_1610_);
v___x_1615_ = lean_apply_4(v_post_1609_, v_e_1610_, v___y_1612_, v___y_1613_, lean_box(0));
if (lean_obj_tag(v___x_1615_) == 0)
{
lean_object* v_a_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1634_; 
v_a_1616_ = lean_ctor_get(v___x_1615_, 0);
v_isSharedCheck_1634_ = !lean_is_exclusive(v___x_1615_);
if (v_isSharedCheck_1634_ == 0)
{
v___x_1618_ = v___x_1615_;
v_isShared_1619_ = v_isSharedCheck_1634_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_a_1616_);
lean_dec(v___x_1615_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1634_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
switch(lean_obj_tag(v_a_1616_))
{
case 0:
{
lean_object* v_e_1620_; lean_object* v___x_1622_; 
lean_dec_ref(v_e_1610_);
lean_dec_ref(v_post_1609_);
lean_dec_ref(v_pre_1608_);
v_e_1620_ = lean_ctor_get(v_a_1616_, 0);
lean_inc_ref(v_e_1620_);
lean_dec_ref_known(v_a_1616_, 1);
if (v_isShared_1619_ == 0)
{
lean_ctor_set(v___x_1618_, 0, v_e_1620_);
v___x_1622_ = v___x_1618_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v_e_1620_);
v___x_1622_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
return v___x_1622_;
}
}
case 1:
{
lean_object* v_e_1624_; lean_object* v___x_1625_; 
lean_del_object(v___x_1618_);
lean_dec_ref(v_e_1610_);
v_e_1624_ = lean_ctor_get(v_a_1616_, 0);
lean_inc_ref(v_e_1624_);
lean_dec_ref_known(v_a_1616_, 1);
v___x_1625_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1608_, v_post_1609_, v_e_1624_, v_a_1611_, v___y_1612_, v___y_1613_);
return v___x_1625_;
}
default: 
{
lean_object* v_e_x3f_1626_; 
lean_dec_ref(v_post_1609_);
lean_dec_ref(v_pre_1608_);
v_e_x3f_1626_ = lean_ctor_get(v_a_1616_, 0);
lean_inc(v_e_x3f_1626_);
lean_dec_ref_known(v_a_1616_, 1);
if (lean_obj_tag(v_e_x3f_1626_) == 0)
{
lean_object* v___x_1628_; 
if (v_isShared_1619_ == 0)
{
lean_ctor_set(v___x_1618_, 0, v_e_1610_);
v___x_1628_ = v___x_1618_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v_e_1610_);
v___x_1628_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
return v___x_1628_;
}
}
else
{
lean_object* v_val_1630_; lean_object* v___x_1632_; 
lean_dec_ref(v_e_1610_);
v_val_1630_ = lean_ctor_get(v_e_x3f_1626_, 0);
lean_inc(v_val_1630_);
lean_dec_ref_known(v_e_x3f_1626_, 1);
if (v_isShared_1619_ == 0)
{
lean_ctor_set(v___x_1618_, 0, v_val_1630_);
v___x_1632_ = v___x_1618_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v_val_1630_);
v___x_1632_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
return v___x_1632_;
}
}
}
}
}
}
else
{
lean_object* v_a_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1642_; 
lean_dec_ref(v_e_1610_);
lean_dec_ref(v_post_1609_);
lean_dec_ref(v_pre_1608_);
v_a_1635_ = lean_ctor_get(v___x_1615_, 0);
v_isSharedCheck_1642_ = !lean_is_exclusive(v___x_1615_);
if (v_isSharedCheck_1642_ == 0)
{
v___x_1637_ = v___x_1615_;
v_isShared_1638_ = v_isSharedCheck_1642_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_a_1635_);
lean_dec(v___x_1615_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1642_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v___x_1640_; 
if (v_isShared_1638_ == 0)
{
v___x_1640_ = v___x_1637_;
goto v_reusejp_1639_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v_a_1635_);
v___x_1640_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1639_;
}
v_reusejp_1639_:
{
return v___x_1640_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3___boxed(lean_object* v_pre_1643_, lean_object* v_post_1644_, lean_object* v_e_1645_, lean_object* v_a_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_){
_start:
{
lean_object* v_res_1650_; 
v_res_1650_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__3(v_pre_1643_, v_post_1644_, v_e_1645_, v_a_1646_, v___y_1647_, v___y_1648_);
lean_dec(v___y_1648_);
lean_dec_ref(v___y_1647_);
lean_dec(v_a_1646_);
return v_res_1650_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_1651_, lean_object* v_post_1652_, lean_object* v_sz_1653_, lean_object* v_i_1654_, lean_object* v_bs_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_){
_start:
{
size_t v_sz_boxed_1660_; size_t v_i_boxed_1661_; lean_object* v_res_1662_; 
v_sz_boxed_1660_ = lean_unbox_usize(v_sz_1653_);
lean_dec(v_sz_1653_);
v_i_boxed_1661_ = lean_unbox_usize(v_i_1654_);
lean_dec(v_i_1654_);
v_res_1662_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__2(v_pre_1651_, v_post_1652_, v_sz_boxed_1660_, v_i_boxed_1661_, v_bs_1655_, v___y_1656_, v___y_1657_, v___y_1658_);
lean_dec(v___y_1658_);
lean_dec_ref(v___y_1657_);
lean_dec(v___y_1656_);
return v_res_1662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__4___boxed(lean_object* v_pre_1663_, lean_object* v_post_1664_, lean_object* v___y_1665_, lean_object* v_x_1666_, lean_object* v_x_1667_, lean_object* v_x_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_){
_start:
{
lean_object* v_res_1673_; 
v_res_1673_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__4(v_pre_1663_, v_post_1664_, v___y_1665_, v_x_1666_, v_x_1667_, v_x_1668_, v___y_1669_, v___y_1670_, v___y_1671_);
lean_dec(v___y_1671_);
lean_dec_ref(v___y_1670_);
lean_dec(v___y_1669_);
lean_dec_ref(v___y_1665_);
return v_res_1673_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___boxed(lean_object* v_pre_1674_, lean_object* v_post_1675_, lean_object* v_e_1676_, lean_object* v_a_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_){
_start:
{
lean_object* v_res_1681_; 
v_res_1681_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1674_, v_post_1675_, v_e_1676_, v_a_1677_, v___y_1678_, v___y_1679_);
lean_dec(v___y_1679_);
lean_dec_ref(v___y_1678_);
lean_dec(v_a_1677_);
return v_res_1681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___lam__0(lean_object* v_00_u03b1_1682_, lean_object* v_x_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_){
_start:
{
lean_object* v___x_1687_; lean_object* v___x_1688_; 
v___x_1687_ = lean_apply_1(v_x_1683_, lean_box(0));
v___x_1688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1688_, 0, v___x_1687_);
return v___x_1688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___lam__0___boxed(lean_object* v_00_u03b1_1689_, lean_object* v_x_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_){
_start:
{
lean_object* v_res_1694_; 
v_res_1694_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___lam__0(v_00_u03b1_1689_, v_x_1690_, v___y_1691_, v___y_1692_);
lean_dec(v___y_1692_);
lean_dec_ref(v___y_1691_);
return v_res_1694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(lean_object* v_input_1695_, lean_object* v_pre_1696_, lean_object* v_post_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_){
_start:
{
lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v_a_1703_; lean_object* v___x_1704_; 
v___x_1701_ = lean_obj_once(&l_Lean_Core_transform___redArg___closed__2, &l_Lean_Core_transform___redArg___closed__2_once, _init_l_Lean_Core_transform___redArg___closed__2);
v___x_1702_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___lam__0(lean_box(0), v___x_1701_, v___y_1698_, v___y_1699_);
v_a_1703_ = lean_ctor_get(v___x_1702_, 0);
lean_inc(v_a_1703_);
lean_dec_ref(v___x_1702_);
v___x_1704_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0(v_pre_1696_, v_post_1697_, v_input_1695_, v_a_1703_, v___y_1698_, v___y_1699_);
if (lean_obj_tag(v___x_1704_) == 0)
{
lean_object* v_a_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1714_; 
v_a_1705_ = lean_ctor_get(v___x_1704_, 0);
lean_inc(v_a_1705_);
lean_dec_ref_known(v___x_1704_, 1);
v___x_1706_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1706_, 0, lean_box(0));
lean_closure_set(v___x_1706_, 1, lean_box(0));
lean_closure_set(v___x_1706_, 2, v_a_1703_);
v___x_1707_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___lam__0(lean_box(0), v___x_1706_, v___y_1698_, v___y_1699_);
v_isSharedCheck_1714_ = !lean_is_exclusive(v___x_1707_);
if (v_isSharedCheck_1714_ == 0)
{
lean_object* v_unused_1715_; 
v_unused_1715_ = lean_ctor_get(v___x_1707_, 0);
lean_dec(v_unused_1715_);
v___x_1709_ = v___x_1707_;
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
else
{
lean_dec(v___x_1707_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
lean_object* v___x_1712_; 
if (v_isShared_1710_ == 0)
{
lean_ctor_set(v___x_1709_, 0, v_a_1705_);
v___x_1712_ = v___x_1709_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v_a_1705_);
v___x_1712_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
return v___x_1712_;
}
}
}
else
{
lean_dec(v_a_1703_);
return v___x_1704_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0___boxed(lean_object* v_input_1716_, lean_object* v_pre_1717_, lean_object* v_post_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_){
_start:
{
lean_object* v_res_1722_; 
v_res_1722_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_input_1716_, v_pre_1717_, v_post_1718_, v___y_1719_, v___y_1720_);
lean_dec(v___y_1720_);
lean_dec_ref(v___y_1719_);
return v_res_1722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_betaReduce(lean_object* v_e_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_){
_start:
{
lean_object* v___f_1729_; lean_object* v___f_1730_; lean_object* v___x_1731_; 
v___f_1729_ = ((lean_object*)(l_Lean_Core_betaReduce___closed__0));
v___f_1730_ = ((lean_object*)(l_Lean_Core_betaReduce___closed__1));
v___x_1731_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_1725_, v___f_1729_, v___f_1730_, v_a_1726_, v_a_1727_);
return v___x_1731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_betaReduce___boxed(lean_object* v_e_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_){
_start:
{
lean_object* v_res_1736_; 
v_res_1736_ = l_Lean_Core_betaReduce(v_e_1732_, v_a_1733_, v_a_1734_);
lean_dec(v_a_1734_);
lean_dec_ref(v_a_1733_);
return v_res_1736_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1737_, lean_object* v_m_1738_, lean_object* v_a_1739_){
_start:
{
lean_object* v___x_1740_; 
v___x_1740_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1___redArg(v_m_1738_, v_a_1739_);
return v___x_1740_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1741_, lean_object* v_m_1742_, lean_object* v_a_1743_){
_start:
{
lean_object* v_res_1744_; 
v_res_1744_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1(v_00_u03b2_1741_, v_m_1742_, v_a_1743_);
lean_dec_ref(v_a_1743_);
lean_dec_ref(v_m_1742_);
return v_res_1744_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_1745_, lean_object* v_ref_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_){
_start:
{
lean_object* v___x_1750_; 
v___x_1750_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_1746_);
return v___x_1750_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1751_, lean_object* v_ref_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_){
_start:
{
lean_object* v_res_1756_; 
v_res_1756_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_1751_, v_ref_1752_, v___y_1753_, v___y_1754_);
lean_dec(v___y_1754_);
lean_dec_ref(v___y_1753_);
return v_res_1756_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8(lean_object* v_00_u03b1_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_){
_start:
{
lean_object* v___x_1761_; 
v___x_1761_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___redArg();
return v___x_1761_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8___boxed(lean_object* v_00_u03b1_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_){
_start:
{
lean_object* v_res_1766_; 
v_res_1766_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__8(v_00_u03b1_1762_, v___y_1763_, v___y_1764_);
lean_dec(v___y_1764_);
lean_dec_ref(v___y_1763_);
return v_res_1766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5(lean_object* v_00_u03b1_1767_, lean_object* v_x_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_){
_start:
{
lean_object* v___x_1773_; 
v___x_1773_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___redArg(v_x_1768_, v___y_1769_, v___y_1770_, v___y_1771_);
return v___x_1773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b1_1774_, lean_object* v_x_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_){
_start:
{
lean_object* v_res_1780_; 
v_res_1780_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5(v_00_u03b1_1774_, v_x_1775_, v___y_1776_, v___y_1777_, v___y_1778_);
lean_dec(v___y_1778_);
lean_dec_ref(v___y_1777_);
lean_dec(v___y_1776_);
return v_res_1780_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6(lean_object* v_00_u03b2_1781_, lean_object* v_m_1782_, lean_object* v_a_1783_, lean_object* v_b_1784_){
_start:
{
lean_object* v___x_1785_; 
v___x_1785_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6___redArg(v_m_1782_, v_a_1783_, v_b_1784_);
return v___x_1785_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1786_, lean_object* v_a_1787_, lean_object* v_x_1788_){
_start:
{
lean_object* v___x_1789_; 
v___x_1789_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1_spec__2___redArg(v_a_1787_, v_x_1788_);
return v___x_1789_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1790_, lean_object* v_a_1791_, lean_object* v_x_1792_){
_start:
{
lean_object* v_res_1793_; 
v_res_1793_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1_spec__2(v_00_u03b2_1790_, v_a_1791_, v_x_1792_);
lean_dec(v_x_1792_);
lean_dec_ref(v_a_1791_);
return v_res_1793_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10(lean_object* v_00_u03b2_1794_, lean_object* v_a_1795_, lean_object* v_x_1796_){
_start:
{
uint8_t v___x_1797_; 
v___x_1797_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___redArg(v_a_1795_, v_x_1796_);
return v___x_1797_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10___boxed(lean_object* v_00_u03b2_1798_, lean_object* v_a_1799_, lean_object* v_x_1800_){
_start:
{
uint8_t v_res_1801_; lean_object* v_r_1802_; 
v_res_1801_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__10(v_00_u03b2_1798_, v_a_1799_, v_x_1800_);
lean_dec(v_x_1800_);
lean_dec_ref(v_a_1799_);
v_r_1802_ = lean_box(v_res_1801_);
return v_r_1802_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11(lean_object* v_00_u03b2_1803_, lean_object* v_data_1804_){
_start:
{
lean_object* v___x_1805_; 
v___x_1805_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11___redArg(v_data_1804_);
return v___x_1805_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__12(lean_object* v_00_u03b2_1806_, lean_object* v_a_1807_, lean_object* v_b_1808_, lean_object* v_x_1809_){
_start:
{
lean_object* v___x_1810_; 
v___x_1810_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__12___redArg(v_a_1807_, v_b_1808_, v_x_1809_);
return v___x_1810_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12(lean_object* v_00_u03b2_1811_, lean_object* v_i_1812_, lean_object* v_source_1813_, lean_object* v_target_1814_){
_start:
{
lean_object* v___x_1815_; 
v___x_1815_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v_i_1812_, v_source_1813_, v_target_1814_);
return v___x_1815_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13(lean_object* v_00_u03b2_1816_, lean_object* v_x_1817_, lean_object* v_x_1818_){
_start:
{
lean_object* v___x_1819_; 
v___x_1819_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_x_1817_, v_x_1818_);
return v___x_1819_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__0(lean_object* v_toApplicative_1820_, lean_object* v_a_1821_){
_start:
{
lean_object* v_toPure_1822_; lean_object* v___x_1823_; 
v_toPure_1822_ = lean_ctor_get(v_toApplicative_1820_, 1);
lean_inc(v_toPure_1822_);
lean_dec_ref(v_toApplicative_1820_);
v___x_1823_ = lean_apply_2(v_toPure_1822_, lean_box(0), v_a_1821_);
return v___x_1823_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__13(lean_object* v___x_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_){
_start:
{
lean_object* v___x_1830_; 
v___x_1830_ = l_Lean_Core_checkSystem(v___x_1824_, v___y_1827_, v___y_1828_);
return v___x_1830_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__13___boxed(lean_object* v___x_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_){
_start:
{
lean_object* v_res_1837_; 
v_res_1837_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__13(v___x_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_);
lean_dec(v___y_1835_);
lean_dec_ref(v___y_1834_);
lean_dec(v___y_1833_);
lean_dec_ref(v___y_1832_);
return v_res_1837_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14(lean_object* v_inst_1840_, lean_object* v_x_1841_, lean_object* v___x_1842_, lean_object* v___x_1843_, lean_object* v_inst_1844_, lean_object* v___f_1845_, lean_object* v___x_1846_, lean_object* v___x_1847_, lean_object* v_a_1848_, lean_object* v_toBind_1849_, lean_object* v___f_1850_, lean_object* v_toApplicative_1851_, lean_object* v_a_1852_){
_start:
{
if (lean_obj_tag(v_a_1852_) == 0)
{
lean_object* v___f_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_3322__overap_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; 
lean_dec_ref(v_toApplicative_1851_);
v___f_1853_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14___closed__0));
v___x_1854_ = lean_apply_2(v_inst_1840_, lean_box(0), v___f_1853_);
lean_inc_ref(v___x_1843_);
lean_inc_ref(v___x_1842_);
v___x_1855_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonadLift___aux__1___boxed), 10, 9);
lean_closure_set(v___x_1855_, 0, lean_box(0));
lean_closure_set(v___x_1855_, 1, lean_box(0));
lean_closure_set(v___x_1855_, 2, lean_box(0));
lean_closure_set(v___x_1855_, 3, lean_box(0));
lean_closure_set(v___x_1855_, 4, v_x_1841_);
lean_closure_set(v___x_1855_, 5, v___x_1842_);
lean_closure_set(v___x_1855_, 6, v___x_1843_);
lean_closure_set(v___x_1855_, 7, lean_box(0));
lean_closure_set(v___x_1855_, 8, v___x_1854_);
v___x_1856_ = lean_alloc_closure((void*)(l_Lean_MonadCacheT_instMonad___aux__13___boxed), 13, 12);
lean_closure_set(v___x_1856_, 0, lean_box(0));
lean_closure_set(v___x_1856_, 1, lean_box(0));
lean_closure_set(v___x_1856_, 2, lean_box(0));
lean_closure_set(v___x_1856_, 3, lean_box(0));
lean_closure_set(v___x_1856_, 4, v_x_1841_);
lean_closure_set(v___x_1856_, 5, v___x_1842_);
lean_closure_set(v___x_1856_, 6, v___x_1843_);
lean_closure_set(v___x_1856_, 7, v_inst_1844_);
lean_closure_set(v___x_1856_, 8, lean_box(0));
lean_closure_set(v___x_1856_, 9, lean_box(0));
lean_closure_set(v___x_1856_, 10, v___x_1855_);
lean_closure_set(v___x_1856_, 11, v___f_1845_);
v___x_3322__overap_1857_ = l_Lean_Meta_withIncRecDepth___redArg(v___x_1846_, v___x_1847_, v___x_1856_);
lean_inc(v_a_1848_);
v___x_1858_ = lean_apply_1(v___x_3322__overap_1857_, v_a_1848_);
v___x_1859_ = lean_apply_4(v_toBind_1849_, lean_box(0), lean_box(0), v___x_1858_, v___f_1850_);
return v___x_1859_;
}
else
{
lean_object* v_val_1860_; lean_object* v_toPure_1861_; lean_object* v___x_1862_; 
lean_dec(v___f_1850_);
lean_dec(v_toBind_1849_);
lean_dec_ref(v___x_1847_);
lean_dec_ref(v___x_1846_);
lean_dec(v___f_1845_);
lean_dec_ref(v_inst_1844_);
lean_dec_ref(v___x_1843_);
lean_dec_ref(v___x_1842_);
lean_dec(v_inst_1840_);
v_val_1860_ = lean_ctor_get(v_a_1852_, 0);
lean_inc(v_val_1860_);
lean_dec_ref_known(v_a_1852_, 1);
v_toPure_1861_ = lean_ctor_get(v_toApplicative_1851_, 1);
lean_inc(v_toPure_1861_);
lean_dec_ref(v_toApplicative_1851_);
v___x_1862_ = lean_apply_2(v_toPure_1861_, lean_box(0), v_val_1860_);
return v___x_1862_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14___boxed(lean_object* v_inst_1863_, lean_object* v_x_1864_, lean_object* v___x_1865_, lean_object* v___x_1866_, lean_object* v_inst_1867_, lean_object* v___f_1868_, lean_object* v___x_1869_, lean_object* v___x_1870_, lean_object* v_a_1871_, lean_object* v_toBind_1872_, lean_object* v___f_1873_, lean_object* v_toApplicative_1874_, lean_object* v_a_1875_){
_start:
{
lean_object* v_res_1876_; 
v_res_1876_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14(v_inst_1863_, v_x_1864_, v___x_1865_, v___x_1866_, v_inst_1867_, v___f_1868_, v___x_1869_, v___x_1870_, v_a_1871_, v_toBind_1872_, v___f_1873_, v_toApplicative_1874_, v_a_1875_);
lean_dec(v_a_1871_);
return v_res_1876_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__1(lean_object* v___x_1877_, lean_object* v___x_1878_, lean_object* v_declName_1879_, lean_object* v_a_1880_, lean_object* v___f_1881_, uint8_t v_nondep_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_){
_start:
{
uint8_t v___x_1885_; lean_object* v___x_3341__overap_1886_; lean_object* v___x_1887_; 
v___x_1885_ = 0;
v___x_3341__overap_1886_ = l_Lean_Meta_withLetDecl___redArg(v___x_1877_, v___x_1878_, v_declName_1879_, v_a_1880_, v_a_1884_, v___f_1881_, v_nondep_1882_, v___x_1885_);
lean_inc(v_a_1883_);
v___x_1887_ = lean_apply_1(v___x_3341__overap_1886_, v_a_1883_);
return v___x_1887_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__1___boxed(lean_object* v___x_1888_, lean_object* v___x_1889_, lean_object* v_declName_1890_, lean_object* v_a_1891_, lean_object* v___f_1892_, lean_object* v_nondep_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_){
_start:
{
uint8_t v_nondep_3520__boxed_1896_; lean_object* v_res_1897_; 
v_nondep_3520__boxed_1896_ = lean_unbox(v_nondep_1893_);
v_res_1897_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__1(v___x_1888_, v___x_1889_, v_declName_1890_, v_a_1891_, v___f_1892_, v_nondep_3520__boxed_1896_, v_a_1894_, v_a_1895_);
lean_dec(v_a_1894_);
return v_res_1897_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__4(lean_object* v_fvars_1898_, uint8_t v_usedLetOnly_1899_, lean_object* v_inst_1900_, lean_object* v_toBind_1901_, lean_object* v___f_1902_, lean_object* v_a_1903_){
_start:
{
uint8_t v___x_1904_; uint8_t v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; 
v___x_1904_ = 0;
v___x_1905_ = 1;
v___x_1906_ = lean_box(v_usedLetOnly_1899_);
v___x_1907_ = lean_box(v___x_1904_);
v___x_1908_ = lean_box(v___x_1905_);
v___x_1909_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLetFVars___boxed), 10, 5);
lean_closure_set(v___x_1909_, 0, v_fvars_1898_);
lean_closure_set(v___x_1909_, 1, v_a_1903_);
lean_closure_set(v___x_1909_, 2, v___x_1906_);
lean_closure_set(v___x_1909_, 3, v___x_1907_);
lean_closure_set(v___x_1909_, 4, v___x_1908_);
v___x_1910_ = lean_apply_2(v_inst_1900_, lean_box(0), v___x_1909_);
v___x_1911_ = lean_apply_4(v_toBind_1901_, lean_box(0), lean_box(0), v___x_1910_, v___f_1902_);
return v___x_1911_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__4___boxed(lean_object* v_fvars_1912_, lean_object* v_usedLetOnly_1913_, lean_object* v_inst_1914_, lean_object* v_toBind_1915_, lean_object* v___f_1916_, lean_object* v_a_1917_){
_start:
{
uint8_t v_usedLetOnly_boxed_1918_; lean_object* v_res_1919_; 
v_usedLetOnly_boxed_1918_ = lean_unbox(v_usedLetOnly_1913_);
v_res_1919_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__4(v_fvars_1912_, v_usedLetOnly_boxed_1918_, v_inst_1914_, v_toBind_1915_, v___f_1916_, v_a_1917_);
return v_res_1919_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__3(lean_object* v_fvars_1920_, uint8_t v_usedLetOnly_1921_, lean_object* v_inst_1922_, lean_object* v_toBind_1923_, lean_object* v___f_1924_, lean_object* v_a_1925_){
_start:
{
uint8_t v___x_1926_; uint8_t v___x_1927_; uint8_t v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; 
v___x_1926_ = 0;
v___x_1927_ = 1;
v___x_1928_ = 1;
v___x_1929_ = lean_box(v___x_1926_);
v___x_1930_ = lean_box(v_usedLetOnly_1921_);
v___x_1931_ = lean_box(v___x_1926_);
v___x_1932_ = lean_box(v___x_1927_);
v___x_1933_ = lean_box(v___x_1928_);
v___x_1934_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(v___x_1934_, 0, v_fvars_1920_);
lean_closure_set(v___x_1934_, 1, v_a_1925_);
lean_closure_set(v___x_1934_, 2, v___x_1929_);
lean_closure_set(v___x_1934_, 3, v___x_1930_);
lean_closure_set(v___x_1934_, 4, v___x_1931_);
lean_closure_set(v___x_1934_, 5, v___x_1932_);
lean_closure_set(v___x_1934_, 6, v___x_1933_);
v___x_1935_ = lean_apply_2(v_inst_1922_, lean_box(0), v___x_1934_);
v___x_1936_ = lean_apply_4(v_toBind_1923_, lean_box(0), lean_box(0), v___x_1935_, v___f_1924_);
return v___x_1936_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__3___boxed(lean_object* v_fvars_1937_, lean_object* v_usedLetOnly_1938_, lean_object* v_inst_1939_, lean_object* v_toBind_1940_, lean_object* v___f_1941_, lean_object* v_a_1942_){
_start:
{
uint8_t v_usedLetOnly_boxed_1943_; lean_object* v_res_1944_; 
v_usedLetOnly_boxed_1943_ = lean_unbox(v_usedLetOnly_1938_);
v_res_1944_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__3(v_fvars_1937_, v_usedLetOnly_boxed_1943_, v_inst_1939_, v_toBind_1940_, v___f_1941_, v_a_1942_);
return v_res_1944_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1(lean_object* v___x_1945_, lean_object* v___x_1946_, lean_object* v_binderName_1947_, uint8_t v_binderInfo_1948_, lean_object* v___f_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_){
_start:
{
uint8_t v___x_1952_; lean_object* v___x_3399__overap_1953_; lean_object* v___x_1954_; 
v___x_1952_ = 0;
v___x_3399__overap_1953_ = l_Lean_Meta_withLocalDecl___redArg(v___x_1945_, v___x_1946_, v_binderName_1947_, v_binderInfo_1948_, v_a_1951_, v___f_1949_, v___x_1952_);
lean_inc(v_a_1950_);
v___x_1954_ = lean_apply_1(v___x_3399__overap_1953_, v_a_1950_);
return v___x_1954_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1___boxed(lean_object* v___x_1955_, lean_object* v___x_1956_, lean_object* v_binderName_1957_, lean_object* v_binderInfo_1958_, lean_object* v___f_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_){
_start:
{
uint8_t v_binderInfo_3588__boxed_1962_; lean_object* v_res_1963_; 
v_binderInfo_3588__boxed_1962_ = lean_unbox(v_binderInfo_1958_);
v_res_1963_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1(v___x_1955_, v___x_1956_, v_binderName_1957_, v_binderInfo_3588__boxed_1962_, v___f_1959_, v_a_1960_, v_a_1961_);
lean_dec(v_a_1960_);
return v_res_1963_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__3(lean_object* v_fvars_1964_, uint8_t v_usedLetOnly_1965_, lean_object* v_inst_1966_, lean_object* v_toBind_1967_, lean_object* v___f_1968_, lean_object* v_a_1969_){
_start:
{
uint8_t v___x_1970_; uint8_t v___x_1971_; uint8_t v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; 
v___x_1970_ = 0;
v___x_1971_ = 1;
v___x_1972_ = 1;
v___x_1973_ = lean_box(v___x_1970_);
v___x_1974_ = lean_box(v_usedLetOnly_1965_);
v___x_1975_ = lean_box(v___x_1971_);
v___x_1976_ = lean_box(v___x_1972_);
v___x_1977_ = lean_alloc_closure((void*)(l_Lean_Meta_mkForallFVars___boxed), 11, 6);
lean_closure_set(v___x_1977_, 0, v_fvars_1964_);
lean_closure_set(v___x_1977_, 1, v_a_1969_);
lean_closure_set(v___x_1977_, 2, v___x_1973_);
lean_closure_set(v___x_1977_, 3, v___x_1974_);
lean_closure_set(v___x_1977_, 4, v___x_1975_);
lean_closure_set(v___x_1977_, 5, v___x_1976_);
v___x_1978_ = lean_apply_2(v_inst_1966_, lean_box(0), v___x_1977_);
v___x_1979_ = lean_apply_4(v_toBind_1967_, lean_box(0), lean_box(0), v___x_1978_, v___f_1968_);
return v___x_1979_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__3___boxed(lean_object* v_fvars_1980_, lean_object* v_usedLetOnly_1981_, lean_object* v_inst_1982_, lean_object* v_toBind_1983_, lean_object* v___f_1984_, lean_object* v_a_1985_){
_start:
{
uint8_t v_usedLetOnly_boxed_1986_; lean_object* v_res_1987_; 
v_usedLetOnly_boxed_1986_ = lean_unbox(v_usedLetOnly_1981_);
v_res_1987_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__3(v_fvars_1980_, v_usedLetOnly_boxed_1986_, v_inst_1982_, v_toBind_1983_, v___f_1984_, v_a_1985_);
return v_res_1987_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__7(lean_object* v___f_1988_, lean_object* v___y_1989_, lean_object* v_a_1990_){
_start:
{
lean_object* v___x_1991_; 
lean_inc(v___y_1989_);
v___x_1991_ = lean_apply_2(v___f_1988_, v_a_1990_, v___y_1989_);
return v___x_1991_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__7___boxed(lean_object* v___f_1992_, lean_object* v___y_1993_, lean_object* v_a_1994_){
_start:
{
lean_object* v_res_1995_; 
v_res_1995_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__7(v___f_1992_, v___y_1993_, v_a_1994_);
lean_dec(v___y_1993_);
return v_res_1995_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1(lean_object* v_toApplicative_1996_, lean_object* v_acc_1997_, lean_object* v_next_1998_, lean_object* v_a_1999_){
_start:
{
lean_object* v_toPure_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; 
v_toPure_2000_ = lean_ctor_get(v_toApplicative_1996_, 1);
lean_inc(v_toPure_2000_);
lean_dec_ref(v_toApplicative_1996_);
v___x_2001_ = lean_array_fset(v_acc_1997_, v_next_1998_, v_a_1999_);
v___x_2002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2002_, 0, v___x_2001_);
v___x_2003_ = lean_apply_2(v_toPure_2000_, lean_box(0), v___x_2002_);
return v___x_2003_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1___boxed(lean_object* v_toApplicative_2004_, lean_object* v_acc_2005_, lean_object* v_next_2006_, lean_object* v_a_2007_){
_start:
{
lean_object* v_res_2008_; 
v_res_2008_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1(v_toApplicative_2004_, v_acc_2005_, v_next_2006_, v_a_2007_);
lean_dec(v_next_2006_);
return v_res_2008_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__2(lean_object* v_toApplicative_2009_, lean_object* v_next_2010_, lean_object* v_G_2011_, lean_object* v___y_2012_, lean_object* v_a_2013_){
_start:
{
if (lean_obj_tag(v_a_2013_) == 0)
{
lean_object* v_a_2014_; lean_object* v_toPure_2015_; lean_object* v___x_2016_; 
lean_dec(v_G_2011_);
v_a_2014_ = lean_ctor_get(v_a_2013_, 0);
lean_inc(v_a_2014_);
lean_dec_ref_known(v_a_2013_, 1);
v_toPure_2015_ = lean_ctor_get(v_toApplicative_2009_, 1);
lean_inc(v_toPure_2015_);
lean_dec_ref(v_toApplicative_2009_);
v___x_2016_ = lean_apply_2(v_toPure_2015_, lean_box(0), v_a_2014_);
return v___x_2016_;
}
else
{
lean_object* v_a_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; 
lean_dec_ref(v_toApplicative_2009_);
v_a_2017_ = lean_ctor_get(v_a_2013_, 0);
lean_inc(v_a_2017_);
lean_dec_ref_known(v_a_2013_, 1);
v___x_2018_ = lean_unsigned_to_nat(1u);
v___x_2019_ = lean_nat_add(v_next_2010_, v___x_2018_);
lean_inc(v___y_2012_);
v___x_2020_ = lean_apply_5(v_G_2011_, v___x_2019_, v_a_2017_, lean_box(0), lean_box(0), v___y_2012_);
return v___x_2020_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__2___boxed(lean_object* v_toApplicative_2021_, lean_object* v_next_2022_, lean_object* v_G_2023_, lean_object* v___y_2024_, lean_object* v_a_2025_){
_start:
{
lean_object* v_res_2026_; 
v_res_2026_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__2(v_toApplicative_2021_, v_next_2022_, v_G_2023_, v___y_2024_, v_a_2025_);
lean_dec(v___y_2024_);
lean_dec(v_next_2022_);
return v_res_2026_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5(lean_object* v_f_2027_, lean_object* v_inst_2028_, lean_object* v_inst_2029_, lean_object* v_inst_2030_, lean_object* v_pre_2031_, lean_object* v_post_2032_, uint8_t v_usedLetOnly_2033_, uint8_t v_skipConstInApp_2034_, uint8_t v_skipInstances_2035_, lean_object* v_x_2036_, lean_object* v_x_2037_, lean_object* v___y_2038_, lean_object* v_a_2039_){
_start:
{
lean_object* v___x_2040_; lean_object* v___x_2041_; 
v___x_2040_ = l_Lean_mkAppN(v_f_2027_, v_a_2039_);
v___x_2041_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2028_, v_inst_2029_, v_inst_2030_, v_pre_2031_, v_post_2032_, v_usedLetOnly_2033_, v_skipConstInApp_2034_, v_skipInstances_2035_, v_x_2036_, v_x_2037_, v___x_2040_, v___y_2038_);
return v___x_2041_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5___boxed(lean_object* v_f_2042_, lean_object* v_inst_2043_, lean_object* v_inst_2044_, lean_object* v_inst_2045_, lean_object* v_pre_2046_, lean_object* v_post_2047_, lean_object* v_usedLetOnly_2048_, lean_object* v_skipConstInApp_2049_, lean_object* v_skipInstances_2050_, lean_object* v_x_2051_, lean_object* v_x_2052_, lean_object* v___y_2053_, lean_object* v_a_2054_){
_start:
{
uint8_t v_usedLetOnly_boxed_2055_; uint8_t v_skipConstInApp_boxed_2056_; uint8_t v_skipInstances_boxed_2057_; lean_object* v_res_2058_; 
v_usedLetOnly_boxed_2055_ = lean_unbox(v_usedLetOnly_2048_);
v_skipConstInApp_boxed_2056_ = lean_unbox(v_skipConstInApp_2049_);
v_skipInstances_boxed_2057_ = lean_unbox(v_skipInstances_2050_);
v_res_2058_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5(v_f_2042_, v_inst_2043_, v_inst_2044_, v_inst_2045_, v_pre_2046_, v_post_2047_, v_usedLetOnly_boxed_2055_, v_skipConstInApp_boxed_2056_, v_skipInstances_boxed_2057_, v_x_2051_, v_x_2052_, v___y_2053_, v_a_2054_);
lean_dec_ref(v_a_2054_);
lean_dec(v___y_2053_);
return v_res_2058_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___boxed(lean_object* v_inst_2059_, lean_object* v_inst_2060_, lean_object* v_inst_2061_, lean_object* v_pre_2062_, lean_object* v_post_2063_, lean_object* v_usedLetOnly_2064_, lean_object* v_skipConstInApp_2065_, lean_object* v_skipInstances_2066_, lean_object* v_x_2067_, lean_object* v_x_2068_, lean_object* v_e_2069_, lean_object* v_a_2070_){
_start:
{
uint8_t v_usedLetOnly_boxed_2071_; uint8_t v_skipConstInApp_boxed_2072_; uint8_t v_skipInstances_boxed_2073_; lean_object* v_res_2074_; 
v_usedLetOnly_boxed_2071_ = lean_unbox(v_usedLetOnly_2064_);
v_skipConstInApp_boxed_2072_ = lean_unbox(v_skipConstInApp_2065_);
v_skipInstances_boxed_2073_ = lean_unbox(v_skipInstances_2066_);
v_res_2074_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2059_, v_inst_2060_, v_inst_2061_, v_pre_2062_, v_post_2063_, v_usedLetOnly_boxed_2071_, v_skipConstInApp_boxed_2072_, v_skipInstances_boxed_2073_, v_x_2067_, v_x_2068_, v_e_2069_, v_a_2070_);
lean_dec(v_a_2070_);
return v_res_2074_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__4(lean_object* v___x_2075_, lean_object* v_toApplicative_2076_, lean_object* v_toBind_2077_, lean_object* v___f_2078_, lean_object* v_paramInfo_2079_, lean_object* v_inst_2080_, lean_object* v_inst_2081_, lean_object* v_inst_2082_, lean_object* v_pre_2083_, lean_object* v_post_2084_, uint8_t v_usedLetOnly_2085_, uint8_t v_skipConstInApp_2086_, uint8_t v_skipInstances_2087_, lean_object* v_x_2088_, lean_object* v_x_2089_, lean_object* v_next_2090_, lean_object* v_acc_2091_, lean_object* v_h_2092_, lean_object* v_G_2093_, lean_object* v___y_2094_){
_start:
{
uint8_t v___x_2095_; 
v___x_2095_ = lean_nat_dec_lt(v_next_2090_, v___x_2075_);
if (v___x_2095_ == 0)
{
lean_object* v_toPure_2096_; lean_object* v___x_2097_; 
lean_dec(v_G_2093_);
lean_dec(v_next_2090_);
lean_dec(v_x_2089_);
lean_dec(v_post_2084_);
lean_dec(v_pre_2083_);
lean_dec_ref(v_inst_2082_);
lean_dec(v_inst_2081_);
lean_dec_ref(v_inst_2080_);
lean_dec(v___f_2078_);
lean_dec(v_toBind_2077_);
v_toPure_2096_ = lean_ctor_get(v_toApplicative_2076_, 1);
lean_inc(v_toPure_2096_);
lean_dec_ref(v_toApplicative_2076_);
v___x_2097_ = lean_apply_2(v_toPure_2096_, lean_box(0), v_acc_2091_);
return v___x_2097_;
}
else
{
lean_object* v___f_2098_; lean_object* v___y_2100_; lean_object* v___x_2103_; lean_object* v___x_2104_; uint8_t v___x_2105_; 
lean_inc(v___y_2094_);
lean_inc(v_next_2090_);
lean_inc_ref(v_toApplicative_2076_);
v___f_2098_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__2___boxed), 5, 4);
lean_closure_set(v___f_2098_, 0, v_toApplicative_2076_);
lean_closure_set(v___f_2098_, 1, v_next_2090_);
lean_closure_set(v___f_2098_, 2, v_G_2093_);
lean_closure_set(v___f_2098_, 3, v___y_2094_);
v___x_2103_ = lean_array_fget_borrowed(v_acc_2091_, v_next_2090_);
v___x_2104_ = lean_array_get_size(v_paramInfo_2079_);
v___x_2105_ = lean_nat_dec_lt(v_next_2090_, v___x_2104_);
if (v___x_2105_ == 0)
{
lean_object* v___f_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; 
lean_inc(v___x_2103_);
v___f_2106_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2106_, 0, v_toApplicative_2076_);
lean_closure_set(v___f_2106_, 1, v_acc_2091_);
lean_closure_set(v___f_2106_, 2, v_next_2090_);
v___x_2107_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2080_, v_inst_2081_, v_inst_2082_, v_pre_2083_, v_post_2084_, v_usedLetOnly_2085_, v_skipConstInApp_2086_, v_skipInstances_2087_, v_x_2088_, v_x_2089_, v___x_2103_, v___y_2094_);
lean_inc(v_toBind_2077_);
v___x_2108_ = lean_apply_4(v_toBind_2077_, lean_box(0), lean_box(0), v___x_2107_, v___f_2106_);
v___y_2100_ = v___x_2108_;
goto v___jp_2099_;
}
else
{
lean_object* v___x_2109_; uint8_t v_isInstance_2110_; 
v___x_2109_ = lean_array_fget_borrowed(v_paramInfo_2079_, v_next_2090_);
v_isInstance_2110_ = lean_ctor_get_uint8(v___x_2109_, sizeof(void*)*1 + 4);
if (v_isInstance_2110_ == 0)
{
lean_object* v___f_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; 
lean_inc(v___x_2103_);
v___f_2111_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2111_, 0, v_toApplicative_2076_);
lean_closure_set(v___f_2111_, 1, v_acc_2091_);
lean_closure_set(v___f_2111_, 2, v_next_2090_);
v___x_2112_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2080_, v_inst_2081_, v_inst_2082_, v_pre_2083_, v_post_2084_, v_usedLetOnly_2085_, v_skipConstInApp_2086_, v_skipInstances_2087_, v_x_2088_, v_x_2089_, v___x_2103_, v___y_2094_);
lean_inc(v_toBind_2077_);
v___x_2113_ = lean_apply_4(v_toBind_2077_, lean_box(0), lean_box(0), v___x_2112_, v___f_2111_);
v___y_2100_ = v___x_2113_;
goto v___jp_2099_;
}
else
{
lean_object* v_toPure_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; 
lean_dec(v_next_2090_);
lean_dec(v_x_2089_);
lean_dec(v_post_2084_);
lean_dec(v_pre_2083_);
lean_dec_ref(v_inst_2082_);
lean_dec(v_inst_2081_);
lean_dec_ref(v_inst_2080_);
v_toPure_2114_ = lean_ctor_get(v_toApplicative_2076_, 1);
lean_inc(v_toPure_2114_);
lean_dec_ref(v_toApplicative_2076_);
v___x_2115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2115_, 0, v_acc_2091_);
v___x_2116_ = lean_apply_2(v_toPure_2114_, lean_box(0), v___x_2115_);
v___y_2100_ = v___x_2116_;
goto v___jp_2099_;
}
}
v___jp_2099_:
{
lean_object* v___x_2101_; lean_object* v___x_2102_; 
lean_inc(v_toBind_2077_);
v___x_2101_ = lean_apply_4(v_toBind_2077_, lean_box(0), lean_box(0), v___y_2100_, v___f_2078_);
v___x_2102_ = lean_apply_4(v_toBind_2077_, lean_box(0), lean_box(0), v___x_2101_, v___f_2098_);
return v___x_2102_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__4___boxed(lean_object** _args){
lean_object* v___x_2117_ = _args[0];
lean_object* v_toApplicative_2118_ = _args[1];
lean_object* v_toBind_2119_ = _args[2];
lean_object* v___f_2120_ = _args[3];
lean_object* v_paramInfo_2121_ = _args[4];
lean_object* v_inst_2122_ = _args[5];
lean_object* v_inst_2123_ = _args[6];
lean_object* v_inst_2124_ = _args[7];
lean_object* v_pre_2125_ = _args[8];
lean_object* v_post_2126_ = _args[9];
lean_object* v_usedLetOnly_2127_ = _args[10];
lean_object* v_skipConstInApp_2128_ = _args[11];
lean_object* v_skipInstances_2129_ = _args[12];
lean_object* v_x_2130_ = _args[13];
lean_object* v_x_2131_ = _args[14];
lean_object* v_next_2132_ = _args[15];
lean_object* v_acc_2133_ = _args[16];
lean_object* v_h_2134_ = _args[17];
lean_object* v_G_2135_ = _args[18];
lean_object* v___y_2136_ = _args[19];
_start:
{
uint8_t v_usedLetOnly_boxed_2137_; uint8_t v_skipConstInApp_boxed_2138_; uint8_t v_skipInstances_boxed_2139_; lean_object* v_res_2140_; 
v_usedLetOnly_boxed_2137_ = lean_unbox(v_usedLetOnly_2127_);
v_skipConstInApp_boxed_2138_ = lean_unbox(v_skipConstInApp_2128_);
v_skipInstances_boxed_2139_ = lean_unbox(v_skipInstances_2129_);
v_res_2140_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__4(v___x_2117_, v_toApplicative_2118_, v_toBind_2119_, v___f_2120_, v_paramInfo_2121_, v_inst_2122_, v_inst_2123_, v_inst_2124_, v_pre_2125_, v_post_2126_, v_usedLetOnly_boxed_2137_, v_skipConstInApp_boxed_2138_, v_skipInstances_boxed_2139_, v_x_2130_, v_x_2131_, v_next_2132_, v_acc_2133_, v_h_2134_, v_G_2135_, v___y_2136_);
lean_dec(v___y_2136_);
lean_dec_ref(v_paramInfo_2121_);
lean_dec(v___x_2117_);
return v_res_2140_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__3(lean_object* v___x_2141_, lean_object* v_toApplicative_2142_, lean_object* v_toBind_2143_, lean_object* v___f_2144_, lean_object* v_inst_2145_, lean_object* v_inst_2146_, lean_object* v_inst_2147_, lean_object* v_pre_2148_, lean_object* v_post_2149_, uint8_t v_usedLetOnly_2150_, uint8_t v_skipConstInApp_2151_, uint8_t v_skipInstances_2152_, lean_object* v_x_2153_, lean_object* v_x_2154_, lean_object* v_args_2155_, lean_object* v___y_2156_, lean_object* v___f_2157_, lean_object* v_a_2158_){
_start:
{
lean_object* v_paramInfo_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___f_2164_; lean_object* v___x_3159__overap_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; 
v_paramInfo_2159_ = lean_ctor_get(v_a_2158_, 0);
lean_inc_ref(v_paramInfo_2159_);
lean_dec_ref(v_a_2158_);
v___x_2160_ = lean_unsigned_to_nat(0u);
v___x_2161_ = lean_box(v_usedLetOnly_2150_);
v___x_2162_ = lean_box(v_skipConstInApp_2151_);
v___x_2163_ = lean_box(v_skipInstances_2152_);
lean_inc(v_toBind_2143_);
v___f_2164_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__4___boxed), 20, 15);
lean_closure_set(v___f_2164_, 0, v___x_2141_);
lean_closure_set(v___f_2164_, 1, v_toApplicative_2142_);
lean_closure_set(v___f_2164_, 2, v_toBind_2143_);
lean_closure_set(v___f_2164_, 3, v___f_2144_);
lean_closure_set(v___f_2164_, 4, v_paramInfo_2159_);
lean_closure_set(v___f_2164_, 5, v_inst_2145_);
lean_closure_set(v___f_2164_, 6, v_inst_2146_);
lean_closure_set(v___f_2164_, 7, v_inst_2147_);
lean_closure_set(v___f_2164_, 8, v_pre_2148_);
lean_closure_set(v___f_2164_, 9, v_post_2149_);
lean_closure_set(v___f_2164_, 10, v___x_2161_);
lean_closure_set(v___f_2164_, 11, v___x_2162_);
lean_closure_set(v___f_2164_, 12, v___x_2163_);
lean_closure_set(v___f_2164_, 13, v_x_2153_);
lean_closure_set(v___f_2164_, 14, v_x_2154_);
v___x_3159__overap_2165_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_2164_, v___x_2160_, v_args_2155_, lean_box(0));
lean_inc(v___y_2156_);
v___x_2166_ = lean_apply_1(v___x_3159__overap_2165_, v___y_2156_);
v___x_2167_ = lean_apply_4(v_toBind_2143_, lean_box(0), lean_box(0), v___x_2166_, v___f_2157_);
return v___x_2167_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__3___boxed(lean_object** _args){
lean_object* v___x_2168_ = _args[0];
lean_object* v_toApplicative_2169_ = _args[1];
lean_object* v_toBind_2170_ = _args[2];
lean_object* v___f_2171_ = _args[3];
lean_object* v_inst_2172_ = _args[4];
lean_object* v_inst_2173_ = _args[5];
lean_object* v_inst_2174_ = _args[6];
lean_object* v_pre_2175_ = _args[7];
lean_object* v_post_2176_ = _args[8];
lean_object* v_usedLetOnly_2177_ = _args[9];
lean_object* v_skipConstInApp_2178_ = _args[10];
lean_object* v_skipInstances_2179_ = _args[11];
lean_object* v_x_2180_ = _args[12];
lean_object* v_x_2181_ = _args[13];
lean_object* v_args_2182_ = _args[14];
lean_object* v___y_2183_ = _args[15];
lean_object* v___f_2184_ = _args[16];
lean_object* v_a_2185_ = _args[17];
_start:
{
uint8_t v_usedLetOnly_boxed_2186_; uint8_t v_skipConstInApp_boxed_2187_; uint8_t v_skipInstances_boxed_2188_; lean_object* v_res_2189_; 
v_usedLetOnly_boxed_2186_ = lean_unbox(v_usedLetOnly_2177_);
v_skipConstInApp_boxed_2187_ = lean_unbox(v_skipConstInApp_2178_);
v_skipInstances_boxed_2188_ = lean_unbox(v_skipInstances_2179_);
v_res_2189_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__3(v___x_2168_, v_toApplicative_2169_, v_toBind_2170_, v___f_2171_, v_inst_2172_, v_inst_2173_, v_inst_2174_, v_pre_2175_, v_post_2176_, v_usedLetOnly_boxed_2186_, v_skipConstInApp_boxed_2187_, v_skipInstances_boxed_2188_, v_x_2180_, v_x_2181_, v_args_2182_, v___y_2183_, v___f_2184_, v_a_2185_);
lean_dec(v___y_2183_);
return v_res_2189_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__6(uint8_t v_skipInstances_2190_, lean_object* v_inst_2191_, lean_object* v_inst_2192_, lean_object* v_inst_2193_, lean_object* v_pre_2194_, lean_object* v_post_2195_, uint8_t v_usedLetOnly_2196_, uint8_t v_skipConstInApp_2197_, lean_object* v_x_2198_, lean_object* v_x_2199_, lean_object* v_args_2200_, lean_object* v___x_2201_, lean_object* v_toBind_2202_, lean_object* v_toApplicative_2203_, lean_object* v___f_2204_, lean_object* v_f_2205_, lean_object* v___y_2206_){
_start:
{
if (v_skipInstances_2190_ == 0)
{
lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___f_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; size_t v_sz_2215_; size_t v___x_2216_; lean_object* v___x_3172__overap_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; 
lean_dec(v___f_2204_);
lean_dec_ref(v_toApplicative_2203_);
v___x_2207_ = lean_box(v_usedLetOnly_2196_);
v___x_2208_ = lean_box(v_skipConstInApp_2197_);
v___x_2209_ = lean_box(v_skipInstances_2190_);
lean_inc_n(v___y_2206_, 2);
lean_inc(v_x_2199_);
lean_inc(v_post_2195_);
lean_inc(v_pre_2194_);
lean_inc_ref(v_inst_2193_);
lean_inc(v_inst_2192_);
lean_inc_ref(v_inst_2191_);
v___f_2210_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5___boxed), 13, 12);
lean_closure_set(v___f_2210_, 0, v_f_2205_);
lean_closure_set(v___f_2210_, 1, v_inst_2191_);
lean_closure_set(v___f_2210_, 2, v_inst_2192_);
lean_closure_set(v___f_2210_, 3, v_inst_2193_);
lean_closure_set(v___f_2210_, 4, v_pre_2194_);
lean_closure_set(v___f_2210_, 5, v_post_2195_);
lean_closure_set(v___f_2210_, 6, v___x_2207_);
lean_closure_set(v___f_2210_, 7, v___x_2208_);
lean_closure_set(v___f_2210_, 8, v___x_2209_);
lean_closure_set(v___f_2210_, 9, v_x_2198_);
lean_closure_set(v___f_2210_, 10, v_x_2199_);
lean_closure_set(v___f_2210_, 11, v___y_2206_);
v___x_2211_ = lean_box(v_usedLetOnly_2196_);
v___x_2212_ = lean_box(v_skipConstInApp_2197_);
v___x_2213_ = lean_box(v_skipInstances_2190_);
v___x_2214_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___boxed), 12, 10);
lean_closure_set(v___x_2214_, 0, v_inst_2191_);
lean_closure_set(v___x_2214_, 1, v_inst_2192_);
lean_closure_set(v___x_2214_, 2, v_inst_2193_);
lean_closure_set(v___x_2214_, 3, v_pre_2194_);
lean_closure_set(v___x_2214_, 4, v_post_2195_);
lean_closure_set(v___x_2214_, 5, v___x_2211_);
lean_closure_set(v___x_2214_, 6, v___x_2212_);
lean_closure_set(v___x_2214_, 7, v___x_2213_);
lean_closure_set(v___x_2214_, 8, v_x_2198_);
lean_closure_set(v___x_2214_, 9, v_x_2199_);
v_sz_2215_ = lean_array_size(v_args_2200_);
v___x_2216_ = ((size_t)0ULL);
v___x_3172__overap_2217_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2201_, v___x_2214_, v_sz_2215_, v___x_2216_, v_args_2200_);
v___x_2218_ = lean_apply_1(v___x_3172__overap_2217_, v___y_2206_);
v___x_2219_ = lean_apply_4(v_toBind_2202_, lean_box(0), lean_box(0), v___x_2218_, v___f_2210_);
return v___x_2219_;
}
else
{
lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___f_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___f_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; 
lean_dec_ref(v___x_2201_);
v___x_2220_ = lean_box(v_usedLetOnly_2196_);
v___x_2221_ = lean_box(v_skipConstInApp_2197_);
v___x_2222_ = lean_box(v_skipInstances_2190_);
lean_inc_n(v___y_2206_, 2);
lean_inc(v_x_2199_);
lean_inc(v_post_2195_);
lean_inc(v_pre_2194_);
lean_inc_ref(v_inst_2193_);
lean_inc_n(v_inst_2192_, 2);
lean_inc_ref(v_inst_2191_);
lean_inc_ref(v_f_2205_);
v___f_2223_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__5___boxed), 13, 12);
lean_closure_set(v___f_2223_, 0, v_f_2205_);
lean_closure_set(v___f_2223_, 1, v_inst_2191_);
lean_closure_set(v___f_2223_, 2, v_inst_2192_);
lean_closure_set(v___f_2223_, 3, v_inst_2193_);
lean_closure_set(v___f_2223_, 4, v_pre_2194_);
lean_closure_set(v___f_2223_, 5, v_post_2195_);
lean_closure_set(v___f_2223_, 6, v___x_2220_);
lean_closure_set(v___f_2223_, 7, v___x_2221_);
lean_closure_set(v___f_2223_, 8, v___x_2222_);
lean_closure_set(v___f_2223_, 9, v_x_2198_);
lean_closure_set(v___f_2223_, 10, v_x_2199_);
lean_closure_set(v___f_2223_, 11, v___y_2206_);
v___x_2224_ = lean_array_get_size(v_args_2200_);
v___x_2225_ = lean_box(v_usedLetOnly_2196_);
v___x_2226_ = lean_box(v_skipConstInApp_2197_);
v___x_2227_ = lean_box(v_skipInstances_2190_);
lean_inc(v_toBind_2202_);
v___f_2228_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__3___boxed), 18, 17);
lean_closure_set(v___f_2228_, 0, v___x_2224_);
lean_closure_set(v___f_2228_, 1, v_toApplicative_2203_);
lean_closure_set(v___f_2228_, 2, v_toBind_2202_);
lean_closure_set(v___f_2228_, 3, v___f_2204_);
lean_closure_set(v___f_2228_, 4, v_inst_2191_);
lean_closure_set(v___f_2228_, 5, v_inst_2192_);
lean_closure_set(v___f_2228_, 6, v_inst_2193_);
lean_closure_set(v___f_2228_, 7, v_pre_2194_);
lean_closure_set(v___f_2228_, 8, v_post_2195_);
lean_closure_set(v___f_2228_, 9, v___x_2225_);
lean_closure_set(v___f_2228_, 10, v___x_2226_);
lean_closure_set(v___f_2228_, 11, v___x_2227_);
lean_closure_set(v___f_2228_, 12, v_x_2198_);
lean_closure_set(v___f_2228_, 13, v_x_2199_);
lean_closure_set(v___f_2228_, 14, v_args_2200_);
lean_closure_set(v___f_2228_, 15, v___y_2206_);
lean_closure_set(v___f_2228_, 16, v___f_2223_);
v___x_2229_ = lean_alloc_closure((void*)(l_Lean_Meta_getFunInfoNArgs___boxed), 7, 2);
lean_closure_set(v___x_2229_, 0, v_f_2205_);
lean_closure_set(v___x_2229_, 1, v___x_2224_);
v___x_2230_ = lean_apply_2(v_inst_2192_, lean_box(0), v___x_2229_);
v___x_2231_ = lean_apply_4(v_toBind_2202_, lean_box(0), lean_box(0), v___x_2230_, v___f_2228_);
return v___x_2231_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__6___boxed(lean_object** _args){
lean_object* v_skipInstances_2232_ = _args[0];
lean_object* v_inst_2233_ = _args[1];
lean_object* v_inst_2234_ = _args[2];
lean_object* v_inst_2235_ = _args[3];
lean_object* v_pre_2236_ = _args[4];
lean_object* v_post_2237_ = _args[5];
lean_object* v_usedLetOnly_2238_ = _args[6];
lean_object* v_skipConstInApp_2239_ = _args[7];
lean_object* v_x_2240_ = _args[8];
lean_object* v_x_2241_ = _args[9];
lean_object* v_args_2242_ = _args[10];
lean_object* v___x_2243_ = _args[11];
lean_object* v_toBind_2244_ = _args[12];
lean_object* v_toApplicative_2245_ = _args[13];
lean_object* v___f_2246_ = _args[14];
lean_object* v_f_2247_ = _args[15];
lean_object* v___y_2248_ = _args[16];
_start:
{
uint8_t v_skipInstances_boxed_2249_; uint8_t v_usedLetOnly_boxed_2250_; uint8_t v_skipConstInApp_boxed_2251_; lean_object* v_res_2252_; 
v_skipInstances_boxed_2249_ = lean_unbox(v_skipInstances_2232_);
v_usedLetOnly_boxed_2250_ = lean_unbox(v_usedLetOnly_2238_);
v_skipConstInApp_boxed_2251_ = lean_unbox(v_skipConstInApp_2239_);
v_res_2252_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__6(v_skipInstances_boxed_2249_, v_inst_2233_, v_inst_2234_, v_inst_2235_, v_pre_2236_, v_post_2237_, v_usedLetOnly_boxed_2250_, v_skipConstInApp_boxed_2251_, v_x_2240_, v_x_2241_, v_args_2242_, v___x_2243_, v_toBind_2244_, v_toApplicative_2245_, v___f_2246_, v_f_2247_, v___y_2248_);
lean_dec(v___y_2248_);
return v_res_2252_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__9(uint8_t v_skipInstances_2253_, lean_object* v_inst_2254_, lean_object* v_inst_2255_, lean_object* v_inst_2256_, lean_object* v_pre_2257_, lean_object* v_post_2258_, uint8_t v_usedLetOnly_2259_, uint8_t v_skipConstInApp_2260_, lean_object* v_x_2261_, lean_object* v_x_2262_, lean_object* v___x_2263_, lean_object* v_toBind_2264_, lean_object* v_toApplicative_2265_, lean_object* v___f_2266_, lean_object* v_f_2267_, lean_object* v_args_2268_, lean_object* v___y_2269_){
_start:
{
lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___f_2273_; lean_object* v___f_2274_; 
v___x_2270_ = lean_box(v_skipInstances_2253_);
v___x_2271_ = lean_box(v_usedLetOnly_2259_);
v___x_2272_ = lean_box(v_skipConstInApp_2260_);
lean_inc_ref(v_toApplicative_2265_);
lean_inc(v_toBind_2264_);
lean_inc(v_x_2262_);
lean_inc(v_post_2258_);
lean_inc(v_pre_2257_);
lean_inc_ref(v_inst_2256_);
lean_inc(v_inst_2255_);
lean_inc_ref(v_inst_2254_);
v___f_2273_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__6___boxed), 17, 15);
lean_closure_set(v___f_2273_, 0, v___x_2270_);
lean_closure_set(v___f_2273_, 1, v_inst_2254_);
lean_closure_set(v___f_2273_, 2, v_inst_2255_);
lean_closure_set(v___f_2273_, 3, v_inst_2256_);
lean_closure_set(v___f_2273_, 4, v_pre_2257_);
lean_closure_set(v___f_2273_, 5, v_post_2258_);
lean_closure_set(v___f_2273_, 6, v___x_2271_);
lean_closure_set(v___f_2273_, 7, v___x_2272_);
lean_closure_set(v___f_2273_, 8, v_x_2261_);
lean_closure_set(v___f_2273_, 9, v_x_2262_);
lean_closure_set(v___f_2273_, 10, v_args_2268_);
lean_closure_set(v___f_2273_, 11, v___x_2263_);
lean_closure_set(v___f_2273_, 12, v_toBind_2264_);
lean_closure_set(v___f_2273_, 13, v_toApplicative_2265_);
lean_closure_set(v___f_2273_, 14, v___f_2266_);
lean_inc(v___y_2269_);
v___f_2274_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__7___boxed), 3, 2);
lean_closure_set(v___f_2274_, 0, v___f_2273_);
lean_closure_set(v___f_2274_, 1, v___y_2269_);
if (v_skipConstInApp_2260_ == 0)
{
lean_dec_ref(v_toApplicative_2265_);
goto v___jp_2275_;
}
else
{
uint8_t v___x_2278_; 
v___x_2278_ = l_Lean_Expr_isConst(v_f_2267_);
if (v___x_2278_ == 0)
{
lean_dec_ref(v_toApplicative_2265_);
goto v___jp_2275_;
}
else
{
lean_object* v_toPure_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; 
lean_dec(v_x_2262_);
lean_dec(v_post_2258_);
lean_dec(v_pre_2257_);
lean_dec_ref(v_inst_2256_);
lean_dec(v_inst_2255_);
lean_dec_ref(v_inst_2254_);
v_toPure_2279_ = lean_ctor_get(v_toApplicative_2265_, 1);
lean_inc(v_toPure_2279_);
lean_dec_ref(v_toApplicative_2265_);
v___x_2280_ = lean_apply_2(v_toPure_2279_, lean_box(0), v_f_2267_);
v___x_2281_ = lean_apply_4(v_toBind_2264_, lean_box(0), lean_box(0), v___x_2280_, v___f_2274_);
return v___x_2281_;
}
}
v___jp_2275_:
{
lean_object* v___x_2276_; lean_object* v___x_2277_; 
v___x_2276_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2254_, v_inst_2255_, v_inst_2256_, v_pre_2257_, v_post_2258_, v_usedLetOnly_2259_, v_skipConstInApp_2260_, v_skipInstances_2253_, v_x_2261_, v_x_2262_, v_f_2267_, v___y_2269_);
v___x_2277_ = lean_apply_4(v_toBind_2264_, lean_box(0), lean_box(0), v___x_2276_, v___f_2274_);
return v___x_2277_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__9___boxed(lean_object** _args){
lean_object* v_skipInstances_2282_ = _args[0];
lean_object* v_inst_2283_ = _args[1];
lean_object* v_inst_2284_ = _args[2];
lean_object* v_inst_2285_ = _args[3];
lean_object* v_pre_2286_ = _args[4];
lean_object* v_post_2287_ = _args[5];
lean_object* v_usedLetOnly_2288_ = _args[6];
lean_object* v_skipConstInApp_2289_ = _args[7];
lean_object* v_x_2290_ = _args[8];
lean_object* v_x_2291_ = _args[9];
lean_object* v___x_2292_ = _args[10];
lean_object* v_toBind_2293_ = _args[11];
lean_object* v_toApplicative_2294_ = _args[12];
lean_object* v___f_2295_ = _args[13];
lean_object* v_f_2296_ = _args[14];
lean_object* v_args_2297_ = _args[15];
lean_object* v___y_2298_ = _args[16];
_start:
{
uint8_t v_skipInstances_boxed_2299_; uint8_t v_usedLetOnly_boxed_2300_; uint8_t v_skipConstInApp_boxed_2301_; lean_object* v_res_2302_; 
v_skipInstances_boxed_2299_ = lean_unbox(v_skipInstances_2282_);
v_usedLetOnly_boxed_2300_ = lean_unbox(v_usedLetOnly_2288_);
v_skipConstInApp_boxed_2301_ = lean_unbox(v_skipConstInApp_2289_);
v_res_2302_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__9(v_skipInstances_boxed_2299_, v_inst_2283_, v_inst_2284_, v_inst_2285_, v_pre_2286_, v_post_2287_, v_usedLetOnly_boxed_2300_, v_skipConstInApp_boxed_2301_, v_x_2290_, v_x_2291_, v___x_2292_, v_toBind_2293_, v_toApplicative_2294_, v___f_2295_, v_f_2296_, v_args_2297_, v___y_2298_);
lean_dec(v___y_2298_);
return v_res_2302_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__0(lean_object* v_fvars_2305_, lean_object* v_inst_2306_, lean_object* v_inst_2307_, lean_object* v_inst_2308_, lean_object* v_pre_2309_, lean_object* v_post_2310_, uint8_t v_usedLetOnly_2311_, uint8_t v_skipConstInApp_2312_, uint8_t v_skipInstances_2313_, lean_object* v_x_2314_, lean_object* v_x_2315_, lean_object* v_body_2316_, lean_object* v_x_2317_, lean_object* v___y_2318_){
_start:
{
lean_object* v___x_2319_; lean_object* v___x_2320_; 
v___x_2319_ = lean_array_push(v_fvars_2305_, v_x_2317_);
v___x_2320_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(v_inst_2306_, v_inst_2307_, v_inst_2308_, v_pre_2309_, v_post_2310_, v_usedLetOnly_2311_, v_skipConstInApp_2312_, v_skipInstances_2313_, v_x_2314_, v_x_2315_, v___x_2319_, v_body_2316_, v___y_2318_);
return v___x_2320_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__0___boxed(lean_object* v_fvars_2321_, lean_object* v_inst_2322_, lean_object* v_inst_2323_, lean_object* v_inst_2324_, lean_object* v_pre_2325_, lean_object* v_post_2326_, lean_object* v_usedLetOnly_2327_, lean_object* v_skipConstInApp_2328_, lean_object* v_skipInstances_2329_, lean_object* v_x_2330_, lean_object* v_x_2331_, lean_object* v_body_2332_, lean_object* v_x_2333_, lean_object* v___y_2334_){
_start:
{
uint8_t v_usedLetOnly_boxed_2335_; uint8_t v_skipConstInApp_boxed_2336_; uint8_t v_skipInstances_boxed_2337_; lean_object* v_res_2338_; 
v_usedLetOnly_boxed_2335_ = lean_unbox(v_usedLetOnly_2327_);
v_skipConstInApp_boxed_2336_ = lean_unbox(v_skipConstInApp_2328_);
v_skipInstances_boxed_2337_ = lean_unbox(v_skipInstances_2329_);
v_res_2338_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__0(v_fvars_2321_, v_inst_2322_, v_inst_2323_, v_inst_2324_, v_pre_2325_, v_post_2326_, v_usedLetOnly_boxed_2335_, v_skipConstInApp_boxed_2336_, v_skipInstances_boxed_2337_, v_x_2330_, v_x_2331_, v_body_2332_, v_x_2333_, v___y_2334_);
lean_dec(v___y_2334_);
return v_res_2338_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3___boxed(lean_object* v_inst_2339_, lean_object* v_inst_2340_, lean_object* v_inst_2341_, lean_object* v_pre_2342_, lean_object* v_post_2343_, lean_object* v_usedLetOnly_2344_, lean_object* v_skipConstInApp_2345_, lean_object* v_skipInstances_2346_, lean_object* v_x_2347_, lean_object* v_x_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_){
_start:
{
uint8_t v_usedLetOnly_boxed_2351_; uint8_t v_skipConstInApp_boxed_2352_; uint8_t v_skipInstances_boxed_2353_; lean_object* v_res_2354_; 
v_usedLetOnly_boxed_2351_ = lean_unbox(v_usedLetOnly_2344_);
v_skipConstInApp_boxed_2352_ = lean_unbox(v_skipConstInApp_2345_);
v_skipInstances_boxed_2353_ = lean_unbox(v_skipInstances_2346_);
v_res_2354_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3(v_inst_2339_, v_inst_2340_, v_inst_2341_, v_pre_2342_, v_post_2343_, v_usedLetOnly_boxed_2351_, v_skipConstInApp_boxed_2352_, v_skipInstances_boxed_2353_, v_x_2347_, v_x_2348_, v_a_2349_, v_a_2350_);
lean_dec(v_a_2349_);
return v_res_2354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(lean_object* v_inst_2355_, lean_object* v_inst_2356_, lean_object* v_inst_2357_, lean_object* v_pre_2358_, lean_object* v_post_2359_, uint8_t v_usedLetOnly_2360_, uint8_t v_skipConstInApp_2361_, uint8_t v_skipInstances_2362_, lean_object* v_x_2363_, lean_object* v_x_2364_, lean_object* v_fvars_2365_, lean_object* v_e_2366_, lean_object* v_a_2367_){
_start:
{
lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___f_2372_; lean_object* v___f_2373_; lean_object* v___x_2374_; 
v___x_2368_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0));
v___x_2369_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1));
lean_inc_ref(v_inst_2355_);
v___x_2370_ = l_Lean_MonadCacheT_instMonad___redArg(v_x_2363_, v___x_2368_, v___x_2369_, v_inst_2355_);
v___x_2371_ = l_Lean_MonadCacheT_instMonadControl___redArg(v_x_2363_, v___x_2368_, v___x_2369_);
lean_inc_ref_n(v_inst_2357_, 2);
lean_inc_ref(v___x_2371_);
v___f_2372_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_2372_, 0, v___x_2371_);
lean_closure_set(v___f_2372_, 1, v_inst_2357_);
v___f_2373_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_2373_, 0, v___x_2371_);
lean_closure_set(v___f_2373_, 1, v_inst_2357_);
v___x_2374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2374_, 0, v___f_2372_);
lean_ctor_set(v___x_2374_, 1, v___f_2373_);
if (lean_obj_tag(v_e_2366_) == 7)
{
lean_object* v_binderName_2375_; lean_object* v_binderType_2376_; lean_object* v_body_2377_; uint8_t v_binderInfo_2378_; lean_object* v_toBind_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___f_2383_; lean_object* v___x_2384_; lean_object* v___f_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; 
v_binderName_2375_ = lean_ctor_get(v_e_2366_, 0);
lean_inc(v_binderName_2375_);
v_binderType_2376_ = lean_ctor_get(v_e_2366_, 1);
lean_inc_ref(v_binderType_2376_);
v_body_2377_ = lean_ctor_get(v_e_2366_, 2);
lean_inc_ref(v_body_2377_);
v_binderInfo_2378_ = lean_ctor_get_uint8(v_e_2366_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2366_, 3);
v_toBind_2379_ = lean_ctor_get(v_inst_2355_, 1);
lean_inc(v_toBind_2379_);
v___x_2380_ = lean_box(v_usedLetOnly_2360_);
v___x_2381_ = lean_box(v_skipConstInApp_2361_);
v___x_2382_ = lean_box(v_skipInstances_2362_);
lean_inc(v_x_2364_);
lean_inc(v_post_2359_);
lean_inc(v_pre_2358_);
lean_inc_ref(v_inst_2357_);
lean_inc(v_inst_2356_);
lean_inc_ref(v_inst_2355_);
lean_inc_ref(v_fvars_2365_);
v___f_2383_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__0___boxed), 14, 12);
lean_closure_set(v___f_2383_, 0, v_fvars_2365_);
lean_closure_set(v___f_2383_, 1, v_inst_2355_);
lean_closure_set(v___f_2383_, 2, v_inst_2356_);
lean_closure_set(v___f_2383_, 3, v_inst_2357_);
lean_closure_set(v___f_2383_, 4, v_pre_2358_);
lean_closure_set(v___f_2383_, 5, v_post_2359_);
lean_closure_set(v___f_2383_, 6, v___x_2380_);
lean_closure_set(v___f_2383_, 7, v___x_2381_);
lean_closure_set(v___f_2383_, 8, v___x_2382_);
lean_closure_set(v___f_2383_, 9, v_x_2363_);
lean_closure_set(v___f_2383_, 10, v_x_2364_);
lean_closure_set(v___f_2383_, 11, v_body_2377_);
v___x_2384_ = lean_box(v_binderInfo_2378_);
lean_inc(v_a_2367_);
v___f_2385_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_2385_, 0, v___x_2374_);
lean_closure_set(v___f_2385_, 1, v___x_2370_);
lean_closure_set(v___f_2385_, 2, v_binderName_2375_);
lean_closure_set(v___f_2385_, 3, v___x_2384_);
lean_closure_set(v___f_2385_, 4, v___f_2383_);
lean_closure_set(v___f_2385_, 5, v_a_2367_);
v___x_2386_ = lean_expr_instantiate_rev(v_binderType_2376_, v_fvars_2365_);
lean_dec_ref(v_fvars_2365_);
lean_dec_ref(v_binderType_2376_);
v___x_2387_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2355_, v_inst_2356_, v_inst_2357_, v_pre_2358_, v_post_2359_, v_usedLetOnly_2360_, v_skipConstInApp_2361_, v_skipInstances_2362_, v_x_2363_, v_x_2364_, v___x_2386_, v_a_2367_);
v___x_2388_ = lean_apply_4(v_toBind_2379_, lean_box(0), lean_box(0), v___x_2387_, v___f_2385_);
return v___x_2388_;
}
else
{
lean_object* v_toBind_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___f_2393_; lean_object* v___x_2394_; lean_object* v___f_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; 
lean_dec_ref_known(v___x_2374_, 2);
lean_dec_ref(v___x_2370_);
v_toBind_2389_ = lean_ctor_get(v_inst_2355_, 1);
lean_inc_n(v_toBind_2389_, 2);
v___x_2390_ = lean_box(v_usedLetOnly_2360_);
v___x_2391_ = lean_box(v_skipConstInApp_2361_);
v___x_2392_ = lean_box(v_skipInstances_2362_);
lean_inc(v_a_2367_);
lean_inc(v_x_2364_);
lean_inc(v_post_2359_);
lean_inc(v_pre_2358_);
lean_inc_ref(v_inst_2357_);
lean_inc_n(v_inst_2356_, 2);
lean_inc_ref(v_inst_2355_);
v___f_2393_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3___boxed), 12, 11);
lean_closure_set(v___f_2393_, 0, v_inst_2355_);
lean_closure_set(v___f_2393_, 1, v_inst_2356_);
lean_closure_set(v___f_2393_, 2, v_inst_2357_);
lean_closure_set(v___f_2393_, 3, v_pre_2358_);
lean_closure_set(v___f_2393_, 4, v_post_2359_);
lean_closure_set(v___f_2393_, 5, v___x_2390_);
lean_closure_set(v___f_2393_, 6, v___x_2391_);
lean_closure_set(v___f_2393_, 7, v___x_2392_);
lean_closure_set(v___f_2393_, 8, v_x_2363_);
lean_closure_set(v___f_2393_, 9, v_x_2364_);
lean_closure_set(v___f_2393_, 10, v_a_2367_);
v___x_2394_ = lean_box(v_usedLetOnly_2360_);
lean_inc_ref(v_fvars_2365_);
v___f_2395_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___lam__3___boxed), 6, 5);
lean_closure_set(v___f_2395_, 0, v_fvars_2365_);
lean_closure_set(v___f_2395_, 1, v___x_2394_);
lean_closure_set(v___f_2395_, 2, v_inst_2356_);
lean_closure_set(v___f_2395_, 3, v_toBind_2389_);
lean_closure_set(v___f_2395_, 4, v___f_2393_);
v___x_2396_ = lean_expr_instantiate_rev(v_e_2366_, v_fvars_2365_);
lean_dec_ref(v_fvars_2365_);
lean_dec_ref(v_e_2366_);
v___x_2397_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2355_, v_inst_2356_, v_inst_2357_, v_pre_2358_, v_post_2359_, v_usedLetOnly_2360_, v_skipConstInApp_2361_, v_skipInstances_2362_, v_x_2363_, v_x_2364_, v___x_2396_, v_a_2367_);
v___x_2398_ = lean_apply_4(v_toBind_2389_, lean_box(0), lean_box(0), v___x_2397_, v___f_2395_);
return v___x_2398_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__0(lean_object* v_fvars_2399_, lean_object* v_inst_2400_, lean_object* v_inst_2401_, lean_object* v_inst_2402_, lean_object* v_pre_2403_, lean_object* v_post_2404_, uint8_t v_usedLetOnly_2405_, uint8_t v_skipConstInApp_2406_, uint8_t v_skipInstances_2407_, lean_object* v_x_2408_, lean_object* v_x_2409_, lean_object* v_body_2410_, lean_object* v_x_2411_, lean_object* v___y_2412_){
_start:
{
lean_object* v___x_2413_; lean_object* v___x_2414_; 
v___x_2413_ = lean_array_push(v_fvars_2399_, v_x_2411_);
v___x_2414_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(v_inst_2400_, v_inst_2401_, v_inst_2402_, v_pre_2403_, v_post_2404_, v_usedLetOnly_2405_, v_skipConstInApp_2406_, v_skipInstances_2407_, v_x_2408_, v_x_2409_, v___x_2413_, v_body_2410_, v___y_2412_);
return v___x_2414_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__0___boxed(lean_object* v_fvars_2415_, lean_object* v_inst_2416_, lean_object* v_inst_2417_, lean_object* v_inst_2418_, lean_object* v_pre_2419_, lean_object* v_post_2420_, lean_object* v_usedLetOnly_2421_, lean_object* v_skipConstInApp_2422_, lean_object* v_skipInstances_2423_, lean_object* v_x_2424_, lean_object* v_x_2425_, lean_object* v_body_2426_, lean_object* v_x_2427_, lean_object* v___y_2428_){
_start:
{
uint8_t v_usedLetOnly_boxed_2429_; uint8_t v_skipConstInApp_boxed_2430_; uint8_t v_skipInstances_boxed_2431_; lean_object* v_res_2432_; 
v_usedLetOnly_boxed_2429_ = lean_unbox(v_usedLetOnly_2421_);
v_skipConstInApp_boxed_2430_ = lean_unbox(v_skipConstInApp_2422_);
v_skipInstances_boxed_2431_ = lean_unbox(v_skipInstances_2423_);
v_res_2432_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__0(v_fvars_2415_, v_inst_2416_, v_inst_2417_, v_inst_2418_, v_pre_2419_, v_post_2420_, v_usedLetOnly_boxed_2429_, v_skipConstInApp_boxed_2430_, v_skipInstances_boxed_2431_, v_x_2424_, v_x_2425_, v_body_2426_, v_x_2427_, v___y_2428_);
lean_dec(v___y_2428_);
return v_res_2432_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(lean_object* v_inst_2433_, lean_object* v_inst_2434_, lean_object* v_inst_2435_, lean_object* v_pre_2436_, lean_object* v_post_2437_, uint8_t v_usedLetOnly_2438_, uint8_t v_skipConstInApp_2439_, uint8_t v_skipInstances_2440_, lean_object* v_x_2441_, lean_object* v_x_2442_, lean_object* v_fvars_2443_, lean_object* v_e_2444_, lean_object* v_a_2445_){
_start:
{
lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___f_2450_; lean_object* v___f_2451_; lean_object* v___x_2452_; 
v___x_2446_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0));
v___x_2447_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1));
lean_inc_ref(v_inst_2433_);
v___x_2448_ = l_Lean_MonadCacheT_instMonad___redArg(v_x_2441_, v___x_2446_, v___x_2447_, v_inst_2433_);
v___x_2449_ = l_Lean_MonadCacheT_instMonadControl___redArg(v_x_2441_, v___x_2446_, v___x_2447_);
lean_inc_ref_n(v_inst_2435_, 2);
lean_inc_ref(v___x_2449_);
v___f_2450_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_2450_, 0, v___x_2449_);
lean_closure_set(v___f_2450_, 1, v_inst_2435_);
v___f_2451_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_2451_, 0, v___x_2449_);
lean_closure_set(v___f_2451_, 1, v_inst_2435_);
v___x_2452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2452_, 0, v___f_2450_);
lean_ctor_set(v___x_2452_, 1, v___f_2451_);
if (lean_obj_tag(v_e_2444_) == 6)
{
lean_object* v_binderName_2453_; lean_object* v_binderType_2454_; lean_object* v_body_2455_; uint8_t v_binderInfo_2456_; lean_object* v_toBind_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___f_2461_; lean_object* v___x_2462_; lean_object* v___f_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; 
v_binderName_2453_ = lean_ctor_get(v_e_2444_, 0);
lean_inc(v_binderName_2453_);
v_binderType_2454_ = lean_ctor_get(v_e_2444_, 1);
lean_inc_ref(v_binderType_2454_);
v_body_2455_ = lean_ctor_get(v_e_2444_, 2);
lean_inc_ref(v_body_2455_);
v_binderInfo_2456_ = lean_ctor_get_uint8(v_e_2444_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2444_, 3);
v_toBind_2457_ = lean_ctor_get(v_inst_2433_, 1);
lean_inc(v_toBind_2457_);
v___x_2458_ = lean_box(v_usedLetOnly_2438_);
v___x_2459_ = lean_box(v_skipConstInApp_2439_);
v___x_2460_ = lean_box(v_skipInstances_2440_);
lean_inc(v_x_2442_);
lean_inc(v_post_2437_);
lean_inc(v_pre_2436_);
lean_inc_ref(v_inst_2435_);
lean_inc(v_inst_2434_);
lean_inc_ref(v_inst_2433_);
lean_inc_ref(v_fvars_2443_);
v___f_2461_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__0___boxed), 14, 12);
lean_closure_set(v___f_2461_, 0, v_fvars_2443_);
lean_closure_set(v___f_2461_, 1, v_inst_2433_);
lean_closure_set(v___f_2461_, 2, v_inst_2434_);
lean_closure_set(v___f_2461_, 3, v_inst_2435_);
lean_closure_set(v___f_2461_, 4, v_pre_2436_);
lean_closure_set(v___f_2461_, 5, v_post_2437_);
lean_closure_set(v___f_2461_, 6, v___x_2458_);
lean_closure_set(v___f_2461_, 7, v___x_2459_);
lean_closure_set(v___f_2461_, 8, v___x_2460_);
lean_closure_set(v___f_2461_, 9, v_x_2441_);
lean_closure_set(v___f_2461_, 10, v_x_2442_);
lean_closure_set(v___f_2461_, 11, v_body_2455_);
v___x_2462_ = lean_box(v_binderInfo_2456_);
lean_inc(v_a_2445_);
v___f_2463_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_2463_, 0, v___x_2452_);
lean_closure_set(v___f_2463_, 1, v___x_2448_);
lean_closure_set(v___f_2463_, 2, v_binderName_2453_);
lean_closure_set(v___f_2463_, 3, v___x_2462_);
lean_closure_set(v___f_2463_, 4, v___f_2461_);
lean_closure_set(v___f_2463_, 5, v_a_2445_);
v___x_2464_ = lean_expr_instantiate_rev(v_binderType_2454_, v_fvars_2443_);
lean_dec_ref(v_fvars_2443_);
lean_dec_ref(v_binderType_2454_);
v___x_2465_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2433_, v_inst_2434_, v_inst_2435_, v_pre_2436_, v_post_2437_, v_usedLetOnly_2438_, v_skipConstInApp_2439_, v_skipInstances_2440_, v_x_2441_, v_x_2442_, v___x_2464_, v_a_2445_);
v___x_2466_ = lean_apply_4(v_toBind_2457_, lean_box(0), lean_box(0), v___x_2465_, v___f_2463_);
return v___x_2466_;
}
else
{
lean_object* v_toBind_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___f_2471_; lean_object* v___x_2472_; lean_object* v___f_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; 
lean_dec_ref_known(v___x_2452_, 2);
lean_dec_ref(v___x_2448_);
v_toBind_2467_ = lean_ctor_get(v_inst_2433_, 1);
lean_inc_n(v_toBind_2467_, 2);
v___x_2468_ = lean_box(v_usedLetOnly_2438_);
v___x_2469_ = lean_box(v_skipConstInApp_2439_);
v___x_2470_ = lean_box(v_skipInstances_2440_);
lean_inc(v_a_2445_);
lean_inc(v_x_2442_);
lean_inc(v_post_2437_);
lean_inc(v_pre_2436_);
lean_inc_ref(v_inst_2435_);
lean_inc_n(v_inst_2434_, 2);
lean_inc_ref(v_inst_2433_);
v___f_2471_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3___boxed), 12, 11);
lean_closure_set(v___f_2471_, 0, v_inst_2433_);
lean_closure_set(v___f_2471_, 1, v_inst_2434_);
lean_closure_set(v___f_2471_, 2, v_inst_2435_);
lean_closure_set(v___f_2471_, 3, v_pre_2436_);
lean_closure_set(v___f_2471_, 4, v_post_2437_);
lean_closure_set(v___f_2471_, 5, v___x_2468_);
lean_closure_set(v___f_2471_, 6, v___x_2469_);
lean_closure_set(v___f_2471_, 7, v___x_2470_);
lean_closure_set(v___f_2471_, 8, v_x_2441_);
lean_closure_set(v___f_2471_, 9, v_x_2442_);
lean_closure_set(v___f_2471_, 10, v_a_2445_);
v___x_2472_ = lean_box(v_usedLetOnly_2438_);
lean_inc_ref(v_fvars_2443_);
v___f_2473_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___lam__3___boxed), 6, 5);
lean_closure_set(v___f_2473_, 0, v_fvars_2443_);
lean_closure_set(v___f_2473_, 1, v___x_2472_);
lean_closure_set(v___f_2473_, 2, v_inst_2434_);
lean_closure_set(v___f_2473_, 3, v_toBind_2467_);
lean_closure_set(v___f_2473_, 4, v___f_2471_);
v___x_2474_ = lean_expr_instantiate_rev(v_e_2444_, v_fvars_2443_);
lean_dec_ref(v_fvars_2443_);
lean_dec_ref(v_e_2444_);
v___x_2475_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2433_, v_inst_2434_, v_inst_2435_, v_pre_2436_, v_post_2437_, v_usedLetOnly_2438_, v_skipConstInApp_2439_, v_skipInstances_2440_, v_x_2441_, v_x_2442_, v___x_2474_, v_a_2445_);
v___x_2476_ = lean_apply_4(v_toBind_2467_, lean_box(0), lean_box(0), v___x_2475_, v___f_2473_);
return v___x_2476_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__0(lean_object* v_fvars_2477_, lean_object* v_inst_2478_, lean_object* v_inst_2479_, lean_object* v_inst_2480_, lean_object* v_pre_2481_, lean_object* v_post_2482_, uint8_t v_usedLetOnly_2483_, uint8_t v_skipConstInApp_2484_, uint8_t v_skipInstances_2485_, lean_object* v_x_2486_, lean_object* v_x_2487_, lean_object* v_body_2488_, lean_object* v_x_2489_, lean_object* v___y_2490_){
_start:
{
lean_object* v___x_2491_; lean_object* v___x_2492_; 
v___x_2491_ = lean_array_push(v_fvars_2477_, v_x_2489_);
v___x_2492_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(v_inst_2478_, v_inst_2479_, v_inst_2480_, v_pre_2481_, v_post_2482_, v_usedLetOnly_2483_, v_skipConstInApp_2484_, v_skipInstances_2485_, v_x_2486_, v_x_2487_, v___x_2491_, v_body_2488_, v___y_2490_);
return v___x_2492_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__0___boxed(lean_object* v_fvars_2493_, lean_object* v_inst_2494_, lean_object* v_inst_2495_, lean_object* v_inst_2496_, lean_object* v_pre_2497_, lean_object* v_post_2498_, lean_object* v_usedLetOnly_2499_, lean_object* v_skipConstInApp_2500_, lean_object* v_skipInstances_2501_, lean_object* v_x_2502_, lean_object* v_x_2503_, lean_object* v_body_2504_, lean_object* v_x_2505_, lean_object* v___y_2506_){
_start:
{
uint8_t v_usedLetOnly_boxed_2507_; uint8_t v_skipConstInApp_boxed_2508_; uint8_t v_skipInstances_boxed_2509_; lean_object* v_res_2510_; 
v_usedLetOnly_boxed_2507_ = lean_unbox(v_usedLetOnly_2499_);
v_skipConstInApp_boxed_2508_ = lean_unbox(v_skipConstInApp_2500_);
v_skipInstances_boxed_2509_ = lean_unbox(v_skipInstances_2501_);
v_res_2510_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__0(v_fvars_2493_, v_inst_2494_, v_inst_2495_, v_inst_2496_, v_pre_2497_, v_post_2498_, v_usedLetOnly_boxed_2507_, v_skipConstInApp_boxed_2508_, v_skipInstances_boxed_2509_, v_x_2502_, v_x_2503_, v_body_2504_, v_x_2505_, v___y_2506_);
lean_dec(v___y_2506_);
return v_res_2510_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__2(lean_object* v___x_2511_, lean_object* v___x_2512_, lean_object* v_declName_2513_, lean_object* v___f_2514_, uint8_t v_nondep_2515_, lean_object* v_a_2516_, lean_object* v_value_2517_, lean_object* v_fvars_2518_, lean_object* v_inst_2519_, lean_object* v_inst_2520_, lean_object* v_inst_2521_, lean_object* v_pre_2522_, lean_object* v_post_2523_, uint8_t v_usedLetOnly_2524_, uint8_t v_skipConstInApp_2525_, uint8_t v_skipInstances_2526_, lean_object* v_x_2527_, lean_object* v_x_2528_, lean_object* v_toBind_2529_, lean_object* v_a_2530_){
_start:
{
lean_object* v___x_2531_; lean_object* v___f_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; 
v___x_2531_ = lean_box(v_nondep_2515_);
lean_inc(v_a_2516_);
v___f_2532_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_2532_, 0, v___x_2511_);
lean_closure_set(v___f_2532_, 1, v___x_2512_);
lean_closure_set(v___f_2532_, 2, v_declName_2513_);
lean_closure_set(v___f_2532_, 3, v_a_2530_);
lean_closure_set(v___f_2532_, 4, v___f_2514_);
lean_closure_set(v___f_2532_, 5, v___x_2531_);
lean_closure_set(v___f_2532_, 6, v_a_2516_);
v___x_2533_ = lean_expr_instantiate_rev(v_value_2517_, v_fvars_2518_);
v___x_2534_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2519_, v_inst_2520_, v_inst_2521_, v_pre_2522_, v_post_2523_, v_usedLetOnly_2524_, v_skipConstInApp_2525_, v_skipInstances_2526_, v_x_2527_, v_x_2528_, v___x_2533_, v_a_2516_);
v___x_2535_ = lean_apply_4(v_toBind_2529_, lean_box(0), lean_box(0), v___x_2534_, v___f_2532_);
return v___x_2535_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__2___boxed(lean_object** _args){
lean_object* v___x_2536_ = _args[0];
lean_object* v___x_2537_ = _args[1];
lean_object* v_declName_2538_ = _args[2];
lean_object* v___f_2539_ = _args[3];
lean_object* v_nondep_2540_ = _args[4];
lean_object* v_a_2541_ = _args[5];
lean_object* v_value_2542_ = _args[6];
lean_object* v_fvars_2543_ = _args[7];
lean_object* v_inst_2544_ = _args[8];
lean_object* v_inst_2545_ = _args[9];
lean_object* v_inst_2546_ = _args[10];
lean_object* v_pre_2547_ = _args[11];
lean_object* v_post_2548_ = _args[12];
lean_object* v_usedLetOnly_2549_ = _args[13];
lean_object* v_skipConstInApp_2550_ = _args[14];
lean_object* v_skipInstances_2551_ = _args[15];
lean_object* v_x_2552_ = _args[16];
lean_object* v_x_2553_ = _args[17];
lean_object* v_toBind_2554_ = _args[18];
lean_object* v_a_2555_ = _args[19];
_start:
{
uint8_t v_nondep_3730__boxed_2556_; uint8_t v_usedLetOnly_boxed_2557_; uint8_t v_skipConstInApp_boxed_2558_; uint8_t v_skipInstances_boxed_2559_; lean_object* v_res_2560_; 
v_nondep_3730__boxed_2556_ = lean_unbox(v_nondep_2540_);
v_usedLetOnly_boxed_2557_ = lean_unbox(v_usedLetOnly_2549_);
v_skipConstInApp_boxed_2558_ = lean_unbox(v_skipConstInApp_2550_);
v_skipInstances_boxed_2559_ = lean_unbox(v_skipInstances_2551_);
v_res_2560_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__2(v___x_2536_, v___x_2537_, v_declName_2538_, v___f_2539_, v_nondep_3730__boxed_2556_, v_a_2541_, v_value_2542_, v_fvars_2543_, v_inst_2544_, v_inst_2545_, v_inst_2546_, v_pre_2547_, v_post_2548_, v_usedLetOnly_boxed_2557_, v_skipConstInApp_boxed_2558_, v_skipInstances_boxed_2559_, v_x_2552_, v_x_2553_, v_toBind_2554_, v_a_2555_);
lean_dec_ref(v_fvars_2543_);
lean_dec_ref(v_value_2542_);
lean_dec(v_a_2541_);
return v_res_2560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(lean_object* v_inst_2561_, lean_object* v_inst_2562_, lean_object* v_inst_2563_, lean_object* v_pre_2564_, lean_object* v_post_2565_, uint8_t v_usedLetOnly_2566_, uint8_t v_skipConstInApp_2567_, uint8_t v_skipInstances_2568_, lean_object* v_x_2569_, lean_object* v_x_2570_, lean_object* v_fvars_2571_, lean_object* v_e_2572_, lean_object* v_a_2573_){
_start:
{
lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___f_2578_; lean_object* v___f_2579_; lean_object* v___x_2580_; 
v___x_2574_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0));
v___x_2575_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1));
lean_inc_ref(v_inst_2561_);
v___x_2576_ = l_Lean_MonadCacheT_instMonad___redArg(v_x_2569_, v___x_2574_, v___x_2575_, v_inst_2561_);
v___x_2577_ = l_Lean_MonadCacheT_instMonadControl___redArg(v_x_2569_, v___x_2574_, v___x_2575_);
lean_inc_ref_n(v_inst_2563_, 2);
lean_inc_ref(v___x_2577_);
v___f_2578_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_2578_, 0, v___x_2577_);
lean_closure_set(v___f_2578_, 1, v_inst_2563_);
v___f_2579_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_2579_, 0, v___x_2577_);
lean_closure_set(v___f_2579_, 1, v_inst_2563_);
v___x_2580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2580_, 0, v___f_2578_);
lean_ctor_set(v___x_2580_, 1, v___f_2579_);
if (lean_obj_tag(v_e_2572_) == 8)
{
lean_object* v_declName_2581_; lean_object* v_type_2582_; lean_object* v_value_2583_; lean_object* v_body_2584_; uint8_t v_nondep_2585_; lean_object* v_toBind_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___f_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___f_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; 
v_declName_2581_ = lean_ctor_get(v_e_2572_, 0);
lean_inc(v_declName_2581_);
v_type_2582_ = lean_ctor_get(v_e_2572_, 1);
lean_inc_ref(v_type_2582_);
v_value_2583_ = lean_ctor_get(v_e_2572_, 2);
lean_inc_ref(v_value_2583_);
v_body_2584_ = lean_ctor_get(v_e_2572_, 3);
lean_inc_ref(v_body_2584_);
v_nondep_2585_ = lean_ctor_get_uint8(v_e_2572_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_2572_, 4);
v_toBind_2586_ = lean_ctor_get(v_inst_2561_, 1);
lean_inc_n(v_toBind_2586_, 2);
v___x_2587_ = lean_box(v_usedLetOnly_2566_);
v___x_2588_ = lean_box(v_skipConstInApp_2567_);
v___x_2589_ = lean_box(v_skipInstances_2568_);
lean_inc_n(v_x_2570_, 2);
lean_inc_n(v_post_2565_, 2);
lean_inc_n(v_pre_2564_, 2);
lean_inc_ref_n(v_inst_2563_, 2);
lean_inc_n(v_inst_2562_, 2);
lean_inc_ref_n(v_inst_2561_, 2);
lean_inc_ref_n(v_fvars_2571_, 2);
v___f_2590_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__0___boxed), 14, 12);
lean_closure_set(v___f_2590_, 0, v_fvars_2571_);
lean_closure_set(v___f_2590_, 1, v_inst_2561_);
lean_closure_set(v___f_2590_, 2, v_inst_2562_);
lean_closure_set(v___f_2590_, 3, v_inst_2563_);
lean_closure_set(v___f_2590_, 4, v_pre_2564_);
lean_closure_set(v___f_2590_, 5, v_post_2565_);
lean_closure_set(v___f_2590_, 6, v___x_2587_);
lean_closure_set(v___f_2590_, 7, v___x_2588_);
lean_closure_set(v___f_2590_, 8, v___x_2589_);
lean_closure_set(v___f_2590_, 9, v_x_2569_);
lean_closure_set(v___f_2590_, 10, v_x_2570_);
lean_closure_set(v___f_2590_, 11, v_body_2584_);
v___x_2591_ = lean_box(v_nondep_2585_);
v___x_2592_ = lean_box(v_usedLetOnly_2566_);
v___x_2593_ = lean_box(v_skipConstInApp_2567_);
v___x_2594_ = lean_box(v_skipInstances_2568_);
lean_inc(v_a_2573_);
v___f_2595_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__2___boxed), 20, 19);
lean_closure_set(v___f_2595_, 0, v___x_2580_);
lean_closure_set(v___f_2595_, 1, v___x_2576_);
lean_closure_set(v___f_2595_, 2, v_declName_2581_);
lean_closure_set(v___f_2595_, 3, v___f_2590_);
lean_closure_set(v___f_2595_, 4, v___x_2591_);
lean_closure_set(v___f_2595_, 5, v_a_2573_);
lean_closure_set(v___f_2595_, 6, v_value_2583_);
lean_closure_set(v___f_2595_, 7, v_fvars_2571_);
lean_closure_set(v___f_2595_, 8, v_inst_2561_);
lean_closure_set(v___f_2595_, 9, v_inst_2562_);
lean_closure_set(v___f_2595_, 10, v_inst_2563_);
lean_closure_set(v___f_2595_, 11, v_pre_2564_);
lean_closure_set(v___f_2595_, 12, v_post_2565_);
lean_closure_set(v___f_2595_, 13, v___x_2592_);
lean_closure_set(v___f_2595_, 14, v___x_2593_);
lean_closure_set(v___f_2595_, 15, v___x_2594_);
lean_closure_set(v___f_2595_, 16, v_x_2569_);
lean_closure_set(v___f_2595_, 17, v_x_2570_);
lean_closure_set(v___f_2595_, 18, v_toBind_2586_);
v___x_2596_ = lean_expr_instantiate_rev(v_type_2582_, v_fvars_2571_);
lean_dec_ref(v_fvars_2571_);
lean_dec_ref(v_type_2582_);
v___x_2597_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2561_, v_inst_2562_, v_inst_2563_, v_pre_2564_, v_post_2565_, v_usedLetOnly_2566_, v_skipConstInApp_2567_, v_skipInstances_2568_, v_x_2569_, v_x_2570_, v___x_2596_, v_a_2573_);
v___x_2598_ = lean_apply_4(v_toBind_2586_, lean_box(0), lean_box(0), v___x_2597_, v___f_2595_);
return v___x_2598_;
}
else
{
lean_object* v_toBind_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___f_2603_; lean_object* v___x_2604_; lean_object* v___f_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; 
lean_dec_ref_known(v___x_2580_, 2);
lean_dec_ref(v___x_2576_);
v_toBind_2599_ = lean_ctor_get(v_inst_2561_, 1);
lean_inc_n(v_toBind_2599_, 2);
v___x_2600_ = lean_box(v_usedLetOnly_2566_);
v___x_2601_ = lean_box(v_skipConstInApp_2567_);
v___x_2602_ = lean_box(v_skipInstances_2568_);
lean_inc(v_a_2573_);
lean_inc(v_x_2570_);
lean_inc(v_post_2565_);
lean_inc(v_pre_2564_);
lean_inc_ref(v_inst_2563_);
lean_inc_n(v_inst_2562_, 2);
lean_inc_ref(v_inst_2561_);
v___f_2603_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3___boxed), 12, 11);
lean_closure_set(v___f_2603_, 0, v_inst_2561_);
lean_closure_set(v___f_2603_, 1, v_inst_2562_);
lean_closure_set(v___f_2603_, 2, v_inst_2563_);
lean_closure_set(v___f_2603_, 3, v_pre_2564_);
lean_closure_set(v___f_2603_, 4, v_post_2565_);
lean_closure_set(v___f_2603_, 5, v___x_2600_);
lean_closure_set(v___f_2603_, 6, v___x_2601_);
lean_closure_set(v___f_2603_, 7, v___x_2602_);
lean_closure_set(v___f_2603_, 8, v_x_2569_);
lean_closure_set(v___f_2603_, 9, v_x_2570_);
lean_closure_set(v___f_2603_, 10, v_a_2573_);
v___x_2604_ = lean_box(v_usedLetOnly_2566_);
lean_inc_ref(v_fvars_2571_);
v___f_2605_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__4___boxed), 6, 5);
lean_closure_set(v___f_2605_, 0, v_fvars_2571_);
lean_closure_set(v___f_2605_, 1, v___x_2604_);
lean_closure_set(v___f_2605_, 2, v_inst_2562_);
lean_closure_set(v___f_2605_, 3, v_toBind_2599_);
lean_closure_set(v___f_2605_, 4, v___f_2603_);
v___x_2606_ = lean_expr_instantiate_rev(v_e_2572_, v_fvars_2571_);
lean_dec_ref(v_fvars_2571_);
lean_dec_ref(v_e_2572_);
v___x_2607_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2561_, v_inst_2562_, v_inst_2563_, v_pre_2564_, v_post_2565_, v_usedLetOnly_2566_, v_skipConstInApp_2567_, v_skipInstances_2568_, v_x_2569_, v_x_2570_, v___x_2606_, v_a_2573_);
v___x_2608_ = lean_apply_4(v_toBind_2599_, lean_box(0), lean_box(0), v___x_2607_, v___f_2605_);
return v___x_2608_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__8(lean_object* v_expr_2609_, lean_object* v_data_2610_, lean_object* v_inst_2611_, lean_object* v_inst_2612_, lean_object* v_inst_2613_, lean_object* v_pre_2614_, lean_object* v_post_2615_, uint8_t v_usedLetOnly_2616_, uint8_t v_skipConstInApp_2617_, uint8_t v_skipInstances_2618_, lean_object* v_x_2619_, lean_object* v_x_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v_a_2623_){
_start:
{
size_t v___x_2624_; size_t v___x_2625_; uint8_t v___x_2626_; 
v___x_2624_ = lean_ptr_addr(v_expr_2609_);
v___x_2625_ = lean_ptr_addr(v_a_2623_);
v___x_2626_ = lean_usize_dec_eq(v___x_2624_, v___x_2625_);
if (v___x_2626_ == 0)
{
lean_object* v___x_2627_; lean_object* v___x_2628_; 
lean_dec_ref(v___y_2622_);
v___x_2627_ = l_Lean_Expr_mdata___override(v_data_2610_, v_a_2623_);
v___x_2628_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2611_, v_inst_2612_, v_inst_2613_, v_pre_2614_, v_post_2615_, v_usedLetOnly_2616_, v_skipConstInApp_2617_, v_skipInstances_2618_, v_x_2619_, v_x_2620_, v___x_2627_, v___y_2621_);
return v___x_2628_;
}
else
{
lean_object* v___x_2629_; 
lean_dec_ref(v_a_2623_);
lean_dec(v_data_2610_);
v___x_2629_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2611_, v_inst_2612_, v_inst_2613_, v_pre_2614_, v_post_2615_, v_usedLetOnly_2616_, v_skipConstInApp_2617_, v_skipInstances_2618_, v_x_2619_, v_x_2620_, v___y_2622_, v___y_2621_);
return v___x_2629_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__8___boxed(lean_object* v_expr_2630_, lean_object* v_data_2631_, lean_object* v_inst_2632_, lean_object* v_inst_2633_, lean_object* v_inst_2634_, lean_object* v_pre_2635_, lean_object* v_post_2636_, lean_object* v_usedLetOnly_2637_, lean_object* v_skipConstInApp_2638_, lean_object* v_skipInstances_2639_, lean_object* v_x_2640_, lean_object* v_x_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v_a_2644_){
_start:
{
uint8_t v_usedLetOnly_boxed_2645_; uint8_t v_skipConstInApp_boxed_2646_; uint8_t v_skipInstances_boxed_2647_; lean_object* v_res_2648_; 
v_usedLetOnly_boxed_2645_ = lean_unbox(v_usedLetOnly_2637_);
v_skipConstInApp_boxed_2646_ = lean_unbox(v_skipConstInApp_2638_);
v_skipInstances_boxed_2647_ = lean_unbox(v_skipInstances_2639_);
v_res_2648_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__8(v_expr_2630_, v_data_2631_, v_inst_2632_, v_inst_2633_, v_inst_2634_, v_pre_2635_, v_post_2636_, v_usedLetOnly_boxed_2645_, v_skipConstInApp_boxed_2646_, v_skipInstances_boxed_2647_, v_x_2640_, v_x_2641_, v___y_2642_, v___y_2643_, v_a_2644_);
lean_dec(v___y_2642_);
lean_dec_ref(v_expr_2630_);
return v_res_2648_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__10(lean_object* v_struct_2649_, lean_object* v_typeName_2650_, lean_object* v_idx_2651_, lean_object* v_inst_2652_, lean_object* v_inst_2653_, lean_object* v_inst_2654_, lean_object* v_pre_2655_, lean_object* v_post_2656_, uint8_t v_usedLetOnly_2657_, uint8_t v_skipConstInApp_2658_, uint8_t v_skipInstances_2659_, lean_object* v_x_2660_, lean_object* v_x_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v_a_2664_){
_start:
{
size_t v___x_2665_; size_t v___x_2666_; uint8_t v___x_2667_; 
v___x_2665_ = lean_ptr_addr(v_struct_2649_);
v___x_2666_ = lean_ptr_addr(v_a_2664_);
v___x_2667_ = lean_usize_dec_eq(v___x_2665_, v___x_2666_);
if (v___x_2667_ == 0)
{
lean_object* v___x_2668_; lean_object* v___x_2669_; 
lean_dec_ref(v___y_2663_);
v___x_2668_ = l_Lean_Expr_proj___override(v_typeName_2650_, v_idx_2651_, v_a_2664_);
v___x_2669_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2652_, v_inst_2653_, v_inst_2654_, v_pre_2655_, v_post_2656_, v_usedLetOnly_2657_, v_skipConstInApp_2658_, v_skipInstances_2659_, v_x_2660_, v_x_2661_, v___x_2668_, v___y_2662_);
return v___x_2669_;
}
else
{
lean_object* v___x_2670_; 
lean_dec_ref(v_a_2664_);
lean_dec(v_idx_2651_);
lean_dec(v_typeName_2650_);
v___x_2670_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2652_, v_inst_2653_, v_inst_2654_, v_pre_2655_, v_post_2656_, v_usedLetOnly_2657_, v_skipConstInApp_2658_, v_skipInstances_2659_, v_x_2660_, v_x_2661_, v___y_2663_, v___y_2662_);
return v___x_2670_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__10___boxed(lean_object* v_struct_2671_, lean_object* v_typeName_2672_, lean_object* v_idx_2673_, lean_object* v_inst_2674_, lean_object* v_inst_2675_, lean_object* v_inst_2676_, lean_object* v_pre_2677_, lean_object* v_post_2678_, lean_object* v_usedLetOnly_2679_, lean_object* v_skipConstInApp_2680_, lean_object* v_skipInstances_2681_, lean_object* v_x_2682_, lean_object* v_x_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v_a_2686_){
_start:
{
uint8_t v_usedLetOnly_boxed_2687_; uint8_t v_skipConstInApp_boxed_2688_; uint8_t v_skipInstances_boxed_2689_; lean_object* v_res_2690_; 
v_usedLetOnly_boxed_2687_ = lean_unbox(v_usedLetOnly_2679_);
v_skipConstInApp_boxed_2688_ = lean_unbox(v_skipConstInApp_2680_);
v_skipInstances_boxed_2689_ = lean_unbox(v_skipInstances_2681_);
v_res_2690_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__10(v_struct_2671_, v_typeName_2672_, v_idx_2673_, v_inst_2674_, v_inst_2675_, v_inst_2676_, v_pre_2677_, v_post_2678_, v_usedLetOnly_boxed_2687_, v_skipConstInApp_boxed_2688_, v_skipInstances_boxed_2689_, v_x_2682_, v_x_2683_, v___y_2684_, v___y_2685_, v_a_2686_);
lean_dec(v___y_2684_);
lean_dec_ref(v_struct_2671_);
return v_res_2690_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11(lean_object* v_toApplicative_2691_, lean_object* v_inst_2692_, lean_object* v_inst_2693_, lean_object* v_inst_2694_, lean_object* v_pre_2695_, lean_object* v_post_2696_, uint8_t v_usedLetOnly_2697_, uint8_t v_skipConstInApp_2698_, uint8_t v_skipInstances_2699_, lean_object* v_x_2700_, lean_object* v_x_2701_, lean_object* v___y_2702_, lean_object* v___f_2703_, lean_object* v_toBind_2704_, lean_object* v_e_2705_, lean_object* v_a_2706_){
_start:
{
lean_object* v___y_2708_; 
switch(lean_obj_tag(v_a_2706_))
{
case 0:
{
lean_object* v_e_2740_; lean_object* v_toPure_2741_; lean_object* v___x_2742_; 
lean_dec_ref(v_e_2705_);
lean_dec(v_toBind_2704_);
lean_dec(v___f_2703_);
lean_dec(v_x_2701_);
lean_dec(v_post_2696_);
lean_dec(v_pre_2695_);
lean_dec_ref(v_inst_2694_);
lean_dec(v_inst_2693_);
lean_dec_ref(v_inst_2692_);
v_e_2740_ = lean_ctor_get(v_a_2706_, 0);
lean_inc_ref(v_e_2740_);
lean_dec_ref_known(v_a_2706_, 1);
v_toPure_2741_ = lean_ctor_get(v_toApplicative_2691_, 1);
lean_inc(v_toPure_2741_);
lean_dec_ref(v_toApplicative_2691_);
v___x_2742_ = lean_apply_2(v_toPure_2741_, lean_box(0), v_e_2740_);
return v___x_2742_;
}
case 1:
{
lean_object* v_e_2743_; lean_object* v___x_2744_; 
lean_dec_ref(v_e_2705_);
lean_dec(v_toBind_2704_);
lean_dec(v___f_2703_);
lean_dec_ref(v_toApplicative_2691_);
v_e_2743_ = lean_ctor_get(v_a_2706_, 0);
lean_inc_ref(v_e_2743_);
lean_dec_ref_known(v_a_2706_, 1);
v___x_2744_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2692_, v_inst_2693_, v_inst_2694_, v_pre_2695_, v_post_2696_, v_usedLetOnly_2697_, v_skipConstInApp_2698_, v_skipInstances_2699_, v_x_2700_, v_x_2701_, v_e_2743_, v___y_2702_);
return v___x_2744_;
}
default: 
{
lean_object* v_e_x3f_2745_; 
lean_dec_ref(v_toApplicative_2691_);
v_e_x3f_2745_ = lean_ctor_get(v_a_2706_, 0);
lean_inc(v_e_x3f_2745_);
lean_dec_ref_known(v_a_2706_, 1);
if (lean_obj_tag(v_e_x3f_2745_) == 0)
{
v___y_2708_ = v_e_2705_;
goto v___jp_2707_;
}
else
{
lean_object* v_val_2746_; 
lean_dec_ref(v_e_2705_);
v_val_2746_ = lean_ctor_get(v_e_x3f_2745_, 0);
lean_inc(v_val_2746_);
lean_dec_ref_known(v_e_x3f_2745_, 1);
v___y_2708_ = v_val_2746_;
goto v___jp_2707_;
}
}
}
v___jp_2707_:
{
switch(lean_obj_tag(v___y_2708_))
{
case 7:
{
lean_object* v___x_2709_; lean_object* v___x_2710_; 
lean_dec(v_toBind_2704_);
lean_dec(v___f_2703_);
v___x_2709_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_2710_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(v_inst_2692_, v_inst_2693_, v_inst_2694_, v_pre_2695_, v_post_2696_, v_usedLetOnly_2697_, v_skipConstInApp_2698_, v_skipInstances_2699_, v_x_2700_, v_x_2701_, v___x_2709_, v___y_2708_, v___y_2702_);
return v___x_2710_;
}
case 6:
{
lean_object* v___x_2711_; lean_object* v___x_2712_; 
lean_dec(v_toBind_2704_);
lean_dec(v___f_2703_);
v___x_2711_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_2712_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(v_inst_2692_, v_inst_2693_, v_inst_2694_, v_pre_2695_, v_post_2696_, v_usedLetOnly_2697_, v_skipConstInApp_2698_, v_skipInstances_2699_, v_x_2700_, v_x_2701_, v___x_2711_, v___y_2708_, v___y_2702_);
return v___x_2712_;
}
case 8:
{
lean_object* v___x_2713_; lean_object* v___x_2714_; 
lean_dec(v_toBind_2704_);
lean_dec(v___f_2703_);
v___x_2713_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_2714_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(v_inst_2692_, v_inst_2693_, v_inst_2694_, v_pre_2695_, v_post_2696_, v_usedLetOnly_2697_, v_skipConstInApp_2698_, v_skipInstances_2699_, v_x_2700_, v_x_2701_, v___x_2713_, v___y_2708_, v___y_2702_);
return v___x_2714_;
}
case 5:
{
lean_object* v_dummy_2715_; lean_object* v_nargs_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_3276__overap_2720_; lean_object* v___x_2721_; 
lean_dec(v_toBind_2704_);
lean_dec(v_x_2701_);
lean_dec(v_post_2696_);
lean_dec(v_pre_2695_);
lean_dec_ref(v_inst_2694_);
lean_dec(v_inst_2693_);
lean_dec_ref(v_inst_2692_);
v_dummy_2715_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__18___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__18___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__18___closed__0);
v_nargs_2716_ = l_Lean_Expr_getAppNumArgs(v___y_2708_);
lean_inc(v_nargs_2716_);
v___x_2717_ = lean_mk_array(v_nargs_2716_, v_dummy_2715_);
v___x_2718_ = lean_unsigned_to_nat(1u);
v___x_2719_ = lean_nat_sub(v_nargs_2716_, v___x_2718_);
lean_dec(v_nargs_2716_);
v___x_3276__overap_2720_ = l_Lean_Expr_withAppAux___redArg(v___f_2703_, v___y_2708_, v___x_2717_, v___x_2719_);
lean_inc(v___y_2702_);
v___x_2721_ = lean_apply_1(v___x_3276__overap_2720_, v___y_2702_);
return v___x_2721_;
}
case 10:
{
lean_object* v_data_2722_; lean_object* v_expr_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___f_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; 
lean_dec(v___f_2703_);
v_data_2722_ = lean_ctor_get(v___y_2708_, 0);
lean_inc(v_data_2722_);
v_expr_2723_ = lean_ctor_get(v___y_2708_, 1);
lean_inc_ref_n(v_expr_2723_, 2);
v___x_2724_ = lean_box(v_usedLetOnly_2697_);
v___x_2725_ = lean_box(v_skipConstInApp_2698_);
v___x_2726_ = lean_box(v_skipInstances_2699_);
lean_inc(v___y_2702_);
lean_inc(v_x_2701_);
lean_inc(v_post_2696_);
lean_inc(v_pre_2695_);
lean_inc_ref(v_inst_2694_);
lean_inc(v_inst_2693_);
lean_inc_ref(v_inst_2692_);
v___f_2727_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__8___boxed), 15, 14);
lean_closure_set(v___f_2727_, 0, v_expr_2723_);
lean_closure_set(v___f_2727_, 1, v_data_2722_);
lean_closure_set(v___f_2727_, 2, v_inst_2692_);
lean_closure_set(v___f_2727_, 3, v_inst_2693_);
lean_closure_set(v___f_2727_, 4, v_inst_2694_);
lean_closure_set(v___f_2727_, 5, v_pre_2695_);
lean_closure_set(v___f_2727_, 6, v_post_2696_);
lean_closure_set(v___f_2727_, 7, v___x_2724_);
lean_closure_set(v___f_2727_, 8, v___x_2725_);
lean_closure_set(v___f_2727_, 9, v___x_2726_);
lean_closure_set(v___f_2727_, 10, v_x_2700_);
lean_closure_set(v___f_2727_, 11, v_x_2701_);
lean_closure_set(v___f_2727_, 12, v___y_2702_);
lean_closure_set(v___f_2727_, 13, v___y_2708_);
v___x_2728_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2692_, v_inst_2693_, v_inst_2694_, v_pre_2695_, v_post_2696_, v_usedLetOnly_2697_, v_skipConstInApp_2698_, v_skipInstances_2699_, v_x_2700_, v_x_2701_, v_expr_2723_, v___y_2702_);
v___x_2729_ = lean_apply_4(v_toBind_2704_, lean_box(0), lean_box(0), v___x_2728_, v___f_2727_);
return v___x_2729_;
}
case 11:
{
lean_object* v_typeName_2730_; lean_object* v_idx_2731_; lean_object* v_struct_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___f_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; 
lean_dec(v___f_2703_);
v_typeName_2730_ = lean_ctor_get(v___y_2708_, 0);
lean_inc(v_typeName_2730_);
v_idx_2731_ = lean_ctor_get(v___y_2708_, 1);
lean_inc(v_idx_2731_);
v_struct_2732_ = lean_ctor_get(v___y_2708_, 2);
lean_inc_ref_n(v_struct_2732_, 2);
v___x_2733_ = lean_box(v_usedLetOnly_2697_);
v___x_2734_ = lean_box(v_skipConstInApp_2698_);
v___x_2735_ = lean_box(v_skipInstances_2699_);
lean_inc(v___y_2702_);
lean_inc(v_x_2701_);
lean_inc(v_post_2696_);
lean_inc(v_pre_2695_);
lean_inc_ref(v_inst_2694_);
lean_inc(v_inst_2693_);
lean_inc_ref(v_inst_2692_);
v___f_2736_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__10___boxed), 16, 15);
lean_closure_set(v___f_2736_, 0, v_struct_2732_);
lean_closure_set(v___f_2736_, 1, v_typeName_2730_);
lean_closure_set(v___f_2736_, 2, v_idx_2731_);
lean_closure_set(v___f_2736_, 3, v_inst_2692_);
lean_closure_set(v___f_2736_, 4, v_inst_2693_);
lean_closure_set(v___f_2736_, 5, v_inst_2694_);
lean_closure_set(v___f_2736_, 6, v_pre_2695_);
lean_closure_set(v___f_2736_, 7, v_post_2696_);
lean_closure_set(v___f_2736_, 8, v___x_2733_);
lean_closure_set(v___f_2736_, 9, v___x_2734_);
lean_closure_set(v___f_2736_, 10, v___x_2735_);
lean_closure_set(v___f_2736_, 11, v_x_2700_);
lean_closure_set(v___f_2736_, 12, v_x_2701_);
lean_closure_set(v___f_2736_, 13, v___y_2702_);
lean_closure_set(v___f_2736_, 14, v___y_2708_);
v___x_2737_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2692_, v_inst_2693_, v_inst_2694_, v_pre_2695_, v_post_2696_, v_usedLetOnly_2697_, v_skipConstInApp_2698_, v_skipInstances_2699_, v_x_2700_, v_x_2701_, v_struct_2732_, v___y_2702_);
v___x_2738_ = lean_apply_4(v_toBind_2704_, lean_box(0), lean_box(0), v___x_2737_, v___f_2736_);
return v___x_2738_;
}
default: 
{
lean_object* v___x_2739_; 
lean_dec(v_toBind_2704_);
lean_dec(v___f_2703_);
v___x_2739_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2692_, v_inst_2693_, v_inst_2694_, v_pre_2695_, v_post_2696_, v_usedLetOnly_2697_, v_skipConstInApp_2698_, v_skipInstances_2699_, v_x_2700_, v_x_2701_, v___y_2708_, v___y_2702_);
return v___x_2739_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___boxed(lean_object* v_toApplicative_2747_, lean_object* v_inst_2748_, lean_object* v_inst_2749_, lean_object* v_inst_2750_, lean_object* v_pre_2751_, lean_object* v_post_2752_, lean_object* v_usedLetOnly_2753_, lean_object* v_skipConstInApp_2754_, lean_object* v_skipInstances_2755_, lean_object* v_x_2756_, lean_object* v_x_2757_, lean_object* v___y_2758_, lean_object* v___f_2759_, lean_object* v_toBind_2760_, lean_object* v_e_2761_, lean_object* v_a_2762_){
_start:
{
uint8_t v_usedLetOnly_boxed_2763_; uint8_t v_skipConstInApp_boxed_2764_; uint8_t v_skipInstances_boxed_2765_; lean_object* v_res_2766_; 
v_usedLetOnly_boxed_2763_ = lean_unbox(v_usedLetOnly_2753_);
v_skipConstInApp_boxed_2764_ = lean_unbox(v_skipConstInApp_2754_);
v_skipInstances_boxed_2765_ = lean_unbox(v_skipInstances_2755_);
v_res_2766_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11(v_toApplicative_2747_, v_inst_2748_, v_inst_2749_, v_inst_2750_, v_pre_2751_, v_post_2752_, v_usedLetOnly_boxed_2763_, v_skipConstInApp_boxed_2764_, v_skipInstances_boxed_2765_, v_x_2756_, v_x_2757_, v___y_2758_, v___f_2759_, v_toBind_2760_, v_e_2761_, v_a_2762_);
lean_dec(v___y_2758_);
return v_res_2766_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12(lean_object* v_toApplicative_2767_, lean_object* v_inst_2768_, lean_object* v_inst_2769_, lean_object* v_inst_2770_, lean_object* v_pre_2771_, lean_object* v_post_2772_, uint8_t v_usedLetOnly_2773_, uint8_t v_skipConstInApp_2774_, uint8_t v_skipInstances_2775_, lean_object* v_x_2776_, lean_object* v_x_2777_, lean_object* v___f_2778_, lean_object* v_toBind_2779_, lean_object* v_e_2780_, lean_object* v_____r_2781_, lean_object* v___y_2782_){
_start:
{
lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___f_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; 
v___x_2783_ = lean_box(v_usedLetOnly_2773_);
v___x_2784_ = lean_box(v_skipConstInApp_2774_);
v___x_2785_ = lean_box(v_skipInstances_2775_);
lean_inc_ref(v_e_2780_);
lean_inc(v_toBind_2779_);
lean_inc(v___y_2782_);
lean_inc(v_pre_2771_);
v___f_2786_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___boxed), 16, 15);
lean_closure_set(v___f_2786_, 0, v_toApplicative_2767_);
lean_closure_set(v___f_2786_, 1, v_inst_2768_);
lean_closure_set(v___f_2786_, 2, v_inst_2769_);
lean_closure_set(v___f_2786_, 3, v_inst_2770_);
lean_closure_set(v___f_2786_, 4, v_pre_2771_);
lean_closure_set(v___f_2786_, 5, v_post_2772_);
lean_closure_set(v___f_2786_, 6, v___x_2783_);
lean_closure_set(v___f_2786_, 7, v___x_2784_);
lean_closure_set(v___f_2786_, 8, v___x_2785_);
lean_closure_set(v___f_2786_, 9, v_x_2776_);
lean_closure_set(v___f_2786_, 10, v_x_2777_);
lean_closure_set(v___f_2786_, 11, v___y_2782_);
lean_closure_set(v___f_2786_, 12, v___f_2778_);
lean_closure_set(v___f_2786_, 13, v_toBind_2779_);
lean_closure_set(v___f_2786_, 14, v_e_2780_);
v___x_2787_ = lean_apply_1(v_pre_2771_, v_e_2780_);
v___x_2788_ = lean_apply_4(v_toBind_2779_, lean_box(0), lean_box(0), v___x_2787_, v___f_2786_);
return v___x_2788_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12___boxed(lean_object* v_toApplicative_2789_, lean_object* v_inst_2790_, lean_object* v_inst_2791_, lean_object* v_inst_2792_, lean_object* v_pre_2793_, lean_object* v_post_2794_, lean_object* v_usedLetOnly_2795_, lean_object* v_skipConstInApp_2796_, lean_object* v_skipInstances_2797_, lean_object* v_x_2798_, lean_object* v_x_2799_, lean_object* v___f_2800_, lean_object* v_toBind_2801_, lean_object* v_e_2802_, lean_object* v_____r_2803_, lean_object* v___y_2804_){
_start:
{
uint8_t v_usedLetOnly_boxed_2805_; uint8_t v_skipConstInApp_boxed_2806_; uint8_t v_skipInstances_boxed_2807_; lean_object* v_res_2808_; 
v_usedLetOnly_boxed_2805_ = lean_unbox(v_usedLetOnly_2795_);
v_skipConstInApp_boxed_2806_ = lean_unbox(v_skipConstInApp_2796_);
v_skipInstances_boxed_2807_ = lean_unbox(v_skipInstances_2797_);
v_res_2808_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12(v_toApplicative_2789_, v_inst_2790_, v_inst_2791_, v_inst_2792_, v_pre_2793_, v_post_2794_, v_usedLetOnly_boxed_2805_, v_skipConstInApp_boxed_2806_, v_skipInstances_boxed_2807_, v_x_2798_, v_x_2799_, v___f_2800_, v_toBind_2801_, v_e_2802_, v_____r_2803_, v___y_2804_);
lean_dec(v___y_2804_);
return v_res_2808_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(lean_object* v_inst_2809_, lean_object* v_inst_2810_, lean_object* v_inst_2811_, lean_object* v_pre_2812_, lean_object* v_post_2813_, uint8_t v_usedLetOnly_2814_, uint8_t v_skipConstInApp_2815_, uint8_t v_skipInstances_2816_, lean_object* v_x_2817_, lean_object* v_x_2818_, lean_object* v_e_2819_, lean_object* v_a_2820_){
_start:
{
lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___f_2825_; lean_object* v___f_2826_; lean_object* v___x_2827_; lean_object* v_toApplicative_2828_; lean_object* v_toBind_2829_; lean_object* v___f_2830_; lean_object* v___f_2831_; lean_object* v___f_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___f_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___f_2840_; lean_object* v___f_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; 
v___x_2821_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__0));
v___x_2822_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___closed__1));
lean_inc_ref_n(v_inst_2809_, 3);
v___x_2823_ = l_Lean_MonadCacheT_instMonad___redArg(v_x_2817_, v___x_2821_, v___x_2822_, v_inst_2809_);
v___x_2824_ = l_Lean_MonadCacheT_instMonadControl___redArg(v_x_2817_, v___x_2821_, v___x_2822_);
lean_inc_ref_n(v_inst_2811_, 3);
lean_inc_ref(v___x_2824_);
v___f_2825_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_2825_, 0, v___x_2824_);
lean_closure_set(v___f_2825_, 1, v_inst_2811_);
v___f_2826_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_2826_, 0, v___x_2824_);
lean_closure_set(v___f_2826_, 1, v_inst_2811_);
v___x_2827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2827_, 0, v___f_2825_);
lean_ctor_set(v___x_2827_, 1, v___f_2826_);
v_toApplicative_2828_ = lean_ctor_get(v_inst_2809_, 0);
lean_inc_ref_n(v_toApplicative_2828_, 6);
v_toBind_2829_ = lean_ctor_get(v_inst_2809_, 1);
lean_inc_n(v_toBind_2829_, 6);
v___f_2830_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2830_, 0, v_toApplicative_2828_);
lean_inc_n(v_x_2818_, 3);
lean_inc_n(v_a_2820_, 3);
lean_inc_ref_n(v_e_2819_, 2);
v___f_2831_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__3___boxed), 8, 7);
lean_closure_set(v___f_2831_, 0, v_toApplicative_2828_);
lean_closure_set(v___f_2831_, 1, v___x_2821_);
lean_closure_set(v___f_2831_, 2, v___x_2822_);
lean_closure_set(v___f_2831_, 3, v_e_2819_);
lean_closure_set(v___f_2831_, 4, v_a_2820_);
lean_closure_set(v___f_2831_, 5, v_x_2818_);
lean_closure_set(v___f_2831_, 6, v_toBind_2829_);
v___f_2832_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2832_, 0, v_toApplicative_2828_);
lean_closure_set(v___f_2832_, 1, v___x_2821_);
lean_closure_set(v___f_2832_, 2, v___x_2822_);
lean_closure_set(v___f_2832_, 3, v_e_2819_);
v___x_2833_ = lean_box(v_skipInstances_2816_);
v___x_2834_ = lean_box(v_usedLetOnly_2814_);
v___x_2835_ = lean_box(v_skipConstInApp_2815_);
lean_inc_ref(v___x_2823_);
lean_inc(v_post_2813_);
lean_inc(v_pre_2812_);
lean_inc_n(v_inst_2810_, 2);
v___f_2836_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__9___boxed), 17, 14);
lean_closure_set(v___f_2836_, 0, v___x_2833_);
lean_closure_set(v___f_2836_, 1, v_inst_2809_);
lean_closure_set(v___f_2836_, 2, v_inst_2810_);
lean_closure_set(v___f_2836_, 3, v_inst_2811_);
lean_closure_set(v___f_2836_, 4, v_pre_2812_);
lean_closure_set(v___f_2836_, 5, v_post_2813_);
lean_closure_set(v___f_2836_, 6, v___x_2834_);
lean_closure_set(v___f_2836_, 7, v___x_2835_);
lean_closure_set(v___f_2836_, 8, v_x_2817_);
lean_closure_set(v___f_2836_, 9, v_x_2818_);
lean_closure_set(v___f_2836_, 10, v___x_2823_);
lean_closure_set(v___f_2836_, 11, v_toBind_2829_);
lean_closure_set(v___f_2836_, 12, v_toApplicative_2828_);
lean_closure_set(v___f_2836_, 13, v___f_2830_);
v___x_2837_ = lean_box(v_usedLetOnly_2814_);
v___x_2838_ = lean_box(v_skipConstInApp_2815_);
v___x_2839_ = lean_box(v_skipInstances_2816_);
v___f_2840_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__12___boxed), 16, 14);
lean_closure_set(v___f_2840_, 0, v_toApplicative_2828_);
lean_closure_set(v___f_2840_, 1, v_inst_2809_);
lean_closure_set(v___f_2840_, 2, v_inst_2810_);
lean_closure_set(v___f_2840_, 3, v_inst_2811_);
lean_closure_set(v___f_2840_, 4, v_pre_2812_);
lean_closure_set(v___f_2840_, 5, v_post_2813_);
lean_closure_set(v___f_2840_, 6, v___x_2837_);
lean_closure_set(v___f_2840_, 7, v___x_2838_);
lean_closure_set(v___f_2840_, 8, v___x_2839_);
lean_closure_set(v___f_2840_, 9, v_x_2817_);
lean_closure_set(v___f_2840_, 10, v_x_2818_);
lean_closure_set(v___f_2840_, 11, v___f_2836_);
lean_closure_set(v___f_2840_, 12, v_toBind_2829_);
lean_closure_set(v___f_2840_, 13, v_e_2819_);
v___f_2841_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__14___boxed), 13, 12);
lean_closure_set(v___f_2841_, 0, v_inst_2810_);
lean_closure_set(v___f_2841_, 1, v_x_2817_);
lean_closure_set(v___f_2841_, 2, v___x_2821_);
lean_closure_set(v___f_2841_, 3, v___x_2822_);
lean_closure_set(v___f_2841_, 4, v_inst_2809_);
lean_closure_set(v___f_2841_, 5, v___f_2840_);
lean_closure_set(v___f_2841_, 6, v___x_2827_);
lean_closure_set(v___f_2841_, 7, v___x_2823_);
lean_closure_set(v___f_2841_, 8, v_a_2820_);
lean_closure_set(v___f_2841_, 9, v_toBind_2829_);
lean_closure_set(v___f_2841_, 10, v___f_2831_);
lean_closure_set(v___f_2841_, 11, v_toApplicative_2828_);
v___x_2842_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2842_, 0, lean_box(0));
lean_closure_set(v___x_2842_, 1, lean_box(0));
lean_closure_set(v___x_2842_, 2, v_a_2820_);
v___x_2843_ = lean_apply_2(v_x_2818_, lean_box(0), v___x_2842_);
v___x_2844_ = lean_apply_4(v_toBind_2829_, lean_box(0), lean_box(0), v___x_2843_, v___f_2832_);
v___x_2845_ = lean_apply_4(v_toBind_2829_, lean_box(0), lean_box(0), v___x_2844_, v___f_2841_);
return v___x_2845_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___lam__0(lean_object* v_toApplicative_2846_, lean_object* v_inst_2847_, lean_object* v_inst_2848_, lean_object* v_inst_2849_, lean_object* v_pre_2850_, lean_object* v_post_2851_, uint8_t v_usedLetOnly_2852_, uint8_t v_skipConstInApp_2853_, uint8_t v_skipInstances_2854_, lean_object* v_x_2855_, lean_object* v_x_2856_, lean_object* v_a_2857_, lean_object* v_e_2858_, lean_object* v_a_2859_){
_start:
{
lean_object* v___y_2861_; 
switch(lean_obj_tag(v_a_2859_))
{
case 0:
{
lean_object* v_e_2864_; lean_object* v_toPure_2865_; lean_object* v___x_2866_; 
lean_dec_ref(v_e_2858_);
lean_dec(v_x_2856_);
lean_dec(v_post_2851_);
lean_dec(v_pre_2850_);
lean_dec_ref(v_inst_2849_);
lean_dec(v_inst_2848_);
lean_dec_ref(v_inst_2847_);
v_e_2864_ = lean_ctor_get(v_a_2859_, 0);
lean_inc_ref(v_e_2864_);
lean_dec_ref_known(v_a_2859_, 1);
v_toPure_2865_ = lean_ctor_get(v_toApplicative_2846_, 1);
lean_inc(v_toPure_2865_);
lean_dec_ref(v_toApplicative_2846_);
v___x_2866_ = lean_apply_2(v_toPure_2865_, lean_box(0), v_e_2864_);
return v___x_2866_;
}
case 1:
{
lean_object* v_e_2867_; lean_object* v___x_2868_; 
lean_dec_ref(v_e_2858_);
lean_dec_ref(v_toApplicative_2846_);
v_e_2867_ = lean_ctor_get(v_a_2859_, 0);
lean_inc_ref(v_e_2867_);
lean_dec_ref_known(v_a_2859_, 1);
v___x_2868_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2847_, v_inst_2848_, v_inst_2849_, v_pre_2850_, v_post_2851_, v_usedLetOnly_2852_, v_skipConstInApp_2853_, v_skipInstances_2854_, v_x_2855_, v_x_2856_, v_e_2867_, v_a_2857_);
return v___x_2868_;
}
default: 
{
lean_object* v_e_x3f_2869_; 
lean_dec(v_x_2856_);
lean_dec(v_post_2851_);
lean_dec(v_pre_2850_);
lean_dec_ref(v_inst_2849_);
lean_dec(v_inst_2848_);
lean_dec_ref(v_inst_2847_);
v_e_x3f_2869_ = lean_ctor_get(v_a_2859_, 0);
lean_inc(v_e_x3f_2869_);
lean_dec_ref_known(v_a_2859_, 1);
if (lean_obj_tag(v_e_x3f_2869_) == 0)
{
v___y_2861_ = v_e_2858_;
goto v___jp_2860_;
}
else
{
lean_object* v_val_2870_; 
lean_dec_ref(v_e_2858_);
v_val_2870_ = lean_ctor_get(v_e_x3f_2869_, 0);
lean_inc(v_val_2870_);
lean_dec_ref_known(v_e_x3f_2869_, 1);
v___y_2861_ = v_val_2870_;
goto v___jp_2860_;
}
}
}
v___jp_2860_:
{
lean_object* v_toPure_2862_; lean_object* v___x_2863_; 
v_toPure_2862_ = lean_ctor_get(v_toApplicative_2846_, 1);
lean_inc(v_toPure_2862_);
lean_dec_ref(v_toApplicative_2846_);
v___x_2863_ = lean_apply_2(v_toPure_2862_, lean_box(0), v___y_2861_);
return v___x_2863_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___lam__0___boxed(lean_object* v_toApplicative_2871_, lean_object* v_inst_2872_, lean_object* v_inst_2873_, lean_object* v_inst_2874_, lean_object* v_pre_2875_, lean_object* v_post_2876_, lean_object* v_usedLetOnly_2877_, lean_object* v_skipConstInApp_2878_, lean_object* v_skipInstances_2879_, lean_object* v_x_2880_, lean_object* v_x_2881_, lean_object* v_a_2882_, lean_object* v_e_2883_, lean_object* v_a_2884_){
_start:
{
uint8_t v_usedLetOnly_boxed_2885_; uint8_t v_skipConstInApp_boxed_2886_; uint8_t v_skipInstances_boxed_2887_; lean_object* v_res_2888_; 
v_usedLetOnly_boxed_2885_ = lean_unbox(v_usedLetOnly_2877_);
v_skipConstInApp_boxed_2886_ = lean_unbox(v_skipConstInApp_2878_);
v_skipInstances_boxed_2887_ = lean_unbox(v_skipInstances_2879_);
v_res_2888_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___lam__0(v_toApplicative_2871_, v_inst_2872_, v_inst_2873_, v_inst_2874_, v_pre_2875_, v_post_2876_, v_usedLetOnly_boxed_2885_, v_skipConstInApp_boxed_2886_, v_skipInstances_boxed_2887_, v_x_2880_, v_x_2881_, v_a_2882_, v_e_2883_, v_a_2884_);
lean_dec(v_a_2882_);
return v_res_2888_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(lean_object* v_inst_2889_, lean_object* v_inst_2890_, lean_object* v_inst_2891_, lean_object* v_pre_2892_, lean_object* v_post_2893_, uint8_t v_usedLetOnly_2894_, uint8_t v_skipConstInApp_2895_, uint8_t v_skipInstances_2896_, lean_object* v_x_2897_, lean_object* v_x_2898_, lean_object* v_e_2899_, lean_object* v_a_2900_){
_start:
{
lean_object* v_toApplicative_2901_; lean_object* v_toBind_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___f_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; 
v_toApplicative_2901_ = lean_ctor_get(v_inst_2889_, 0);
lean_inc_ref(v_toApplicative_2901_);
v_toBind_2902_ = lean_ctor_get(v_inst_2889_, 1);
lean_inc(v_toBind_2902_);
v___x_2903_ = lean_box(v_usedLetOnly_2894_);
v___x_2904_ = lean_box(v_skipConstInApp_2895_);
v___x_2905_ = lean_box(v_skipInstances_2896_);
lean_inc_ref(v_e_2899_);
lean_inc(v_a_2900_);
lean_inc(v_post_2893_);
v___f_2906_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___lam__0___boxed), 14, 13);
lean_closure_set(v___f_2906_, 0, v_toApplicative_2901_);
lean_closure_set(v___f_2906_, 1, v_inst_2889_);
lean_closure_set(v___f_2906_, 2, v_inst_2890_);
lean_closure_set(v___f_2906_, 3, v_inst_2891_);
lean_closure_set(v___f_2906_, 4, v_pre_2892_);
lean_closure_set(v___f_2906_, 5, v_post_2893_);
lean_closure_set(v___f_2906_, 6, v___x_2903_);
lean_closure_set(v___f_2906_, 7, v___x_2904_);
lean_closure_set(v___f_2906_, 8, v___x_2905_);
lean_closure_set(v___f_2906_, 9, v_x_2897_);
lean_closure_set(v___f_2906_, 10, v_x_2898_);
lean_closure_set(v___f_2906_, 11, v_a_2900_);
lean_closure_set(v___f_2906_, 12, v_e_2899_);
v___x_2907_ = lean_apply_1(v_post_2893_, v_e_2899_);
v___x_2908_ = lean_apply_4(v_toBind_2902_, lean_box(0), lean_box(0), v___x_2907_, v___f_2906_);
return v___x_2908_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___lam__3(lean_object* v_inst_2909_, lean_object* v_inst_2910_, lean_object* v_inst_2911_, lean_object* v_pre_2912_, lean_object* v_post_2913_, uint8_t v_usedLetOnly_2914_, uint8_t v_skipConstInApp_2915_, uint8_t v_skipInstances_2916_, lean_object* v_x_2917_, lean_object* v_x_2918_, lean_object* v_a_2919_, lean_object* v_a_2920_){
_start:
{
lean_object* v___x_2921_; 
v___x_2921_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2909_, v_inst_2910_, v_inst_2911_, v_pre_2912_, v_post_2913_, v_usedLetOnly_2914_, v_skipConstInApp_2915_, v_skipInstances_2916_, v_x_2917_, v_x_2918_, v_a_2920_, v_a_2919_);
return v___x_2921_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg___boxed(lean_object* v_inst_2922_, lean_object* v_inst_2923_, lean_object* v_inst_2924_, lean_object* v_pre_2925_, lean_object* v_post_2926_, lean_object* v_usedLetOnly_2927_, lean_object* v_skipConstInApp_2928_, lean_object* v_skipInstances_2929_, lean_object* v_x_2930_, lean_object* v_x_2931_, lean_object* v_e_2932_, lean_object* v_a_2933_){
_start:
{
uint8_t v_usedLetOnly_boxed_2934_; uint8_t v_skipConstInApp_boxed_2935_; uint8_t v_skipInstances_boxed_2936_; lean_object* v_res_2937_; 
v_usedLetOnly_boxed_2934_ = lean_unbox(v_usedLetOnly_2927_);
v_skipConstInApp_boxed_2935_ = lean_unbox(v_skipConstInApp_2928_);
v_skipInstances_boxed_2936_ = lean_unbox(v_skipInstances_2929_);
v_res_2937_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_2922_, v_inst_2923_, v_inst_2924_, v_pre_2925_, v_post_2926_, v_usedLetOnly_boxed_2934_, v_skipConstInApp_boxed_2935_, v_skipInstances_boxed_2936_, v_x_2930_, v_x_2931_, v_e_2932_, v_a_2933_);
lean_dec(v_a_2933_);
return v_res_2937_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg___boxed(lean_object* v_inst_2938_, lean_object* v_inst_2939_, lean_object* v_inst_2940_, lean_object* v_pre_2941_, lean_object* v_post_2942_, lean_object* v_usedLetOnly_2943_, lean_object* v_skipConstInApp_2944_, lean_object* v_skipInstances_2945_, lean_object* v_x_2946_, lean_object* v_x_2947_, lean_object* v_fvars_2948_, lean_object* v_e_2949_, lean_object* v_a_2950_){
_start:
{
uint8_t v_usedLetOnly_boxed_2951_; uint8_t v_skipConstInApp_boxed_2952_; uint8_t v_skipInstances_boxed_2953_; lean_object* v_res_2954_; 
v_usedLetOnly_boxed_2951_ = lean_unbox(v_usedLetOnly_2943_);
v_skipConstInApp_boxed_2952_ = lean_unbox(v_skipConstInApp_2944_);
v_skipInstances_boxed_2953_ = lean_unbox(v_skipInstances_2945_);
v_res_2954_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(v_inst_2938_, v_inst_2939_, v_inst_2940_, v_pre_2941_, v_post_2942_, v_usedLetOnly_boxed_2951_, v_skipConstInApp_boxed_2952_, v_skipInstances_boxed_2953_, v_x_2946_, v_x_2947_, v_fvars_2948_, v_e_2949_, v_a_2950_);
lean_dec(v_a_2950_);
return v_res_2954_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg___boxed(lean_object* v_inst_2955_, lean_object* v_inst_2956_, lean_object* v_inst_2957_, lean_object* v_pre_2958_, lean_object* v_post_2959_, lean_object* v_usedLetOnly_2960_, lean_object* v_skipConstInApp_2961_, lean_object* v_skipInstances_2962_, lean_object* v_x_2963_, lean_object* v_x_2964_, lean_object* v_fvars_2965_, lean_object* v_e_2966_, lean_object* v_a_2967_){
_start:
{
uint8_t v_usedLetOnly_boxed_2968_; uint8_t v_skipConstInApp_boxed_2969_; uint8_t v_skipInstances_boxed_2970_; lean_object* v_res_2971_; 
v_usedLetOnly_boxed_2968_ = lean_unbox(v_usedLetOnly_2960_);
v_skipConstInApp_boxed_2969_ = lean_unbox(v_skipConstInApp_2961_);
v_skipInstances_boxed_2970_ = lean_unbox(v_skipInstances_2962_);
v_res_2971_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(v_inst_2955_, v_inst_2956_, v_inst_2957_, v_pre_2958_, v_post_2959_, v_usedLetOnly_boxed_2968_, v_skipConstInApp_boxed_2969_, v_skipInstances_boxed_2970_, v_x_2963_, v_x_2964_, v_fvars_2965_, v_e_2966_, v_a_2967_);
lean_dec(v_a_2967_);
return v_res_2971_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg___boxed(lean_object* v_inst_2972_, lean_object* v_inst_2973_, lean_object* v_inst_2974_, lean_object* v_pre_2975_, lean_object* v_post_2976_, lean_object* v_usedLetOnly_2977_, lean_object* v_skipConstInApp_2978_, lean_object* v_skipInstances_2979_, lean_object* v_x_2980_, lean_object* v_x_2981_, lean_object* v_fvars_2982_, lean_object* v_e_2983_, lean_object* v_a_2984_){
_start:
{
uint8_t v_usedLetOnly_boxed_2985_; uint8_t v_skipConstInApp_boxed_2986_; uint8_t v_skipInstances_boxed_2987_; lean_object* v_res_2988_; 
v_usedLetOnly_boxed_2985_ = lean_unbox(v_usedLetOnly_2977_);
v_skipConstInApp_boxed_2986_ = lean_unbox(v_skipConstInApp_2978_);
v_skipInstances_boxed_2987_ = lean_unbox(v_skipInstances_2979_);
v_res_2988_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(v_inst_2972_, v_inst_2973_, v_inst_2974_, v_pre_2975_, v_post_2976_, v_usedLetOnly_boxed_2985_, v_skipConstInApp_boxed_2986_, v_skipInstances_boxed_2987_, v_x_2980_, v_x_2981_, v_fvars_2982_, v_e_2983_, v_a_2984_);
lean_dec(v_a_2984_);
return v_res_2988_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit(lean_object* v_m_2989_, lean_object* v_inst_2990_, lean_object* v_inst_2991_, lean_object* v_inst_2992_, lean_object* v_pre_2993_, lean_object* v_post_2994_, uint8_t v_usedLetOnly_2995_, uint8_t v_skipConstInApp_2996_, uint8_t v_skipInstances_2997_, lean_object* v_x_2998_, lean_object* v_x_2999_, lean_object* v_e_3000_, lean_object* v_a_3001_){
_start:
{
lean_object* v___x_3002_; 
v___x_3002_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_2990_, v_inst_2991_, v_inst_2992_, v_pre_2993_, v_post_2994_, v_usedLetOnly_2995_, v_skipConstInApp_2996_, v_skipInstances_2997_, v_x_2998_, v_x_2999_, v_e_3000_, v_a_3001_);
return v___x_3002_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___boxed(lean_object* v_m_3003_, lean_object* v_inst_3004_, lean_object* v_inst_3005_, lean_object* v_inst_3006_, lean_object* v_pre_3007_, lean_object* v_post_3008_, lean_object* v_usedLetOnly_3009_, lean_object* v_skipConstInApp_3010_, lean_object* v_skipInstances_3011_, lean_object* v_x_3012_, lean_object* v_x_3013_, lean_object* v_e_3014_, lean_object* v_a_3015_){
_start:
{
uint8_t v_usedLetOnly_boxed_3016_; uint8_t v_skipConstInApp_boxed_3017_; uint8_t v_skipInstances_boxed_3018_; lean_object* v_res_3019_; 
v_usedLetOnly_boxed_3016_ = lean_unbox(v_usedLetOnly_3009_);
v_skipConstInApp_boxed_3017_ = lean_unbox(v_skipConstInApp_3010_);
v_skipInstances_boxed_3018_ = lean_unbox(v_skipInstances_3011_);
v_res_3019_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit(v_m_3003_, v_inst_3004_, v_inst_3005_, v_inst_3006_, v_pre_3007_, v_post_3008_, v_usedLetOnly_boxed_3016_, v_skipConstInApp_boxed_3017_, v_skipInstances_boxed_3018_, v_x_3012_, v_x_3013_, v_e_3014_, v_a_3015_);
lean_dec(v_a_3015_);
return v_res_3019_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet(lean_object* v_m_3020_, lean_object* v_inst_3021_, lean_object* v_inst_3022_, lean_object* v_inst_3023_, lean_object* v_pre_3024_, lean_object* v_post_3025_, uint8_t v_usedLetOnly_3026_, uint8_t v_skipConstInApp_3027_, uint8_t v_skipInstances_3028_, lean_object* v_x_3029_, lean_object* v_x_3030_, lean_object* v_fvars_3031_, lean_object* v_e_3032_, lean_object* v_a_3033_){
_start:
{
lean_object* v___x_3034_; 
v___x_3034_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___redArg(v_inst_3021_, v_inst_3022_, v_inst_3023_, v_pre_3024_, v_post_3025_, v_usedLetOnly_3026_, v_skipConstInApp_3027_, v_skipInstances_3028_, v_x_3029_, v_x_3030_, v_fvars_3031_, v_e_3032_, v_a_3033_);
return v___x_3034_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___boxed(lean_object* v_m_3035_, lean_object* v_inst_3036_, lean_object* v_inst_3037_, lean_object* v_inst_3038_, lean_object* v_pre_3039_, lean_object* v_post_3040_, lean_object* v_usedLetOnly_3041_, lean_object* v_skipConstInApp_3042_, lean_object* v_skipInstances_3043_, lean_object* v_x_3044_, lean_object* v_x_3045_, lean_object* v_fvars_3046_, lean_object* v_e_3047_, lean_object* v_a_3048_){
_start:
{
uint8_t v_usedLetOnly_boxed_3049_; uint8_t v_skipConstInApp_boxed_3050_; uint8_t v_skipInstances_boxed_3051_; lean_object* v_res_3052_; 
v_usedLetOnly_boxed_3049_ = lean_unbox(v_usedLetOnly_3041_);
v_skipConstInApp_boxed_3050_ = lean_unbox(v_skipConstInApp_3042_);
v_skipInstances_boxed_3051_ = lean_unbox(v_skipInstances_3043_);
v_res_3052_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet(v_m_3035_, v_inst_3036_, v_inst_3037_, v_inst_3038_, v_pre_3039_, v_post_3040_, v_usedLetOnly_boxed_3049_, v_skipConstInApp_boxed_3050_, v_skipInstances_boxed_3051_, v_x_3044_, v_x_3045_, v_fvars_3046_, v_e_3047_, v_a_3048_);
lean_dec(v_a_3048_);
return v_res_3052_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost(lean_object* v_m_3053_, lean_object* v_inst_3054_, lean_object* v_inst_3055_, lean_object* v_inst_3056_, lean_object* v_pre_3057_, lean_object* v_post_3058_, uint8_t v_usedLetOnly_3059_, uint8_t v_skipConstInApp_3060_, uint8_t v_skipInstances_3061_, lean_object* v_x_3062_, lean_object* v_x_3063_, lean_object* v_e_3064_, lean_object* v_a_3065_){
_start:
{
lean_object* v___x_3066_; 
v___x_3066_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___redArg(v_inst_3054_, v_inst_3055_, v_inst_3056_, v_pre_3057_, v_post_3058_, v_usedLetOnly_3059_, v_skipConstInApp_3060_, v_skipInstances_3061_, v_x_3062_, v_x_3063_, v_e_3064_, v_a_3065_);
return v___x_3066_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___boxed(lean_object* v_m_3067_, lean_object* v_inst_3068_, lean_object* v_inst_3069_, lean_object* v_inst_3070_, lean_object* v_pre_3071_, lean_object* v_post_3072_, lean_object* v_usedLetOnly_3073_, lean_object* v_skipConstInApp_3074_, lean_object* v_skipInstances_3075_, lean_object* v_x_3076_, lean_object* v_x_3077_, lean_object* v_e_3078_, lean_object* v_a_3079_){
_start:
{
uint8_t v_usedLetOnly_boxed_3080_; uint8_t v_skipConstInApp_boxed_3081_; uint8_t v_skipInstances_boxed_3082_; lean_object* v_res_3083_; 
v_usedLetOnly_boxed_3080_ = lean_unbox(v_usedLetOnly_3073_);
v_skipConstInApp_boxed_3081_ = lean_unbox(v_skipConstInApp_3074_);
v_skipInstances_boxed_3082_ = lean_unbox(v_skipInstances_3075_);
v_res_3083_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost(v_m_3067_, v_inst_3068_, v_inst_3069_, v_inst_3070_, v_pre_3071_, v_post_3072_, v_usedLetOnly_boxed_3080_, v_skipConstInApp_boxed_3081_, v_skipInstances_boxed_3082_, v_x_3076_, v_x_3077_, v_e_3078_, v_a_3079_);
lean_dec(v_a_3079_);
return v_res_3083_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda(lean_object* v_m_3084_, lean_object* v_inst_3085_, lean_object* v_inst_3086_, lean_object* v_inst_3087_, lean_object* v_pre_3088_, lean_object* v_post_3089_, uint8_t v_usedLetOnly_3090_, uint8_t v_skipConstInApp_3091_, uint8_t v_skipInstances_3092_, lean_object* v_x_3093_, lean_object* v_x_3094_, lean_object* v_fvars_3095_, lean_object* v_e_3096_, lean_object* v_a_3097_){
_start:
{
lean_object* v___x_3098_; 
v___x_3098_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___redArg(v_inst_3085_, v_inst_3086_, v_inst_3087_, v_pre_3088_, v_post_3089_, v_usedLetOnly_3090_, v_skipConstInApp_3091_, v_skipInstances_3092_, v_x_3093_, v_x_3094_, v_fvars_3095_, v_e_3096_, v_a_3097_);
return v___x_3098_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___boxed(lean_object* v_m_3099_, lean_object* v_inst_3100_, lean_object* v_inst_3101_, lean_object* v_inst_3102_, lean_object* v_pre_3103_, lean_object* v_post_3104_, lean_object* v_usedLetOnly_3105_, lean_object* v_skipConstInApp_3106_, lean_object* v_skipInstances_3107_, lean_object* v_x_3108_, lean_object* v_x_3109_, lean_object* v_fvars_3110_, lean_object* v_e_3111_, lean_object* v_a_3112_){
_start:
{
uint8_t v_usedLetOnly_boxed_3113_; uint8_t v_skipConstInApp_boxed_3114_; uint8_t v_skipInstances_boxed_3115_; lean_object* v_res_3116_; 
v_usedLetOnly_boxed_3113_ = lean_unbox(v_usedLetOnly_3105_);
v_skipConstInApp_boxed_3114_ = lean_unbox(v_skipConstInApp_3106_);
v_skipInstances_boxed_3115_ = lean_unbox(v_skipInstances_3107_);
v_res_3116_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda(v_m_3099_, v_inst_3100_, v_inst_3101_, v_inst_3102_, v_pre_3103_, v_post_3104_, v_usedLetOnly_boxed_3113_, v_skipConstInApp_boxed_3114_, v_skipInstances_boxed_3115_, v_x_3108_, v_x_3109_, v_fvars_3110_, v_e_3111_, v_a_3112_);
lean_dec(v_a_3112_);
return v_res_3116_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall(lean_object* v_m_3117_, lean_object* v_inst_3118_, lean_object* v_inst_3119_, lean_object* v_inst_3120_, lean_object* v_pre_3121_, lean_object* v_post_3122_, uint8_t v_usedLetOnly_3123_, uint8_t v_skipConstInApp_3124_, uint8_t v_skipInstances_3125_, lean_object* v_x_3126_, lean_object* v_x_3127_, lean_object* v_fvars_3128_, lean_object* v_e_3129_, lean_object* v_a_3130_){
_start:
{
lean_object* v___x_3131_; 
v___x_3131_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___redArg(v_inst_3118_, v_inst_3119_, v_inst_3120_, v_pre_3121_, v_post_3122_, v_usedLetOnly_3123_, v_skipConstInApp_3124_, v_skipInstances_3125_, v_x_3126_, v_x_3127_, v_fvars_3128_, v_e_3129_, v_a_3130_);
return v___x_3131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___boxed(lean_object* v_m_3132_, lean_object* v_inst_3133_, lean_object* v_inst_3134_, lean_object* v_inst_3135_, lean_object* v_pre_3136_, lean_object* v_post_3137_, lean_object* v_usedLetOnly_3138_, lean_object* v_skipConstInApp_3139_, lean_object* v_skipInstances_3140_, lean_object* v_x_3141_, lean_object* v_x_3142_, lean_object* v_fvars_3143_, lean_object* v_e_3144_, lean_object* v_a_3145_){
_start:
{
uint8_t v_usedLetOnly_boxed_3146_; uint8_t v_skipConstInApp_boxed_3147_; uint8_t v_skipInstances_boxed_3148_; lean_object* v_res_3149_; 
v_usedLetOnly_boxed_3146_ = lean_unbox(v_usedLetOnly_3138_);
v_skipConstInApp_boxed_3147_ = lean_unbox(v_skipConstInApp_3139_);
v_skipInstances_boxed_3148_ = lean_unbox(v_skipInstances_3140_);
v_res_3149_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall(v_m_3132_, v_inst_3133_, v_inst_3134_, v_inst_3135_, v_pre_3136_, v_post_3137_, v_usedLetOnly_boxed_3146_, v_skipConstInApp_boxed_3147_, v_skipInstances_boxed_3148_, v_x_3141_, v_x_3142_, v_fvars_3143_, v_e_3144_, v_a_3145_);
lean_dec(v_a_3145_);
return v_res_3149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__0(lean_object* v_x_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_){
_start:
{
lean_object* v___x_3156_; lean_object* v___x_3157_; 
v___x_3156_ = lean_apply_1(v_x_3150_, lean_box(0));
v___x_3157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3157_, 0, v___x_3156_);
return v___x_3157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__0___boxed(lean_object* v_x_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_){
_start:
{
lean_object* v_res_3164_; 
v_res_3164_ = l_Lean_Meta_transformWithCache___redArg___lam__0(v_x_3158_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_);
lean_dec(v___y_3162_);
lean_dec_ref(v___y_3161_);
lean_dec(v___y_3160_);
lean_dec_ref(v___y_3159_);
return v_res_3164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__1(lean_object* v_inst_3165_, lean_object* v_00_u03b1_3166_, lean_object* v_x_3167_){
_start:
{
lean_object* v___f_3168_; lean_object* v___x_3169_; 
v___f_3168_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_3168_, 0, v_x_3167_);
v___x_3169_ = lean_apply_2(v_inst_3165_, lean_box(0), v___f_3168_);
return v___x_3169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__4(lean_object* v_toPure_3170_, lean_object* v_x_3171_, lean_object* v_toBind_3172_, lean_object* v_inst_3173_, lean_object* v_inst_3174_, lean_object* v_inst_3175_, lean_object* v_pre_3176_, lean_object* v_post_3177_, uint8_t v_usedLetOnly_3178_, uint8_t v_skipConstInApp_3179_, uint8_t v_skipInstances_3180_, lean_object* v_x_3181_, lean_object* v_input_3182_, lean_object* v_ref_3183_){
_start:
{
lean_object* v___f_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; 
lean_inc(v_toBind_3172_);
lean_inc(v_x_3171_);
lean_inc(v_ref_3183_);
v___f_3184_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__4), 5, 4);
lean_closure_set(v___f_3184_, 0, v_toPure_3170_);
lean_closure_set(v___f_3184_, 1, v_ref_3183_);
lean_closure_set(v___f_3184_, 2, v_x_3171_);
lean_closure_set(v___f_3184_, 3, v_toBind_3172_);
v___x_3185_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_3173_, v_inst_3174_, v_inst_3175_, v_pre_3176_, v_post_3177_, v_usedLetOnly_3178_, v_skipConstInApp_3179_, v_skipInstances_3180_, v_x_3181_, v_x_3171_, v_input_3182_, v_ref_3183_);
lean_dec(v_ref_3183_);
v___x_3186_ = lean_apply_4(v_toBind_3172_, lean_box(0), lean_box(0), v___x_3185_, v___f_3184_);
return v___x_3186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___lam__4___boxed(lean_object* v_toPure_3187_, lean_object* v_x_3188_, lean_object* v_toBind_3189_, lean_object* v_inst_3190_, lean_object* v_inst_3191_, lean_object* v_inst_3192_, lean_object* v_pre_3193_, lean_object* v_post_3194_, lean_object* v_usedLetOnly_3195_, lean_object* v_skipConstInApp_3196_, lean_object* v_skipInstances_3197_, lean_object* v_x_3198_, lean_object* v_input_3199_, lean_object* v_ref_3200_){
_start:
{
uint8_t v_usedLetOnly_boxed_3201_; uint8_t v_skipConstInApp_boxed_3202_; uint8_t v_skipInstances_boxed_3203_; lean_object* v_res_3204_; 
v_usedLetOnly_boxed_3201_ = lean_unbox(v_usedLetOnly_3195_);
v_skipConstInApp_boxed_3202_ = lean_unbox(v_skipConstInApp_3196_);
v_skipInstances_boxed_3203_ = lean_unbox(v_skipInstances_3197_);
v_res_3204_ = l_Lean_Meta_transformWithCache___redArg___lam__4(v_toPure_3187_, v_x_3188_, v_toBind_3189_, v_inst_3190_, v_inst_3191_, v_inst_3192_, v_pre_3193_, v_post_3194_, v_usedLetOnly_boxed_3201_, v_skipConstInApp_boxed_3202_, v_skipInstances_boxed_3203_, v_x_3198_, v_input_3199_, v_ref_3200_);
return v_res_3204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg(lean_object* v_inst_3205_, lean_object* v_inst_3206_, lean_object* v_inst_3207_, lean_object* v_input_3208_, lean_object* v_cache_3209_, lean_object* v_pre_3210_, lean_object* v_post_3211_, uint8_t v_usedLetOnly_3212_, uint8_t v_skipConstInApp_3213_, uint8_t v_skipInstances_3214_){
_start:
{
lean_object* v_x_3215_; lean_object* v_toApplicative_3216_; lean_object* v_toBind_3217_; lean_object* v_toPure_3218_; lean_object* v_x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___f_3225_; lean_object* v___x_3226_; 
v_x_3215_ = lean_box(0);
v_toApplicative_3216_ = lean_ctor_get(v_inst_3205_, 0);
v_toBind_3217_ = lean_ctor_get(v_inst_3205_, 1);
lean_inc_n(v_toBind_3217_, 2);
v_toPure_3218_ = lean_ctor_get(v_toApplicative_3216_, 1);
lean_inc(v_toPure_3218_);
lean_inc_n(v_inst_3206_, 2);
v_x_3219_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__1), 3, 1);
lean_closure_set(v_x_3219_, 0, v_inst_3206_);
v___x_3220_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_3220_, 0, lean_box(0));
lean_closure_set(v___x_3220_, 1, lean_box(0));
lean_closure_set(v___x_3220_, 2, v_cache_3209_);
v___x_3221_ = l_Lean_Meta_transformWithCache___redArg___lam__1(v_inst_3206_, lean_box(0), v___x_3220_);
v___x_3222_ = lean_box(v_usedLetOnly_3212_);
v___x_3223_ = lean_box(v_skipConstInApp_3213_);
v___x_3224_ = lean_box(v_skipInstances_3214_);
v___f_3225_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__4___boxed), 14, 13);
lean_closure_set(v___f_3225_, 0, v_toPure_3218_);
lean_closure_set(v___f_3225_, 1, v_x_3219_);
lean_closure_set(v___f_3225_, 2, v_toBind_3217_);
lean_closure_set(v___f_3225_, 3, v_inst_3205_);
lean_closure_set(v___f_3225_, 4, v_inst_3206_);
lean_closure_set(v___f_3225_, 5, v_inst_3207_);
lean_closure_set(v___f_3225_, 6, v_pre_3210_);
lean_closure_set(v___f_3225_, 7, v_post_3211_);
lean_closure_set(v___f_3225_, 8, v___x_3222_);
lean_closure_set(v___f_3225_, 9, v___x_3223_);
lean_closure_set(v___f_3225_, 10, v___x_3224_);
lean_closure_set(v___f_3225_, 11, v_x_3215_);
lean_closure_set(v___f_3225_, 12, v_input_3208_);
v___x_3226_ = lean_apply_4(v_toBind_3217_, lean_box(0), lean_box(0), v___x_3221_, v___f_3225_);
return v___x_3226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___redArg___boxed(lean_object* v_inst_3227_, lean_object* v_inst_3228_, lean_object* v_inst_3229_, lean_object* v_input_3230_, lean_object* v_cache_3231_, lean_object* v_pre_3232_, lean_object* v_post_3233_, lean_object* v_usedLetOnly_3234_, lean_object* v_skipConstInApp_3235_, lean_object* v_skipInstances_3236_){
_start:
{
uint8_t v_usedLetOnly_boxed_3237_; uint8_t v_skipConstInApp_boxed_3238_; uint8_t v_skipInstances_boxed_3239_; lean_object* v_res_3240_; 
v_usedLetOnly_boxed_3237_ = lean_unbox(v_usedLetOnly_3234_);
v_skipConstInApp_boxed_3238_ = lean_unbox(v_skipConstInApp_3235_);
v_skipInstances_boxed_3239_ = lean_unbox(v_skipInstances_3236_);
v_res_3240_ = l_Lean_Meta_transformWithCache___redArg(v_inst_3227_, v_inst_3228_, v_inst_3229_, v_input_3230_, v_cache_3231_, v_pre_3232_, v_post_3233_, v_usedLetOnly_boxed_3237_, v_skipConstInApp_boxed_3238_, v_skipInstances_boxed_3239_);
return v_res_3240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache(lean_object* v_m_3241_, lean_object* v_inst_3242_, lean_object* v_inst_3243_, lean_object* v_inst_3244_, lean_object* v_input_3245_, lean_object* v_cache_3246_, lean_object* v_pre_3247_, lean_object* v_post_3248_, uint8_t v_usedLetOnly_3249_, uint8_t v_skipConstInApp_3250_, uint8_t v_skipInstances_3251_){
_start:
{
lean_object* v_x_3252_; lean_object* v_toApplicative_3253_; lean_object* v_toBind_3254_; lean_object* v_toPure_3255_; lean_object* v_x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___f_3262_; lean_object* v___x_3263_; 
v_x_3252_ = lean_box(0);
v_toApplicative_3253_ = lean_ctor_get(v_inst_3242_, 0);
v_toBind_3254_ = lean_ctor_get(v_inst_3242_, 1);
lean_inc_n(v_toBind_3254_, 2);
v_toPure_3255_ = lean_ctor_get(v_toApplicative_3253_, 1);
lean_inc(v_toPure_3255_);
lean_inc_n(v_inst_3243_, 2);
v_x_3256_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__1), 3, 1);
lean_closure_set(v_x_3256_, 0, v_inst_3243_);
v___x_3257_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_3257_, 0, lean_box(0));
lean_closure_set(v___x_3257_, 1, lean_box(0));
lean_closure_set(v___x_3257_, 2, v_cache_3246_);
v___x_3258_ = l_Lean_Meta_transformWithCache___redArg___lam__1(v_inst_3243_, lean_box(0), v___x_3257_);
v___x_3259_ = lean_box(v_usedLetOnly_3249_);
v___x_3260_ = lean_box(v_skipConstInApp_3250_);
v___x_3261_ = lean_box(v_skipInstances_3251_);
v___f_3262_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__4___boxed), 14, 13);
lean_closure_set(v___f_3262_, 0, v_toPure_3255_);
lean_closure_set(v___f_3262_, 1, v_x_3256_);
lean_closure_set(v___f_3262_, 2, v_toBind_3254_);
lean_closure_set(v___f_3262_, 3, v_inst_3242_);
lean_closure_set(v___f_3262_, 4, v_inst_3243_);
lean_closure_set(v___f_3262_, 5, v_inst_3244_);
lean_closure_set(v___f_3262_, 6, v_pre_3247_);
lean_closure_set(v___f_3262_, 7, v_post_3248_);
lean_closure_set(v___f_3262_, 8, v___x_3259_);
lean_closure_set(v___f_3262_, 9, v___x_3260_);
lean_closure_set(v___f_3262_, 10, v___x_3261_);
lean_closure_set(v___f_3262_, 11, v_x_3252_);
lean_closure_set(v___f_3262_, 12, v_input_3245_);
v___x_3263_ = lean_apply_4(v_toBind_3254_, lean_box(0), lean_box(0), v___x_3258_, v___f_3262_);
return v___x_3263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transformWithCache___boxed(lean_object* v_m_3264_, lean_object* v_inst_3265_, lean_object* v_inst_3266_, lean_object* v_inst_3267_, lean_object* v_input_3268_, lean_object* v_cache_3269_, lean_object* v_pre_3270_, lean_object* v_post_3271_, lean_object* v_usedLetOnly_3272_, lean_object* v_skipConstInApp_3273_, lean_object* v_skipInstances_3274_){
_start:
{
uint8_t v_usedLetOnly_boxed_3275_; uint8_t v_skipConstInApp_boxed_3276_; uint8_t v_skipInstances_boxed_3277_; lean_object* v_res_3278_; 
v_usedLetOnly_boxed_3275_ = lean_unbox(v_usedLetOnly_3272_);
v_skipConstInApp_boxed_3276_ = lean_unbox(v_skipConstInApp_3273_);
v_skipInstances_boxed_3277_ = lean_unbox(v_skipInstances_3274_);
v_res_3278_ = l_Lean_Meta_transformWithCache(v_m_3264_, v_inst_3265_, v_inst_3266_, v_inst_3267_, v_input_3268_, v_cache_3269_, v_pre_3270_, v_post_3271_, v_usedLetOnly_boxed_3275_, v_skipConstInApp_boxed_3276_, v_skipInstances_boxed_3277_);
return v_res_3278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___redArg___lam__5(lean_object* v_toPure_3279_, lean_object* v_x_3280_, lean_object* v_toBind_3281_, lean_object* v_inst_3282_, lean_object* v_inst_3283_, lean_object* v_inst_3284_, lean_object* v_pre_3285_, lean_object* v_post_3286_, uint8_t v_usedLetOnly_3287_, uint8_t v_skipConstInApp_3288_, uint8_t v___x_3289_, lean_object* v_x_3290_, lean_object* v_input_3291_, lean_object* v_ref_3292_){
_start:
{
lean_object* v___f_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; 
lean_inc(v_toBind_3281_);
lean_inc(v_x_3280_);
lean_inc(v_ref_3292_);
v___f_3293_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__4), 5, 4);
lean_closure_set(v___f_3293_, 0, v_toPure_3279_);
lean_closure_set(v___f_3293_, 1, v_ref_3292_);
lean_closure_set(v___f_3293_, 2, v_x_3280_);
lean_closure_set(v___f_3293_, 3, v_toBind_3281_);
v___x_3294_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg(v_inst_3282_, v_inst_3283_, v_inst_3284_, v_pre_3285_, v_post_3286_, v_usedLetOnly_3287_, v_skipConstInApp_3288_, v___x_3289_, v_x_3290_, v_x_3280_, v_input_3291_, v_ref_3292_);
lean_dec(v_ref_3292_);
v___x_3295_ = lean_apply_4(v_toBind_3281_, lean_box(0), lean_box(0), v___x_3294_, v___f_3293_);
return v___x_3295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___redArg___lam__5___boxed(lean_object* v_toPure_3296_, lean_object* v_x_3297_, lean_object* v_toBind_3298_, lean_object* v_inst_3299_, lean_object* v_inst_3300_, lean_object* v_inst_3301_, lean_object* v_pre_3302_, lean_object* v_post_3303_, lean_object* v_usedLetOnly_3304_, lean_object* v_skipConstInApp_3305_, lean_object* v___x_3306_, lean_object* v_x_3307_, lean_object* v_input_3308_, lean_object* v_ref_3309_){
_start:
{
uint8_t v_usedLetOnly_boxed_3310_; uint8_t v_skipConstInApp_boxed_3311_; uint8_t v___x_115__boxed_3312_; lean_object* v_res_3313_; 
v_usedLetOnly_boxed_3310_ = lean_unbox(v_usedLetOnly_3304_);
v_skipConstInApp_boxed_3311_ = lean_unbox(v_skipConstInApp_3305_);
v___x_115__boxed_3312_ = lean_unbox(v___x_3306_);
v_res_3313_ = l_Lean_Meta_transform___redArg___lam__5(v_toPure_3296_, v_x_3297_, v_toBind_3298_, v_inst_3299_, v_inst_3300_, v_inst_3301_, v_pre_3302_, v_post_3303_, v_usedLetOnly_boxed_3310_, v_skipConstInApp_boxed_3311_, v___x_115__boxed_3312_, v_x_3307_, v_input_3308_, v_ref_3309_);
return v_res_3313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___redArg(lean_object* v_inst_3314_, lean_object* v_inst_3315_, lean_object* v_inst_3316_, lean_object* v_input_3317_, lean_object* v_pre_3318_, lean_object* v_post_3319_, uint8_t v_usedLetOnly_3320_, uint8_t v_skipConstInApp_3321_){
_start:
{
lean_object* v_toApplicative_3322_; lean_object* v_toBind_3323_; lean_object* v_x_3324_; lean_object* v_toPure_3325_; lean_object* v_x_3326_; uint8_t v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___f_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___f_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; 
v_toApplicative_3322_ = lean_ctor_get(v_inst_3314_, 0);
v_toBind_3323_ = lean_ctor_get(v_inst_3314_, 1);
lean_inc_n(v_toBind_3323_, 3);
v_x_3324_ = lean_box(0);
v_toPure_3325_ = lean_ctor_get(v_toApplicative_3322_, 1);
lean_inc_n(v_toPure_3325_, 2);
lean_inc_n(v_inst_3315_, 2);
v_x_3326_ = lean_alloc_closure((void*)(l_Lean_Meta_transformWithCache___redArg___lam__1), 3, 1);
lean_closure_set(v_x_3326_, 0, v_inst_3315_);
v___x_3327_ = 0;
v___x_3328_ = lean_obj_once(&l_Lean_Core_transform___redArg___closed__2, &l_Lean_Core_transform___redArg___closed__2_once, _init_l_Lean_Core_transform___redArg___closed__2);
v___x_3329_ = l_Lean_Meta_transformWithCache___redArg___lam__1(v_inst_3315_, lean_box(0), v___x_3328_);
v___f_3330_ = lean_alloc_closure((void*)(l_Lean_Core_transform___redArg___lam__2), 2, 1);
lean_closure_set(v___f_3330_, 0, v_toPure_3325_);
v___x_3331_ = lean_box(v_usedLetOnly_3320_);
v___x_3332_ = lean_box(v_skipConstInApp_3321_);
v___x_3333_ = lean_box(v___x_3327_);
v___f_3334_ = lean_alloc_closure((void*)(l_Lean_Meta_transform___redArg___lam__5___boxed), 14, 13);
lean_closure_set(v___f_3334_, 0, v_toPure_3325_);
lean_closure_set(v___f_3334_, 1, v_x_3326_);
lean_closure_set(v___f_3334_, 2, v_toBind_3323_);
lean_closure_set(v___f_3334_, 3, v_inst_3314_);
lean_closure_set(v___f_3334_, 4, v_inst_3315_);
lean_closure_set(v___f_3334_, 5, v_inst_3316_);
lean_closure_set(v___f_3334_, 6, v_pre_3318_);
lean_closure_set(v___f_3334_, 7, v_post_3319_);
lean_closure_set(v___f_3334_, 8, v___x_3331_);
lean_closure_set(v___f_3334_, 9, v___x_3332_);
lean_closure_set(v___f_3334_, 10, v___x_3333_);
lean_closure_set(v___f_3334_, 11, v_x_3324_);
lean_closure_set(v___f_3334_, 12, v_input_3317_);
v___x_3335_ = lean_apply_4(v_toBind_3323_, lean_box(0), lean_box(0), v___x_3329_, v___f_3334_);
v___x_3336_ = lean_apply_4(v_toBind_3323_, lean_box(0), lean_box(0), v___x_3335_, v___f_3330_);
return v___x_3336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___redArg___boxed(lean_object* v_inst_3337_, lean_object* v_inst_3338_, lean_object* v_inst_3339_, lean_object* v_input_3340_, lean_object* v_pre_3341_, lean_object* v_post_3342_, lean_object* v_usedLetOnly_3343_, lean_object* v_skipConstInApp_3344_){
_start:
{
uint8_t v_usedLetOnly_boxed_3345_; uint8_t v_skipConstInApp_boxed_3346_; lean_object* v_res_3347_; 
v_usedLetOnly_boxed_3345_ = lean_unbox(v_usedLetOnly_3343_);
v_skipConstInApp_boxed_3346_ = lean_unbox(v_skipConstInApp_3344_);
v_res_3347_ = l_Lean_Meta_transform___redArg(v_inst_3337_, v_inst_3338_, v_inst_3339_, v_input_3340_, v_pre_3341_, v_post_3342_, v_usedLetOnly_boxed_3345_, v_skipConstInApp_boxed_3346_);
return v_res_3347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform(lean_object* v_m_3348_, lean_object* v_inst_3349_, lean_object* v_inst_3350_, lean_object* v_inst_3351_, lean_object* v_input_3352_, lean_object* v_pre_3353_, lean_object* v_post_3354_, uint8_t v_usedLetOnly_3355_, uint8_t v_skipConstInApp_3356_){
_start:
{
lean_object* v___x_3357_; 
v___x_3357_ = l_Lean_Meta_transform___redArg(v_inst_3349_, v_inst_3350_, v_inst_3351_, v_input_3352_, v_pre_3353_, v_post_3354_, v_usedLetOnly_3355_, v_skipConstInApp_3356_);
return v___x_3357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___boxed(lean_object* v_m_3358_, lean_object* v_inst_3359_, lean_object* v_inst_3360_, lean_object* v_inst_3361_, lean_object* v_input_3362_, lean_object* v_pre_3363_, lean_object* v_post_3364_, lean_object* v_usedLetOnly_3365_, lean_object* v_skipConstInApp_3366_){
_start:
{
uint8_t v_usedLetOnly_boxed_3367_; uint8_t v_skipConstInApp_boxed_3368_; lean_object* v_res_3369_; 
v_usedLetOnly_boxed_3367_ = lean_unbox(v_usedLetOnly_3365_);
v_skipConstInApp_boxed_3368_ = lean_unbox(v_skipConstInApp_3366_);
v_res_3369_ = l_Lean_Meta_transform(v_m_3358_, v_inst_3359_, v_inst_3360_, v_inst_3361_, v_input_3362_, v_pre_3363_, v_post_3364_, v_usedLetOnly_boxed_3367_, v_skipConstInApp_boxed_3368_);
return v_res_3369_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(lean_object* v_e_3370_, lean_object* v___y_3371_){
_start:
{
uint8_t v___x_3373_; 
v___x_3373_ = l_Lean_Expr_hasMVar(v_e_3370_);
if (v___x_3373_ == 0)
{
lean_object* v___x_3374_; 
v___x_3374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3374_, 0, v_e_3370_);
return v___x_3374_;
}
else
{
lean_object* v___x_3375_; lean_object* v_mctx_3376_; lean_object* v___x_3377_; lean_object* v_fst_3378_; lean_object* v_snd_3379_; lean_object* v___x_3380_; lean_object* v_cache_3381_; lean_object* v_zetaDeltaFVarIds_3382_; lean_object* v_postponed_3383_; lean_object* v_diag_3384_; lean_object* v___x_3386_; uint8_t v_isShared_3387_; uint8_t v_isSharedCheck_3393_; 
v___x_3375_ = lean_st_ref_get(v___y_3371_);
v_mctx_3376_ = lean_ctor_get(v___x_3375_, 0);
lean_inc_ref(v_mctx_3376_);
lean_dec(v___x_3375_);
v___x_3377_ = l_Lean_instantiateMVarsCore(v_mctx_3376_, v_e_3370_);
v_fst_3378_ = lean_ctor_get(v___x_3377_, 0);
lean_inc(v_fst_3378_);
v_snd_3379_ = lean_ctor_get(v___x_3377_, 1);
lean_inc(v_snd_3379_);
lean_dec_ref(v___x_3377_);
v___x_3380_ = lean_st_ref_take(v___y_3371_);
v_cache_3381_ = lean_ctor_get(v___x_3380_, 1);
v_zetaDeltaFVarIds_3382_ = lean_ctor_get(v___x_3380_, 2);
v_postponed_3383_ = lean_ctor_get(v___x_3380_, 3);
v_diag_3384_ = lean_ctor_get(v___x_3380_, 4);
v_isSharedCheck_3393_ = !lean_is_exclusive(v___x_3380_);
if (v_isSharedCheck_3393_ == 0)
{
lean_object* v_unused_3394_; 
v_unused_3394_ = lean_ctor_get(v___x_3380_, 0);
lean_dec(v_unused_3394_);
v___x_3386_ = v___x_3380_;
v_isShared_3387_ = v_isSharedCheck_3393_;
goto v_resetjp_3385_;
}
else
{
lean_inc(v_diag_3384_);
lean_inc(v_postponed_3383_);
lean_inc(v_zetaDeltaFVarIds_3382_);
lean_inc(v_cache_3381_);
lean_dec(v___x_3380_);
v___x_3386_ = lean_box(0);
v_isShared_3387_ = v_isSharedCheck_3393_;
goto v_resetjp_3385_;
}
v_resetjp_3385_:
{
lean_object* v___x_3389_; 
if (v_isShared_3387_ == 0)
{
lean_ctor_set(v___x_3386_, 0, v_snd_3379_);
v___x_3389_ = v___x_3386_;
goto v_reusejp_3388_;
}
else
{
lean_object* v_reuseFailAlloc_3392_; 
v_reuseFailAlloc_3392_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3392_, 0, v_snd_3379_);
lean_ctor_set(v_reuseFailAlloc_3392_, 1, v_cache_3381_);
lean_ctor_set(v_reuseFailAlloc_3392_, 2, v_zetaDeltaFVarIds_3382_);
lean_ctor_set(v_reuseFailAlloc_3392_, 3, v_postponed_3383_);
lean_ctor_set(v_reuseFailAlloc_3392_, 4, v_diag_3384_);
v___x_3389_ = v_reuseFailAlloc_3392_;
goto v_reusejp_3388_;
}
v_reusejp_3388_:
{
lean_object* v___x_3390_; lean_object* v___x_3391_; 
v___x_3390_ = lean_st_ref_put(v___y_3371_, v___x_3389_);
v___x_3391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3391_, 0, v_fst_3378_);
return v___x_3391_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg___boxed(lean_object* v_e_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_){
_start:
{
lean_object* v_res_3398_; 
v_res_3398_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(v_e_3395_, v___y_3396_);
lean_dec(v___y_3396_);
return v_res_3398_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0(lean_object* v_e_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_){
_start:
{
lean_object* v___x_3405_; 
v___x_3405_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(v_e_3399_, v___y_3401_);
return v___x_3405_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___boxed(lean_object* v_e_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_){
_start:
{
lean_object* v_res_3412_; 
v_res_3412_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0(v_e_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_);
lean_dec(v___y_3410_);
lean_dec_ref(v___y_3409_);
lean_dec(v___y_3408_);
lean_dec_ref(v___y_3407_);
return v_res_3412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__0(uint8_t v_zetaHave_3413_, lean_object* v___x_3414_, uint8_t v_zetaDelta_3415_, lean_object* v_fvarId_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_){
_start:
{
lean_object* v___x_3422_; 
v___x_3422_ = l_Lean_FVarId_findDecl_x3f___redArg(v_fvarId_3416_, v___y_3417_);
if (lean_obj_tag(v___x_3422_) == 0)
{
lean_object* v_a_3423_; lean_object* v___x_3425_; uint8_t v_isShared_3426_; uint8_t v_isSharedCheck_3451_; 
v_a_3423_ = lean_ctor_get(v___x_3422_, 0);
v_isSharedCheck_3451_ = !lean_is_exclusive(v___x_3422_);
if (v_isSharedCheck_3451_ == 0)
{
v___x_3425_ = v___x_3422_;
v_isShared_3426_ = v_isSharedCheck_3451_;
goto v_resetjp_3424_;
}
else
{
lean_inc(v_a_3423_);
lean_dec(v___x_3422_);
v___x_3425_ = lean_box(0);
v_isShared_3426_ = v_isSharedCheck_3451_;
goto v_resetjp_3424_;
}
v_resetjp_3424_:
{
if (lean_obj_tag(v_a_3423_) == 1)
{
lean_object* v_val_3427_; lean_object* v___x_3429_; uint8_t v_isShared_3430_; uint8_t v_isSharedCheck_3446_; 
v_val_3427_ = lean_ctor_get(v_a_3423_, 0);
v_isSharedCheck_3446_ = !lean_is_exclusive(v_a_3423_);
if (v_isSharedCheck_3446_ == 0)
{
v___x_3429_ = v_a_3423_;
v_isShared_3430_ = v_isSharedCheck_3446_;
goto v_resetjp_3428_;
}
else
{
lean_inc(v_val_3427_);
lean_dec(v_a_3423_);
v___x_3429_ = lean_box(0);
v_isShared_3430_ = v_isSharedCheck_3446_;
goto v_resetjp_3428_;
}
v_resetjp_3428_:
{
uint8_t v___y_3432_; 
if (v_zetaDelta_3415_ == 0)
{
lean_object* v___x_3440_; uint8_t v___x_3441_; 
v___x_3440_ = l_Lean_LocalDecl_index(v_val_3427_);
v___x_3441_ = lean_nat_dec_lt(v___x_3440_, v___x_3414_);
lean_dec(v___x_3440_);
if (v___x_3441_ == 0)
{
lean_del_object(v___x_3429_);
goto v___jp_3437_;
}
else
{
lean_object* v___x_3442_; lean_object* v___x_3444_; 
lean_dec(v_val_3427_);
lean_del_object(v___x_3425_);
v___x_3442_ = lean_box(0);
if (v_isShared_3430_ == 0)
{
lean_ctor_set_tag(v___x_3429_, 0);
lean_ctor_set(v___x_3429_, 0, v___x_3442_);
v___x_3444_ = v___x_3429_;
goto v_reusejp_3443_;
}
else
{
lean_object* v_reuseFailAlloc_3445_; 
v_reuseFailAlloc_3445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3445_, 0, v___x_3442_);
v___x_3444_ = v_reuseFailAlloc_3445_;
goto v_reusejp_3443_;
}
v_reusejp_3443_:
{
return v___x_3444_;
}
}
}
else
{
lean_del_object(v___x_3429_);
goto v___jp_3437_;
}
v___jp_3431_:
{
lean_object* v___x_3433_; lean_object* v___x_3435_; 
v___x_3433_ = l_Lean_LocalDecl_value_x3f(v_val_3427_, v___y_3432_);
lean_dec(v_val_3427_);
if (v_isShared_3426_ == 0)
{
lean_ctor_set(v___x_3425_, 0, v___x_3433_);
v___x_3435_ = v___x_3425_;
goto v_reusejp_3434_;
}
else
{
lean_object* v_reuseFailAlloc_3436_; 
v_reuseFailAlloc_3436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3436_, 0, v___x_3433_);
v___x_3435_ = v_reuseFailAlloc_3436_;
goto v_reusejp_3434_;
}
v_reusejp_3434_:
{
return v___x_3435_;
}
}
v___jp_3437_:
{
if (v_zetaHave_3413_ == 0)
{
v___y_3432_ = v_zetaHave_3413_;
goto v___jp_3431_;
}
else
{
lean_object* v___x_3438_; uint8_t v___x_3439_; 
v___x_3438_ = l_Lean_LocalDecl_index(v_val_3427_);
v___x_3439_ = lean_nat_dec_le(v___x_3414_, v___x_3438_);
lean_dec(v___x_3438_);
v___y_3432_ = v___x_3439_;
goto v___jp_3431_;
}
}
}
}
else
{
lean_object* v___x_3447_; lean_object* v___x_3449_; 
lean_dec(v_a_3423_);
v___x_3447_ = lean_box(0);
if (v_isShared_3426_ == 0)
{
lean_ctor_set(v___x_3425_, 0, v___x_3447_);
v___x_3449_ = v___x_3425_;
goto v_reusejp_3448_;
}
else
{
lean_object* v_reuseFailAlloc_3450_; 
v_reuseFailAlloc_3450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3450_, 0, v___x_3447_);
v___x_3449_ = v_reuseFailAlloc_3450_;
goto v_reusejp_3448_;
}
v_reusejp_3448_:
{
return v___x_3449_;
}
}
}
}
else
{
lean_object* v_a_3452_; lean_object* v___x_3454_; uint8_t v_isShared_3455_; uint8_t v_isSharedCheck_3459_; 
v_a_3452_ = lean_ctor_get(v___x_3422_, 0);
v_isSharedCheck_3459_ = !lean_is_exclusive(v___x_3422_);
if (v_isSharedCheck_3459_ == 0)
{
v___x_3454_ = v___x_3422_;
v_isShared_3455_ = v_isSharedCheck_3459_;
goto v_resetjp_3453_;
}
else
{
lean_inc(v_a_3452_);
lean_dec(v___x_3422_);
v___x_3454_ = lean_box(0);
v_isShared_3455_ = v_isSharedCheck_3459_;
goto v_resetjp_3453_;
}
v_resetjp_3453_:
{
lean_object* v___x_3457_; 
if (v_isShared_3455_ == 0)
{
v___x_3457_ = v___x_3454_;
goto v_reusejp_3456_;
}
else
{
lean_object* v_reuseFailAlloc_3458_; 
v_reuseFailAlloc_3458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3458_, 0, v_a_3452_);
v___x_3457_ = v_reuseFailAlloc_3458_;
goto v_reusejp_3456_;
}
v_reusejp_3456_:
{
return v___x_3457_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__0___boxed(lean_object* v_zetaHave_3460_, lean_object* v___x_3461_, lean_object* v_zetaDelta_3462_, lean_object* v_fvarId_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_){
_start:
{
uint8_t v_zetaHave_boxed_3469_; uint8_t v_zetaDelta_boxed_3470_; lean_object* v_res_3471_; 
v_zetaHave_boxed_3469_ = lean_unbox(v_zetaHave_3460_);
v_zetaDelta_boxed_3470_ = lean_unbox(v_zetaDelta_3462_);
v_res_3471_ = l_Lean_Meta_zetaReduce___lam__0(v_zetaHave_boxed_3469_, v___x_3461_, v_zetaDelta_boxed_3470_, v_fvarId_3463_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_);
lean_dec(v___y_3467_);
lean_dec_ref(v___y_3466_);
lean_dec(v___y_3465_);
lean_dec_ref(v___y_3464_);
lean_dec(v___x_3461_);
return v_res_3471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__1(lean_object* v_e_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_){
_start:
{
lean_object* v___x_3478_; lean_object* v___x_3479_; 
v___x_3478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3478_, 0, v_e_3472_);
v___x_3479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3479_, 0, v___x_3478_);
return v___x_3479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__1___boxed(lean_object* v_e_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_){
_start:
{
lean_object* v_res_3486_; 
v_res_3486_ = l_Lean_Meta_zetaReduce___lam__1(v_e_3480_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_);
lean_dec(v___y_3484_);
lean_dec_ref(v___y_3483_);
lean_dec(v___y_3482_);
lean_dec_ref(v___y_3481_);
return v_res_3486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__2(lean_object* v___f_3487_, lean_object* v_e_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_){
_start:
{
if (lean_obj_tag(v_e_3488_) == 1)
{
lean_object* v_fvarId_3494_; lean_object* v___x_3495_; 
v_fvarId_3494_ = lean_ctor_get(v_e_3488_, 0);
lean_inc(v___y_3492_);
lean_inc_ref(v___y_3491_);
lean_inc(v___y_3490_);
lean_inc_ref(v___y_3489_);
lean_inc(v_fvarId_3494_);
v___x_3495_ = lean_apply_6(v___f_3487_, v_fvarId_3494_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_, lean_box(0));
if (lean_obj_tag(v___x_3495_) == 0)
{
lean_object* v_a_3496_; lean_object* v___x_3498_; uint8_t v_isShared_3499_; uint8_t v_isSharedCheck_3521_; 
v_a_3496_ = lean_ctor_get(v___x_3495_, 0);
v_isSharedCheck_3521_ = !lean_is_exclusive(v___x_3495_);
if (v_isSharedCheck_3521_ == 0)
{
v___x_3498_ = v___x_3495_;
v_isShared_3499_ = v_isSharedCheck_3521_;
goto v_resetjp_3497_;
}
else
{
lean_inc(v_a_3496_);
lean_dec(v___x_3495_);
v___x_3498_ = lean_box(0);
v_isShared_3499_ = v_isSharedCheck_3521_;
goto v_resetjp_3497_;
}
v_resetjp_3497_:
{
if (lean_obj_tag(v_a_3496_) == 1)
{
lean_object* v_val_3500_; lean_object* v___x_3502_; uint8_t v_isShared_3503_; uint8_t v_isSharedCheck_3516_; 
lean_del_object(v___x_3498_);
lean_dec_ref_known(v_e_3488_, 1);
v_val_3500_ = lean_ctor_get(v_a_3496_, 0);
v_isSharedCheck_3516_ = !lean_is_exclusive(v_a_3496_);
if (v_isSharedCheck_3516_ == 0)
{
v___x_3502_ = v_a_3496_;
v_isShared_3503_ = v_isSharedCheck_3516_;
goto v_resetjp_3501_;
}
else
{
lean_inc(v_val_3500_);
lean_dec(v_a_3496_);
v___x_3502_ = lean_box(0);
v_isShared_3503_ = v_isSharedCheck_3516_;
goto v_resetjp_3501_;
}
v_resetjp_3501_:
{
lean_object* v___x_3504_; lean_object* v_a_3505_; lean_object* v___x_3507_; uint8_t v_isShared_3508_; uint8_t v_isSharedCheck_3515_; 
v___x_3504_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(v_val_3500_, v___y_3490_);
v_a_3505_ = lean_ctor_get(v___x_3504_, 0);
v_isSharedCheck_3515_ = !lean_is_exclusive(v___x_3504_);
if (v_isSharedCheck_3515_ == 0)
{
v___x_3507_ = v___x_3504_;
v_isShared_3508_ = v_isSharedCheck_3515_;
goto v_resetjp_3506_;
}
else
{
lean_inc(v_a_3505_);
lean_dec(v___x_3504_);
v___x_3507_ = lean_box(0);
v_isShared_3508_ = v_isSharedCheck_3515_;
goto v_resetjp_3506_;
}
v_resetjp_3506_:
{
lean_object* v___x_3510_; 
if (v_isShared_3503_ == 0)
{
lean_ctor_set(v___x_3502_, 0, v_a_3505_);
v___x_3510_ = v___x_3502_;
goto v_reusejp_3509_;
}
else
{
lean_object* v_reuseFailAlloc_3514_; 
v_reuseFailAlloc_3514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3514_, 0, v_a_3505_);
v___x_3510_ = v_reuseFailAlloc_3514_;
goto v_reusejp_3509_;
}
v_reusejp_3509_:
{
lean_object* v___x_3512_; 
if (v_isShared_3508_ == 0)
{
lean_ctor_set(v___x_3507_, 0, v___x_3510_);
v___x_3512_ = v___x_3507_;
goto v_reusejp_3511_;
}
else
{
lean_object* v_reuseFailAlloc_3513_; 
v_reuseFailAlloc_3513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3513_, 0, v___x_3510_);
v___x_3512_ = v_reuseFailAlloc_3513_;
goto v_reusejp_3511_;
}
v_reusejp_3511_:
{
return v___x_3512_;
}
}
}
}
}
else
{
lean_object* v___x_3517_; lean_object* v___x_3519_; 
lean_dec(v_a_3496_);
v___x_3517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3517_, 0, v_e_3488_);
if (v_isShared_3499_ == 0)
{
lean_ctor_set(v___x_3498_, 0, v___x_3517_);
v___x_3519_ = v___x_3498_;
goto v_reusejp_3518_;
}
else
{
lean_object* v_reuseFailAlloc_3520_; 
v_reuseFailAlloc_3520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3520_, 0, v___x_3517_);
v___x_3519_ = v_reuseFailAlloc_3520_;
goto v_reusejp_3518_;
}
v_reusejp_3518_:
{
return v___x_3519_;
}
}
}
}
else
{
lean_object* v_a_3522_; lean_object* v___x_3524_; uint8_t v_isShared_3525_; uint8_t v_isSharedCheck_3529_; 
lean_dec_ref_known(v_e_3488_, 1);
v_a_3522_ = lean_ctor_get(v___x_3495_, 0);
v_isSharedCheck_3529_ = !lean_is_exclusive(v___x_3495_);
if (v_isSharedCheck_3529_ == 0)
{
v___x_3524_ = v___x_3495_;
v_isShared_3525_ = v_isSharedCheck_3529_;
goto v_resetjp_3523_;
}
else
{
lean_inc(v_a_3522_);
lean_dec(v___x_3495_);
v___x_3524_ = lean_box(0);
v_isShared_3525_ = v_isSharedCheck_3529_;
goto v_resetjp_3523_;
}
v_resetjp_3523_:
{
lean_object* v___x_3527_; 
if (v_isShared_3525_ == 0)
{
v___x_3527_ = v___x_3524_;
goto v_reusejp_3526_;
}
else
{
lean_object* v_reuseFailAlloc_3528_; 
v_reuseFailAlloc_3528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3528_, 0, v_a_3522_);
v___x_3527_ = v_reuseFailAlloc_3528_;
goto v_reusejp_3526_;
}
v_reusejp_3526_:
{
return v___x_3527_;
}
}
}
}
else
{
lean_object* v___x_3530_; lean_object* v___x_3531_; 
lean_dec_ref(v_e_3488_);
lean_dec_ref(v___f_3487_);
v___x_3530_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_3531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3531_, 0, v___x_3530_);
return v___x_3531_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__2___boxed(lean_object* v___f_3532_, lean_object* v_e_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_){
_start:
{
lean_object* v_res_3539_; 
v_res_3539_ = l_Lean_Meta_zetaReduce___lam__2(v___f_3532_, v_e_3533_, v___y_3534_, v___y_3535_, v___y_3536_, v___y_3537_);
lean_dec(v___y_3537_);
lean_dec_ref(v___y_3536_);
lean_dec(v___y_3535_);
lean_dec_ref(v___y_3534_);
return v_res_3539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__4(lean_object* v___f_3540_, lean_object* v_e_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_){
_start:
{
lean_object* v___x_3547_; 
v___x_3547_ = l_Lean_Expr_getAppFn(v_e_3541_);
if (lean_obj_tag(v___x_3547_) == 1)
{
lean_object* v_fvarId_3548_; lean_object* v___x_3549_; 
v_fvarId_3548_ = lean_ctor_get(v___x_3547_, 0);
lean_inc(v_fvarId_3548_);
lean_dec_ref_known(v___x_3547_, 1);
lean_inc(v___y_3545_);
lean_inc_ref(v___y_3544_);
lean_inc(v___y_3543_);
lean_inc_ref(v___y_3542_);
v___x_3549_ = lean_apply_6(v___f_3540_, v_fvarId_3548_, v___y_3542_, v___y_3543_, v___y_3544_, v___y_3545_, lean_box(0));
if (lean_obj_tag(v___x_3549_) == 0)
{
lean_object* v_a_3550_; lean_object* v___x_3552_; uint8_t v_isShared_3553_; uint8_t v_isSharedCheck_3582_; 
v_a_3550_ = lean_ctor_get(v___x_3549_, 0);
v_isSharedCheck_3582_ = !lean_is_exclusive(v___x_3549_);
if (v_isSharedCheck_3582_ == 0)
{
v___x_3552_ = v___x_3549_;
v_isShared_3553_ = v_isSharedCheck_3582_;
goto v_resetjp_3551_;
}
else
{
lean_inc(v_a_3550_);
lean_dec(v___x_3549_);
v___x_3552_ = lean_box(0);
v_isShared_3553_ = v_isSharedCheck_3582_;
goto v_resetjp_3551_;
}
v_resetjp_3551_:
{
if (lean_obj_tag(v_a_3550_) == 1)
{
lean_object* v_val_3554_; lean_object* v___x_3556_; uint8_t v_isShared_3557_; uint8_t v_isSharedCheck_3577_; 
lean_del_object(v___x_3552_);
v_val_3554_ = lean_ctor_get(v_a_3550_, 0);
v_isSharedCheck_3577_ = !lean_is_exclusive(v_a_3550_);
if (v_isSharedCheck_3577_ == 0)
{
v___x_3556_ = v_a_3550_;
v_isShared_3557_ = v_isSharedCheck_3577_;
goto v_resetjp_3555_;
}
else
{
lean_inc(v_val_3554_);
lean_dec(v_a_3550_);
v___x_3556_ = lean_box(0);
v_isShared_3557_ = v_isSharedCheck_3577_;
goto v_resetjp_3555_;
}
v_resetjp_3555_:
{
lean_object* v___x_3558_; lean_object* v_a_3559_; lean_object* v___x_3561_; uint8_t v_isShared_3562_; uint8_t v_isSharedCheck_3576_; 
v___x_3558_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(v_val_3554_, v___y_3543_);
v_a_3559_ = lean_ctor_get(v___x_3558_, 0);
v_isSharedCheck_3576_ = !lean_is_exclusive(v___x_3558_);
if (v_isSharedCheck_3576_ == 0)
{
v___x_3561_ = v___x_3558_;
v_isShared_3562_ = v_isSharedCheck_3576_;
goto v_resetjp_3560_;
}
else
{
lean_inc(v_a_3559_);
lean_dec(v___x_3558_);
v___x_3561_ = lean_box(0);
v_isShared_3562_ = v_isSharedCheck_3576_;
goto v_resetjp_3560_;
}
v_resetjp_3560_:
{
lean_object* v_dummy_3563_; lean_object* v_nargs_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3571_; 
v_dummy_3563_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__18___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__18___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__18___closed__0);
v_nargs_3564_ = l_Lean_Expr_getAppNumArgs(v_e_3541_);
lean_inc(v_nargs_3564_);
v___x_3565_ = lean_mk_array(v_nargs_3564_, v_dummy_3563_);
v___x_3566_ = lean_unsigned_to_nat(1u);
v___x_3567_ = lean_nat_sub(v_nargs_3564_, v___x_3566_);
lean_dec(v_nargs_3564_);
v___x_3568_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3541_, v___x_3565_, v___x_3567_);
v___x_3569_ = l_Lean_Expr_beta(v_a_3559_, v___x_3568_);
if (v_isShared_3557_ == 0)
{
lean_ctor_set(v___x_3556_, 0, v___x_3569_);
v___x_3571_ = v___x_3556_;
goto v_reusejp_3570_;
}
else
{
lean_object* v_reuseFailAlloc_3575_; 
v_reuseFailAlloc_3575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3575_, 0, v___x_3569_);
v___x_3571_ = v_reuseFailAlloc_3575_;
goto v_reusejp_3570_;
}
v_reusejp_3570_:
{
lean_object* v___x_3573_; 
if (v_isShared_3562_ == 0)
{
lean_ctor_set(v___x_3561_, 0, v___x_3571_);
v___x_3573_ = v___x_3561_;
goto v_reusejp_3572_;
}
else
{
lean_object* v_reuseFailAlloc_3574_; 
v_reuseFailAlloc_3574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3574_, 0, v___x_3571_);
v___x_3573_ = v_reuseFailAlloc_3574_;
goto v_reusejp_3572_;
}
v_reusejp_3572_:
{
return v___x_3573_;
}
}
}
}
}
else
{
lean_object* v___x_3578_; lean_object* v___x_3580_; 
lean_dec(v_a_3550_);
lean_dec_ref(v_e_3541_);
v___x_3578_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
if (v_isShared_3553_ == 0)
{
lean_ctor_set(v___x_3552_, 0, v___x_3578_);
v___x_3580_ = v___x_3552_;
goto v_reusejp_3579_;
}
else
{
lean_object* v_reuseFailAlloc_3581_; 
v_reuseFailAlloc_3581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3581_, 0, v___x_3578_);
v___x_3580_ = v_reuseFailAlloc_3581_;
goto v_reusejp_3579_;
}
v_reusejp_3579_:
{
return v___x_3580_;
}
}
}
}
else
{
lean_object* v_a_3583_; lean_object* v___x_3585_; uint8_t v_isShared_3586_; uint8_t v_isSharedCheck_3590_; 
lean_dec_ref(v_e_3541_);
v_a_3583_ = lean_ctor_get(v___x_3549_, 0);
v_isSharedCheck_3590_ = !lean_is_exclusive(v___x_3549_);
if (v_isSharedCheck_3590_ == 0)
{
v___x_3585_ = v___x_3549_;
v_isShared_3586_ = v_isSharedCheck_3590_;
goto v_resetjp_3584_;
}
else
{
lean_inc(v_a_3583_);
lean_dec(v___x_3549_);
v___x_3585_ = lean_box(0);
v_isShared_3586_ = v_isSharedCheck_3590_;
goto v_resetjp_3584_;
}
v_resetjp_3584_:
{
lean_object* v___x_3588_; 
if (v_isShared_3586_ == 0)
{
v___x_3588_ = v___x_3585_;
goto v_reusejp_3587_;
}
else
{
lean_object* v_reuseFailAlloc_3589_; 
v_reuseFailAlloc_3589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3589_, 0, v_a_3583_);
v___x_3588_ = v_reuseFailAlloc_3589_;
goto v_reusejp_3587_;
}
v_reusejp_3587_:
{
return v___x_3588_;
}
}
}
}
else
{
lean_object* v___x_3591_; lean_object* v___x_3592_; 
lean_dec_ref(v___x_3547_);
lean_dec_ref(v_e_3541_);
lean_dec_ref(v___f_3540_);
v___x_3591_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_3592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3592_, 0, v___x_3591_);
return v___x_3592_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___lam__4___boxed(lean_object* v___f_3593_, lean_object* v_e_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_){
_start:
{
lean_object* v_res_3600_; 
v_res_3600_ = l_Lean_Meta_zetaReduce___lam__4(v___f_3593_, v_e_3594_, v___y_3595_, v___y_3596_, v___y_3597_, v___y_3598_);
lean_dec(v___y_3598_);
lean_dec_ref(v___y_3597_);
lean_dec(v___y_3596_);
lean_dec_ref(v___y_3595_);
return v_res_3600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0(lean_object* v_00_u03b1_3601_, lean_object* v_x_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_){
_start:
{
lean_object* v___x_3608_; lean_object* v___x_3609_; 
v___x_3608_ = lean_apply_1(v_x_3602_, lean_box(0));
v___x_3609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3609_, 0, v___x_3608_);
return v___x_3609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0___boxed(lean_object* v_00_u03b1_3610_, lean_object* v_x_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_){
_start:
{
lean_object* v_res_3617_; 
v_res_3617_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0(v_00_u03b1_3610_, v_x_3611_, v___y_3612_, v___y_3613_, v___y_3614_, v___y_3615_);
lean_dec(v___y_3615_);
lean_dec_ref(v___y_3614_);
lean_dec(v___y_3613_);
lean_dec_ref(v___y_3612_);
return v_res_3617_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__2(lean_object* v___x_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_){
_start:
{
lean_object* v___x_3624_; 
v___x_3624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3624_, 0, v___x_3618_);
return v___x_3624_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__2___boxed(lean_object* v___x_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_){
_start:
{
lean_object* v_res_3631_; 
v_res_3631_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__2(v___x_3625_, v___y_3626_, v___y_3627_, v___y_3628_, v___y_3629_);
lean_dec(v___y_3629_);
lean_dec_ref(v___y_3628_);
lean_dec(v___y_3627_);
lean_dec_ref(v___y_3626_);
return v_res_3631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0(lean_object* v_k_3632_, lean_object* v___y_3633_, lean_object* v_b_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_){
_start:
{
lean_object* v___x_3640_; 
lean_inc(v___y_3638_);
lean_inc_ref(v___y_3637_);
lean_inc(v___y_3636_);
lean_inc_ref(v___y_3635_);
lean_inc(v___y_3633_);
v___x_3640_ = lean_apply_7(v_k_3632_, v_b_3634_, v___y_3633_, v___y_3635_, v___y_3636_, v___y_3637_, v___y_3638_, lean_box(0));
return v___x_3640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0___boxed(lean_object* v_k_3641_, lean_object* v___y_3642_, lean_object* v_b_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_){
_start:
{
lean_object* v_res_3649_; 
v_res_3649_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0(v_k_3641_, v___y_3642_, v_b_3643_, v___y_3644_, v___y_3645_, v___y_3646_, v___y_3647_);
lean_dec(v___y_3647_);
lean_dec_ref(v___y_3646_);
lean_dec(v___y_3645_);
lean_dec_ref(v___y_3644_);
lean_dec(v___y_3642_);
return v_res_3649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(lean_object* v_name_3650_, uint8_t v_bi_3651_, lean_object* v_type_3652_, lean_object* v_k_3653_, uint8_t v_kind_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_){
_start:
{
lean_object* v___f_3661_; lean_object* v___x_3662_; 
lean_inc(v___y_3655_);
v___f_3661_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3661_, 0, v_k_3653_);
lean_closure_set(v___f_3661_, 1, v___y_3655_);
v___x_3662_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3650_, v_bi_3651_, v_type_3652_, v___f_3661_, v_kind_3654_, v___y_3656_, v___y_3657_, v___y_3658_, v___y_3659_);
if (lean_obj_tag(v___x_3662_) == 0)
{
return v___x_3662_;
}
else
{
lean_object* v_a_3663_; lean_object* v___x_3665_; uint8_t v_isShared_3666_; uint8_t v_isSharedCheck_3670_; 
v_a_3663_ = lean_ctor_get(v___x_3662_, 0);
v_isSharedCheck_3670_ = !lean_is_exclusive(v___x_3662_);
if (v_isSharedCheck_3670_ == 0)
{
v___x_3665_ = v___x_3662_;
v_isShared_3666_ = v_isSharedCheck_3670_;
goto v_resetjp_3664_;
}
else
{
lean_inc(v_a_3663_);
lean_dec(v___x_3662_);
v___x_3665_ = lean_box(0);
v_isShared_3666_ = v_isSharedCheck_3670_;
goto v_resetjp_3664_;
}
v_resetjp_3664_:
{
lean_object* v___x_3668_; 
if (v_isShared_3666_ == 0)
{
v___x_3668_ = v___x_3665_;
goto v_reusejp_3667_;
}
else
{
lean_object* v_reuseFailAlloc_3669_; 
v_reuseFailAlloc_3669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3669_, 0, v_a_3663_);
v___x_3668_ = v_reuseFailAlloc_3669_;
goto v_reusejp_3667_;
}
v_reusejp_3667_:
{
return v___x_3668_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___boxed(lean_object* v_name_3671_, lean_object* v_bi_3672_, lean_object* v_type_3673_, lean_object* v_k_3674_, lean_object* v_kind_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_){
_start:
{
uint8_t v_bi_boxed_3682_; uint8_t v_kind_boxed_3683_; lean_object* v_res_3684_; 
v_bi_boxed_3682_ = lean_unbox(v_bi_3672_);
v_kind_boxed_3683_ = lean_unbox(v_kind_3675_);
v_res_3684_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_name_3671_, v_bi_boxed_3682_, v_type_3673_, v_k_3674_, v_kind_boxed_3683_, v___y_3676_, v___y_3677_, v___y_3678_, v___y_3679_, v___y_3680_);
lean_dec(v___y_3680_);
lean_dec_ref(v___y_3679_);
lean_dec(v___y_3678_);
lean_dec_ref(v___y_3677_);
lean_dec(v___y_3676_);
return v_res_3684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg(lean_object* v_name_3685_, lean_object* v_type_3686_, lean_object* v_val_3687_, lean_object* v_k_3688_, uint8_t v_nondep_3689_, uint8_t v_kind_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_){
_start:
{
lean_object* v___f_3697_; lean_object* v___x_3698_; 
lean_inc(v___y_3691_);
v___f_3697_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3697_, 0, v_k_3688_);
lean_closure_set(v___f_3697_, 1, v___y_3691_);
v___x_3698_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_3685_, v_type_3686_, v_val_3687_, v___f_3697_, v_nondep_3689_, v_kind_3690_, v___y_3692_, v___y_3693_, v___y_3694_, v___y_3695_);
if (lean_obj_tag(v___x_3698_) == 0)
{
return v___x_3698_;
}
else
{
lean_object* v_a_3699_; lean_object* v___x_3701_; uint8_t v_isShared_3702_; uint8_t v_isSharedCheck_3706_; 
v_a_3699_ = lean_ctor_get(v___x_3698_, 0);
v_isSharedCheck_3706_ = !lean_is_exclusive(v___x_3698_);
if (v_isSharedCheck_3706_ == 0)
{
v___x_3701_ = v___x_3698_;
v_isShared_3702_ = v_isSharedCheck_3706_;
goto v_resetjp_3700_;
}
else
{
lean_inc(v_a_3699_);
lean_dec(v___x_3698_);
v___x_3701_ = lean_box(0);
v_isShared_3702_ = v_isSharedCheck_3706_;
goto v_resetjp_3700_;
}
v_resetjp_3700_:
{
lean_object* v___x_3704_; 
if (v_isShared_3702_ == 0)
{
v___x_3704_ = v___x_3701_;
goto v_reusejp_3703_;
}
else
{
lean_object* v_reuseFailAlloc_3705_; 
v_reuseFailAlloc_3705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3705_, 0, v_a_3699_);
v___x_3704_ = v_reuseFailAlloc_3705_;
goto v_reusejp_3703_;
}
v_reusejp_3703_:
{
return v___x_3704_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg___boxed(lean_object* v_name_3707_, lean_object* v_type_3708_, lean_object* v_val_3709_, lean_object* v_k_3710_, lean_object* v_nondep_3711_, lean_object* v_kind_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_){
_start:
{
uint8_t v_nondep_boxed_3719_; uint8_t v_kind_boxed_3720_; lean_object* v_res_3721_; 
v_nondep_boxed_3719_ = lean_unbox(v_nondep_3711_);
v_kind_boxed_3720_ = lean_unbox(v_kind_3712_);
v_res_3721_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg(v_name_3707_, v_type_3708_, v_val_3709_, v_k_3710_, v_nondep_boxed_3719_, v_kind_boxed_3720_, v___y_3713_, v___y_3714_, v___y_3715_, v___y_3716_, v___y_3717_);
lean_dec(v___y_3717_);
lean_dec_ref(v___y_3716_);
lean_dec(v___y_3715_);
lean_dec_ref(v___y_3714_);
lean_dec(v___y_3713_);
return v_res_3721_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0(lean_object* v_00_u03b1_3722_, lean_object* v_x_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_){
_start:
{
lean_object* v___x_3729_; lean_object* v___x_3730_; 
v___x_3729_ = lean_apply_1(v_x_3723_, lean_box(0));
v___x_3730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3730_, 0, v___x_3729_);
return v___x_3730_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0___boxed(lean_object* v_00_u03b1_3731_, lean_object* v_x_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_){
_start:
{
lean_object* v_res_3738_; 
v_res_3738_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0(v_00_u03b1_3731_, v_x_3732_, v___y_3733_, v___y_3734_, v___y_3735_, v___y_3736_);
lean_dec(v___y_3736_);
lean_dec_ref(v___y_3735_);
lean_dec(v___y_3734_);
lean_dec_ref(v___y_3733_);
return v_res_3738_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg(lean_object* v_ref_3739_){
_start:
{
lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; 
v___x_3741_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__5_spec__7___redArg___closed__5);
v___x_3742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3742_, 0, v_ref_3739_);
lean_ctor_set(v___x_3742_, 1, v___x_3741_);
v___x_3743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3743_, 0, v___x_3742_);
return v___x_3743_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg___boxed(lean_object* v_ref_3744_, lean_object* v___y_3745_){
_start:
{
lean_object* v_res_3746_; 
v_res_3746_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg(v_ref_3744_);
return v_res_3746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg(lean_object* v_x_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_){
_start:
{
lean_object* v___y_3755_; lean_object* v_toCold_3764_; lean_object* v_currRecDepth_3765_; lean_object* v_ref_3766_; uint16_t v_optionFlags_3767_; uint8_t v_suppressElabErrors_3768_; uint8_t v_checkDeprecated_3769_; uint8_t v_isRecordingDeps_3770_; lean_object* v_maxRecDepth_3776_; lean_object* v___x_3777_; uint8_t v___x_3778_; 
v_toCold_3764_ = lean_ctor_get(v___y_3751_, 0);
v_currRecDepth_3765_ = lean_ctor_get(v___y_3751_, 1);
v_ref_3766_ = lean_ctor_get(v___y_3751_, 2);
v_optionFlags_3767_ = lean_ctor_get_uint16(v___y_3751_, sizeof(void*)*3);
v_suppressElabErrors_3768_ = lean_ctor_get_uint8(v___y_3751_, sizeof(void*)*3 + 2);
v_checkDeprecated_3769_ = lean_ctor_get_uint8(v___y_3751_, sizeof(void*)*3 + 3);
v_isRecordingDeps_3770_ = lean_ctor_get_uint8(v___y_3751_, sizeof(void*)*3 + 4);
v_maxRecDepth_3776_ = lean_ctor_get(v_toCold_3764_, 3);
v___x_3777_ = lean_unsigned_to_nat(0u);
v___x_3778_ = lean_nat_dec_eq(v_maxRecDepth_3776_, v___x_3777_);
if (v___x_3778_ == 0)
{
uint8_t v___x_3779_; 
v___x_3779_ = lean_nat_dec_eq(v_currRecDepth_3765_, v_maxRecDepth_3776_);
if (v___x_3779_ == 0)
{
goto v___jp_3771_;
}
else
{
lean_object* v___x_3780_; 
lean_dec_ref(v_x_3747_);
lean_inc(v_ref_3766_);
v___x_3780_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg(v_ref_3766_);
v___y_3755_ = v___x_3780_;
goto v___jp_3754_;
}
}
else
{
goto v___jp_3771_;
}
v___jp_3754_:
{
if (lean_obj_tag(v___y_3755_) == 0)
{
return v___y_3755_;
}
else
{
lean_object* v_a_3756_; lean_object* v___x_3758_; uint8_t v_isShared_3759_; uint8_t v_isSharedCheck_3763_; 
v_a_3756_ = lean_ctor_get(v___y_3755_, 0);
v_isSharedCheck_3763_ = !lean_is_exclusive(v___y_3755_);
if (v_isSharedCheck_3763_ == 0)
{
v___x_3758_ = v___y_3755_;
v_isShared_3759_ = v_isSharedCheck_3763_;
goto v_resetjp_3757_;
}
else
{
lean_inc(v_a_3756_);
lean_dec(v___y_3755_);
v___x_3758_ = lean_box(0);
v_isShared_3759_ = v_isSharedCheck_3763_;
goto v_resetjp_3757_;
}
v_resetjp_3757_:
{
lean_object* v___x_3761_; 
if (v_isShared_3759_ == 0)
{
v___x_3761_ = v___x_3758_;
goto v_reusejp_3760_;
}
else
{
lean_object* v_reuseFailAlloc_3762_; 
v_reuseFailAlloc_3762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3762_, 0, v_a_3756_);
v___x_3761_ = v_reuseFailAlloc_3762_;
goto v_reusejp_3760_;
}
v_reusejp_3760_:
{
return v___x_3761_;
}
}
}
}
v___jp_3771_:
{
lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; 
v___x_3772_ = lean_unsigned_to_nat(1u);
v___x_3773_ = lean_nat_add(v_currRecDepth_3765_, v___x_3772_);
lean_inc(v_ref_3766_);
lean_inc_ref(v_toCold_3764_);
v___x_3774_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_3774_, 0, v_toCold_3764_);
lean_ctor_set(v___x_3774_, 1, v___x_3773_);
lean_ctor_set(v___x_3774_, 2, v_ref_3766_);
lean_ctor_set_uint16(v___x_3774_, sizeof(void*)*3, v_optionFlags_3767_);
lean_ctor_set_uint8(v___x_3774_, sizeof(void*)*3 + 2, v_suppressElabErrors_3768_);
lean_ctor_set_uint8(v___x_3774_, sizeof(void*)*3 + 3, v_checkDeprecated_3769_);
lean_ctor_set_uint8(v___x_3774_, sizeof(void*)*3 + 4, v_isRecordingDeps_3770_);
lean_inc(v___y_3752_);
lean_inc(v___y_3750_);
lean_inc_ref(v___y_3749_);
lean_inc(v___y_3748_);
v___x_3775_ = lean_apply_6(v_x_3747_, v___y_3748_, v___y_3749_, v___y_3750_, v___x_3774_, v___y_3752_, lean_box(0));
v___y_3755_ = v___x_3775_;
goto v___jp_3754_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg___boxed(lean_object* v_x_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_){
_start:
{
lean_object* v_res_3788_; 
v_res_3788_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg(v_x_3781_, v___y_3782_, v___y_3783_, v___y_3784_, v___y_3785_, v___y_3786_);
lean_dec(v___y_3786_);
lean_dec_ref(v___y_3785_);
lean_dec(v___y_3784_);
lean_dec_ref(v___y_3783_);
lean_dec(v___y_3782_);
return v_res_3788_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___lam__0___boxed(lean_object* v_fvars_3789_, lean_object* v_pre_3790_, lean_object* v_post_3791_, lean_object* v_usedLetOnly_3792_, lean_object* v_skipConstInApp_3793_, lean_object* v_skipInstances_3794_, lean_object* v_body_3795_, lean_object* v_x_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_){
_start:
{
uint8_t v_usedLetOnly_boxed_3803_; uint8_t v_skipConstInApp_boxed_3804_; uint8_t v_skipInstances_boxed_3805_; lean_object* v_res_3806_; 
v_usedLetOnly_boxed_3803_ = lean_unbox(v_usedLetOnly_3792_);
v_skipConstInApp_boxed_3804_ = lean_unbox(v_skipConstInApp_3793_);
v_skipInstances_boxed_3805_ = lean_unbox(v_skipInstances_3794_);
v_res_3806_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___lam__0(v_fvars_3789_, v_pre_3790_, v_post_3791_, v_usedLetOnly_boxed_3803_, v_skipConstInApp_boxed_3804_, v_skipInstances_boxed_3805_, v_body_3795_, v_x_3796_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_, v___y_3801_);
lean_dec(v___y_3801_);
lean_dec_ref(v___y_3800_);
lean_dec(v___y_3799_);
lean_dec_ref(v___y_3798_);
lean_dec(v___y_3797_);
return v_res_3806_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___lam__0(lean_object* v_fvars_3807_, lean_object* v_pre_3808_, lean_object* v_post_3809_, uint8_t v_usedLetOnly_3810_, uint8_t v_skipConstInApp_3811_, uint8_t v_skipInstances_3812_, lean_object* v_body_3813_, lean_object* v_x_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_){
_start:
{
lean_object* v___x_3821_; lean_object* v___x_3822_; 
v___x_3821_ = lean_array_push(v_fvars_3807_, v_x_3814_);
v___x_3822_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6(v_pre_3808_, v_post_3809_, v_usedLetOnly_3810_, v_skipConstInApp_3811_, v_skipInstances_3812_, v___x_3821_, v_body_3813_, v___y_3815_, v___y_3816_, v___y_3817_, v___y_3818_, v___y_3819_);
return v___x_3822_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___lam__0___boxed(lean_object* v_fvars_3823_, lean_object* v_pre_3824_, lean_object* v_post_3825_, lean_object* v_usedLetOnly_3826_, lean_object* v_skipConstInApp_3827_, lean_object* v_skipInstances_3828_, lean_object* v_body_3829_, lean_object* v_x_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_){
_start:
{
uint8_t v_usedLetOnly_boxed_3837_; uint8_t v_skipConstInApp_boxed_3838_; uint8_t v_skipInstances_boxed_3839_; lean_object* v_res_3840_; 
v_usedLetOnly_boxed_3837_ = lean_unbox(v_usedLetOnly_3826_);
v_skipConstInApp_boxed_3838_ = lean_unbox(v_skipConstInApp_3827_);
v_skipInstances_boxed_3839_ = lean_unbox(v_skipInstances_3828_);
v_res_3840_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___lam__0(v_fvars_3823_, v_pre_3824_, v_post_3825_, v_usedLetOnly_boxed_3837_, v_skipConstInApp_boxed_3838_, v_skipInstances_boxed_3839_, v_body_3829_, v_x_3830_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_);
lean_dec(v___y_3835_);
lean_dec_ref(v___y_3834_);
lean_dec(v___y_3833_);
lean_dec_ref(v___y_3832_);
lean_dec(v___y_3831_);
return v_res_3840_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(lean_object* v_pre_3841_, lean_object* v_post_3842_, uint8_t v_usedLetOnly_3843_, uint8_t v_skipConstInApp_3844_, uint8_t v_skipInstances_3845_, lean_object* v_e_3846_, lean_object* v_a_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_){
_start:
{
lean_object* v___x_3853_; 
lean_inc_ref(v_post_3842_);
lean_inc(v___y_3851_);
lean_inc_ref(v___y_3850_);
lean_inc(v___y_3849_);
lean_inc_ref(v___y_3848_);
lean_inc_ref(v_e_3846_);
v___x_3853_ = lean_apply_6(v_post_3842_, v_e_3846_, v___y_3848_, v___y_3849_, v___y_3850_, v___y_3851_, lean_box(0));
if (lean_obj_tag(v___x_3853_) == 0)
{
lean_object* v_a_3854_; lean_object* v___x_3856_; uint8_t v_isShared_3857_; uint8_t v_isSharedCheck_3872_; 
v_a_3854_ = lean_ctor_get(v___x_3853_, 0);
v_isSharedCheck_3872_ = !lean_is_exclusive(v___x_3853_);
if (v_isSharedCheck_3872_ == 0)
{
v___x_3856_ = v___x_3853_;
v_isShared_3857_ = v_isSharedCheck_3872_;
goto v_resetjp_3855_;
}
else
{
lean_inc(v_a_3854_);
lean_dec(v___x_3853_);
v___x_3856_ = lean_box(0);
v_isShared_3857_ = v_isSharedCheck_3872_;
goto v_resetjp_3855_;
}
v_resetjp_3855_:
{
switch(lean_obj_tag(v_a_3854_))
{
case 0:
{
lean_object* v_e_3858_; lean_object* v___x_3860_; 
lean_dec_ref(v_e_3846_);
lean_dec_ref(v_post_3842_);
lean_dec_ref(v_pre_3841_);
v_e_3858_ = lean_ctor_get(v_a_3854_, 0);
lean_inc_ref(v_e_3858_);
lean_dec_ref_known(v_a_3854_, 1);
if (v_isShared_3857_ == 0)
{
lean_ctor_set(v___x_3856_, 0, v_e_3858_);
v___x_3860_ = v___x_3856_;
goto v_reusejp_3859_;
}
else
{
lean_object* v_reuseFailAlloc_3861_; 
v_reuseFailAlloc_3861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3861_, 0, v_e_3858_);
v___x_3860_ = v_reuseFailAlloc_3861_;
goto v_reusejp_3859_;
}
v_reusejp_3859_:
{
return v___x_3860_;
}
}
case 1:
{
lean_object* v_e_3862_; lean_object* v___x_3863_; 
lean_del_object(v___x_3856_);
lean_dec_ref(v_e_3846_);
v_e_3862_ = lean_ctor_get(v_a_3854_, 0);
lean_inc_ref(v_e_3862_);
lean_dec_ref_known(v_a_3854_, 1);
v___x_3863_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3841_, v_post_3842_, v_usedLetOnly_3843_, v_skipConstInApp_3844_, v_skipInstances_3845_, v_e_3862_, v_a_3847_, v___y_3848_, v___y_3849_, v___y_3850_, v___y_3851_);
return v___x_3863_;
}
default: 
{
lean_object* v_e_x3f_3864_; 
lean_dec_ref(v_post_3842_);
lean_dec_ref(v_pre_3841_);
v_e_x3f_3864_ = lean_ctor_get(v_a_3854_, 0);
lean_inc(v_e_x3f_3864_);
lean_dec_ref_known(v_a_3854_, 1);
if (lean_obj_tag(v_e_x3f_3864_) == 0)
{
lean_object* v___x_3866_; 
if (v_isShared_3857_ == 0)
{
lean_ctor_set(v___x_3856_, 0, v_e_3846_);
v___x_3866_ = v___x_3856_;
goto v_reusejp_3865_;
}
else
{
lean_object* v_reuseFailAlloc_3867_; 
v_reuseFailAlloc_3867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3867_, 0, v_e_3846_);
v___x_3866_ = v_reuseFailAlloc_3867_;
goto v_reusejp_3865_;
}
v_reusejp_3865_:
{
return v___x_3866_;
}
}
else
{
lean_object* v_val_3868_; lean_object* v___x_3870_; 
lean_dec_ref(v_e_3846_);
v_val_3868_ = lean_ctor_get(v_e_x3f_3864_, 0);
lean_inc(v_val_3868_);
lean_dec_ref_known(v_e_x3f_3864_, 1);
if (v_isShared_3857_ == 0)
{
lean_ctor_set(v___x_3856_, 0, v_val_3868_);
v___x_3870_ = v___x_3856_;
goto v_reusejp_3869_;
}
else
{
lean_object* v_reuseFailAlloc_3871_; 
v_reuseFailAlloc_3871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3871_, 0, v_val_3868_);
v___x_3870_ = v_reuseFailAlloc_3871_;
goto v_reusejp_3869_;
}
v_reusejp_3869_:
{
return v___x_3870_;
}
}
}
}
}
}
else
{
lean_object* v_a_3873_; lean_object* v___x_3875_; uint8_t v_isShared_3876_; uint8_t v_isSharedCheck_3880_; 
lean_dec_ref(v_e_3846_);
lean_dec_ref(v_post_3842_);
lean_dec_ref(v_pre_3841_);
v_a_3873_ = lean_ctor_get(v___x_3853_, 0);
v_isSharedCheck_3880_ = !lean_is_exclusive(v___x_3853_);
if (v_isSharedCheck_3880_ == 0)
{
v___x_3875_ = v___x_3853_;
v_isShared_3876_ = v_isSharedCheck_3880_;
goto v_resetjp_3874_;
}
else
{
lean_inc(v_a_3873_);
lean_dec(v___x_3853_);
v___x_3875_ = lean_box(0);
v_isShared_3876_ = v_isSharedCheck_3880_;
goto v_resetjp_3874_;
}
v_resetjp_3874_:
{
lean_object* v___x_3878_; 
if (v_isShared_3876_ == 0)
{
v___x_3878_ = v___x_3875_;
goto v_reusejp_3877_;
}
else
{
lean_object* v_reuseFailAlloc_3879_; 
v_reuseFailAlloc_3879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3879_, 0, v_a_3873_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6(lean_object* v_pre_3881_, lean_object* v_post_3882_, uint8_t v_usedLetOnly_3883_, uint8_t v_skipConstInApp_3884_, uint8_t v_skipInstances_3885_, lean_object* v_fvars_3886_, lean_object* v_e_3887_, lean_object* v_a_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_){
_start:
{
if (lean_obj_tag(v_e_3887_) == 6)
{
lean_object* v_binderName_3894_; lean_object* v_binderType_3895_; lean_object* v_body_3896_; uint8_t v_binderInfo_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___f_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; 
v_binderName_3894_ = lean_ctor_get(v_e_3887_, 0);
lean_inc(v_binderName_3894_);
v_binderType_3895_ = lean_ctor_get(v_e_3887_, 1);
lean_inc_ref(v_binderType_3895_);
v_body_3896_ = lean_ctor_get(v_e_3887_, 2);
lean_inc_ref(v_body_3896_);
v_binderInfo_3897_ = lean_ctor_get_uint8(v_e_3887_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_3887_, 3);
v___x_3898_ = lean_box(v_usedLetOnly_3883_);
v___x_3899_ = lean_box(v_skipConstInApp_3884_);
v___x_3900_ = lean_box(v_skipInstances_3885_);
lean_inc_ref(v_post_3882_);
lean_inc_ref(v_pre_3881_);
lean_inc_ref(v_fvars_3886_);
v___f_3901_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___lam__0___boxed), 14, 7);
lean_closure_set(v___f_3901_, 0, v_fvars_3886_);
lean_closure_set(v___f_3901_, 1, v_pre_3881_);
lean_closure_set(v___f_3901_, 2, v_post_3882_);
lean_closure_set(v___f_3901_, 3, v___x_3898_);
lean_closure_set(v___f_3901_, 4, v___x_3899_);
lean_closure_set(v___f_3901_, 5, v___x_3900_);
lean_closure_set(v___f_3901_, 6, v_body_3896_);
v___x_3902_ = lean_expr_instantiate_rev(v_binderType_3895_, v_fvars_3886_);
lean_dec_ref(v_fvars_3886_);
lean_dec_ref(v_binderType_3895_);
v___x_3903_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3881_, v_post_3882_, v_usedLetOnly_3883_, v_skipConstInApp_3884_, v_skipInstances_3885_, v___x_3902_, v_a_3888_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_);
if (lean_obj_tag(v___x_3903_) == 0)
{
lean_object* v_a_3904_; uint8_t v___x_3905_; lean_object* v___x_3906_; 
v_a_3904_ = lean_ctor_get(v___x_3903_, 0);
lean_inc(v_a_3904_);
lean_dec_ref_known(v___x_3903_, 1);
v___x_3905_ = 0;
v___x_3906_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_binderName_3894_, v_binderInfo_3897_, v_a_3904_, v___f_3901_, v___x_3905_, v_a_3888_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_);
return v___x_3906_;
}
else
{
lean_dec_ref(v___f_3901_);
lean_dec(v_binderName_3894_);
return v___x_3903_;
}
}
else
{
lean_object* v___x_3907_; lean_object* v___x_3908_; 
v___x_3907_ = lean_expr_instantiate_rev(v_e_3887_, v_fvars_3886_);
lean_dec_ref(v_e_3887_);
lean_inc_ref(v_post_3882_);
lean_inc_ref(v_pre_3881_);
v___x_3908_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3881_, v_post_3882_, v_usedLetOnly_3883_, v_skipConstInApp_3884_, v_skipInstances_3885_, v___x_3907_, v_a_3888_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_);
if (lean_obj_tag(v___x_3908_) == 0)
{
lean_object* v_a_3909_; uint8_t v___x_3910_; uint8_t v___x_3911_; uint8_t v___x_3912_; lean_object* v___x_3913_; 
v_a_3909_ = lean_ctor_get(v___x_3908_, 0);
lean_inc(v_a_3909_);
lean_dec_ref_known(v___x_3908_, 1);
v___x_3910_ = 0;
v___x_3911_ = 1;
v___x_3912_ = 1;
v___x_3913_ = l_Lean_Meta_mkLambdaFVars(v_fvars_3886_, v_a_3909_, v___x_3910_, v_usedLetOnly_3883_, v___x_3910_, v___x_3911_, v___x_3912_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_);
lean_dec_ref(v_fvars_3886_);
if (lean_obj_tag(v___x_3913_) == 0)
{
lean_object* v_a_3914_; lean_object* v___x_3915_; 
v_a_3914_ = lean_ctor_get(v___x_3913_, 0);
lean_inc(v_a_3914_);
lean_dec_ref_known(v___x_3913_, 1);
v___x_3915_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_3881_, v_post_3882_, v_usedLetOnly_3883_, v_skipConstInApp_3884_, v_skipInstances_3885_, v_a_3914_, v_a_3888_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_);
return v___x_3915_;
}
else
{
lean_dec_ref(v_post_3882_);
lean_dec_ref(v_pre_3881_);
return v___x_3913_;
}
}
else
{
lean_dec_ref(v_fvars_3886_);
lean_dec_ref(v_post_3882_);
lean_dec_ref(v_pre_3881_);
return v___x_3908_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___lam__0(lean_object* v_fvars_3916_, lean_object* v_pre_3917_, lean_object* v_post_3918_, uint8_t v_usedLetOnly_3919_, uint8_t v_skipConstInApp_3920_, uint8_t v_skipInstances_3921_, lean_object* v_body_3922_, lean_object* v_x_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_){
_start:
{
lean_object* v___x_3930_; lean_object* v___x_3931_; 
v___x_3930_ = lean_array_push(v_fvars_3916_, v_x_3923_);
v___x_3931_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7(v_pre_3917_, v_post_3918_, v_usedLetOnly_3919_, v_skipConstInApp_3920_, v_skipInstances_3921_, v___x_3930_, v_body_3922_, v___y_3924_, v___y_3925_, v___y_3926_, v___y_3927_, v___y_3928_);
return v___x_3931_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___lam__0___boxed(lean_object* v_fvars_3932_, lean_object* v_pre_3933_, lean_object* v_post_3934_, lean_object* v_usedLetOnly_3935_, lean_object* v_skipConstInApp_3936_, lean_object* v_skipInstances_3937_, lean_object* v_body_3938_, lean_object* v_x_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_){
_start:
{
uint8_t v_usedLetOnly_boxed_3946_; uint8_t v_skipConstInApp_boxed_3947_; uint8_t v_skipInstances_boxed_3948_; lean_object* v_res_3949_; 
v_usedLetOnly_boxed_3946_ = lean_unbox(v_usedLetOnly_3935_);
v_skipConstInApp_boxed_3947_ = lean_unbox(v_skipConstInApp_3936_);
v_skipInstances_boxed_3948_ = lean_unbox(v_skipInstances_3937_);
v_res_3949_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___lam__0(v_fvars_3932_, v_pre_3933_, v_post_3934_, v_usedLetOnly_boxed_3946_, v_skipConstInApp_boxed_3947_, v_skipInstances_boxed_3948_, v_body_3938_, v_x_3939_, v___y_3940_, v___y_3941_, v___y_3942_, v___y_3943_, v___y_3944_);
lean_dec(v___y_3944_);
lean_dec_ref(v___y_3943_);
lean_dec(v___y_3942_);
lean_dec_ref(v___y_3941_);
lean_dec(v___y_3940_);
return v_res_3949_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7(lean_object* v_pre_3950_, lean_object* v_post_3951_, uint8_t v_usedLetOnly_3952_, uint8_t v_skipConstInApp_3953_, uint8_t v_skipInstances_3954_, lean_object* v_fvars_3955_, lean_object* v_e_3956_, lean_object* v_a_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_){
_start:
{
if (lean_obj_tag(v_e_3956_) == 8)
{
lean_object* v_declName_3963_; lean_object* v_type_3964_; lean_object* v_value_3965_; lean_object* v_body_3966_; uint8_t v_nondep_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___f_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; 
v_declName_3963_ = lean_ctor_get(v_e_3956_, 0);
lean_inc(v_declName_3963_);
v_type_3964_ = lean_ctor_get(v_e_3956_, 1);
lean_inc_ref(v_type_3964_);
v_value_3965_ = lean_ctor_get(v_e_3956_, 2);
lean_inc_ref(v_value_3965_);
v_body_3966_ = lean_ctor_get(v_e_3956_, 3);
lean_inc_ref(v_body_3966_);
v_nondep_3967_ = lean_ctor_get_uint8(v_e_3956_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_3956_, 4);
v___x_3968_ = lean_box(v_usedLetOnly_3952_);
v___x_3969_ = lean_box(v_skipConstInApp_3953_);
v___x_3970_ = lean_box(v_skipInstances_3954_);
lean_inc_ref_n(v_post_3951_, 2);
lean_inc_ref_n(v_pre_3950_, 2);
lean_inc_ref(v_fvars_3955_);
v___f_3971_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___lam__0___boxed), 14, 7);
lean_closure_set(v___f_3971_, 0, v_fvars_3955_);
lean_closure_set(v___f_3971_, 1, v_pre_3950_);
lean_closure_set(v___f_3971_, 2, v_post_3951_);
lean_closure_set(v___f_3971_, 3, v___x_3968_);
lean_closure_set(v___f_3971_, 4, v___x_3969_);
lean_closure_set(v___f_3971_, 5, v___x_3970_);
lean_closure_set(v___f_3971_, 6, v_body_3966_);
v___x_3972_ = lean_expr_instantiate_rev(v_type_3964_, v_fvars_3955_);
lean_dec_ref(v_type_3964_);
v___x_3973_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3950_, v_post_3951_, v_usedLetOnly_3952_, v_skipConstInApp_3953_, v_skipInstances_3954_, v___x_3972_, v_a_3957_, v___y_3958_, v___y_3959_, v___y_3960_, v___y_3961_);
if (lean_obj_tag(v___x_3973_) == 0)
{
lean_object* v_a_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; 
v_a_3974_ = lean_ctor_get(v___x_3973_, 0);
lean_inc(v_a_3974_);
lean_dec_ref_known(v___x_3973_, 1);
v___x_3975_ = lean_expr_instantiate_rev(v_value_3965_, v_fvars_3955_);
lean_dec_ref(v_fvars_3955_);
lean_dec_ref(v_value_3965_);
v___x_3976_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3950_, v_post_3951_, v_usedLetOnly_3952_, v_skipConstInApp_3953_, v_skipInstances_3954_, v___x_3975_, v_a_3957_, v___y_3958_, v___y_3959_, v___y_3960_, v___y_3961_);
if (lean_obj_tag(v___x_3976_) == 0)
{
lean_object* v_a_3977_; uint8_t v___x_3978_; lean_object* v___x_3979_; 
v_a_3977_ = lean_ctor_get(v___x_3976_, 0);
lean_inc(v_a_3977_);
lean_dec_ref_known(v___x_3976_, 1);
v___x_3978_ = 0;
v___x_3979_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg(v_declName_3963_, v_a_3974_, v_a_3977_, v___f_3971_, v_nondep_3967_, v___x_3978_, v_a_3957_, v___y_3958_, v___y_3959_, v___y_3960_, v___y_3961_);
return v___x_3979_;
}
else
{
lean_dec(v_a_3974_);
lean_dec_ref(v___f_3971_);
lean_dec(v_declName_3963_);
return v___x_3976_;
}
}
else
{
lean_dec_ref(v___f_3971_);
lean_dec_ref(v_value_3965_);
lean_dec(v_declName_3963_);
lean_dec_ref(v_fvars_3955_);
lean_dec_ref(v_post_3951_);
lean_dec_ref(v_pre_3950_);
return v___x_3973_;
}
}
else
{
lean_object* v___x_3980_; lean_object* v___x_3981_; 
v___x_3980_ = lean_expr_instantiate_rev(v_e_3956_, v_fvars_3955_);
lean_dec_ref(v_e_3956_);
lean_inc_ref(v_post_3951_);
lean_inc_ref(v_pre_3950_);
v___x_3981_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3950_, v_post_3951_, v_usedLetOnly_3952_, v_skipConstInApp_3953_, v_skipInstances_3954_, v___x_3980_, v_a_3957_, v___y_3958_, v___y_3959_, v___y_3960_, v___y_3961_);
if (lean_obj_tag(v___x_3981_) == 0)
{
lean_object* v_a_3982_; uint8_t v___x_3983_; uint8_t v___x_3984_; lean_object* v___x_3985_; 
v_a_3982_ = lean_ctor_get(v___x_3981_, 0);
lean_inc(v_a_3982_);
lean_dec_ref_known(v___x_3981_, 1);
v___x_3983_ = 0;
v___x_3984_ = 1;
v___x_3985_ = l_Lean_Meta_mkLetFVars(v_fvars_3955_, v_a_3982_, v_usedLetOnly_3952_, v___x_3983_, v___x_3984_, v___y_3958_, v___y_3959_, v___y_3960_, v___y_3961_);
lean_dec_ref(v_fvars_3955_);
if (lean_obj_tag(v___x_3985_) == 0)
{
lean_object* v_a_3986_; lean_object* v___x_3987_; 
v_a_3986_ = lean_ctor_get(v___x_3985_, 0);
lean_inc(v_a_3986_);
lean_dec_ref_known(v___x_3985_, 1);
v___x_3987_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_3950_, v_post_3951_, v_usedLetOnly_3952_, v_skipConstInApp_3953_, v_skipInstances_3954_, v_a_3986_, v_a_3957_, v___y_3958_, v___y_3959_, v___y_3960_, v___y_3961_);
return v___x_3987_;
}
else
{
lean_dec_ref(v_post_3951_);
lean_dec_ref(v_pre_3950_);
return v___x_3985_;
}
}
else
{
lean_dec_ref(v_fvars_3955_);
lean_dec_ref(v_post_3951_);
lean_dec_ref(v_pre_3950_);
return v___x_3981_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__2(lean_object* v_pre_3988_, lean_object* v_post_3989_, uint8_t v_usedLetOnly_3990_, uint8_t v_skipConstInApp_3991_, uint8_t v_skipInstances_3992_, size_t v_sz_3993_, size_t v_i_3994_, lean_object* v_bs_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_, lean_object* v___y_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_){
_start:
{
uint8_t v___x_4002_; 
v___x_4002_ = lean_usize_dec_lt(v_i_3994_, v_sz_3993_);
if (v___x_4002_ == 0)
{
lean_object* v___x_4003_; 
lean_dec_ref(v_post_3989_);
lean_dec_ref(v_pre_3988_);
v___x_4003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4003_, 0, v_bs_3995_);
return v___x_4003_;
}
else
{
lean_object* v_v_4004_; lean_object* v___x_4005_; lean_object* v_bs_x27_4006_; lean_object* v___x_4007_; 
v_v_4004_ = lean_array_uget(v_bs_3995_, v_i_3994_);
v___x_4005_ = lean_unsigned_to_nat(0u);
v_bs_x27_4006_ = lean_array_uset(v_bs_3995_, v_i_3994_, v___x_4005_);
lean_inc_ref(v_post_3989_);
lean_inc_ref(v_pre_3988_);
v___x_4007_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_3988_, v_post_3989_, v_usedLetOnly_3990_, v_skipConstInApp_3991_, v_skipInstances_3992_, v_v_4004_, v___y_3996_, v___y_3997_, v___y_3998_, v___y_3999_, v___y_4000_);
if (lean_obj_tag(v___x_4007_) == 0)
{
lean_object* v_a_4008_; size_t v___x_4009_; size_t v___x_4010_; lean_object* v___x_4011_; 
v_a_4008_ = lean_ctor_get(v___x_4007_, 0);
lean_inc(v_a_4008_);
lean_dec_ref_known(v___x_4007_, 1);
v___x_4009_ = ((size_t)1ULL);
v___x_4010_ = lean_usize_add(v_i_3994_, v___x_4009_);
v___x_4011_ = lean_array_uset(v_bs_x27_4006_, v_i_3994_, v_a_4008_);
v_i_3994_ = v___x_4010_;
v_bs_3995_ = v___x_4011_;
goto _start;
}
else
{
lean_object* v_a_4013_; lean_object* v___x_4015_; uint8_t v_isShared_4016_; uint8_t v_isSharedCheck_4020_; 
lean_dec_ref(v_bs_x27_4006_);
lean_dec_ref(v_post_3989_);
lean_dec_ref(v_pre_3988_);
v_a_4013_ = lean_ctor_get(v___x_4007_, 0);
v_isSharedCheck_4020_ = !lean_is_exclusive(v___x_4007_);
if (v_isSharedCheck_4020_ == 0)
{
v___x_4015_ = v___x_4007_;
v_isShared_4016_ = v_isSharedCheck_4020_;
goto v_resetjp_4014_;
}
else
{
lean_inc(v_a_4013_);
lean_dec(v___x_4007_);
v___x_4015_ = lean_box(0);
v_isShared_4016_ = v_isSharedCheck_4020_;
goto v_resetjp_4014_;
}
v_resetjp_4014_:
{
lean_object* v___x_4018_; 
if (v_isShared_4016_ == 0)
{
v___x_4018_ = v___x_4015_;
goto v_reusejp_4017_;
}
else
{
lean_object* v_reuseFailAlloc_4019_; 
v_reuseFailAlloc_4019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4019_, 0, v_a_4013_);
v___x_4018_ = v_reuseFailAlloc_4019_;
goto v_reusejp_4017_;
}
v_reusejp_4017_:
{
return v___x_4018_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0(lean_object* v_pre_4021_, lean_object* v_post_4022_, uint8_t v_usedLetOnly_4023_, uint8_t v_skipConstInApp_4024_, uint8_t v_skipInstances_4025_, lean_object* v___x_4026_, lean_object* v___y_4027_, lean_object* v_b_4028_, lean_object* v_a_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_){
_start:
{
lean_object* v___x_4035_; 
v___x_4035_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4021_, v_post_4022_, v_usedLetOnly_4023_, v_skipConstInApp_4024_, v_skipInstances_4025_, v___x_4026_, v___y_4027_, v___y_4030_, v___y_4031_, v___y_4032_, v___y_4033_);
if (lean_obj_tag(v___x_4035_) == 0)
{
lean_object* v_a_4036_; lean_object* v___x_4038_; uint8_t v_isShared_4039_; uint8_t v_isSharedCheck_4045_; 
v_a_4036_ = lean_ctor_get(v___x_4035_, 0);
v_isSharedCheck_4045_ = !lean_is_exclusive(v___x_4035_);
if (v_isSharedCheck_4045_ == 0)
{
v___x_4038_ = v___x_4035_;
v_isShared_4039_ = v_isSharedCheck_4045_;
goto v_resetjp_4037_;
}
else
{
lean_inc(v_a_4036_);
lean_dec(v___x_4035_);
v___x_4038_ = lean_box(0);
v_isShared_4039_ = v_isSharedCheck_4045_;
goto v_resetjp_4037_;
}
v_resetjp_4037_:
{
lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4043_; 
v___x_4040_ = lean_array_fset(v_b_4028_, v_a_4029_, v_a_4036_);
v___x_4041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4041_, 0, v___x_4040_);
if (v_isShared_4039_ == 0)
{
lean_ctor_set(v___x_4038_, 0, v___x_4041_);
v___x_4043_ = v___x_4038_;
goto v_reusejp_4042_;
}
else
{
lean_object* v_reuseFailAlloc_4044_; 
v_reuseFailAlloc_4044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4044_, 0, v___x_4041_);
v___x_4043_ = v_reuseFailAlloc_4044_;
goto v_reusejp_4042_;
}
v_reusejp_4042_:
{
return v___x_4043_;
}
}
}
else
{
lean_object* v_a_4046_; lean_object* v___x_4048_; uint8_t v_isShared_4049_; uint8_t v_isSharedCheck_4053_; 
lean_dec_ref(v_b_4028_);
v_a_4046_ = lean_ctor_get(v___x_4035_, 0);
v_isSharedCheck_4053_ = !lean_is_exclusive(v___x_4035_);
if (v_isSharedCheck_4053_ == 0)
{
v___x_4048_ = v___x_4035_;
v_isShared_4049_ = v_isSharedCheck_4053_;
goto v_resetjp_4047_;
}
else
{
lean_inc(v_a_4046_);
lean_dec(v___x_4035_);
v___x_4048_ = lean_box(0);
v_isShared_4049_ = v_isSharedCheck_4053_;
goto v_resetjp_4047_;
}
v_resetjp_4047_:
{
lean_object* v___x_4051_; 
if (v_isShared_4049_ == 0)
{
v___x_4051_ = v___x_4048_;
goto v_reusejp_4050_;
}
else
{
lean_object* v_reuseFailAlloc_4052_; 
v_reuseFailAlloc_4052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4052_, 0, v_a_4046_);
v___x_4051_ = v_reuseFailAlloc_4052_;
goto v_reusejp_4050_;
}
v_reusejp_4050_:
{
return v___x_4051_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed(lean_object* v_pre_4054_, lean_object* v_post_4055_, lean_object* v_usedLetOnly_4056_, lean_object* v_skipConstInApp_4057_, lean_object* v_skipInstances_4058_, lean_object* v___x_4059_, lean_object* v___y_4060_, lean_object* v_b_4061_, lean_object* v_a_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_){
_start:
{
uint8_t v_usedLetOnly_boxed_4068_; uint8_t v_skipConstInApp_boxed_4069_; uint8_t v_skipInstances_boxed_4070_; lean_object* v_res_4071_; 
v_usedLetOnly_boxed_4068_ = lean_unbox(v_usedLetOnly_4056_);
v_skipConstInApp_boxed_4069_ = lean_unbox(v_skipConstInApp_4057_);
v_skipInstances_boxed_4070_ = lean_unbox(v_skipInstances_4058_);
v_res_4071_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0(v_pre_4054_, v_post_4055_, v_usedLetOnly_boxed_4068_, v_skipConstInApp_boxed_4069_, v_skipInstances_boxed_4070_, v___x_4059_, v___y_4060_, v_b_4061_, v_a_4062_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_);
lean_dec(v___y_4066_);
lean_dec_ref(v___y_4065_);
lean_dec(v___y_4064_);
lean_dec_ref(v___y_4063_);
lean_dec(v_a_4062_);
lean_dec(v___y_4060_);
return v_res_4071_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg(lean_object* v_upperBound_4072_, lean_object* v___x_4073_, lean_object* v_pre_4074_, lean_object* v_post_4075_, uint8_t v_usedLetOnly_4076_, uint8_t v_skipConstInApp_4077_, uint8_t v_skipInstances_4078_, lean_object* v_a_4079_, lean_object* v_b_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_){
_start:
{
lean_object* v___y_4088_; uint8_t v___x_4111_; 
v___x_4111_ = lean_nat_dec_lt(v_a_4079_, v_upperBound_4072_);
if (v___x_4111_ == 0)
{
lean_object* v___x_4112_; 
lean_dec(v_a_4079_);
lean_dec_ref(v_post_4075_);
lean_dec_ref(v_pre_4074_);
v___x_4112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4112_, 0, v_b_4080_);
return v___x_4112_;
}
else
{
lean_object* v___x_4113_; lean_object* v___x_4114_; uint8_t v___x_4115_; 
v___x_4113_ = lean_array_fget_borrowed(v_b_4080_, v_a_4079_);
v___x_4114_ = lean_array_get_size(v___x_4073_);
v___x_4115_ = lean_nat_dec_lt(v_a_4079_, v___x_4114_);
if (v___x_4115_ == 0)
{
lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___f_4119_; 
lean_inc(v___x_4113_);
v___x_4116_ = lean_box(v_usedLetOnly_4076_);
v___x_4117_ = lean_box(v_skipConstInApp_4077_);
v___x_4118_ = lean_box(v_skipInstances_4078_);
lean_inc(v_a_4079_);
lean_inc(v___y_4081_);
lean_inc_ref(v_post_4075_);
lean_inc_ref(v_pre_4074_);
v___f_4119_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_4119_, 0, v_pre_4074_);
lean_closure_set(v___f_4119_, 1, v_post_4075_);
lean_closure_set(v___f_4119_, 2, v___x_4116_);
lean_closure_set(v___f_4119_, 3, v___x_4117_);
lean_closure_set(v___f_4119_, 4, v___x_4118_);
lean_closure_set(v___f_4119_, 5, v___x_4113_);
lean_closure_set(v___f_4119_, 6, v___y_4081_);
lean_closure_set(v___f_4119_, 7, v_b_4080_);
lean_closure_set(v___f_4119_, 8, v_a_4079_);
v___y_4088_ = v___f_4119_;
goto v___jp_4087_;
}
else
{
lean_object* v___x_4120_; uint8_t v_isInstance_4121_; 
v___x_4120_ = lean_array_fget_borrowed(v___x_4073_, v_a_4079_);
v_isInstance_4121_ = lean_ctor_get_uint8(v___x_4120_, sizeof(void*)*1 + 4);
if (v_isInstance_4121_ == 0)
{
lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___f_4125_; 
lean_inc(v___x_4113_);
v___x_4122_ = lean_box(v_usedLetOnly_4076_);
v___x_4123_ = lean_box(v_skipConstInApp_4077_);
v___x_4124_ = lean_box(v_skipInstances_4078_);
lean_inc(v_a_4079_);
lean_inc(v___y_4081_);
lean_inc_ref(v_post_4075_);
lean_inc_ref(v_pre_4074_);
v___f_4125_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_4125_, 0, v_pre_4074_);
lean_closure_set(v___f_4125_, 1, v_post_4075_);
lean_closure_set(v___f_4125_, 2, v___x_4122_);
lean_closure_set(v___f_4125_, 3, v___x_4123_);
lean_closure_set(v___f_4125_, 4, v___x_4124_);
lean_closure_set(v___f_4125_, 5, v___x_4113_);
lean_closure_set(v___f_4125_, 6, v___y_4081_);
lean_closure_set(v___f_4125_, 7, v_b_4080_);
lean_closure_set(v___f_4125_, 8, v_a_4079_);
v___y_4088_ = v___f_4125_;
goto v___jp_4087_;
}
else
{
lean_object* v___x_4126_; lean_object* v___f_4127_; 
v___x_4126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4126_, 0, v_b_4080_);
v___f_4127_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_4127_, 0, v___x_4126_);
v___y_4088_ = v___f_4127_;
goto v___jp_4087_;
}
}
}
v___jp_4087_:
{
lean_object* v___x_4089_; 
lean_inc(v___y_4085_);
lean_inc_ref(v___y_4084_);
lean_inc(v___y_4083_);
lean_inc_ref(v___y_4082_);
v___x_4089_ = lean_apply_5(v___y_4088_, v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_, lean_box(0));
if (lean_obj_tag(v___x_4089_) == 0)
{
lean_object* v_a_4090_; lean_object* v___x_4092_; uint8_t v_isShared_4093_; uint8_t v_isSharedCheck_4102_; 
v_a_4090_ = lean_ctor_get(v___x_4089_, 0);
v_isSharedCheck_4102_ = !lean_is_exclusive(v___x_4089_);
if (v_isSharedCheck_4102_ == 0)
{
v___x_4092_ = v___x_4089_;
v_isShared_4093_ = v_isSharedCheck_4102_;
goto v_resetjp_4091_;
}
else
{
lean_inc(v_a_4090_);
lean_dec(v___x_4089_);
v___x_4092_ = lean_box(0);
v_isShared_4093_ = v_isSharedCheck_4102_;
goto v_resetjp_4091_;
}
v_resetjp_4091_:
{
if (lean_obj_tag(v_a_4090_) == 0)
{
lean_object* v_a_4094_; lean_object* v___x_4096_; 
lean_dec(v_a_4079_);
lean_dec_ref(v_post_4075_);
lean_dec_ref(v_pre_4074_);
v_a_4094_ = lean_ctor_get(v_a_4090_, 0);
lean_inc(v_a_4094_);
lean_dec_ref_known(v_a_4090_, 1);
if (v_isShared_4093_ == 0)
{
lean_ctor_set(v___x_4092_, 0, v_a_4094_);
v___x_4096_ = v___x_4092_;
goto v_reusejp_4095_;
}
else
{
lean_object* v_reuseFailAlloc_4097_; 
v_reuseFailAlloc_4097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4097_, 0, v_a_4094_);
v___x_4096_ = v_reuseFailAlloc_4097_;
goto v_reusejp_4095_;
}
v_reusejp_4095_:
{
return v___x_4096_;
}
}
else
{
lean_object* v_a_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; 
lean_del_object(v___x_4092_);
v_a_4098_ = lean_ctor_get(v_a_4090_, 0);
lean_inc(v_a_4098_);
lean_dec_ref_known(v_a_4090_, 1);
v___x_4099_ = lean_unsigned_to_nat(1u);
v___x_4100_ = lean_nat_add(v_a_4079_, v___x_4099_);
lean_dec(v_a_4079_);
v_a_4079_ = v___x_4100_;
v_b_4080_ = v_a_4098_;
goto _start;
}
}
}
else
{
lean_object* v_a_4103_; lean_object* v___x_4105_; uint8_t v_isShared_4106_; uint8_t v_isSharedCheck_4110_; 
lean_dec(v_a_4079_);
lean_dec_ref(v_post_4075_);
lean_dec_ref(v_pre_4074_);
v_a_4103_ = lean_ctor_get(v___x_4089_, 0);
v_isSharedCheck_4110_ = !lean_is_exclusive(v___x_4089_);
if (v_isSharedCheck_4110_ == 0)
{
v___x_4105_ = v___x_4089_;
v_isShared_4106_ = v_isSharedCheck_4110_;
goto v_resetjp_4104_;
}
else
{
lean_inc(v_a_4103_);
lean_dec(v___x_4089_);
v___x_4105_ = lean_box(0);
v_isShared_4106_ = v_isSharedCheck_4110_;
goto v_resetjp_4104_;
}
v_resetjp_4104_:
{
lean_object* v___x_4108_; 
if (v_isShared_4106_ == 0)
{
v___x_4108_ = v___x_4105_;
goto v_reusejp_4107_;
}
else
{
lean_object* v_reuseFailAlloc_4109_; 
v_reuseFailAlloc_4109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4109_, 0, v_a_4103_);
v___x_4108_ = v_reuseFailAlloc_4109_;
goto v_reusejp_4107_;
}
v_reusejp_4107_:
{
return v___x_4108_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__8(uint8_t v_skipInstances_4128_, lean_object* v_pre_4129_, lean_object* v_post_4130_, uint8_t v_usedLetOnly_4131_, uint8_t v_skipConstInApp_4132_, lean_object* v_x_4133_, lean_object* v_x_4134_, lean_object* v_x_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_){
_start:
{
lean_object* v_f_4143_; lean_object* v___y_4144_; lean_object* v___y_4145_; lean_object* v___y_4146_; lean_object* v___y_4147_; lean_object* v___y_4148_; 
if (lean_obj_tag(v_x_4133_) == 5)
{
lean_object* v_fn_4191_; lean_object* v_arg_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; 
v_fn_4191_ = lean_ctor_get(v_x_4133_, 0);
lean_inc_ref(v_fn_4191_);
v_arg_4192_ = lean_ctor_get(v_x_4133_, 1);
lean_inc_ref(v_arg_4192_);
lean_dec_ref_known(v_x_4133_, 2);
v___x_4193_ = lean_array_set(v_x_4134_, v_x_4135_, v_arg_4192_);
v___x_4194_ = lean_unsigned_to_nat(1u);
v___x_4195_ = lean_nat_sub(v_x_4135_, v___x_4194_);
lean_dec(v_x_4135_);
v_x_4133_ = v_fn_4191_;
v_x_4134_ = v___x_4193_;
v_x_4135_ = v___x_4195_;
goto _start;
}
else
{
lean_dec(v_x_4135_);
if (v_skipConstInApp_4132_ == 0)
{
goto v___jp_4188_;
}
else
{
uint8_t v___x_4197_; 
v___x_4197_ = l_Lean_Expr_isConst(v_x_4133_);
if (v___x_4197_ == 0)
{
goto v___jp_4188_;
}
else
{
v_f_4143_ = v_x_4133_;
v___y_4144_ = v___y_4136_;
v___y_4145_ = v___y_4137_;
v___y_4146_ = v___y_4138_;
v___y_4147_ = v___y_4139_;
v___y_4148_ = v___y_4140_;
goto v___jp_4142_;
}
}
}
v___jp_4142_:
{
if (v_skipInstances_4128_ == 0)
{
size_t v_sz_4149_; size_t v___x_4150_; lean_object* v___x_4151_; 
v_sz_4149_ = lean_array_size(v_x_4134_);
v___x_4150_ = ((size_t)0ULL);
lean_inc_ref(v_post_4130_);
lean_inc_ref(v_pre_4129_);
v___x_4151_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__2(v_pre_4129_, v_post_4130_, v_usedLetOnly_4131_, v_skipConstInApp_4132_, v_skipInstances_4128_, v_sz_4149_, v___x_4150_, v_x_4134_, v___y_4144_, v___y_4145_, v___y_4146_, v___y_4147_, v___y_4148_);
if (lean_obj_tag(v___x_4151_) == 0)
{
lean_object* v_a_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; 
v_a_4152_ = lean_ctor_get(v___x_4151_, 0);
lean_inc(v_a_4152_);
lean_dec_ref_known(v___x_4151_, 1);
v___x_4153_ = l_Lean_mkAppN(v_f_4143_, v_a_4152_);
lean_dec(v_a_4152_);
v___x_4154_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4129_, v_post_4130_, v_usedLetOnly_4131_, v_skipConstInApp_4132_, v_skipInstances_4128_, v___x_4153_, v___y_4144_, v___y_4145_, v___y_4146_, v___y_4147_, v___y_4148_);
return v___x_4154_;
}
else
{
lean_object* v_a_4155_; lean_object* v___x_4157_; uint8_t v_isShared_4158_; uint8_t v_isSharedCheck_4162_; 
lean_dec_ref(v_f_4143_);
lean_dec_ref(v_post_4130_);
lean_dec_ref(v_pre_4129_);
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
lean_object* v___x_4163_; lean_object* v___x_4164_; 
v___x_4163_ = lean_array_get_size(v_x_4134_);
lean_inc_ref(v_f_4143_);
v___x_4164_ = l_Lean_Meta_getFunInfoNArgs(v_f_4143_, v___x_4163_, v___y_4145_, v___y_4146_, v___y_4147_, v___y_4148_);
if (lean_obj_tag(v___x_4164_) == 0)
{
lean_object* v_a_4165_; lean_object* v_paramInfo_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; 
v_a_4165_ = lean_ctor_get(v___x_4164_, 0);
lean_inc(v_a_4165_);
lean_dec_ref_known(v___x_4164_, 1);
v_paramInfo_4166_ = lean_ctor_get(v_a_4165_, 0);
lean_inc_ref(v_paramInfo_4166_);
lean_dec(v_a_4165_);
v___x_4167_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_4130_);
lean_inc_ref(v_pre_4129_);
v___x_4168_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg(v___x_4163_, v_paramInfo_4166_, v_pre_4129_, v_post_4130_, v_usedLetOnly_4131_, v_skipConstInApp_4132_, v_skipInstances_4128_, v___x_4167_, v_x_4134_, v___y_4144_, v___y_4145_, v___y_4146_, v___y_4147_, v___y_4148_);
lean_dec_ref(v_paramInfo_4166_);
if (lean_obj_tag(v___x_4168_) == 0)
{
lean_object* v_a_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; 
v_a_4169_ = lean_ctor_get(v___x_4168_, 0);
lean_inc(v_a_4169_);
lean_dec_ref_known(v___x_4168_, 1);
v___x_4170_ = l_Lean_mkAppN(v_f_4143_, v_a_4169_);
lean_dec(v_a_4169_);
v___x_4171_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4129_, v_post_4130_, v_usedLetOnly_4131_, v_skipConstInApp_4132_, v_skipInstances_4128_, v___x_4170_, v___y_4144_, v___y_4145_, v___y_4146_, v___y_4147_, v___y_4148_);
return v___x_4171_;
}
else
{
lean_object* v_a_4172_; lean_object* v___x_4174_; uint8_t v_isShared_4175_; uint8_t v_isSharedCheck_4179_; 
lean_dec_ref(v_f_4143_);
lean_dec_ref(v_post_4130_);
lean_dec_ref(v_pre_4129_);
v_a_4172_ = lean_ctor_get(v___x_4168_, 0);
v_isSharedCheck_4179_ = !lean_is_exclusive(v___x_4168_);
if (v_isSharedCheck_4179_ == 0)
{
v___x_4174_ = v___x_4168_;
v_isShared_4175_ = v_isSharedCheck_4179_;
goto v_resetjp_4173_;
}
else
{
lean_inc(v_a_4172_);
lean_dec(v___x_4168_);
v___x_4174_ = lean_box(0);
v_isShared_4175_ = v_isSharedCheck_4179_;
goto v_resetjp_4173_;
}
v_resetjp_4173_:
{
lean_object* v___x_4177_; 
if (v_isShared_4175_ == 0)
{
v___x_4177_ = v___x_4174_;
goto v_reusejp_4176_;
}
else
{
lean_object* v_reuseFailAlloc_4178_; 
v_reuseFailAlloc_4178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4178_, 0, v_a_4172_);
v___x_4177_ = v_reuseFailAlloc_4178_;
goto v_reusejp_4176_;
}
v_reusejp_4176_:
{
return v___x_4177_;
}
}
}
}
else
{
lean_object* v_a_4180_; lean_object* v___x_4182_; uint8_t v_isShared_4183_; uint8_t v_isSharedCheck_4187_; 
lean_dec_ref(v_f_4143_);
lean_dec_ref(v_x_4134_);
lean_dec_ref(v_post_4130_);
lean_dec_ref(v_pre_4129_);
v_a_4180_ = lean_ctor_get(v___x_4164_, 0);
v_isSharedCheck_4187_ = !lean_is_exclusive(v___x_4164_);
if (v_isSharedCheck_4187_ == 0)
{
v___x_4182_ = v___x_4164_;
v_isShared_4183_ = v_isSharedCheck_4187_;
goto v_resetjp_4181_;
}
else
{
lean_inc(v_a_4180_);
lean_dec(v___x_4164_);
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
}
v___jp_4188_:
{
lean_object* v___x_4189_; 
lean_inc_ref(v_post_4130_);
lean_inc_ref(v_pre_4129_);
v___x_4189_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4129_, v_post_4130_, v_usedLetOnly_4131_, v_skipConstInApp_4132_, v_skipInstances_4128_, v_x_4133_, v___y_4136_, v___y_4137_, v___y_4138_, v___y_4139_, v___y_4140_);
if (lean_obj_tag(v___x_4189_) == 0)
{
lean_object* v_a_4190_; 
v_a_4190_ = lean_ctor_get(v___x_4189_, 0);
lean_inc(v_a_4190_);
lean_dec_ref_known(v___x_4189_, 1);
v_f_4143_ = v_a_4190_;
v___y_4144_ = v___y_4136_;
v___y_4145_ = v___y_4137_;
v___y_4146_ = v___y_4138_;
v___y_4147_ = v___y_4139_;
v___y_4148_ = v___y_4140_;
goto v___jp_4142_;
}
else
{
lean_dec_ref(v_x_4134_);
lean_dec_ref(v_post_4130_);
lean_dec_ref(v_pre_4129_);
return v___x_4189_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1(lean_object* v___x_4198_, lean_object* v_pre_4199_, lean_object* v_e_4200_, lean_object* v_post_4201_, uint8_t v_usedLetOnly_4202_, uint8_t v_skipConstInApp_4203_, uint8_t v_skipInstances_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_){
_start:
{
lean_object* v___x_4211_; 
v___x_4211_ = l_Lean_Core_checkSystem(v___x_4198_, v___y_4208_, v___y_4209_);
if (lean_obj_tag(v___x_4211_) == 0)
{
lean_object* v___x_4212_; 
lean_dec_ref_known(v___x_4211_, 1);
lean_inc_ref(v_pre_4199_);
lean_inc(v___y_4209_);
lean_inc_ref(v___y_4208_);
lean_inc(v___y_4207_);
lean_inc_ref(v___y_4206_);
lean_inc_ref(v_e_4200_);
v___x_4212_ = lean_apply_6(v_pre_4199_, v_e_4200_, v___y_4206_, v___y_4207_, v___y_4208_, v___y_4209_, lean_box(0));
if (lean_obj_tag(v___x_4212_) == 0)
{
lean_object* v_a_4213_; lean_object* v___x_4215_; uint8_t v_isShared_4216_; uint8_t v_isSharedCheck_4261_; 
v_a_4213_ = lean_ctor_get(v___x_4212_, 0);
v_isSharedCheck_4261_ = !lean_is_exclusive(v___x_4212_);
if (v_isSharedCheck_4261_ == 0)
{
v___x_4215_ = v___x_4212_;
v_isShared_4216_ = v_isSharedCheck_4261_;
goto v_resetjp_4214_;
}
else
{
lean_inc(v_a_4213_);
lean_dec(v___x_4212_);
v___x_4215_ = lean_box(0);
v_isShared_4216_ = v_isSharedCheck_4261_;
goto v_resetjp_4214_;
}
v_resetjp_4214_:
{
lean_object* v___y_4218_; 
switch(lean_obj_tag(v_a_4213_))
{
case 0:
{
lean_object* v_e_4253_; lean_object* v___x_4255_; 
lean_dec_ref(v_post_4201_);
lean_dec_ref(v_e_4200_);
lean_dec_ref(v_pre_4199_);
v_e_4253_ = lean_ctor_get(v_a_4213_, 0);
lean_inc_ref(v_e_4253_);
lean_dec_ref_known(v_a_4213_, 1);
if (v_isShared_4216_ == 0)
{
lean_ctor_set(v___x_4215_, 0, v_e_4253_);
v___x_4255_ = v___x_4215_;
goto v_reusejp_4254_;
}
else
{
lean_object* v_reuseFailAlloc_4256_; 
v_reuseFailAlloc_4256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4256_, 0, v_e_4253_);
v___x_4255_ = v_reuseFailAlloc_4256_;
goto v_reusejp_4254_;
}
v_reusejp_4254_:
{
return v___x_4255_;
}
}
case 1:
{
lean_object* v_e_4257_; lean_object* v___x_4258_; 
lean_del_object(v___x_4215_);
lean_dec_ref(v_e_4200_);
v_e_4257_ = lean_ctor_get(v_a_4213_, 0);
lean_inc_ref(v_e_4257_);
lean_dec_ref_known(v_a_4213_, 1);
v___x_4258_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4199_, v_post_4201_, v_usedLetOnly_4202_, v_skipConstInApp_4203_, v_skipInstances_4204_, v_e_4257_, v___y_4205_, v___y_4206_, v___y_4207_, v___y_4208_, v___y_4209_);
return v___x_4258_;
}
default: 
{
lean_object* v_e_x3f_4259_; 
lean_del_object(v___x_4215_);
v_e_x3f_4259_ = lean_ctor_get(v_a_4213_, 0);
lean_inc(v_e_x3f_4259_);
lean_dec_ref_known(v_a_4213_, 1);
if (lean_obj_tag(v_e_x3f_4259_) == 0)
{
v___y_4218_ = v_e_4200_;
goto v___jp_4217_;
}
else
{
lean_object* v_val_4260_; 
lean_dec_ref(v_e_4200_);
v_val_4260_ = lean_ctor_get(v_e_x3f_4259_, 0);
lean_inc(v_val_4260_);
lean_dec_ref_known(v_e_x3f_4259_, 1);
v___y_4218_ = v_val_4260_;
goto v___jp_4217_;
}
}
}
v___jp_4217_:
{
switch(lean_obj_tag(v___y_4218_))
{
case 7:
{
lean_object* v___x_4219_; lean_object* v___x_4220_; 
v___x_4219_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_4220_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5(v_pre_4199_, v_post_4201_, v_usedLetOnly_4202_, v_skipConstInApp_4203_, v_skipInstances_4204_, v___x_4219_, v___y_4218_, v___y_4205_, v___y_4206_, v___y_4207_, v___y_4208_, v___y_4209_);
return v___x_4220_;
}
case 6:
{
lean_object* v___x_4221_; lean_object* v___x_4222_; 
v___x_4221_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_4222_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6(v_pre_4199_, v_post_4201_, v_usedLetOnly_4202_, v_skipConstInApp_4203_, v_skipInstances_4204_, v___x_4221_, v___y_4218_, v___y_4205_, v___y_4206_, v___y_4207_, v___y_4208_, v___y_4209_);
return v___x_4222_;
}
case 8:
{
lean_object* v___x_4223_; lean_object* v___x_4224_; 
v___x_4223_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___redArg___lam__11___closed__0));
v___x_4224_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7(v_pre_4199_, v_post_4201_, v_usedLetOnly_4202_, v_skipConstInApp_4203_, v_skipInstances_4204_, v___x_4223_, v___y_4218_, v___y_4205_, v___y_4206_, v___y_4207_, v___y_4208_, v___y_4209_);
return v___x_4224_;
}
case 5:
{
lean_object* v_dummy_4225_; lean_object* v_nargs_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; 
v_dummy_4225_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__18___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__18___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__18___closed__0);
v_nargs_4226_ = l_Lean_Expr_getAppNumArgs(v___y_4218_);
lean_inc(v_nargs_4226_);
v___x_4227_ = lean_mk_array(v_nargs_4226_, v_dummy_4225_);
v___x_4228_ = lean_unsigned_to_nat(1u);
v___x_4229_ = lean_nat_sub(v_nargs_4226_, v___x_4228_);
lean_dec(v_nargs_4226_);
v___x_4230_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__8(v_skipInstances_4204_, v_pre_4199_, v_post_4201_, v_usedLetOnly_4202_, v_skipConstInApp_4203_, v___y_4218_, v___x_4227_, v___x_4229_, v___y_4205_, v___y_4206_, v___y_4207_, v___y_4208_, v___y_4209_);
return v___x_4230_;
}
case 10:
{
lean_object* v_data_4231_; lean_object* v_expr_4232_; lean_object* v___x_4233_; 
v_data_4231_ = lean_ctor_get(v___y_4218_, 0);
v_expr_4232_ = lean_ctor_get(v___y_4218_, 1);
lean_inc_ref(v_expr_4232_);
lean_inc_ref(v_post_4201_);
lean_inc_ref(v_pre_4199_);
v___x_4233_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4199_, v_post_4201_, v_usedLetOnly_4202_, v_skipConstInApp_4203_, v_skipInstances_4204_, v_expr_4232_, v___y_4205_, v___y_4206_, v___y_4207_, v___y_4208_, v___y_4209_);
if (lean_obj_tag(v___x_4233_) == 0)
{
lean_object* v_a_4234_; size_t v___x_4235_; size_t v___x_4236_; uint8_t v___x_4237_; 
v_a_4234_ = lean_ctor_get(v___x_4233_, 0);
lean_inc(v_a_4234_);
lean_dec_ref_known(v___x_4233_, 1);
v___x_4235_ = lean_ptr_addr(v_expr_4232_);
v___x_4236_ = lean_ptr_addr(v_a_4234_);
v___x_4237_ = lean_usize_dec_eq(v___x_4235_, v___x_4236_);
if (v___x_4237_ == 0)
{
lean_object* v___x_4238_; lean_object* v___x_4239_; 
lean_inc(v_data_4231_);
lean_dec_ref_known(v___y_4218_, 2);
v___x_4238_ = l_Lean_Expr_mdata___override(v_data_4231_, v_a_4234_);
v___x_4239_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4199_, v_post_4201_, v_usedLetOnly_4202_, v_skipConstInApp_4203_, v_skipInstances_4204_, v___x_4238_, v___y_4205_, v___y_4206_, v___y_4207_, v___y_4208_, v___y_4209_);
return v___x_4239_;
}
else
{
lean_object* v___x_4240_; 
lean_dec(v_a_4234_);
v___x_4240_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4199_, v_post_4201_, v_usedLetOnly_4202_, v_skipConstInApp_4203_, v_skipInstances_4204_, v___y_4218_, v___y_4205_, v___y_4206_, v___y_4207_, v___y_4208_, v___y_4209_);
return v___x_4240_;
}
}
else
{
lean_dec_ref_known(v___y_4218_, 2);
lean_dec_ref(v_post_4201_);
lean_dec_ref(v_pre_4199_);
return v___x_4233_;
}
}
case 11:
{
lean_object* v_typeName_4241_; lean_object* v_idx_4242_; lean_object* v_struct_4243_; lean_object* v___x_4244_; 
v_typeName_4241_ = lean_ctor_get(v___y_4218_, 0);
v_idx_4242_ = lean_ctor_get(v___y_4218_, 1);
v_struct_4243_ = lean_ctor_get(v___y_4218_, 2);
lean_inc_ref(v_struct_4243_);
lean_inc_ref(v_post_4201_);
lean_inc_ref(v_pre_4199_);
v___x_4244_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4199_, v_post_4201_, v_usedLetOnly_4202_, v_skipConstInApp_4203_, v_skipInstances_4204_, v_struct_4243_, v___y_4205_, v___y_4206_, v___y_4207_, v___y_4208_, v___y_4209_);
if (lean_obj_tag(v___x_4244_) == 0)
{
lean_object* v_a_4245_; size_t v___x_4246_; size_t v___x_4247_; uint8_t v___x_4248_; 
v_a_4245_ = lean_ctor_get(v___x_4244_, 0);
lean_inc(v_a_4245_);
lean_dec_ref_known(v___x_4244_, 1);
v___x_4246_ = lean_ptr_addr(v_struct_4243_);
v___x_4247_ = lean_ptr_addr(v_a_4245_);
v___x_4248_ = lean_usize_dec_eq(v___x_4246_, v___x_4247_);
if (v___x_4248_ == 0)
{
lean_object* v___x_4249_; lean_object* v___x_4250_; 
lean_inc(v_idx_4242_);
lean_inc(v_typeName_4241_);
lean_dec_ref_known(v___y_4218_, 3);
v___x_4249_ = l_Lean_Expr_proj___override(v_typeName_4241_, v_idx_4242_, v_a_4245_);
v___x_4250_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4199_, v_post_4201_, v_usedLetOnly_4202_, v_skipConstInApp_4203_, v_skipInstances_4204_, v___x_4249_, v___y_4205_, v___y_4206_, v___y_4207_, v___y_4208_, v___y_4209_);
return v___x_4250_;
}
else
{
lean_object* v___x_4251_; 
lean_dec(v_a_4245_);
v___x_4251_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4199_, v_post_4201_, v_usedLetOnly_4202_, v_skipConstInApp_4203_, v_skipInstances_4204_, v___y_4218_, v___y_4205_, v___y_4206_, v___y_4207_, v___y_4208_, v___y_4209_);
return v___x_4251_;
}
}
else
{
lean_dec_ref_known(v___y_4218_, 3);
lean_dec_ref(v_post_4201_);
lean_dec_ref(v_pre_4199_);
return v___x_4244_;
}
}
default: 
{
lean_object* v___x_4252_; 
v___x_4252_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4199_, v_post_4201_, v_usedLetOnly_4202_, v_skipConstInApp_4203_, v_skipInstances_4204_, v___y_4218_, v___y_4205_, v___y_4206_, v___y_4207_, v___y_4208_, v___y_4209_);
return v___x_4252_;
}
}
}
}
}
else
{
lean_object* v_a_4262_; lean_object* v___x_4264_; uint8_t v_isShared_4265_; uint8_t v_isSharedCheck_4269_; 
lean_dec_ref(v_post_4201_);
lean_dec_ref(v_e_4200_);
lean_dec_ref(v_pre_4199_);
v_a_4262_ = lean_ctor_get(v___x_4212_, 0);
v_isSharedCheck_4269_ = !lean_is_exclusive(v___x_4212_);
if (v_isSharedCheck_4269_ == 0)
{
v___x_4264_ = v___x_4212_;
v_isShared_4265_ = v_isSharedCheck_4269_;
goto v_resetjp_4263_;
}
else
{
lean_inc(v_a_4262_);
lean_dec(v___x_4212_);
v___x_4264_ = lean_box(0);
v_isShared_4265_ = v_isSharedCheck_4269_;
goto v_resetjp_4263_;
}
v_resetjp_4263_:
{
lean_object* v___x_4267_; 
if (v_isShared_4265_ == 0)
{
v___x_4267_ = v___x_4264_;
goto v_reusejp_4266_;
}
else
{
lean_object* v_reuseFailAlloc_4268_; 
v_reuseFailAlloc_4268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4268_, 0, v_a_4262_);
v___x_4267_ = v_reuseFailAlloc_4268_;
goto v_reusejp_4266_;
}
v_reusejp_4266_:
{
return v___x_4267_;
}
}
}
}
else
{
lean_object* v_a_4270_; lean_object* v___x_4272_; uint8_t v_isShared_4273_; uint8_t v_isSharedCheck_4277_; 
lean_dec_ref(v_post_4201_);
lean_dec_ref(v_e_4200_);
lean_dec_ref(v_pre_4199_);
v_a_4270_ = lean_ctor_get(v___x_4211_, 0);
v_isSharedCheck_4277_ = !lean_is_exclusive(v___x_4211_);
if (v_isSharedCheck_4277_ == 0)
{
v___x_4272_ = v___x_4211_;
v_isShared_4273_ = v_isSharedCheck_4277_;
goto v_resetjp_4271_;
}
else
{
lean_inc(v_a_4270_);
lean_dec(v___x_4211_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1___boxed(lean_object* v___x_4278_, lean_object* v_pre_4279_, lean_object* v_e_4280_, lean_object* v_post_4281_, lean_object* v_usedLetOnly_4282_, lean_object* v_skipConstInApp_4283_, lean_object* v_skipInstances_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_){
_start:
{
uint8_t v_usedLetOnly_boxed_4291_; uint8_t v_skipConstInApp_boxed_4292_; uint8_t v_skipInstances_boxed_4293_; lean_object* v_res_4294_; 
v_usedLetOnly_boxed_4291_ = lean_unbox(v_usedLetOnly_4282_);
v_skipConstInApp_boxed_4292_ = lean_unbox(v_skipConstInApp_4283_);
v_skipInstances_boxed_4293_ = lean_unbox(v_skipInstances_4284_);
v_res_4294_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1(v___x_4278_, v_pre_4279_, v_e_4280_, v_post_4281_, v_usedLetOnly_boxed_4291_, v_skipConstInApp_boxed_4292_, v_skipInstances_boxed_4293_, v___y_4285_, v___y_4286_, v___y_4287_, v___y_4288_, v___y_4289_);
lean_dec(v___y_4289_);
lean_dec_ref(v___y_4288_);
lean_dec(v___y_4287_);
lean_dec_ref(v___y_4286_);
lean_dec(v___y_4285_);
return v_res_4294_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(lean_object* v_pre_4295_, lean_object* v_post_4296_, uint8_t v_usedLetOnly_4297_, uint8_t v_skipConstInApp_4298_, uint8_t v_skipInstances_4299_, lean_object* v_e_4300_, lean_object* v_a_4301_, lean_object* v___y_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_){
_start:
{
lean_object* v___x_4307_; lean_object* v___x_4308_; 
lean_inc(v_a_4301_);
v___x_4307_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_4307_, 0, lean_box(0));
lean_closure_set(v___x_4307_, 1, lean_box(0));
lean_closure_set(v___x_4307_, 2, v_a_4301_);
v___x_4308_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0(lean_box(0), v___x_4307_, v___y_4302_, v___y_4303_, v___y_4304_, v___y_4305_);
if (lean_obj_tag(v___x_4308_) == 0)
{
lean_object* v_a_4309_; lean_object* v___x_4311_; uint8_t v_isShared_4312_; uint8_t v_isSharedCheck_4343_; 
v_a_4309_ = lean_ctor_get(v___x_4308_, 0);
v_isSharedCheck_4343_ = !lean_is_exclusive(v___x_4308_);
if (v_isSharedCheck_4343_ == 0)
{
v___x_4311_ = v___x_4308_;
v_isShared_4312_ = v_isSharedCheck_4343_;
goto v_resetjp_4310_;
}
else
{
lean_inc(v_a_4309_);
lean_dec(v___x_4308_);
v___x_4311_ = lean_box(0);
v_isShared_4312_ = v_isSharedCheck_4343_;
goto v_resetjp_4310_;
}
v_resetjp_4310_:
{
lean_object* v___x_4313_; 
v___x_4313_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0_spec__1___redArg(v_a_4309_, v_e_4300_);
lean_dec(v_a_4309_);
if (lean_obj_tag(v___x_4313_) == 0)
{
lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___f_4318_; lean_object* v___x_4319_; 
lean_del_object(v___x_4311_);
v___x_4314_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__20___closed__0));
v___x_4315_ = lean_box(v_usedLetOnly_4297_);
v___x_4316_ = lean_box(v_skipConstInApp_4298_);
v___x_4317_ = lean_box(v_skipInstances_4299_);
lean_inc_ref(v_e_4300_);
v___f_4318_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__1___boxed), 13, 7);
lean_closure_set(v___f_4318_, 0, v___x_4314_);
lean_closure_set(v___f_4318_, 1, v_pre_4295_);
lean_closure_set(v___f_4318_, 2, v_e_4300_);
lean_closure_set(v___f_4318_, 3, v_post_4296_);
lean_closure_set(v___f_4318_, 4, v___x_4315_);
lean_closure_set(v___f_4318_, 5, v___x_4316_);
lean_closure_set(v___f_4318_, 6, v___x_4317_);
v___x_4319_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg(v___f_4318_, v_a_4301_, v___y_4302_, v___y_4303_, v___y_4304_, v___y_4305_);
if (lean_obj_tag(v___x_4319_) == 0)
{
lean_object* v_a_4320_; lean_object* v___f_4321_; lean_object* v___x_4322_; 
v_a_4320_ = lean_ctor_get(v___x_4319_, 0);
lean_inc_n(v_a_4320_, 2);
lean_dec_ref_known(v___x_4319_, 1);
lean_inc(v_a_4301_);
v___f_4321_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_4321_, 0, v_a_4301_);
lean_closure_set(v___f_4321_, 1, v_e_4300_);
lean_closure_set(v___f_4321_, 2, v_a_4320_);
v___x_4322_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___lam__0(lean_box(0), v___f_4321_, v___y_4302_, v___y_4303_, v___y_4304_, v___y_4305_);
if (lean_obj_tag(v___x_4322_) == 0)
{
lean_object* v___x_4324_; uint8_t v_isShared_4325_; uint8_t v_isSharedCheck_4329_; 
v_isSharedCheck_4329_ = !lean_is_exclusive(v___x_4322_);
if (v_isSharedCheck_4329_ == 0)
{
lean_object* v_unused_4330_; 
v_unused_4330_ = lean_ctor_get(v___x_4322_, 0);
lean_dec(v_unused_4330_);
v___x_4324_ = v___x_4322_;
v_isShared_4325_ = v_isSharedCheck_4329_;
goto v_resetjp_4323_;
}
else
{
lean_dec(v___x_4322_);
v___x_4324_ = lean_box(0);
v_isShared_4325_ = v_isSharedCheck_4329_;
goto v_resetjp_4323_;
}
v_resetjp_4323_:
{
lean_object* v___x_4327_; 
if (v_isShared_4325_ == 0)
{
lean_ctor_set(v___x_4324_, 0, v_a_4320_);
v___x_4327_ = v___x_4324_;
goto v_reusejp_4326_;
}
else
{
lean_object* v_reuseFailAlloc_4328_; 
v_reuseFailAlloc_4328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4328_, 0, v_a_4320_);
v___x_4327_ = v_reuseFailAlloc_4328_;
goto v_reusejp_4326_;
}
v_reusejp_4326_:
{
return v___x_4327_;
}
}
}
else
{
lean_object* v_a_4331_; lean_object* v___x_4333_; uint8_t v_isShared_4334_; uint8_t v_isSharedCheck_4338_; 
lean_dec(v_a_4320_);
v_a_4331_ = lean_ctor_get(v___x_4322_, 0);
v_isSharedCheck_4338_ = !lean_is_exclusive(v___x_4322_);
if (v_isSharedCheck_4338_ == 0)
{
v___x_4333_ = v___x_4322_;
v_isShared_4334_ = v_isSharedCheck_4338_;
goto v_resetjp_4332_;
}
else
{
lean_inc(v_a_4331_);
lean_dec(v___x_4322_);
v___x_4333_ = lean_box(0);
v_isShared_4334_ = v_isSharedCheck_4338_;
goto v_resetjp_4332_;
}
v_resetjp_4332_:
{
lean_object* v___x_4336_; 
if (v_isShared_4334_ == 0)
{
v___x_4336_ = v___x_4333_;
goto v_reusejp_4335_;
}
else
{
lean_object* v_reuseFailAlloc_4337_; 
v_reuseFailAlloc_4337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4337_, 0, v_a_4331_);
v___x_4336_ = v_reuseFailAlloc_4337_;
goto v_reusejp_4335_;
}
v_reusejp_4335_:
{
return v___x_4336_;
}
}
}
}
else
{
lean_dec_ref(v_e_4300_);
return v___x_4319_;
}
}
else
{
lean_object* v_val_4339_; lean_object* v___x_4341_; 
lean_dec_ref(v_e_4300_);
lean_dec_ref(v_post_4296_);
lean_dec_ref(v_pre_4295_);
v_val_4339_ = lean_ctor_get(v___x_4313_, 0);
lean_inc(v_val_4339_);
lean_dec_ref_known(v___x_4313_, 1);
if (v_isShared_4312_ == 0)
{
lean_ctor_set(v___x_4311_, 0, v_val_4339_);
v___x_4341_ = v___x_4311_;
goto v_reusejp_4340_;
}
else
{
lean_object* v_reuseFailAlloc_4342_; 
v_reuseFailAlloc_4342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4342_, 0, v_val_4339_);
v___x_4341_ = v_reuseFailAlloc_4342_;
goto v_reusejp_4340_;
}
v_reusejp_4340_:
{
return v___x_4341_;
}
}
}
}
else
{
lean_object* v_a_4344_; lean_object* v___x_4346_; uint8_t v_isShared_4347_; uint8_t v_isSharedCheck_4351_; 
lean_dec_ref(v_e_4300_);
lean_dec_ref(v_post_4296_);
lean_dec_ref(v_pre_4295_);
v_a_4344_ = lean_ctor_get(v___x_4308_, 0);
v_isSharedCheck_4351_ = !lean_is_exclusive(v___x_4308_);
if (v_isSharedCheck_4351_ == 0)
{
v___x_4346_ = v___x_4308_;
v_isShared_4347_ = v_isSharedCheck_4351_;
goto v_resetjp_4345_;
}
else
{
lean_inc(v_a_4344_);
lean_dec(v___x_4308_);
v___x_4346_ = lean_box(0);
v_isShared_4347_ = v_isSharedCheck_4351_;
goto v_resetjp_4345_;
}
v_resetjp_4345_:
{
lean_object* v___x_4349_; 
if (v_isShared_4347_ == 0)
{
v___x_4349_ = v___x_4346_;
goto v_reusejp_4348_;
}
else
{
lean_object* v_reuseFailAlloc_4350_; 
v_reuseFailAlloc_4350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4350_, 0, v_a_4344_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5(lean_object* v_pre_4352_, lean_object* v_post_4353_, uint8_t v_usedLetOnly_4354_, uint8_t v_skipConstInApp_4355_, uint8_t v_skipInstances_4356_, lean_object* v_fvars_4357_, lean_object* v_e_4358_, lean_object* v_a_4359_, lean_object* v___y_4360_, lean_object* v___y_4361_, lean_object* v___y_4362_, lean_object* v___y_4363_){
_start:
{
if (lean_obj_tag(v_e_4358_) == 7)
{
lean_object* v_binderName_4365_; lean_object* v_binderType_4366_; lean_object* v_body_4367_; uint8_t v_binderInfo_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v___f_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; 
v_binderName_4365_ = lean_ctor_get(v_e_4358_, 0);
lean_inc(v_binderName_4365_);
v_binderType_4366_ = lean_ctor_get(v_e_4358_, 1);
lean_inc_ref(v_binderType_4366_);
v_body_4367_ = lean_ctor_get(v_e_4358_, 2);
lean_inc_ref(v_body_4367_);
v_binderInfo_4368_ = lean_ctor_get_uint8(v_e_4358_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_4358_, 3);
v___x_4369_ = lean_box(v_usedLetOnly_4354_);
v___x_4370_ = lean_box(v_skipConstInApp_4355_);
v___x_4371_ = lean_box(v_skipInstances_4356_);
lean_inc_ref(v_post_4353_);
lean_inc_ref(v_pre_4352_);
lean_inc_ref(v_fvars_4357_);
v___f_4372_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___lam__0___boxed), 14, 7);
lean_closure_set(v___f_4372_, 0, v_fvars_4357_);
lean_closure_set(v___f_4372_, 1, v_pre_4352_);
lean_closure_set(v___f_4372_, 2, v_post_4353_);
lean_closure_set(v___f_4372_, 3, v___x_4369_);
lean_closure_set(v___f_4372_, 4, v___x_4370_);
lean_closure_set(v___f_4372_, 5, v___x_4371_);
lean_closure_set(v___f_4372_, 6, v_body_4367_);
v___x_4373_ = lean_expr_instantiate_rev(v_binderType_4366_, v_fvars_4357_);
lean_dec_ref(v_fvars_4357_);
lean_dec_ref(v_binderType_4366_);
v___x_4374_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4352_, v_post_4353_, v_usedLetOnly_4354_, v_skipConstInApp_4355_, v_skipInstances_4356_, v___x_4373_, v_a_4359_, v___y_4360_, v___y_4361_, v___y_4362_, v___y_4363_);
if (lean_obj_tag(v___x_4374_) == 0)
{
lean_object* v_a_4375_; uint8_t v___x_4376_; lean_object* v___x_4377_; 
v_a_4375_ = lean_ctor_get(v___x_4374_, 0);
lean_inc(v_a_4375_);
lean_dec_ref_known(v___x_4374_, 1);
v___x_4376_ = 0;
v___x_4377_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_binderName_4365_, v_binderInfo_4368_, v_a_4375_, v___f_4372_, v___x_4376_, v_a_4359_, v___y_4360_, v___y_4361_, v___y_4362_, v___y_4363_);
return v___x_4377_;
}
else
{
lean_dec_ref(v___f_4372_);
lean_dec(v_binderName_4365_);
return v___x_4374_;
}
}
else
{
lean_object* v___x_4378_; lean_object* v___x_4379_; 
v___x_4378_ = lean_expr_instantiate_rev(v_e_4358_, v_fvars_4357_);
lean_dec_ref(v_e_4358_);
lean_inc_ref(v_post_4353_);
lean_inc_ref(v_pre_4352_);
v___x_4379_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4352_, v_post_4353_, v_usedLetOnly_4354_, v_skipConstInApp_4355_, v_skipInstances_4356_, v___x_4378_, v_a_4359_, v___y_4360_, v___y_4361_, v___y_4362_, v___y_4363_);
if (lean_obj_tag(v___x_4379_) == 0)
{
lean_object* v_a_4380_; uint8_t v___x_4381_; uint8_t v___x_4382_; uint8_t v___x_4383_; lean_object* v___x_4384_; 
v_a_4380_ = lean_ctor_get(v___x_4379_, 0);
lean_inc(v_a_4380_);
lean_dec_ref_known(v___x_4379_, 1);
v___x_4381_ = 0;
v___x_4382_ = 1;
v___x_4383_ = 1;
v___x_4384_ = l_Lean_Meta_mkForallFVars(v_fvars_4357_, v_a_4380_, v___x_4381_, v_usedLetOnly_4354_, v___x_4382_, v___x_4383_, v___y_4360_, v___y_4361_, v___y_4362_, v___y_4363_);
lean_dec_ref(v_fvars_4357_);
if (lean_obj_tag(v___x_4384_) == 0)
{
lean_object* v_a_4385_; lean_object* v___x_4386_; 
v_a_4385_ = lean_ctor_get(v___x_4384_, 0);
lean_inc(v_a_4385_);
lean_dec_ref_known(v___x_4384_, 1);
v___x_4386_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4352_, v_post_4353_, v_usedLetOnly_4354_, v_skipConstInApp_4355_, v_skipInstances_4356_, v_a_4385_, v_a_4359_, v___y_4360_, v___y_4361_, v___y_4362_, v___y_4363_);
return v___x_4386_;
}
else
{
lean_dec_ref(v_post_4353_);
lean_dec_ref(v_pre_4352_);
return v___x_4384_;
}
}
else
{
lean_dec_ref(v_fvars_4357_);
lean_dec_ref(v_post_4353_);
lean_dec_ref(v_pre_4352_);
return v___x_4379_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___lam__0(lean_object* v_fvars_4387_, lean_object* v_pre_4388_, lean_object* v_post_4389_, uint8_t v_usedLetOnly_4390_, uint8_t v_skipConstInApp_4391_, uint8_t v_skipInstances_4392_, lean_object* v_body_4393_, lean_object* v_x_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_, lean_object* v___y_4397_, lean_object* v___y_4398_, lean_object* v___y_4399_){
_start:
{
lean_object* v___x_4401_; lean_object* v___x_4402_; 
v___x_4401_ = lean_array_push(v_fvars_4387_, v_x_4394_);
v___x_4402_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5(v_pre_4388_, v_post_4389_, v_usedLetOnly_4390_, v_skipConstInApp_4391_, v_skipInstances_4392_, v___x_4401_, v_body_4393_, v___y_4395_, v___y_4396_, v___y_4397_, v___y_4398_, v___y_4399_);
return v___x_4402_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3___boxed(lean_object* v_pre_4403_, lean_object* v_post_4404_, lean_object* v_usedLetOnly_4405_, lean_object* v_skipConstInApp_4406_, lean_object* v_skipInstances_4407_, lean_object* v_e_4408_, lean_object* v_a_4409_, lean_object* v___y_4410_, lean_object* v___y_4411_, lean_object* v___y_4412_, lean_object* v___y_4413_, lean_object* v___y_4414_){
_start:
{
uint8_t v_usedLetOnly_boxed_4415_; uint8_t v_skipConstInApp_boxed_4416_; uint8_t v_skipInstances_boxed_4417_; lean_object* v_res_4418_; 
v_usedLetOnly_boxed_4415_ = lean_unbox(v_usedLetOnly_4405_);
v_skipConstInApp_boxed_4416_ = lean_unbox(v_skipConstInApp_4406_);
v_skipInstances_boxed_4417_ = lean_unbox(v_skipInstances_4407_);
v_res_4418_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__3(v_pre_4403_, v_post_4404_, v_usedLetOnly_boxed_4415_, v_skipConstInApp_boxed_4416_, v_skipInstances_boxed_4417_, v_e_4408_, v_a_4409_, v___y_4410_, v___y_4411_, v___y_4412_, v___y_4413_);
lean_dec(v___y_4413_);
lean_dec_ref(v___y_4412_);
lean_dec(v___y_4411_);
lean_dec_ref(v___y_4410_);
lean_dec(v_a_4409_);
return v_res_4418_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__2___boxed(lean_object* v_pre_4419_, lean_object* v_post_4420_, lean_object* v_usedLetOnly_4421_, lean_object* v_skipConstInApp_4422_, lean_object* v_skipInstances_4423_, lean_object* v_sz_4424_, lean_object* v_i_4425_, lean_object* v_bs_4426_, lean_object* v___y_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_){
_start:
{
uint8_t v_usedLetOnly_boxed_4433_; uint8_t v_skipConstInApp_boxed_4434_; uint8_t v_skipInstances_boxed_4435_; size_t v_sz_boxed_4436_; size_t v_i_boxed_4437_; lean_object* v_res_4438_; 
v_usedLetOnly_boxed_4433_ = lean_unbox(v_usedLetOnly_4421_);
v_skipConstInApp_boxed_4434_ = lean_unbox(v_skipConstInApp_4422_);
v_skipInstances_boxed_4435_ = lean_unbox(v_skipInstances_4423_);
v_sz_boxed_4436_ = lean_unbox_usize(v_sz_4424_);
lean_dec(v_sz_4424_);
v_i_boxed_4437_ = lean_unbox_usize(v_i_4425_);
lean_dec(v_i_4425_);
v_res_4438_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__2(v_pre_4419_, v_post_4420_, v_usedLetOnly_boxed_4433_, v_skipConstInApp_boxed_4434_, v_skipInstances_boxed_4435_, v_sz_boxed_4436_, v_i_boxed_4437_, v_bs_4426_, v___y_4427_, v___y_4428_, v___y_4429_, v___y_4430_, v___y_4431_);
lean_dec(v___y_4431_);
lean_dec_ref(v___y_4430_);
lean_dec(v___y_4429_);
lean_dec_ref(v___y_4428_);
lean_dec(v___y_4427_);
return v_res_4438_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1___boxed(lean_object* v_pre_4439_, lean_object* v_post_4440_, lean_object* v_usedLetOnly_4441_, lean_object* v_skipConstInApp_4442_, lean_object* v_skipInstances_4443_, lean_object* v_e_4444_, lean_object* v_a_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_){
_start:
{
uint8_t v_usedLetOnly_boxed_4451_; uint8_t v_skipConstInApp_boxed_4452_; uint8_t v_skipInstances_boxed_4453_; lean_object* v_res_4454_; 
v_usedLetOnly_boxed_4451_ = lean_unbox(v_usedLetOnly_4441_);
v_skipConstInApp_boxed_4452_ = lean_unbox(v_skipConstInApp_4442_);
v_skipInstances_boxed_4453_ = lean_unbox(v_skipInstances_4443_);
v_res_4454_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4439_, v_post_4440_, v_usedLetOnly_boxed_4451_, v_skipConstInApp_boxed_4452_, v_skipInstances_boxed_4453_, v_e_4444_, v_a_4445_, v___y_4446_, v___y_4447_, v___y_4448_, v___y_4449_);
lean_dec(v___y_4449_);
lean_dec_ref(v___y_4448_);
lean_dec(v___y_4447_);
lean_dec_ref(v___y_4446_);
lean_dec(v_a_4445_);
return v_res_4454_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5___boxed(lean_object* v_pre_4455_, lean_object* v_post_4456_, lean_object* v_usedLetOnly_4457_, lean_object* v_skipConstInApp_4458_, lean_object* v_skipInstances_4459_, lean_object* v_fvars_4460_, lean_object* v_e_4461_, lean_object* v_a_4462_, lean_object* v___y_4463_, lean_object* v___y_4464_, lean_object* v___y_4465_, lean_object* v___y_4466_, lean_object* v___y_4467_){
_start:
{
uint8_t v_usedLetOnly_boxed_4468_; uint8_t v_skipConstInApp_boxed_4469_; uint8_t v_skipInstances_boxed_4470_; lean_object* v_res_4471_; 
v_usedLetOnly_boxed_4468_ = lean_unbox(v_usedLetOnly_4457_);
v_skipConstInApp_boxed_4469_ = lean_unbox(v_skipConstInApp_4458_);
v_skipInstances_boxed_4470_ = lean_unbox(v_skipInstances_4459_);
v_res_4471_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5(v_pre_4455_, v_post_4456_, v_usedLetOnly_boxed_4468_, v_skipConstInApp_boxed_4469_, v_skipInstances_boxed_4470_, v_fvars_4460_, v_e_4461_, v_a_4462_, v___y_4463_, v___y_4464_, v___y_4465_, v___y_4466_);
lean_dec(v___y_4466_);
lean_dec_ref(v___y_4465_);
lean_dec(v___y_4464_);
lean_dec_ref(v___y_4463_);
lean_dec(v_a_4462_);
return v_res_4471_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6___boxed(lean_object* v_pre_4472_, lean_object* v_post_4473_, lean_object* v_usedLetOnly_4474_, lean_object* v_skipConstInApp_4475_, lean_object* v_skipInstances_4476_, lean_object* v_fvars_4477_, lean_object* v_e_4478_, lean_object* v_a_4479_, lean_object* v___y_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_, lean_object* v___y_4483_, lean_object* v___y_4484_){
_start:
{
uint8_t v_usedLetOnly_boxed_4485_; uint8_t v_skipConstInApp_boxed_4486_; uint8_t v_skipInstances_boxed_4487_; lean_object* v_res_4488_; 
v_usedLetOnly_boxed_4485_ = lean_unbox(v_usedLetOnly_4474_);
v_skipConstInApp_boxed_4486_ = lean_unbox(v_skipConstInApp_4475_);
v_skipInstances_boxed_4487_ = lean_unbox(v_skipInstances_4476_);
v_res_4488_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__6(v_pre_4472_, v_post_4473_, v_usedLetOnly_boxed_4485_, v_skipConstInApp_boxed_4486_, v_skipInstances_boxed_4487_, v_fvars_4477_, v_e_4478_, v_a_4479_, v___y_4480_, v___y_4481_, v___y_4482_, v___y_4483_);
lean_dec(v___y_4483_);
lean_dec_ref(v___y_4482_);
lean_dec(v___y_4481_);
lean_dec_ref(v___y_4480_);
lean_dec(v_a_4479_);
return v_res_4488_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7___boxed(lean_object* v_pre_4489_, lean_object* v_post_4490_, lean_object* v_usedLetOnly_4491_, lean_object* v_skipConstInApp_4492_, lean_object* v_skipInstances_4493_, lean_object* v_fvars_4494_, lean_object* v_e_4495_, lean_object* v_a_4496_, lean_object* v___y_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_, lean_object* v___y_4500_, lean_object* v___y_4501_){
_start:
{
uint8_t v_usedLetOnly_boxed_4502_; uint8_t v_skipConstInApp_boxed_4503_; uint8_t v_skipInstances_boxed_4504_; lean_object* v_res_4505_; 
v_usedLetOnly_boxed_4502_ = lean_unbox(v_usedLetOnly_4491_);
v_skipConstInApp_boxed_4503_ = lean_unbox(v_skipConstInApp_4492_);
v_skipInstances_boxed_4504_ = lean_unbox(v_skipInstances_4493_);
v_res_4505_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7(v_pre_4489_, v_post_4490_, v_usedLetOnly_boxed_4502_, v_skipConstInApp_boxed_4503_, v_skipInstances_boxed_4504_, v_fvars_4494_, v_e_4495_, v_a_4496_, v___y_4497_, v___y_4498_, v___y_4499_, v___y_4500_);
lean_dec(v___y_4500_);
lean_dec_ref(v___y_4499_);
lean_dec(v___y_4498_);
lean_dec_ref(v___y_4497_);
lean_dec(v_a_4496_);
return v_res_4505_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_upperBound_4506_, lean_object* v___x_4507_, lean_object* v_pre_4508_, lean_object* v_post_4509_, lean_object* v_usedLetOnly_4510_, lean_object* v_skipConstInApp_4511_, lean_object* v_skipInstances_4512_, lean_object* v_a_4513_, lean_object* v_b_4514_, lean_object* v___y_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_){
_start:
{
uint8_t v_usedLetOnly_boxed_4521_; uint8_t v_skipConstInApp_boxed_4522_; uint8_t v_skipInstances_boxed_4523_; lean_object* v_res_4524_; 
v_usedLetOnly_boxed_4521_ = lean_unbox(v_usedLetOnly_4510_);
v_skipConstInApp_boxed_4522_ = lean_unbox(v_skipConstInApp_4511_);
v_skipInstances_boxed_4523_ = lean_unbox(v_skipInstances_4512_);
v_res_4524_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg(v_upperBound_4506_, v___x_4507_, v_pre_4508_, v_post_4509_, v_usedLetOnly_boxed_4521_, v_skipConstInApp_boxed_4522_, v_skipInstances_boxed_4523_, v_a_4513_, v_b_4514_, v___y_4515_, v___y_4516_, v___y_4517_, v___y_4518_, v___y_4519_);
lean_dec(v___y_4519_);
lean_dec_ref(v___y_4518_);
lean_dec(v___y_4517_);
lean_dec_ref(v___y_4516_);
lean_dec(v___y_4515_);
lean_dec_ref(v___x_4507_);
lean_dec(v_upperBound_4506_);
return v_res_4524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__8___boxed(lean_object* v_skipInstances_4525_, lean_object* v_pre_4526_, lean_object* v_post_4527_, lean_object* v_usedLetOnly_4528_, lean_object* v_skipConstInApp_4529_, lean_object* v_x_4530_, lean_object* v_x_4531_, lean_object* v_x_4532_, lean_object* v___y_4533_, lean_object* v___y_4534_, lean_object* v___y_4535_, lean_object* v___y_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_){
_start:
{
uint8_t v_skipInstances_boxed_4539_; uint8_t v_usedLetOnly_boxed_4540_; uint8_t v_skipConstInApp_boxed_4541_; lean_object* v_res_4542_; 
v_skipInstances_boxed_4539_ = lean_unbox(v_skipInstances_4525_);
v_usedLetOnly_boxed_4540_ = lean_unbox(v_usedLetOnly_4528_);
v_skipConstInApp_boxed_4541_ = lean_unbox(v_skipConstInApp_4529_);
v_res_4542_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__8(v_skipInstances_boxed_4539_, v_pre_4526_, v_post_4527_, v_usedLetOnly_boxed_4540_, v_skipConstInApp_boxed_4541_, v_x_4530_, v_x_4531_, v_x_4532_, v___y_4533_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_);
lean_dec(v___y_4537_);
lean_dec_ref(v___y_4536_);
lean_dec(v___y_4535_);
lean_dec_ref(v___y_4534_);
lean_dec(v___y_4533_);
return v_res_4542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(lean_object* v_input_4543_, lean_object* v_pre_4544_, lean_object* v_post_4545_, uint8_t v_usedLetOnly_4546_, uint8_t v_skipConstInApp_4547_, lean_object* v___y_4548_, lean_object* v___y_4549_, lean_object* v___y_4550_, lean_object* v___y_4551_){
_start:
{
uint8_t v___x_4553_; lean_object* v___x_4554_; lean_object* v___x_4555_; lean_object* v_a_4556_; lean_object* v___x_4557_; 
v___x_4553_ = 0;
v___x_4554_ = lean_obj_once(&l_Lean_Core_transform___redArg___closed__2, &l_Lean_Core_transform___redArg___closed__2_once, _init_l_Lean_Core_transform___redArg___closed__2);
v___x_4555_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0(lean_box(0), v___x_4554_, v___y_4548_, v___y_4549_, v___y_4550_, v___y_4551_);
v_a_4556_ = lean_ctor_get(v___x_4555_, 0);
lean_inc(v_a_4556_);
lean_dec_ref(v___x_4555_);
v___x_4557_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1(v_pre_4544_, v_post_4545_, v_usedLetOnly_4546_, v_skipConstInApp_4547_, v___x_4553_, v_input_4543_, v_a_4556_, v___y_4548_, v___y_4549_, v___y_4550_, v___y_4551_);
if (lean_obj_tag(v___x_4557_) == 0)
{
lean_object* v_a_4558_; lean_object* v___x_4559_; lean_object* v___x_4560_; lean_object* v___x_4562_; uint8_t v_isShared_4563_; uint8_t v_isSharedCheck_4567_; 
v_a_4558_ = lean_ctor_get(v___x_4557_, 0);
lean_inc(v_a_4558_);
lean_dec_ref_known(v___x_4557_, 1);
v___x_4559_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_4559_, 0, lean_box(0));
lean_closure_set(v___x_4559_, 1, lean_box(0));
lean_closure_set(v___x_4559_, 2, v_a_4556_);
v___x_4560_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___lam__0(lean_box(0), v___x_4559_, v___y_4548_, v___y_4549_, v___y_4550_, v___y_4551_);
v_isSharedCheck_4567_ = !lean_is_exclusive(v___x_4560_);
if (v_isSharedCheck_4567_ == 0)
{
lean_object* v_unused_4568_; 
v_unused_4568_ = lean_ctor_get(v___x_4560_, 0);
lean_dec(v_unused_4568_);
v___x_4562_ = v___x_4560_;
v_isShared_4563_ = v_isSharedCheck_4567_;
goto v_resetjp_4561_;
}
else
{
lean_dec(v___x_4560_);
v___x_4562_ = lean_box(0);
v_isShared_4563_ = v_isSharedCheck_4567_;
goto v_resetjp_4561_;
}
v_resetjp_4561_:
{
lean_object* v___x_4565_; 
if (v_isShared_4563_ == 0)
{
lean_ctor_set(v___x_4562_, 0, v_a_4558_);
v___x_4565_ = v___x_4562_;
goto v_reusejp_4564_;
}
else
{
lean_object* v_reuseFailAlloc_4566_; 
v_reuseFailAlloc_4566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4566_, 0, v_a_4558_);
v___x_4565_ = v_reuseFailAlloc_4566_;
goto v_reusejp_4564_;
}
v_reusejp_4564_:
{
return v___x_4565_;
}
}
}
else
{
lean_dec(v_a_4556_);
return v___x_4557_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1___boxed(lean_object* v_input_4569_, lean_object* v_pre_4570_, lean_object* v_post_4571_, lean_object* v_usedLetOnly_4572_, lean_object* v_skipConstInApp_4573_, lean_object* v___y_4574_, lean_object* v___y_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_, lean_object* v___y_4578_){
_start:
{
uint8_t v_usedLetOnly_boxed_4579_; uint8_t v_skipConstInApp_boxed_4580_; lean_object* v_res_4581_; 
v_usedLetOnly_boxed_4579_ = lean_unbox(v_usedLetOnly_4572_);
v_skipConstInApp_boxed_4580_ = lean_unbox(v_skipConstInApp_4573_);
v_res_4581_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(v_input_4569_, v_pre_4570_, v_post_4571_, v_usedLetOnly_boxed_4579_, v_skipConstInApp_boxed_4580_, v___y_4574_, v___y_4575_, v___y_4576_, v___y_4577_);
lean_dec(v___y_4577_);
lean_dec_ref(v___y_4576_);
lean_dec(v___y_4575_);
lean_dec_ref(v___y_4574_);
return v_res_4581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce(lean_object* v_e_4583_, uint8_t v_zetaDelta_4584_, uint8_t v_zetaHave_4585_, uint8_t v_beta_4586_, lean_object* v_a_4587_, lean_object* v_a_4588_, lean_object* v_a_4589_, lean_object* v_a_4590_){
_start:
{
lean_object* v_lctx_4592_; lean_object* v___x_4593_; lean_object* v___x_4594_; lean_object* v___x_4595_; lean_object* v___f_4596_; uint8_t v___x_4597_; 
v_lctx_4592_ = lean_ctor_get(v_a_4587_, 2);
lean_inc_ref(v_lctx_4592_);
v___x_4593_ = lean_local_ctx_num_indices(v_lctx_4592_);
v___x_4594_ = lean_box(v_zetaHave_4585_);
v___x_4595_ = lean_box(v_zetaDelta_4584_);
v___f_4596_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaReduce___lam__0___boxed), 9, 3);
lean_closure_set(v___f_4596_, 0, v___x_4594_);
lean_closure_set(v___f_4596_, 1, v___x_4593_);
lean_closure_set(v___f_4596_, 2, v___x_4595_);
v___x_4597_ = 1;
if (v_beta_4586_ == 0)
{
lean_object* v___f_4598_; lean_object* v___f_4599_; lean_object* v___x_4600_; 
v___f_4598_ = ((lean_object*)(l_Lean_Meta_zetaReduce___closed__0));
v___f_4599_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaReduce___lam__2___boxed), 7, 1);
lean_closure_set(v___f_4599_, 0, v___f_4596_);
v___x_4600_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(v_e_4583_, v___f_4599_, v___f_4598_, v___x_4597_, v_beta_4586_, v_a_4587_, v_a_4588_, v_a_4589_, v_a_4590_);
return v___x_4600_;
}
else
{
lean_object* v___f_4601_; lean_object* v___f_4602_; uint8_t v___x_4603_; lean_object* v___x_4604_; 
v___f_4601_ = ((lean_object*)(l_Lean_Meta_zetaReduce___closed__0));
v___f_4602_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaReduce___lam__4___boxed), 7, 1);
lean_closure_set(v___f_4602_, 0, v___f_4596_);
v___x_4603_ = 0;
v___x_4604_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(v_e_4583_, v___f_4602_, v___f_4601_, v___x_4597_, v___x_4603_, v_a_4587_, v_a_4588_, v_a_4589_, v_a_4590_);
return v___x_4604_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaReduce___boxed(lean_object* v_e_4605_, lean_object* v_zetaDelta_4606_, lean_object* v_zetaHave_4607_, lean_object* v_beta_4608_, lean_object* v_a_4609_, lean_object* v_a_4610_, lean_object* v_a_4611_, lean_object* v_a_4612_, lean_object* v_a_4613_){
_start:
{
uint8_t v_zetaDelta_boxed_4614_; uint8_t v_zetaHave_boxed_4615_; uint8_t v_beta_boxed_4616_; lean_object* v_res_4617_; 
v_zetaDelta_boxed_4614_ = lean_unbox(v_zetaDelta_4606_);
v_zetaHave_boxed_4615_ = lean_unbox(v_zetaHave_4607_);
v_beta_boxed_4616_ = lean_unbox(v_beta_4608_);
v_res_4617_ = l_Lean_Meta_zetaReduce(v_e_4605_, v_zetaDelta_boxed_4614_, v_zetaHave_boxed_4615_, v_beta_boxed_4616_, v_a_4609_, v_a_4610_, v_a_4611_, v_a_4612_);
lean_dec(v_a_4612_);
lean_dec_ref(v_a_4611_);
lean_dec(v_a_4610_);
lean_dec_ref(v_a_4609_);
return v_res_4617_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4(lean_object* v_upperBound_4618_, lean_object* v___x_4619_, lean_object* v_pre_4620_, lean_object* v_post_4621_, uint8_t v_usedLetOnly_4622_, uint8_t v_skipConstInApp_4623_, uint8_t v_skipInstances_4624_, lean_object* v___x_4625_, lean_object* v_inst_4626_, lean_object* v_R_4627_, lean_object* v_a_4628_, lean_object* v_b_4629_, lean_object* v_c_4630_, lean_object* v___y_4631_, lean_object* v___y_4632_, lean_object* v___y_4633_, lean_object* v___y_4634_, lean_object* v___y_4635_){
_start:
{
lean_object* v___x_4637_; 
v___x_4637_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___redArg(v_upperBound_4618_, v___x_4619_, v_pre_4620_, v_post_4621_, v_usedLetOnly_4622_, v_skipConstInApp_4623_, v_skipInstances_4624_, v_a_4628_, v_b_4629_, v___y_4631_, v___y_4632_, v___y_4633_, v___y_4634_, v___y_4635_);
return v___x_4637_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4___boxed(lean_object** _args){
lean_object* v_upperBound_4638_ = _args[0];
lean_object* v___x_4639_ = _args[1];
lean_object* v_pre_4640_ = _args[2];
lean_object* v_post_4641_ = _args[3];
lean_object* v_usedLetOnly_4642_ = _args[4];
lean_object* v_skipConstInApp_4643_ = _args[5];
lean_object* v_skipInstances_4644_ = _args[6];
lean_object* v___x_4645_ = _args[7];
lean_object* v_inst_4646_ = _args[8];
lean_object* v_R_4647_ = _args[9];
lean_object* v_a_4648_ = _args[10];
lean_object* v_b_4649_ = _args[11];
lean_object* v_c_4650_ = _args[12];
lean_object* v___y_4651_ = _args[13];
lean_object* v___y_4652_ = _args[14];
lean_object* v___y_4653_ = _args[15];
lean_object* v___y_4654_ = _args[16];
lean_object* v___y_4655_ = _args[17];
lean_object* v___y_4656_ = _args[18];
_start:
{
uint8_t v_usedLetOnly_boxed_4657_; uint8_t v_skipConstInApp_boxed_4658_; uint8_t v_skipInstances_boxed_4659_; lean_object* v_res_4660_; 
v_usedLetOnly_boxed_4657_ = lean_unbox(v_usedLetOnly_4642_);
v_skipConstInApp_boxed_4658_ = lean_unbox(v_skipConstInApp_4643_);
v_skipInstances_boxed_4659_ = lean_unbox(v_skipInstances_4644_);
v_res_4660_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__4(v_upperBound_4638_, v___x_4639_, v_pre_4640_, v_post_4641_, v_usedLetOnly_boxed_4657_, v_skipConstInApp_boxed_4658_, v_skipInstances_boxed_4659_, v___x_4645_, v_inst_4646_, v_R_4647_, v_a_4648_, v_b_4649_, v_c_4650_, v___y_4651_, v___y_4652_, v___y_4653_, v___y_4654_, v___y_4655_);
lean_dec(v___y_4655_);
lean_dec_ref(v___y_4654_);
lean_dec(v___y_4653_);
lean_dec_ref(v___y_4652_);
lean_dec(v___y_4651_);
lean_dec(v___x_4645_);
lean_dec_ref(v___x_4639_);
lean_dec(v_upperBound_4638_);
return v_res_4660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6(lean_object* v_00_u03b1_4661_, lean_object* v_name_4662_, uint8_t v_bi_4663_, lean_object* v_type_4664_, lean_object* v_k_4665_, uint8_t v_kind_4666_, lean_object* v___y_4667_, lean_object* v___y_4668_, lean_object* v___y_4669_, lean_object* v___y_4670_, lean_object* v___y_4671_){
_start:
{
lean_object* v___x_4673_; 
v___x_4673_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_name_4662_, v_bi_4663_, v_type_4664_, v_k_4665_, v_kind_4666_, v___y_4667_, v___y_4668_, v___y_4669_, v___y_4670_, v___y_4671_);
return v___x_4673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6___boxed(lean_object* v_00_u03b1_4674_, lean_object* v_name_4675_, lean_object* v_bi_4676_, lean_object* v_type_4677_, lean_object* v_k_4678_, lean_object* v_kind_4679_, lean_object* v___y_4680_, lean_object* v___y_4681_, lean_object* v___y_4682_, lean_object* v___y_4683_, lean_object* v___y_4684_, lean_object* v___y_4685_){
_start:
{
uint8_t v_bi_boxed_4686_; uint8_t v_kind_boxed_4687_; lean_object* v_res_4688_; 
v_bi_boxed_4686_ = lean_unbox(v_bi_4676_);
v_kind_boxed_4687_ = lean_unbox(v_kind_4679_);
v_res_4688_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__5_spec__6(v_00_u03b1_4674_, v_name_4675_, v_bi_boxed_4686_, v_type_4677_, v_k_4678_, v_kind_boxed_4687_, v___y_4680_, v___y_4681_, v___y_4682_, v___y_4683_, v___y_4684_);
lean_dec(v___y_4684_);
lean_dec_ref(v___y_4683_);
lean_dec(v___y_4682_);
lean_dec_ref(v___y_4681_);
lean_dec(v___y_4680_);
return v_res_4688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9(lean_object* v_00_u03b1_4689_, lean_object* v_name_4690_, lean_object* v_type_4691_, lean_object* v_val_4692_, lean_object* v_k_4693_, uint8_t v_nondep_4694_, uint8_t v_kind_4695_, lean_object* v___y_4696_, lean_object* v___y_4697_, lean_object* v___y_4698_, lean_object* v___y_4699_, lean_object* v___y_4700_){
_start:
{
lean_object* v___x_4702_; 
v___x_4702_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___redArg(v_name_4690_, v_type_4691_, v_val_4692_, v_k_4693_, v_nondep_4694_, v_kind_4695_, v___y_4696_, v___y_4697_, v___y_4698_, v___y_4699_, v___y_4700_);
return v___x_4702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9___boxed(lean_object* v_00_u03b1_4703_, lean_object* v_name_4704_, lean_object* v_type_4705_, lean_object* v_val_4706_, lean_object* v_k_4707_, lean_object* v_nondep_4708_, lean_object* v_kind_4709_, lean_object* v___y_4710_, lean_object* v___y_4711_, lean_object* v___y_4712_, lean_object* v___y_4713_, lean_object* v___y_4714_, lean_object* v___y_4715_){
_start:
{
uint8_t v_nondep_boxed_4716_; uint8_t v_kind_boxed_4717_; lean_object* v_res_4718_; 
v_nondep_boxed_4716_ = lean_unbox(v_nondep_4708_);
v_kind_boxed_4717_ = lean_unbox(v_kind_4709_);
v_res_4718_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__7_spec__9(v_00_u03b1_4703_, v_name_4704_, v_type_4705_, v_val_4706_, v_k_4707_, v_nondep_boxed_4716_, v_kind_boxed_4717_, v___y_4710_, v___y_4711_, v___y_4712_, v___y_4713_, v___y_4714_);
lean_dec(v___y_4714_);
lean_dec_ref(v___y_4713_);
lean_dec(v___y_4712_);
lean_dec_ref(v___y_4711_);
lean_dec(v___y_4710_);
return v_res_4718_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12(lean_object* v_00_u03b1_4719_, lean_object* v_ref_4720_, lean_object* v___y_4721_, lean_object* v___y_4722_, lean_object* v___y_4723_, lean_object* v___y_4724_){
_start:
{
lean_object* v___x_4726_; 
v___x_4726_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___redArg(v_ref_4720_);
return v___x_4726_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12___boxed(lean_object* v_00_u03b1_4727_, lean_object* v_ref_4728_, lean_object* v___y_4729_, lean_object* v___y_4730_, lean_object* v___y_4731_, lean_object* v___y_4732_, lean_object* v___y_4733_){
_start:
{
lean_object* v_res_4734_; 
v_res_4734_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9_spec__12(v_00_u03b1_4727_, v_ref_4728_, v___y_4729_, v___y_4730_, v___y_4731_, v___y_4732_);
lean_dec(v___y_4732_);
lean_dec_ref(v___y_4731_);
lean_dec(v___y_4730_);
lean_dec_ref(v___y_4729_);
return v_res_4734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9(lean_object* v_00_u03b1_4735_, lean_object* v_x_4736_, lean_object* v___y_4737_, lean_object* v___y_4738_, lean_object* v___y_4739_, lean_object* v___y_4740_, lean_object* v___y_4741_){
_start:
{
lean_object* v___x_4743_; 
v___x_4743_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___redArg(v_x_4736_, v___y_4737_, v___y_4738_, v___y_4739_, v___y_4740_, v___y_4741_);
return v___x_4743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9___boxed(lean_object* v_00_u03b1_4744_, lean_object* v_x_4745_, lean_object* v___y_4746_, lean_object* v___y_4747_, lean_object* v___y_4748_, lean_object* v___y_4749_, lean_object* v___y_4750_, lean_object* v___y_4751_){
_start:
{
lean_object* v_res_4752_; 
v_res_4752_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1_spec__1_spec__9(v_00_u03b1_4744_, v_x_4745_, v___y_4746_, v___y_4747_, v___y_4748_, v___y_4749_, v___y_4750_);
lean_dec(v___y_4750_);
lean_dec_ref(v___y_4749_);
lean_dec(v___y_4748_);
lean_dec_ref(v___y_4747_);
lean_dec(v___y_4746_);
return v_res_4752_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0_spec__0(lean_object* v_a_4753_, lean_object* v_as_4754_, size_t v_i_4755_, size_t v_stop_4756_){
_start:
{
uint8_t v___x_4757_; 
v___x_4757_ = lean_usize_dec_eq(v_i_4755_, v_stop_4756_);
if (v___x_4757_ == 0)
{
lean_object* v___x_4758_; uint8_t v___x_4759_; 
v___x_4758_ = lean_array_uget_borrowed(v_as_4754_, v_i_4755_);
v___x_4759_ = l_Lean_instBEqFVarId_beq(v_a_4753_, v___x_4758_);
if (v___x_4759_ == 0)
{
size_t v___x_4760_; size_t v___x_4761_; 
v___x_4760_ = ((size_t)1ULL);
v___x_4761_ = lean_usize_add(v_i_4755_, v___x_4760_);
v_i_4755_ = v___x_4761_;
goto _start;
}
else
{
return v___x_4759_;
}
}
else
{
uint8_t v___x_4763_; 
v___x_4763_ = 0;
return v___x_4763_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0_spec__0___boxed(lean_object* v_a_4764_, lean_object* v_as_4765_, lean_object* v_i_4766_, lean_object* v_stop_4767_){
_start:
{
size_t v_i_boxed_4768_; size_t v_stop_boxed_4769_; uint8_t v_res_4770_; lean_object* v_r_4771_; 
v_i_boxed_4768_ = lean_unbox_usize(v_i_4766_);
lean_dec(v_i_4766_);
v_stop_boxed_4769_ = lean_unbox_usize(v_stop_4767_);
lean_dec(v_stop_4767_);
v_res_4770_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0_spec__0(v_a_4764_, v_as_4765_, v_i_boxed_4768_, v_stop_boxed_4769_);
lean_dec_ref(v_as_4765_);
lean_dec(v_a_4764_);
v_r_4771_ = lean_box(v_res_4770_);
return v_r_4771_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0(lean_object* v_as_4772_, lean_object* v_a_4773_){
_start:
{
lean_object* v___x_4774_; lean_object* v___x_4775_; uint8_t v___x_4776_; 
v___x_4774_ = lean_unsigned_to_nat(0u);
v___x_4775_ = lean_array_get_size(v_as_4772_);
v___x_4776_ = lean_nat_dec_lt(v___x_4774_, v___x_4775_);
if (v___x_4776_ == 0)
{
return v___x_4776_;
}
else
{
size_t v___x_4777_; size_t v___x_4778_; uint8_t v___x_4779_; 
v___x_4777_ = ((size_t)0ULL);
v___x_4778_ = lean_usize_of_nat(v___x_4775_);
v___x_4779_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0_spec__0(v_a_4773_, v_as_4772_, v___x_4777_, v___x_4778_);
return v___x_4779_;
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0___boxed(lean_object* v_as_4780_, lean_object* v_a_4781_){
_start:
{
uint8_t v_res_4782_; lean_object* v_r_4783_; 
v_res_4782_ = l_Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0(v_as_4780_, v_a_4781_);
lean_dec(v_a_4781_);
lean_dec_ref(v_as_4780_);
v_r_4783_ = lean_box(v_res_4782_);
return v_r_4783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaFVars___lam__1(lean_object* v_fvars_4784_, lean_object* v_e_4785_, lean_object* v___y_4786_, lean_object* v___y_4787_, lean_object* v___y_4788_, lean_object* v___y_4789_){
_start:
{
lean_object* v___x_4794_; 
v___x_4794_ = l_Lean_Expr_getAppFn(v_e_4785_);
if (lean_obj_tag(v___x_4794_) == 1)
{
lean_object* v_fvarId_4795_; uint8_t v___x_4796_; 
v_fvarId_4795_ = lean_ctor_get(v___x_4794_, 0);
lean_inc(v_fvarId_4795_);
lean_dec_ref_known(v___x_4794_, 1);
v___x_4796_ = l_Array_contains___at___00Lean_Meta_zetaDeltaFVars_spec__0(v_fvars_4784_, v_fvarId_4795_);
if (v___x_4796_ == 0)
{
lean_dec(v_fvarId_4795_);
lean_dec_ref(v_e_4785_);
goto v___jp_4791_;
}
else
{
uint8_t v___x_4797_; lean_object* v___x_4798_; 
v___x_4797_ = 0;
v___x_4798_ = l_Lean_FVarId_getValue_x3f___redArg(v_fvarId_4795_, v___x_4797_, v___y_4786_, v___y_4788_, v___y_4789_);
if (lean_obj_tag(v___x_4798_) == 0)
{
lean_object* v_a_4799_; 
v_a_4799_ = lean_ctor_get(v___x_4798_, 0);
lean_inc(v_a_4799_);
lean_dec_ref_known(v___x_4798_, 1);
if (lean_obj_tag(v_a_4799_) == 1)
{
lean_object* v_val_4800_; lean_object* v___x_4802_; uint8_t v_isShared_4803_; uint8_t v_isSharedCheck_4823_; 
v_val_4800_ = lean_ctor_get(v_a_4799_, 0);
v_isSharedCheck_4823_ = !lean_is_exclusive(v_a_4799_);
if (v_isSharedCheck_4823_ == 0)
{
v___x_4802_ = v_a_4799_;
v_isShared_4803_ = v_isSharedCheck_4823_;
goto v_resetjp_4801_;
}
else
{
lean_inc(v_val_4800_);
lean_dec(v_a_4799_);
v___x_4802_ = lean_box(0);
v_isShared_4803_ = v_isSharedCheck_4823_;
goto v_resetjp_4801_;
}
v_resetjp_4801_:
{
lean_object* v___x_4804_; lean_object* v_a_4805_; lean_object* v___x_4807_; uint8_t v_isShared_4808_; uint8_t v_isSharedCheck_4822_; 
v___x_4804_ = l_Lean_instantiateMVars___at___00Lean_Meta_zetaReduce_spec__0___redArg(v_val_4800_, v___y_4787_);
v_a_4805_ = lean_ctor_get(v___x_4804_, 0);
v_isSharedCheck_4822_ = !lean_is_exclusive(v___x_4804_);
if (v_isSharedCheck_4822_ == 0)
{
v___x_4807_ = v___x_4804_;
v_isShared_4808_ = v_isSharedCheck_4822_;
goto v_resetjp_4806_;
}
else
{
lean_inc(v_a_4805_);
lean_dec(v___x_4804_);
v___x_4807_ = lean_box(0);
v_isShared_4808_ = v_isSharedCheck_4822_;
goto v_resetjp_4806_;
}
v_resetjp_4806_:
{
lean_object* v_dummy_4809_; lean_object* v_nargs_4810_; lean_object* v___x_4811_; lean_object* v___x_4812_; lean_object* v___x_4813_; lean_object* v___x_4814_; lean_object* v___x_4815_; lean_object* v___x_4817_; 
v_dummy_4809_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__18___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__18___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__18___closed__0);
v_nargs_4810_ = l_Lean_Expr_getAppNumArgs(v_e_4785_);
lean_inc(v_nargs_4810_);
v___x_4811_ = lean_mk_array(v_nargs_4810_, v_dummy_4809_);
v___x_4812_ = lean_unsigned_to_nat(1u);
v___x_4813_ = lean_nat_sub(v_nargs_4810_, v___x_4812_);
lean_dec(v_nargs_4810_);
v___x_4814_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_4785_, v___x_4811_, v___x_4813_);
v___x_4815_ = l_Lean_Expr_beta(v_a_4805_, v___x_4814_);
if (v_isShared_4803_ == 0)
{
lean_ctor_set(v___x_4802_, 0, v___x_4815_);
v___x_4817_ = v___x_4802_;
goto v_reusejp_4816_;
}
else
{
lean_object* v_reuseFailAlloc_4821_; 
v_reuseFailAlloc_4821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4821_, 0, v___x_4815_);
v___x_4817_ = v_reuseFailAlloc_4821_;
goto v_reusejp_4816_;
}
v_reusejp_4816_:
{
lean_object* v___x_4819_; 
if (v_isShared_4808_ == 0)
{
lean_ctor_set(v___x_4807_, 0, v___x_4817_);
v___x_4819_ = v___x_4807_;
goto v_reusejp_4818_;
}
else
{
lean_object* v_reuseFailAlloc_4820_; 
v_reuseFailAlloc_4820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4820_, 0, v___x_4817_);
v___x_4819_ = v_reuseFailAlloc_4820_;
goto v_reusejp_4818_;
}
v_reusejp_4818_:
{
return v___x_4819_;
}
}
}
}
}
else
{
lean_dec(v_a_4799_);
lean_dec_ref(v_e_4785_);
goto v___jp_4791_;
}
}
else
{
lean_object* v_a_4824_; lean_object* v___x_4826_; uint8_t v_isShared_4827_; uint8_t v_isSharedCheck_4831_; 
lean_dec_ref(v_e_4785_);
v_a_4824_ = lean_ctor_get(v___x_4798_, 0);
v_isSharedCheck_4831_ = !lean_is_exclusive(v___x_4798_);
if (v_isSharedCheck_4831_ == 0)
{
v___x_4826_ = v___x_4798_;
v_isShared_4827_ = v_isSharedCheck_4831_;
goto v_resetjp_4825_;
}
else
{
lean_inc(v_a_4824_);
lean_dec(v___x_4798_);
v___x_4826_ = lean_box(0);
v_isShared_4827_ = v_isSharedCheck_4831_;
goto v_resetjp_4825_;
}
v_resetjp_4825_:
{
lean_object* v___x_4829_; 
if (v_isShared_4827_ == 0)
{
v___x_4829_ = v___x_4826_;
goto v_reusejp_4828_;
}
else
{
lean_object* v_reuseFailAlloc_4830_; 
v_reuseFailAlloc_4830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4830_, 0, v_a_4824_);
v___x_4829_ = v_reuseFailAlloc_4830_;
goto v_reusejp_4828_;
}
v_reusejp_4828_:
{
return v___x_4829_;
}
}
}
}
}
else
{
lean_object* v___x_4832_; lean_object* v___x_4833_; 
lean_dec_ref(v___x_4794_);
lean_dec_ref(v_e_4785_);
v___x_4832_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_4833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4833_, 0, v___x_4832_);
return v___x_4833_;
}
v___jp_4791_:
{
lean_object* v___x_4792_; lean_object* v___x_4793_; 
v___x_4792_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_4793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4793_, 0, v___x_4792_);
return v___x_4793_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaFVars___lam__1___boxed(lean_object* v_fvars_4834_, lean_object* v_e_4835_, lean_object* v___y_4836_, lean_object* v___y_4837_, lean_object* v___y_4838_, lean_object* v___y_4839_, lean_object* v___y_4840_){
_start:
{
lean_object* v_res_4841_; 
v_res_4841_ = l_Lean_Meta_zetaDeltaFVars___lam__1(v_fvars_4834_, v_e_4835_, v___y_4836_, v___y_4837_, v___y_4838_, v___y_4839_);
lean_dec(v___y_4839_);
lean_dec_ref(v___y_4838_);
lean_dec(v___y_4837_);
lean_dec_ref(v___y_4836_);
lean_dec_ref(v_fvars_4834_);
return v_res_4841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaFVars(lean_object* v_e_4842_, lean_object* v_fvars_4843_, lean_object* v_a_4844_, lean_object* v_a_4845_, lean_object* v_a_4846_, lean_object* v_a_4847_){
_start:
{
lean_object* v___f_4849_; lean_object* v_pre_4850_; uint8_t v___x_4851_; lean_object* v___x_4852_; 
v___f_4849_ = ((lean_object*)(l_Lean_Meta_zetaReduce___closed__0));
v_pre_4850_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaDeltaFVars___lam__1___boxed), 7, 1);
lean_closure_set(v_pre_4850_, 0, v_fvars_4843_);
v___x_4851_ = 0;
v___x_4852_ = l_Lean_Meta_transform___at___00Lean_Meta_zetaReduce_spec__1(v_e_4842_, v_pre_4850_, v___f_4849_, v___x_4851_, v___x_4851_, v_a_4844_, v_a_4845_, v_a_4846_, v_a_4847_);
return v___x_4852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaFVars___boxed(lean_object* v_e_4853_, lean_object* v_fvars_4854_, lean_object* v_a_4855_, lean_object* v_a_4856_, lean_object* v_a_4857_, lean_object* v_a_4858_, lean_object* v_a_4859_){
_start:
{
lean_object* v_res_4860_; 
v_res_4860_ = l_Lean_Meta_zetaDeltaFVars(v_e_4853_, v_fvars_4854_, v_a_4855_, v_a_4856_, v_a_4857_, v_a_4858_);
lean_dec(v_a_4858_);
lean_dec_ref(v_a_4857_);
lean_dec(v_a_4856_);
lean_dec_ref(v_a_4855_);
return v_res_4860_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_4861_; 
v___x_4861_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_4861_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_4862_; lean_object* v___x_4863_; 
v___x_4862_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__0, &l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__0);
v___x_4863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4863_, 0, v___x_4862_);
return v___x_4863_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_4864_; lean_object* v___x_4865_; 
v___x_4864_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__1, &l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__1);
v___x_4865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4865_, 0, v___x_4864_);
lean_ctor_set(v___x_4865_, 1, v___x_4864_);
return v___x_4865_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(lean_object* v_env_4866_, lean_object* v___y_4867_){
_start:
{
lean_object* v___x_4869_; lean_object* v_nextMacroScope_4870_; lean_object* v_ngen_4871_; lean_object* v_auxDeclNGen_4872_; lean_object* v_traceState_4873_; lean_object* v_recordedDeps_4874_; lean_object* v_messages_4875_; lean_object* v_infoState_4876_; lean_object* v_snapshotTasks_4877_; lean_object* v___x_4879_; uint8_t v_isShared_4880_; uint8_t v_isSharedCheck_4888_; 
v___x_4869_ = lean_st_ref_take(v___y_4867_);
v_nextMacroScope_4870_ = lean_ctor_get(v___x_4869_, 1);
v_ngen_4871_ = lean_ctor_get(v___x_4869_, 2);
v_auxDeclNGen_4872_ = lean_ctor_get(v___x_4869_, 3);
v_traceState_4873_ = lean_ctor_get(v___x_4869_, 4);
v_recordedDeps_4874_ = lean_ctor_get(v___x_4869_, 6);
v_messages_4875_ = lean_ctor_get(v___x_4869_, 7);
v_infoState_4876_ = lean_ctor_get(v___x_4869_, 8);
v_snapshotTasks_4877_ = lean_ctor_get(v___x_4869_, 9);
v_isSharedCheck_4888_ = !lean_is_exclusive(v___x_4869_);
if (v_isSharedCheck_4888_ == 0)
{
lean_object* v_unused_4889_; lean_object* v_unused_4890_; 
v_unused_4889_ = lean_ctor_get(v___x_4869_, 5);
lean_dec(v_unused_4889_);
v_unused_4890_ = lean_ctor_get(v___x_4869_, 0);
lean_dec(v_unused_4890_);
v___x_4879_ = v___x_4869_;
v_isShared_4880_ = v_isSharedCheck_4888_;
goto v_resetjp_4878_;
}
else
{
lean_inc(v_snapshotTasks_4877_);
lean_inc(v_infoState_4876_);
lean_inc(v_messages_4875_);
lean_inc(v_recordedDeps_4874_);
lean_inc(v_traceState_4873_);
lean_inc(v_auxDeclNGen_4872_);
lean_inc(v_ngen_4871_);
lean_inc(v_nextMacroScope_4870_);
lean_dec(v___x_4869_);
v___x_4879_ = lean_box(0);
v_isShared_4880_ = v_isSharedCheck_4888_;
goto v_resetjp_4878_;
}
v_resetjp_4878_:
{
lean_object* v___x_4881_; lean_object* v___x_4882_; lean_object* v___x_4884_; 
v___x_4881_ = lean_box(0);
v___x_4882_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2, &l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2);
if (v_isShared_4880_ == 0)
{
lean_ctor_set(v___x_4879_, 5, v___x_4882_);
lean_ctor_set(v___x_4879_, 0, v_env_4866_);
v___x_4884_ = v___x_4879_;
goto v_reusejp_4883_;
}
else
{
lean_object* v_reuseFailAlloc_4887_; 
v_reuseFailAlloc_4887_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4887_, 0, v_env_4866_);
lean_ctor_set(v_reuseFailAlloc_4887_, 1, v_nextMacroScope_4870_);
lean_ctor_set(v_reuseFailAlloc_4887_, 2, v_ngen_4871_);
lean_ctor_set(v_reuseFailAlloc_4887_, 3, v_auxDeclNGen_4872_);
lean_ctor_set(v_reuseFailAlloc_4887_, 4, v_traceState_4873_);
lean_ctor_set(v_reuseFailAlloc_4887_, 5, v___x_4882_);
lean_ctor_set(v_reuseFailAlloc_4887_, 6, v_recordedDeps_4874_);
lean_ctor_set(v_reuseFailAlloc_4887_, 7, v_messages_4875_);
lean_ctor_set(v_reuseFailAlloc_4887_, 8, v_infoState_4876_);
lean_ctor_set(v_reuseFailAlloc_4887_, 9, v_snapshotTasks_4877_);
v___x_4884_ = v_reuseFailAlloc_4887_;
goto v_reusejp_4883_;
}
v_reusejp_4883_:
{
lean_object* v___x_4885_; lean_object* v___x_4886_; 
v___x_4885_ = lean_st_ref_put(v___y_4867_, v___x_4884_);
v___x_4886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4886_, 0, v___x_4881_);
return v___x_4886_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___boxed(lean_object* v_env_4891_, lean_object* v___y_4892_, lean_object* v___y_4893_){
_start:
{
lean_object* v_res_4894_; 
v_res_4894_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_4891_, v___y_4892_);
lean_dec(v___y_4892_);
return v_res_4894_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0(lean_object* v_env_4895_, lean_object* v___y_4896_, lean_object* v___y_4897_){
_start:
{
lean_object* v___x_4899_; 
v___x_4899_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_4895_, v___y_4897_);
return v___x_4899_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___boxed(lean_object* v_env_4900_, lean_object* v___y_4901_, lean_object* v___y_4902_, lean_object* v___y_4903_){
_start:
{
lean_object* v_res_4904_; 
v_res_4904_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0(v_env_4900_, v___y_4901_, v___y_4902_);
lean_dec(v___y_4902_);
lean_dec_ref(v___y_4901_);
return v_res_4904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___lam__1(lean_object* v_env_4905_, lean_object* v___x_4906_, uint8_t v___x_4907_, lean_object* v_e_4908_, lean_object* v___y_4909_, lean_object* v___y_4910_){
_start:
{
if (lean_obj_tag(v_e_4908_) == 4)
{
lean_object* v_declName_4912_; lean_object* v_us_4913_; uint8_t v___x_4914_; uint8_t v___x_4915_; 
v_declName_4912_ = lean_ctor_get(v_e_4908_, 0);
v_us_4913_ = lean_ctor_get(v_e_4908_, 1);
v___x_4914_ = 1;
lean_inc(v_declName_4912_);
v___x_4915_ = l_Lean_Environment_contains(v_env_4905_, v_declName_4912_, v___x_4914_);
if (v___x_4915_ == 0)
{
lean_object* v___x_4916_; 
lean_inc(v_declName_4912_);
v___x_4916_ = l_Lean_Environment_find_x3f(v___x_4906_, v_declName_4912_, v___x_4907_);
if (lean_obj_tag(v___x_4916_) == 1)
{
lean_object* v_val_4917_; lean_object* v___x_4919_; uint8_t v_isShared_4920_; uint8_t v_isSharedCheck_4946_; 
v_val_4917_ = lean_ctor_get(v___x_4916_, 0);
v_isSharedCheck_4946_ = !lean_is_exclusive(v___x_4916_);
if (v_isSharedCheck_4946_ == 0)
{
v___x_4919_ = v___x_4916_;
v_isShared_4920_ = v_isSharedCheck_4946_;
goto v_resetjp_4918_;
}
else
{
lean_inc(v_val_4917_);
lean_dec(v___x_4916_);
v___x_4919_ = lean_box(0);
v_isShared_4920_ = v_isSharedCheck_4946_;
goto v_resetjp_4918_;
}
v_resetjp_4918_:
{
uint8_t v___x_4921_; 
v___x_4921_ = l_Lean_ConstantInfo_hasValue(v_val_4917_, v___x_4914_);
if (v___x_4921_ == 0)
{
lean_object* v___x_4923_; 
lean_dec(v_val_4917_);
if (v_isShared_4920_ == 0)
{
lean_ctor_set_tag(v___x_4919_, 0);
lean_ctor_set(v___x_4919_, 0, v_e_4908_);
v___x_4923_ = v___x_4919_;
goto v_reusejp_4922_;
}
else
{
lean_object* v_reuseFailAlloc_4925_; 
v_reuseFailAlloc_4925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4925_, 0, v_e_4908_);
v___x_4923_ = v_reuseFailAlloc_4925_;
goto v_reusejp_4922_;
}
v_reusejp_4922_:
{
lean_object* v___x_4924_; 
v___x_4924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4924_, 0, v___x_4923_);
return v___x_4924_;
}
}
else
{
lean_object* v___x_4926_; 
lean_inc(v_us_4913_);
lean_dec_ref_known(v_e_4908_, 2);
v___x_4926_ = l_Lean_Core_instantiateValueLevelParams(v_val_4917_, v_us_4913_, v___x_4914_, v___y_4909_, v___y_4910_);
lean_dec(v_val_4917_);
if (lean_obj_tag(v___x_4926_) == 0)
{
lean_object* v_a_4927_; lean_object* v___x_4929_; uint8_t v_isShared_4930_; uint8_t v_isSharedCheck_4937_; 
v_a_4927_ = lean_ctor_get(v___x_4926_, 0);
v_isSharedCheck_4937_ = !lean_is_exclusive(v___x_4926_);
if (v_isSharedCheck_4937_ == 0)
{
v___x_4929_ = v___x_4926_;
v_isShared_4930_ = v_isSharedCheck_4937_;
goto v_resetjp_4928_;
}
else
{
lean_inc(v_a_4927_);
lean_dec(v___x_4926_);
v___x_4929_ = lean_box(0);
v_isShared_4930_ = v_isSharedCheck_4937_;
goto v_resetjp_4928_;
}
v_resetjp_4928_:
{
lean_object* v___x_4932_; 
if (v_isShared_4920_ == 0)
{
lean_ctor_set(v___x_4919_, 0, v_a_4927_);
v___x_4932_ = v___x_4919_;
goto v_reusejp_4931_;
}
else
{
lean_object* v_reuseFailAlloc_4936_; 
v_reuseFailAlloc_4936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4936_, 0, v_a_4927_);
v___x_4932_ = v_reuseFailAlloc_4936_;
goto v_reusejp_4931_;
}
v_reusejp_4931_:
{
lean_object* v___x_4934_; 
if (v_isShared_4930_ == 0)
{
lean_ctor_set(v___x_4929_, 0, v___x_4932_);
v___x_4934_ = v___x_4929_;
goto v_reusejp_4933_;
}
else
{
lean_object* v_reuseFailAlloc_4935_; 
v_reuseFailAlloc_4935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4935_, 0, v___x_4932_);
v___x_4934_ = v_reuseFailAlloc_4935_;
goto v_reusejp_4933_;
}
v_reusejp_4933_:
{
return v___x_4934_;
}
}
}
}
else
{
lean_object* v_a_4938_; lean_object* v___x_4940_; uint8_t v_isShared_4941_; uint8_t v_isSharedCheck_4945_; 
lean_del_object(v___x_4919_);
v_a_4938_ = lean_ctor_get(v___x_4926_, 0);
v_isSharedCheck_4945_ = !lean_is_exclusive(v___x_4926_);
if (v_isSharedCheck_4945_ == 0)
{
v___x_4940_ = v___x_4926_;
v_isShared_4941_ = v_isSharedCheck_4945_;
goto v_resetjp_4939_;
}
else
{
lean_inc(v_a_4938_);
lean_dec(v___x_4926_);
v___x_4940_ = lean_box(0);
v_isShared_4941_ = v_isSharedCheck_4945_;
goto v_resetjp_4939_;
}
v_resetjp_4939_:
{
lean_object* v___x_4943_; 
if (v_isShared_4941_ == 0)
{
v___x_4943_ = v___x_4940_;
goto v_reusejp_4942_;
}
else
{
lean_object* v_reuseFailAlloc_4944_; 
v_reuseFailAlloc_4944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4944_, 0, v_a_4938_);
v___x_4943_ = v_reuseFailAlloc_4944_;
goto v_reusejp_4942_;
}
v_reusejp_4942_:
{
return v___x_4943_;
}
}
}
}
}
}
else
{
lean_object* v___x_4947_; lean_object* v___x_4948_; 
lean_dec(v___x_4916_);
v___x_4947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4947_, 0, v_e_4908_);
v___x_4948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4948_, 0, v___x_4947_);
return v___x_4948_;
}
}
else
{
lean_object* v___x_4949_; lean_object* v___x_4950_; 
lean_dec_ref(v___x_4906_);
v___x_4949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4949_, 0, v_e_4908_);
v___x_4950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4950_, 0, v___x_4949_);
return v___x_4950_;
}
}
else
{
lean_object* v___x_4951_; lean_object* v___x_4952_; 
lean_dec_ref(v_e_4908_);
lean_dec_ref(v___x_4906_);
lean_dec_ref(v_env_4905_);
v___x_4951_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_4952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4952_, 0, v___x_4951_);
return v___x_4952_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___lam__1___boxed(lean_object* v_env_4953_, lean_object* v___x_4954_, lean_object* v___x_4955_, lean_object* v_e_4956_, lean_object* v___y_4957_, lean_object* v___y_4958_, lean_object* v___y_4959_){
_start:
{
uint8_t v___x_1999__boxed_4960_; lean_object* v_res_4961_; 
v___x_1999__boxed_4960_ = lean_unbox(v___x_4955_);
v_res_4961_ = l_Lean_Meta_unfoldDeclsFrom___lam__1(v_env_4953_, v___x_4954_, v___x_1999__boxed_4960_, v_e_4956_, v___y_4957_, v___y_4958_);
lean_dec(v___y_4958_);
lean_dec_ref(v___y_4957_);
return v_res_4961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___lam__0(lean_object* v_biggerEnv_4962_, lean_object* v_e_4963_, lean_object* v___f_4964_, lean_object* v___y_4965_, lean_object* v___y_4966_){
_start:
{
lean_object* v___x_4968_; lean_object* v_env_4969_; uint8_t v___x_4970_; lean_object* v___x_4971_; lean_object* v___x_4972_; lean_object* v___f_4973_; lean_object* v___x_4974_; lean_object* v___x_4975_; 
v___x_4968_ = lean_st_ref_get(v___y_4966_);
v_env_4969_ = lean_ctor_get(v___x_4968_, 0);
lean_inc_ref(v_env_4969_);
lean_dec(v___x_4968_);
v___x_4970_ = 0;
v___x_4971_ = l_Lean_Environment_setExporting(v_biggerEnv_4962_, v___x_4970_);
v___x_4972_ = lean_box(v___x_4970_);
lean_inc_ref(v___x_4971_);
v___f_4973_ = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDeclsFrom___lam__1___boxed), 7, 3);
lean_closure_set(v___f_4973_, 0, v_env_4969_);
lean_closure_set(v___f_4973_, 1, v___x_4971_);
lean_closure_set(v___f_4973_, 2, v___x_4972_);
v___x_4974_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v___x_4971_, v___y_4966_);
lean_dec_ref(v___x_4974_);
v___x_4975_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_4963_, v___f_4973_, v___f_4964_, v___y_4965_, v___y_4966_);
return v___x_4975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___lam__0___boxed(lean_object* v_biggerEnv_4976_, lean_object* v_e_4977_, lean_object* v___f_4978_, lean_object* v___y_4979_, lean_object* v___y_4980_, lean_object* v___y_4981_){
_start:
{
lean_object* v_res_4982_; 
v_res_4982_ = l_Lean_Meta_unfoldDeclsFrom___lam__0(v_biggerEnv_4976_, v_e_4977_, v___f_4978_, v___y_4979_, v___y_4980_);
lean_dec(v___y_4980_);
lean_dec_ref(v___y_4979_);
return v_res_4982_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg(lean_object* v_env_4983_, lean_object* v_x_4984_, lean_object* v___y_4985_, lean_object* v___y_4986_){
_start:
{
lean_object* v___x_4988_; lean_object* v_env_4989_; lean_object* v_a_4991_; lean_object* v___x_5001_; lean_object* v___x_5002_; 
v___x_4988_ = lean_st_ref_get(v___y_4986_);
v_env_4989_ = lean_ctor_get(v___x_4988_, 0);
lean_inc_ref(v_env_4989_);
lean_dec(v___x_4988_);
v___x_5001_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_4983_, v___y_4986_);
lean_dec_ref(v___x_5001_);
lean_inc(v___y_4986_);
lean_inc_ref(v___y_4985_);
v___x_5002_ = lean_apply_3(v_x_4984_, v___y_4985_, v___y_4986_, lean_box(0));
if (lean_obj_tag(v___x_5002_) == 0)
{
lean_object* v_a_5003_; lean_object* v___x_5004_; lean_object* v___x_5006_; uint8_t v_isShared_5007_; uint8_t v_isSharedCheck_5011_; 
v_a_5003_ = lean_ctor_get(v___x_5002_, 0);
lean_inc(v_a_5003_);
lean_dec_ref_known(v___x_5002_, 1);
v___x_5004_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_4989_, v___y_4986_);
v_isSharedCheck_5011_ = !lean_is_exclusive(v___x_5004_);
if (v_isSharedCheck_5011_ == 0)
{
lean_object* v_unused_5012_; 
v_unused_5012_ = lean_ctor_get(v___x_5004_, 0);
lean_dec(v_unused_5012_);
v___x_5006_ = v___x_5004_;
v_isShared_5007_ = v_isSharedCheck_5011_;
goto v_resetjp_5005_;
}
else
{
lean_dec(v___x_5004_);
v___x_5006_ = lean_box(0);
v_isShared_5007_ = v_isSharedCheck_5011_;
goto v_resetjp_5005_;
}
v_resetjp_5005_:
{
lean_object* v___x_5009_; 
if (v_isShared_5007_ == 0)
{
lean_ctor_set(v___x_5006_, 0, v_a_5003_);
v___x_5009_ = v___x_5006_;
goto v_reusejp_5008_;
}
else
{
lean_object* v_reuseFailAlloc_5010_; 
v_reuseFailAlloc_5010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5010_, 0, v_a_5003_);
v___x_5009_ = v_reuseFailAlloc_5010_;
goto v_reusejp_5008_;
}
v_reusejp_5008_:
{
return v___x_5009_;
}
}
}
else
{
lean_object* v_a_5013_; 
v_a_5013_ = lean_ctor_get(v___x_5002_, 0);
lean_inc(v_a_5013_);
lean_dec_ref_known(v___x_5002_, 1);
v_a_4991_ = v_a_5013_;
goto v___jp_4990_;
}
v___jp_4990_:
{
lean_object* v___x_4992_; lean_object* v___x_4994_; uint8_t v_isShared_4995_; uint8_t v_isSharedCheck_4999_; 
v___x_4992_ = l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg(v_env_4989_, v___y_4986_);
v_isSharedCheck_4999_ = !lean_is_exclusive(v___x_4992_);
if (v_isSharedCheck_4999_ == 0)
{
lean_object* v_unused_5000_; 
v_unused_5000_ = lean_ctor_get(v___x_4992_, 0);
lean_dec(v_unused_5000_);
v___x_4994_ = v___x_4992_;
v_isShared_4995_ = v_isSharedCheck_4999_;
goto v_resetjp_4993_;
}
else
{
lean_dec(v___x_4992_);
v___x_4994_ = lean_box(0);
v_isShared_4995_ = v_isSharedCheck_4999_;
goto v_resetjp_4993_;
}
v_resetjp_4993_:
{
lean_object* v___x_4997_; 
if (v_isShared_4995_ == 0)
{
lean_ctor_set_tag(v___x_4994_, 1);
lean_ctor_set(v___x_4994_, 0, v_a_4991_);
v___x_4997_ = v___x_4994_;
goto v_reusejp_4996_;
}
else
{
lean_object* v_reuseFailAlloc_4998_; 
v_reuseFailAlloc_4998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4998_, 0, v_a_4991_);
v___x_4997_ = v_reuseFailAlloc_4998_;
goto v_reusejp_4996_;
}
v_reusejp_4996_:
{
return v___x_4997_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg___boxed(lean_object* v_env_5014_, lean_object* v_x_5015_, lean_object* v___y_5016_, lean_object* v___y_5017_, lean_object* v___y_5018_){
_start:
{
lean_object* v_res_5019_; 
v_res_5019_ = l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg(v_env_5014_, v_x_5015_, v___y_5016_, v___y_5017_);
lean_dec(v___y_5017_);
lean_dec_ref(v___y_5016_);
return v_res_5019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom(lean_object* v_biggerEnv_5020_, lean_object* v_e_5021_, lean_object* v_a_5022_, lean_object* v_a_5023_){
_start:
{
lean_object* v___f_5025_; lean_object* v___f_5026_; lean_object* v___x_5027_; lean_object* v_env_5028_; lean_object* v___x_5029_; lean_object* v___x_5030_; 
v___f_5025_ = ((lean_object*)(l_Lean_Core_betaReduce___closed__1));
v___f_5026_ = lean_alloc_closure((void*)(l_Lean_Meta_unfoldDeclsFrom___lam__0___boxed), 6, 3);
lean_closure_set(v___f_5026_, 0, v_biggerEnv_5020_);
lean_closure_set(v___f_5026_, 1, v_e_5021_);
lean_closure_set(v___f_5026_, 2, v___f_5025_);
v___x_5027_ = lean_st_ref_get(v_a_5023_);
v_env_5028_ = lean_ctor_get(v___x_5027_, 0);
lean_inc_ref(v_env_5028_);
lean_dec(v___x_5027_);
v___x_5029_ = l_Lean_Environment_unlockAsync(v_env_5028_);
v___x_5030_ = l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg(v___x_5029_, v___f_5026_, v_a_5022_, v_a_5023_);
return v___x_5030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldDeclsFrom___boxed(lean_object* v_biggerEnv_5031_, lean_object* v_e_5032_, lean_object* v_a_5033_, lean_object* v_a_5034_, lean_object* v_a_5035_){
_start:
{
lean_object* v_res_5036_; 
v_res_5036_ = l_Lean_Meta_unfoldDeclsFrom(v_biggerEnv_5031_, v_e_5032_, v_a_5033_, v_a_5034_);
lean_dec(v_a_5034_);
lean_dec_ref(v_a_5033_);
return v_res_5036_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1(lean_object* v_00_u03b1_5037_, lean_object* v_env_5038_, lean_object* v_x_5039_, lean_object* v___y_5040_, lean_object* v___y_5041_){
_start:
{
lean_object* v___x_5043_; 
v___x_5043_ = l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___redArg(v_env_5038_, v_x_5039_, v___y_5040_, v___y_5041_);
return v___x_5043_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1___boxed(lean_object* v_00_u03b1_5044_, lean_object* v_env_5045_, lean_object* v_x_5046_, lean_object* v___y_5047_, lean_object* v___y_5048_, lean_object* v___y_5049_){
_start:
{
lean_object* v_res_5050_; 
v_res_5050_ = l_Lean_withEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__1(v_00_u03b1_5044_, v_env_5045_, v_x_5046_, v___y_5047_, v___y_5048_);
lean_dec(v___y_5048_);
lean_dec_ref(v___y_5047_);
return v_res_5050_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0(lean_object* v_af_5051_, lean_object* v_axs_5052_, lean_object* v_numSectionVars_5053_, lean_object* v_as_5054_, size_t v_i_5055_, size_t v_stop_5056_){
_start:
{
uint8_t v___x_5061_; 
v___x_5061_ = lean_usize_dec_eq(v_i_5055_, v_stop_5056_);
if (v___x_5061_ == 0)
{
lean_object* v___x_5062_; lean_object* v___x_5063_; uint8_t v___x_5064_; 
v___x_5062_ = lean_array_uget_borrowed(v_as_5054_, v_i_5055_);
v___x_5063_ = l_Lean_Expr_constName_x21(v_af_5051_);
v___x_5064_ = lean_name_eq(v___x_5063_, v___x_5062_);
lean_dec(v___x_5063_);
if (v___x_5064_ == 0)
{
goto v___jp_5057_;
}
else
{
lean_object* v___x_5065_; uint8_t v___x_5066_; 
v___x_5065_ = lean_array_get_size(v_axs_5052_);
v___x_5066_ = lean_nat_dec_le(v___x_5065_, v_numSectionVars_5053_);
if (v___x_5066_ == 0)
{
goto v___jp_5057_;
}
else
{
return v___x_5066_;
}
}
}
else
{
uint8_t v___x_5067_; 
v___x_5067_ = 0;
return v___x_5067_;
}
v___jp_5057_:
{
size_t v___x_5058_; size_t v___x_5059_; 
v___x_5058_ = ((size_t)1ULL);
v___x_5059_ = lean_usize_add(v_i_5055_, v___x_5058_);
v_i_5055_ = v___x_5059_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0___boxed(lean_object* v_af_5068_, lean_object* v_axs_5069_, lean_object* v_numSectionVars_5070_, lean_object* v_as_5071_, lean_object* v_i_5072_, lean_object* v_stop_5073_){
_start:
{
size_t v_i_boxed_5074_; size_t v_stop_boxed_5075_; uint8_t v_res_5076_; lean_object* v_r_5077_; 
v_i_boxed_5074_ = lean_unbox_usize(v_i_5072_);
lean_dec(v_i_5072_);
v_stop_boxed_5075_ = lean_unbox_usize(v_stop_5073_);
lean_dec(v_stop_5073_);
v_res_5076_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0(v_af_5068_, v_axs_5069_, v_numSectionVars_5070_, v_as_5071_, v_i_boxed_5074_, v_stop_boxed_5075_);
lean_dec_ref(v_as_5071_);
lean_dec(v_numSectionVars_5070_);
lean_dec_ref(v_axs_5069_);
lean_dec_ref(v_af_5068_);
v_r_5077_ = lean_box(v_res_5076_);
return v_r_5077_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1_spec__1(lean_object* v_fnNames_5078_, lean_object* v_numSectionVars_5079_, lean_object* v_x_5080_, lean_object* v_x_5081_, lean_object* v_x_5082_){
_start:
{
if (lean_obj_tag(v_x_5080_) == 5)
{
lean_object* v_fn_5083_; lean_object* v_arg_5084_; lean_object* v___x_5085_; lean_object* v___x_5086_; lean_object* v___x_5087_; 
v_fn_5083_ = lean_ctor_get(v_x_5080_, 0);
lean_inc_ref(v_fn_5083_);
v_arg_5084_ = lean_ctor_get(v_x_5080_, 1);
lean_inc_ref(v_arg_5084_);
lean_dec_ref_known(v_x_5080_, 2);
v___x_5085_ = lean_array_set(v_x_5081_, v_x_5082_, v_arg_5084_);
v___x_5086_ = lean_unsigned_to_nat(1u);
v___x_5087_ = lean_nat_sub(v_x_5082_, v___x_5086_);
lean_dec(v_x_5082_);
v_x_5080_ = v_fn_5083_;
v_x_5081_ = v___x_5085_;
v_x_5082_ = v___x_5087_;
goto _start;
}
else
{
uint8_t v___x_5089_; 
lean_dec(v_x_5082_);
v___x_5089_ = l_Lean_Expr_isConst(v_x_5080_);
if (v___x_5089_ == 0)
{
lean_dec_ref(v_x_5081_);
lean_dec_ref(v_x_5080_);
return v___x_5089_;
}
else
{
lean_object* v___x_5090_; lean_object* v___x_5091_; uint8_t v___x_5092_; 
v___x_5090_ = lean_unsigned_to_nat(0u);
v___x_5091_ = lean_array_get_size(v_fnNames_5078_);
v___x_5092_ = lean_nat_dec_lt(v___x_5090_, v___x_5091_);
if (v___x_5092_ == 0)
{
lean_dec_ref(v_x_5081_);
lean_dec_ref(v_x_5080_);
return v___x_5092_;
}
else
{
if (v___x_5092_ == 0)
{
lean_dec_ref(v_x_5081_);
lean_dec_ref(v_x_5080_);
return v___x_5092_;
}
else
{
size_t v___x_5093_; size_t v___x_5094_; uint8_t v___x_5095_; 
v___x_5093_ = ((size_t)0ULL);
v___x_5094_ = lean_usize_of_nat(v___x_5091_);
v___x_5095_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0(v_x_5080_, v_x_5081_, v_numSectionVars_5079_, v_fnNames_5078_, v___x_5093_, v___x_5094_);
lean_dec_ref(v_x_5081_);
lean_dec_ref(v_x_5080_);
return v___x_5095_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1_spec__1___boxed(lean_object* v_fnNames_5096_, lean_object* v_numSectionVars_5097_, lean_object* v_x_5098_, lean_object* v_x_5099_, lean_object* v_x_5100_){
_start:
{
uint8_t v_res_5101_; lean_object* v_r_5102_; 
v_res_5101_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1_spec__1(v_fnNames_5096_, v_numSectionVars_5097_, v_x_5098_, v_x_5099_, v_x_5100_);
lean_dec(v_numSectionVars_5097_);
lean_dec_ref(v_fnNames_5096_);
v_r_5102_ = lean_box(v_res_5101_);
return v_r_5102_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1(lean_object* v_numSectionVars_5103_, lean_object* v_fnNames_5104_, lean_object* v_x_5105_, lean_object* v_x_5106_, lean_object* v_x_5107_){
_start:
{
if (lean_obj_tag(v_x_5105_) == 5)
{
lean_object* v_fn_5108_; lean_object* v_arg_5109_; lean_object* v___x_5110_; lean_object* v___x_5111_; lean_object* v___x_5112_; uint8_t v___x_5113_; 
v_fn_5108_ = lean_ctor_get(v_x_5105_, 0);
lean_inc_ref(v_fn_5108_);
v_arg_5109_ = lean_ctor_get(v_x_5105_, 1);
lean_inc_ref(v_arg_5109_);
lean_dec_ref_known(v_x_5105_, 2);
v___x_5110_ = lean_array_set(v_x_5106_, v_x_5107_, v_arg_5109_);
v___x_5111_ = lean_unsigned_to_nat(1u);
v___x_5112_ = lean_nat_sub(v_x_5107_, v___x_5111_);
v___x_5113_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1_spec__1(v_fnNames_5104_, v_numSectionVars_5103_, v_fn_5108_, v___x_5110_, v___x_5112_);
return v___x_5113_;
}
else
{
uint8_t v___x_5114_; 
v___x_5114_ = l_Lean_Expr_isConst(v_x_5105_);
if (v___x_5114_ == 0)
{
lean_dec_ref(v_x_5106_);
lean_dec_ref(v_x_5105_);
return v___x_5114_;
}
else
{
lean_object* v___x_5115_; lean_object* v___x_5116_; uint8_t v___x_5117_; 
v___x_5115_ = lean_unsigned_to_nat(0u);
v___x_5116_ = lean_array_get_size(v_fnNames_5104_);
v___x_5117_ = lean_nat_dec_lt(v___x_5115_, v___x_5116_);
if (v___x_5117_ == 0)
{
lean_dec_ref(v_x_5106_);
lean_dec_ref(v_x_5105_);
return v___x_5117_;
}
else
{
if (v___x_5117_ == 0)
{
lean_dec_ref(v_x_5106_);
lean_dec_ref(v_x_5105_);
return v___x_5117_;
}
else
{
size_t v___x_5118_; size_t v___x_5119_; uint8_t v___x_5120_; 
v___x_5118_ = ((size_t)0ULL);
v___x_5119_ = lean_usize_of_nat(v___x_5116_);
v___x_5120_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__0(v_x_5105_, v_x_5106_, v_numSectionVars_5103_, v_fnNames_5104_, v___x_5118_, v___x_5119_);
lean_dec_ref(v_x_5106_);
lean_dec_ref(v_x_5105_);
return v___x_5120_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1___boxed(lean_object* v_numSectionVars_5121_, lean_object* v_fnNames_5122_, lean_object* v_x_5123_, lean_object* v_x_5124_, lean_object* v_x_5125_){
_start:
{
uint8_t v_res_5126_; lean_object* v_r_5127_; 
v_res_5126_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1(v_numSectionVars_5121_, v_fnNames_5122_, v_x_5123_, v_x_5124_, v_x_5125_);
lean_dec(v_x_5125_);
lean_dec_ref(v_fnNames_5122_);
lean_dec(v_numSectionVars_5121_);
v_r_5127_ = lean_box(v_res_5126_);
return v_r_5127_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg(lean_object* v_fnNames_5128_, lean_object* v_numSectionVars_5129_, lean_object* v_a_5130_){
_start:
{
lean_object* v_dummy_5131_; lean_object* v_nargs_5132_; lean_object* v___x_5133_; lean_object* v___x_5134_; lean_object* v___x_5135_; uint8_t v___x_5136_; 
v_dummy_5131_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__18___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__18___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___redArg___lam__18___closed__0);
v_nargs_5132_ = l_Lean_Expr_getAppNumArgs(v_a_5130_);
lean_inc(v_nargs_5132_);
v___x_5133_ = lean_mk_array(v_nargs_5132_, v_dummy_5131_);
v___x_5134_ = lean_unsigned_to_nat(1u);
v___x_5135_ = lean_nat_sub(v_nargs_5132_, v___x_5134_);
lean_dec(v_nargs_5132_);
v___x_5136_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg_spec__1(v_numSectionVars_5129_, v_fnNames_5128_, v_a_5130_, v___x_5133_, v___x_5135_);
lean_dec(v___x_5135_);
return v___x_5136_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg___boxed(lean_object* v_fnNames_5137_, lean_object* v_numSectionVars_5138_, lean_object* v_a_5139_){
_start:
{
uint8_t v_res_5140_; lean_object* v_r_5141_; 
v_res_5140_ = l___private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg(v_fnNames_5137_, v_numSectionVars_5138_, v_a_5139_);
lean_dec(v_numSectionVars_5138_);
lean_dec_ref(v_fnNames_5137_);
v_r_5141_ = lean_box(v_res_5140_);
return v_r_5141_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__0(lean_object* v_fnNames_5142_, lean_object* v_numSectionVars_5143_, lean_object* v_as_5144_, size_t v_i_5145_, size_t v_stop_5146_){
_start:
{
uint8_t v___x_5147_; 
v___x_5147_ = lean_usize_dec_eq(v_i_5145_, v_stop_5146_);
if (v___x_5147_ == 0)
{
lean_object* v___x_5148_; uint8_t v___x_5149_; 
v___x_5148_ = lean_array_uget_borrowed(v_as_5144_, v_i_5145_);
lean_inc(v___x_5148_);
v___x_5149_ = l___private_Lean_Meta_Transform_0__Lean_Meta_unfoldIfArgIsAppOf_isInterestingArg(v_fnNames_5142_, v_numSectionVars_5143_, v___x_5148_);
if (v___x_5149_ == 0)
{
size_t v___x_5150_; size_t v___x_5151_; 
v___x_5150_ = ((size_t)1ULL);
v___x_5151_ = lean_usize_add(v_i_5145_, v___x_5150_);
v_i_5145_ = v___x_5151_;
goto _start;
}
else
{
return v___x_5149_;
}
}
else
{
uint8_t v___x_5153_; 
v___x_5153_ = 0;
return v___x_5153_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__0___boxed(lean_object* v_fnNames_5154_, lean_object* v_numSectionVars_5155_, lean_object* v_as_5156_, lean_object* v_i_5157_, lean_object* v_stop_5158_){
_start:
{
size_t v_i_boxed_5159_; size_t v_stop_boxed_5160_; uint8_t v_res_5161_; lean_object* v_r_5162_; 
v_i_boxed_5159_ = lean_unbox_usize(v_i_5157_);
lean_dec(v_i_5157_);
v_stop_boxed_5160_ = lean_unbox_usize(v_stop_5158_);
lean_dec(v_stop_5158_);
v_res_5161_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__0(v_fnNames_5154_, v_numSectionVars_5155_, v_as_5156_, v_i_boxed_5159_, v_stop_boxed_5160_);
lean_dec_ref(v_as_5156_);
lean_dec(v_numSectionVars_5155_);
lean_dec_ref(v_fnNames_5154_);
v_r_5162_ = lean_box(v_res_5161_);
return v_r_5162_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__1(lean_object* v_fnNames_5163_, lean_object* v_numSectionVars_5164_, lean_object* v___x_5165_, lean_object* v_x_5166_, lean_object* v_x_5167_, lean_object* v___y_5168_, lean_object* v___y_5169_){
_start:
{
if (lean_obj_tag(v_x_5166_) == 5)
{
lean_object* v_fn_5174_; lean_object* v_arg_5175_; lean_object* v___x_5176_; 
v_fn_5174_ = lean_ctor_get(v_x_5166_, 0);
lean_inc_ref(v_fn_5174_);
v_arg_5175_ = lean_ctor_get(v_x_5166_, 1);
lean_inc_ref(v_arg_5175_);
lean_dec_ref_known(v_x_5166_, 2);
v___x_5176_ = lean_array_push(v_x_5167_, v_arg_5175_);
v_x_5166_ = v_fn_5174_;
v_x_5167_ = v___x_5176_;
goto _start;
}
else
{
uint8_t v___x_5178_; 
v___x_5178_ = l_Lean_Expr_isConst(v_x_5166_);
if (v___x_5178_ == 0)
{
lean_dec_ref(v_x_5167_);
lean_dec_ref(v_x_5166_);
lean_dec_ref(v___x_5165_);
goto v___jp_5171_;
}
else
{
lean_object* v___x_5179_; lean_object* v___x_5180_; uint8_t v___x_5181_; 
v___x_5179_ = lean_unsigned_to_nat(0u);
v___x_5180_ = lean_array_get_size(v_x_5167_);
v___x_5181_ = lean_nat_dec_lt(v___x_5179_, v___x_5180_);
if (v___x_5181_ == 0)
{
lean_dec_ref(v_x_5167_);
lean_dec_ref(v_x_5166_);
lean_dec_ref(v___x_5165_);
goto v___jp_5171_;
}
else
{
if (v___x_5181_ == 0)
{
lean_dec_ref(v_x_5167_);
lean_dec_ref(v_x_5166_);
lean_dec_ref(v___x_5165_);
goto v___jp_5171_;
}
else
{
size_t v___x_5182_; size_t v___x_5183_; uint8_t v___x_5184_; 
v___x_5182_ = ((size_t)0ULL);
v___x_5183_ = lean_usize_of_nat(v___x_5180_);
v___x_5184_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__0(v_fnNames_5163_, v_numSectionVars_5164_, v_x_5167_, v___x_5182_, v___x_5183_);
if (v___x_5184_ == 0)
{
lean_dec_ref(v_x_5167_);
lean_dec_ref(v_x_5166_);
lean_dec_ref(v___x_5165_);
goto v___jp_5171_;
}
else
{
lean_object* v___x_5185_; uint8_t v___x_5186_; lean_object* v___x_5187_; 
v___x_5185_ = l_Lean_Expr_constName_x21(v_x_5166_);
v___x_5186_ = 0;
v___x_5187_ = l_Lean_Environment_find_x3f(v___x_5165_, v___x_5185_, v___x_5186_);
if (lean_obj_tag(v___x_5187_) == 1)
{
lean_object* v_val_5188_; 
v_val_5188_ = lean_ctor_get(v___x_5187_, 0);
lean_inc(v_val_5188_);
lean_dec_ref_known(v___x_5187_, 1);
if (lean_obj_tag(v_val_5188_) == 2)
{
lean_object* v___x_5189_; lean_object* v___x_5190_; lean_object* v___x_5192_; uint8_t v_isShared_5193_; uint8_t v_isSharedCheck_5214_; 
v___x_5189_ = l_Lean_Expr_constLevels_x21(v_x_5166_);
lean_dec_ref(v_x_5166_);
v___x_5190_ = l_Lean_Core_instantiateValueLevelParams(v_val_5188_, v___x_5189_, v___x_5181_, v___y_5168_, v___y_5169_);
v_isSharedCheck_5214_ = !lean_is_exclusive(v_val_5188_);
if (v_isSharedCheck_5214_ == 0)
{
lean_object* v_unused_5215_; 
v_unused_5215_ = lean_ctor_get(v_val_5188_, 0);
lean_dec(v_unused_5215_);
v___x_5192_ = v_val_5188_;
v_isShared_5193_ = v_isSharedCheck_5214_;
goto v_resetjp_5191_;
}
else
{
lean_dec(v_val_5188_);
v___x_5192_ = lean_box(0);
v_isShared_5193_ = v_isSharedCheck_5214_;
goto v_resetjp_5191_;
}
v_resetjp_5191_:
{
if (lean_obj_tag(v___x_5190_) == 0)
{
lean_object* v_a_5194_; lean_object* v___x_5196_; uint8_t v_isShared_5197_; uint8_t v_isSharedCheck_5205_; 
v_a_5194_ = lean_ctor_get(v___x_5190_, 0);
v_isSharedCheck_5205_ = !lean_is_exclusive(v___x_5190_);
if (v_isSharedCheck_5205_ == 0)
{
v___x_5196_ = v___x_5190_;
v_isShared_5197_ = v_isSharedCheck_5205_;
goto v_resetjp_5195_;
}
else
{
lean_inc(v_a_5194_);
lean_dec(v___x_5190_);
v___x_5196_ = lean_box(0);
v_isShared_5197_ = v_isSharedCheck_5205_;
goto v_resetjp_5195_;
}
v_resetjp_5195_:
{
lean_object* v___x_5198_; lean_object* v___x_5200_; 
v___x_5198_ = l_Lean_Expr_betaRev(v_a_5194_, v_x_5167_, v___x_5186_, v___x_5186_);
lean_dec_ref(v_x_5167_);
if (v_isShared_5193_ == 0)
{
lean_ctor_set_tag(v___x_5192_, 1);
lean_ctor_set(v___x_5192_, 0, v___x_5198_);
v___x_5200_ = v___x_5192_;
goto v_reusejp_5199_;
}
else
{
lean_object* v_reuseFailAlloc_5204_; 
v_reuseFailAlloc_5204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5204_, 0, v___x_5198_);
v___x_5200_ = v_reuseFailAlloc_5204_;
goto v_reusejp_5199_;
}
v_reusejp_5199_:
{
lean_object* v___x_5202_; 
if (v_isShared_5197_ == 0)
{
lean_ctor_set(v___x_5196_, 0, v___x_5200_);
v___x_5202_ = v___x_5196_;
goto v_reusejp_5201_;
}
else
{
lean_object* v_reuseFailAlloc_5203_; 
v_reuseFailAlloc_5203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5203_, 0, v___x_5200_);
v___x_5202_ = v_reuseFailAlloc_5203_;
goto v_reusejp_5201_;
}
v_reusejp_5201_:
{
return v___x_5202_;
}
}
}
}
else
{
lean_object* v_a_5206_; lean_object* v___x_5208_; uint8_t v_isShared_5209_; uint8_t v_isSharedCheck_5213_; 
lean_del_object(v___x_5192_);
lean_dec_ref(v_x_5167_);
v_a_5206_ = lean_ctor_get(v___x_5190_, 0);
v_isSharedCheck_5213_ = !lean_is_exclusive(v___x_5190_);
if (v_isSharedCheck_5213_ == 0)
{
v___x_5208_ = v___x_5190_;
v_isShared_5209_ = v_isSharedCheck_5213_;
goto v_resetjp_5207_;
}
else
{
lean_inc(v_a_5206_);
lean_dec(v___x_5190_);
v___x_5208_ = lean_box(0);
v_isShared_5209_ = v_isSharedCheck_5213_;
goto v_resetjp_5207_;
}
v_resetjp_5207_:
{
lean_object* v___x_5211_; 
if (v_isShared_5209_ == 0)
{
v___x_5211_ = v___x_5208_;
goto v_reusejp_5210_;
}
else
{
lean_object* v_reuseFailAlloc_5212_; 
v_reuseFailAlloc_5212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5212_, 0, v_a_5206_);
v___x_5211_ = v_reuseFailAlloc_5212_;
goto v_reusejp_5210_;
}
v_reusejp_5210_:
{
return v___x_5211_;
}
}
}
}
}
else
{
lean_dec(v_val_5188_);
lean_dec_ref(v_x_5167_);
lean_dec_ref(v_x_5166_);
goto v___jp_5171_;
}
}
else
{
lean_dec(v___x_5187_);
lean_dec_ref(v_x_5167_);
lean_dec_ref(v_x_5166_);
goto v___jp_5171_;
}
}
}
}
}
}
v___jp_5171_:
{
lean_object* v___x_5172_; lean_object* v___x_5173_; 
v___x_5172_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_5173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5173_, 0, v___x_5172_);
return v___x_5173_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__1___boxed(lean_object* v_fnNames_5216_, lean_object* v_numSectionVars_5217_, lean_object* v___x_5218_, lean_object* v_x_5219_, lean_object* v_x_5220_, lean_object* v___y_5221_, lean_object* v___y_5222_, lean_object* v___y_5223_){
_start:
{
lean_object* v_res_5224_; 
v_res_5224_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__1(v_fnNames_5216_, v_numSectionVars_5217_, v___x_5218_, v_x_5219_, v_x_5220_, v___y_5221_, v___y_5222_);
lean_dec(v___y_5222_);
lean_dec_ref(v___y_5221_);
lean_dec(v_numSectionVars_5217_);
lean_dec_ref(v_fnNames_5216_);
return v_res_5224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___lam__1(lean_object* v_fnNames_5225_, lean_object* v_numSectionVars_5226_, lean_object* v_env_5227_, lean_object* v_e_5228_, lean_object* v___y_5229_, lean_object* v___y_5230_){
_start:
{
lean_object* v___x_5232_; lean_object* v___x_5233_; lean_object* v___x_5234_; 
v___x_5232_ = l_Lean_Expr_getAppNumArgs(v_e_5228_);
v___x_5233_ = lean_mk_empty_array_with_capacity(v___x_5232_);
lean_dec(v___x_5232_);
v___x_5234_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__1(v_fnNames_5225_, v_numSectionVars_5226_, v_env_5227_, v_e_5228_, v___x_5233_, v___y_5229_, v___y_5230_);
return v___x_5234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___lam__1___boxed(lean_object* v_fnNames_5235_, lean_object* v_numSectionVars_5236_, lean_object* v_env_5237_, lean_object* v_e_5238_, lean_object* v___y_5239_, lean_object* v___y_5240_, lean_object* v___y_5241_){
_start:
{
lean_object* v_res_5242_; 
v_res_5242_ = l_Lean_Meta_unfoldIfArgIsAppOf___lam__1(v_fnNames_5235_, v_numSectionVars_5236_, v_env_5237_, v_e_5238_, v___y_5239_, v___y_5240_);
lean_dec(v___y_5240_);
lean_dec_ref(v___y_5239_);
lean_dec(v_numSectionVars_5236_);
lean_dec_ref(v_fnNames_5235_);
return v_res_5242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___lam__0(lean_object* v_fnNames_5243_, lean_object* v_numSectionVars_5244_, lean_object* v_e_5245_, lean_object* v___f_5246_, lean_object* v___y_5247_, lean_object* v___y_5248_){
_start:
{
lean_object* v___x_5250_; lean_object* v_env_5251_; lean_object* v___f_5252_; lean_object* v___x_5253_; 
v___x_5250_ = lean_st_ref_get(v___y_5248_);
v_env_5251_ = lean_ctor_get(v___x_5250_, 0);
lean_inc_ref(v_env_5251_);
lean_dec(v___x_5250_);
v___f_5252_ = lean_alloc_closure((void*)(l_Lean_Meta_unfoldIfArgIsAppOf___lam__1___boxed), 7, 3);
lean_closure_set(v___f_5252_, 0, v_fnNames_5243_);
lean_closure_set(v___f_5252_, 1, v_numSectionVars_5244_);
lean_closure_set(v___f_5252_, 2, v_env_5251_);
v___x_5253_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_5245_, v___f_5252_, v___f_5246_, v___y_5247_, v___y_5248_);
return v___x_5253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___lam__0___boxed(lean_object* v_fnNames_5254_, lean_object* v_numSectionVars_5255_, lean_object* v_e_5256_, lean_object* v___f_5257_, lean_object* v___y_5258_, lean_object* v___y_5259_, lean_object* v___y_5260_){
_start:
{
lean_object* v_res_5261_; 
v_res_5261_ = l_Lean_Meta_unfoldIfArgIsAppOf___lam__0(v_fnNames_5254_, v_numSectionVars_5255_, v_e_5256_, v___f_5257_, v___y_5258_, v___y_5259_);
lean_dec(v___y_5259_);
lean_dec_ref(v___y_5258_);
return v_res_5261_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0(lean_object* v___y_5262_, uint8_t v_isExporting_5263_, lean_object* v___x_5264_, lean_object* v_a_x3f_5265_){
_start:
{
lean_object* v___x_5267_; lean_object* v_env_5268_; lean_object* v_nextMacroScope_5269_; lean_object* v_ngen_5270_; lean_object* v_auxDeclNGen_5271_; lean_object* v_traceState_5272_; lean_object* v_recordedDeps_5273_; lean_object* v_messages_5274_; lean_object* v_infoState_5275_; lean_object* v_snapshotTasks_5276_; lean_object* v___x_5278_; uint8_t v_isShared_5279_; uint8_t v_isSharedCheck_5287_; 
v___x_5267_ = lean_st_ref_take(v___y_5262_);
v_env_5268_ = lean_ctor_get(v___x_5267_, 0);
v_nextMacroScope_5269_ = lean_ctor_get(v___x_5267_, 1);
v_ngen_5270_ = lean_ctor_get(v___x_5267_, 2);
v_auxDeclNGen_5271_ = lean_ctor_get(v___x_5267_, 3);
v_traceState_5272_ = lean_ctor_get(v___x_5267_, 4);
v_recordedDeps_5273_ = lean_ctor_get(v___x_5267_, 6);
v_messages_5274_ = lean_ctor_get(v___x_5267_, 7);
v_infoState_5275_ = lean_ctor_get(v___x_5267_, 8);
v_snapshotTasks_5276_ = lean_ctor_get(v___x_5267_, 9);
v_isSharedCheck_5287_ = !lean_is_exclusive(v___x_5267_);
if (v_isSharedCheck_5287_ == 0)
{
lean_object* v_unused_5288_; 
v_unused_5288_ = lean_ctor_get(v___x_5267_, 5);
lean_dec(v_unused_5288_);
v___x_5278_ = v___x_5267_;
v_isShared_5279_ = v_isSharedCheck_5287_;
goto v_resetjp_5277_;
}
else
{
lean_inc(v_snapshotTasks_5276_);
lean_inc(v_infoState_5275_);
lean_inc(v_messages_5274_);
lean_inc(v_recordedDeps_5273_);
lean_inc(v_traceState_5272_);
lean_inc(v_auxDeclNGen_5271_);
lean_inc(v_ngen_5270_);
lean_inc(v_nextMacroScope_5269_);
lean_inc(v_env_5268_);
lean_dec(v___x_5267_);
v___x_5278_ = lean_box(0);
v_isShared_5279_ = v_isSharedCheck_5287_;
goto v_resetjp_5277_;
}
v_resetjp_5277_:
{
lean_object* v___x_5280_; lean_object* v___x_5281_; lean_object* v___x_5283_; 
v___x_5280_ = lean_box(0);
v___x_5281_ = l_Lean_Environment_setExporting(v_env_5268_, v_isExporting_5263_);
if (v_isShared_5279_ == 0)
{
lean_ctor_set(v___x_5278_, 5, v___x_5264_);
lean_ctor_set(v___x_5278_, 0, v___x_5281_);
v___x_5283_ = v___x_5278_;
goto v_reusejp_5282_;
}
else
{
lean_object* v_reuseFailAlloc_5286_; 
v_reuseFailAlloc_5286_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5286_, 0, v___x_5281_);
lean_ctor_set(v_reuseFailAlloc_5286_, 1, v_nextMacroScope_5269_);
lean_ctor_set(v_reuseFailAlloc_5286_, 2, v_ngen_5270_);
lean_ctor_set(v_reuseFailAlloc_5286_, 3, v_auxDeclNGen_5271_);
lean_ctor_set(v_reuseFailAlloc_5286_, 4, v_traceState_5272_);
lean_ctor_set(v_reuseFailAlloc_5286_, 5, v___x_5264_);
lean_ctor_set(v_reuseFailAlloc_5286_, 6, v_recordedDeps_5273_);
lean_ctor_set(v_reuseFailAlloc_5286_, 7, v_messages_5274_);
lean_ctor_set(v_reuseFailAlloc_5286_, 8, v_infoState_5275_);
lean_ctor_set(v_reuseFailAlloc_5286_, 9, v_snapshotTasks_5276_);
v___x_5283_ = v_reuseFailAlloc_5286_;
goto v_reusejp_5282_;
}
v_reusejp_5282_:
{
lean_object* v___x_5284_; lean_object* v___x_5285_; 
v___x_5284_ = lean_st_ref_put(v___y_5262_, v___x_5283_);
v___x_5285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5285_, 0, v___x_5280_);
return v___x_5285_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0___boxed(lean_object* v___y_5289_, lean_object* v_isExporting_5290_, lean_object* v___x_5291_, lean_object* v_a_x3f_5292_, lean_object* v___y_5293_){
_start:
{
uint8_t v_isExporting_boxed_5294_; lean_object* v_res_5295_; 
v_isExporting_boxed_5294_ = lean_unbox(v_isExporting_5290_);
v_res_5295_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0(v___y_5289_, v_isExporting_boxed_5294_, v___x_5291_, v_a_x3f_5292_);
lean_dec(v_a_x3f_5292_);
lean_dec(v___y_5289_);
return v_res_5295_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg(lean_object* v_x_5296_, uint8_t v_isExporting_5297_, lean_object* v___y_5298_, lean_object* v___y_5299_){
_start:
{
lean_object* v___x_5301_; lean_object* v_env_5302_; lean_object* v___x_5303_; uint8_t v_isModule_5304_; 
v___x_5301_ = lean_st_ref_get(v___y_5299_);
v_env_5302_ = lean_ctor_get(v___x_5301_, 0);
lean_inc_ref(v_env_5302_);
lean_dec(v___x_5301_);
v___x_5303_ = l_Lean_Environment_header(v_env_5302_);
v_isModule_5304_ = lean_ctor_get_uint8(v___x_5303_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_5303_);
if (v_isModule_5304_ == 0)
{
lean_object* v___x_5305_; 
lean_dec_ref(v_env_5302_);
lean_inc(v___y_5299_);
lean_inc_ref(v___y_5298_);
v___x_5305_ = lean_apply_3(v_x_5296_, v___y_5298_, v___y_5299_, lean_box(0));
return v___x_5305_;
}
else
{
uint8_t v_isExporting_5306_; 
v_isExporting_5306_ = lean_ctor_get_uint8(v_env_5302_, sizeof(void*)*13);
lean_dec_ref(v_env_5302_);
if (v_isExporting_5297_ == 0)
{
if (v_isExporting_5306_ == 0)
{
lean_object* v___x_5358_; 
lean_inc(v___y_5299_);
lean_inc_ref(v___y_5298_);
v___x_5358_ = lean_apply_3(v_x_5296_, v___y_5298_, v___y_5299_, lean_box(0));
return v___x_5358_;
}
else
{
goto v___jp_5307_;
}
}
else
{
if (v_isExporting_5306_ == 0)
{
goto v___jp_5307_;
}
else
{
lean_object* v___x_5359_; 
lean_inc(v___y_5299_);
lean_inc_ref(v___y_5298_);
v___x_5359_ = lean_apply_3(v_x_5296_, v___y_5298_, v___y_5299_, lean_box(0));
return v___x_5359_;
}
}
v___jp_5307_:
{
lean_object* v___x_5308_; lean_object* v_env_5309_; lean_object* v_nextMacroScope_5310_; lean_object* v_ngen_5311_; lean_object* v_auxDeclNGen_5312_; lean_object* v_traceState_5313_; lean_object* v_recordedDeps_5314_; lean_object* v_messages_5315_; lean_object* v_infoState_5316_; lean_object* v_snapshotTasks_5317_; lean_object* v___x_5319_; uint8_t v_isShared_5320_; uint8_t v_isSharedCheck_5356_; 
v___x_5308_ = lean_st_ref_take(v___y_5299_);
v_env_5309_ = lean_ctor_get(v___x_5308_, 0);
v_nextMacroScope_5310_ = lean_ctor_get(v___x_5308_, 1);
v_ngen_5311_ = lean_ctor_get(v___x_5308_, 2);
v_auxDeclNGen_5312_ = lean_ctor_get(v___x_5308_, 3);
v_traceState_5313_ = lean_ctor_get(v___x_5308_, 4);
v_recordedDeps_5314_ = lean_ctor_get(v___x_5308_, 6);
v_messages_5315_ = lean_ctor_get(v___x_5308_, 7);
v_infoState_5316_ = lean_ctor_get(v___x_5308_, 8);
v_snapshotTasks_5317_ = lean_ctor_get(v___x_5308_, 9);
v_isSharedCheck_5356_ = !lean_is_exclusive(v___x_5308_);
if (v_isSharedCheck_5356_ == 0)
{
lean_object* v_unused_5357_; 
v_unused_5357_ = lean_ctor_get(v___x_5308_, 5);
lean_dec(v_unused_5357_);
v___x_5319_ = v___x_5308_;
v_isShared_5320_ = v_isSharedCheck_5356_;
goto v_resetjp_5318_;
}
else
{
lean_inc(v_snapshotTasks_5317_);
lean_inc(v_infoState_5316_);
lean_inc(v_messages_5315_);
lean_inc(v_recordedDeps_5314_);
lean_inc(v_traceState_5313_);
lean_inc(v_auxDeclNGen_5312_);
lean_inc(v_ngen_5311_);
lean_inc(v_nextMacroScope_5310_);
lean_inc(v_env_5309_);
lean_dec(v___x_5308_);
v___x_5319_ = lean_box(0);
v_isShared_5320_ = v_isSharedCheck_5356_;
goto v_resetjp_5318_;
}
v_resetjp_5318_:
{
lean_object* v___x_5321_; lean_object* v___x_5322_; lean_object* v___x_5324_; 
v___x_5321_ = l_Lean_Environment_setExporting(v_env_5309_, v_isExporting_5297_);
v___x_5322_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2, &l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_Meta_unfoldDeclsFrom_spec__0___redArg___closed__2);
if (v_isShared_5320_ == 0)
{
lean_ctor_set(v___x_5319_, 5, v___x_5322_);
lean_ctor_set(v___x_5319_, 0, v___x_5321_);
v___x_5324_ = v___x_5319_;
goto v_reusejp_5323_;
}
else
{
lean_object* v_reuseFailAlloc_5355_; 
v_reuseFailAlloc_5355_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5355_, 0, v___x_5321_);
lean_ctor_set(v_reuseFailAlloc_5355_, 1, v_nextMacroScope_5310_);
lean_ctor_set(v_reuseFailAlloc_5355_, 2, v_ngen_5311_);
lean_ctor_set(v_reuseFailAlloc_5355_, 3, v_auxDeclNGen_5312_);
lean_ctor_set(v_reuseFailAlloc_5355_, 4, v_traceState_5313_);
lean_ctor_set(v_reuseFailAlloc_5355_, 5, v___x_5322_);
lean_ctor_set(v_reuseFailAlloc_5355_, 6, v_recordedDeps_5314_);
lean_ctor_set(v_reuseFailAlloc_5355_, 7, v_messages_5315_);
lean_ctor_set(v_reuseFailAlloc_5355_, 8, v_infoState_5316_);
lean_ctor_set(v_reuseFailAlloc_5355_, 9, v_snapshotTasks_5317_);
v___x_5324_ = v_reuseFailAlloc_5355_;
goto v_reusejp_5323_;
}
v_reusejp_5323_:
{
lean_object* v___x_5325_; lean_object* v_r_5326_; 
v___x_5325_ = lean_st_ref_put(v___y_5299_, v___x_5324_);
lean_inc(v___y_5299_);
lean_inc_ref(v___y_5298_);
v_r_5326_ = lean_apply_3(v_x_5296_, v___y_5298_, v___y_5299_, lean_box(0));
if (lean_obj_tag(v_r_5326_) == 0)
{
lean_object* v_a_5327_; lean_object* v___x_5329_; uint8_t v_isShared_5330_; uint8_t v_isSharedCheck_5343_; 
v_a_5327_ = lean_ctor_get(v_r_5326_, 0);
v_isSharedCheck_5343_ = !lean_is_exclusive(v_r_5326_);
if (v_isSharedCheck_5343_ == 0)
{
v___x_5329_ = v_r_5326_;
v_isShared_5330_ = v_isSharedCheck_5343_;
goto v_resetjp_5328_;
}
else
{
lean_inc(v_a_5327_);
lean_dec(v_r_5326_);
v___x_5329_ = lean_box(0);
v_isShared_5330_ = v_isSharedCheck_5343_;
goto v_resetjp_5328_;
}
v_resetjp_5328_:
{
lean_object* v___x_5332_; 
lean_inc(v_a_5327_);
if (v_isShared_5330_ == 0)
{
lean_ctor_set_tag(v___x_5329_, 1);
v___x_5332_ = v___x_5329_;
goto v_reusejp_5331_;
}
else
{
lean_object* v_reuseFailAlloc_5342_; 
v_reuseFailAlloc_5342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5342_, 0, v_a_5327_);
v___x_5332_ = v_reuseFailAlloc_5342_;
goto v_reusejp_5331_;
}
v_reusejp_5331_:
{
lean_object* v___x_5333_; lean_object* v___x_5335_; uint8_t v_isShared_5336_; uint8_t v_isSharedCheck_5340_; 
v___x_5333_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0(v___y_5299_, v_isExporting_5306_, v___x_5322_, v___x_5332_);
lean_dec_ref(v___x_5332_);
v_isSharedCheck_5340_ = !lean_is_exclusive(v___x_5333_);
if (v_isSharedCheck_5340_ == 0)
{
lean_object* v_unused_5341_; 
v_unused_5341_ = lean_ctor_get(v___x_5333_, 0);
lean_dec(v_unused_5341_);
v___x_5335_ = v___x_5333_;
v_isShared_5336_ = v_isSharedCheck_5340_;
goto v_resetjp_5334_;
}
else
{
lean_dec(v___x_5333_);
v___x_5335_ = lean_box(0);
v_isShared_5336_ = v_isSharedCheck_5340_;
goto v_resetjp_5334_;
}
v_resetjp_5334_:
{
lean_object* v___x_5338_; 
if (v_isShared_5336_ == 0)
{
lean_ctor_set(v___x_5335_, 0, v_a_5327_);
v___x_5338_ = v___x_5335_;
goto v_reusejp_5337_;
}
else
{
lean_object* v_reuseFailAlloc_5339_; 
v_reuseFailAlloc_5339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5339_, 0, v_a_5327_);
v___x_5338_ = v_reuseFailAlloc_5339_;
goto v_reusejp_5337_;
}
v_reusejp_5337_:
{
return v___x_5338_;
}
}
}
}
}
else
{
lean_object* v_a_5344_; lean_object* v___x_5345_; lean_object* v___x_5346_; lean_object* v___x_5348_; uint8_t v_isShared_5349_; uint8_t v_isSharedCheck_5353_; 
v_a_5344_ = lean_ctor_get(v_r_5326_, 0);
lean_inc(v_a_5344_);
lean_dec_ref_known(v_r_5326_, 1);
v___x_5345_ = lean_box(0);
v___x_5346_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___lam__0(v___y_5299_, v_isExporting_5306_, v___x_5322_, v___x_5345_);
v_isSharedCheck_5353_ = !lean_is_exclusive(v___x_5346_);
if (v_isSharedCheck_5353_ == 0)
{
lean_object* v_unused_5354_; 
v_unused_5354_ = lean_ctor_get(v___x_5346_, 0);
lean_dec(v_unused_5354_);
v___x_5348_ = v___x_5346_;
v_isShared_5349_ = v_isSharedCheck_5353_;
goto v_resetjp_5347_;
}
else
{
lean_dec(v___x_5346_);
v___x_5348_ = lean_box(0);
v_isShared_5349_ = v_isSharedCheck_5353_;
goto v_resetjp_5347_;
}
v_resetjp_5347_:
{
lean_object* v___x_5351_; 
if (v_isShared_5349_ == 0)
{
lean_ctor_set_tag(v___x_5348_, 1);
lean_ctor_set(v___x_5348_, 0, v_a_5344_);
v___x_5351_ = v___x_5348_;
goto v_reusejp_5350_;
}
else
{
lean_object* v_reuseFailAlloc_5352_; 
v_reuseFailAlloc_5352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5352_, 0, v_a_5344_);
v___x_5351_ = v_reuseFailAlloc_5352_;
goto v_reusejp_5350_;
}
v_reusejp_5350_:
{
return v___x_5351_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg___boxed(lean_object* v_x_5360_, lean_object* v_isExporting_5361_, lean_object* v___y_5362_, lean_object* v___y_5363_, lean_object* v___y_5364_){
_start:
{
uint8_t v_isExporting_boxed_5365_; lean_object* v_res_5366_; 
v_isExporting_boxed_5365_ = lean_unbox(v_isExporting_5361_);
v_res_5366_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg(v_x_5360_, v_isExporting_boxed_5365_, v___y_5362_, v___y_5363_);
lean_dec(v___y_5363_);
lean_dec_ref(v___y_5362_);
return v_res_5366_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg(lean_object* v_x_5367_, uint8_t v_when_5368_, lean_object* v___y_5369_, lean_object* v___y_5370_){
_start:
{
if (v_when_5368_ == 0)
{
lean_object* v___x_5372_; 
lean_inc(v___y_5370_);
lean_inc_ref(v___y_5369_);
v___x_5372_ = lean_apply_3(v_x_5367_, v___y_5369_, v___y_5370_, lean_box(0));
return v___x_5372_;
}
else
{
uint8_t v___x_5373_; lean_object* v___x_5374_; 
v___x_5373_ = 0;
v___x_5374_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg(v_x_5367_, v___x_5373_, v___y_5369_, v___y_5370_);
return v___x_5374_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg___boxed(lean_object* v_x_5375_, lean_object* v_when_5376_, lean_object* v___y_5377_, lean_object* v___y_5378_, lean_object* v___y_5379_){
_start:
{
uint8_t v_when_boxed_5380_; lean_object* v_res_5381_; 
v_when_boxed_5380_ = lean_unbox(v_when_5376_);
v_res_5381_ = l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg(v_x_5375_, v_when_boxed_5380_, v___y_5377_, v___y_5378_);
lean_dec(v___y_5378_);
lean_dec_ref(v___y_5377_);
return v_res_5381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf(lean_object* v_fnNames_5382_, lean_object* v_numSectionVars_5383_, lean_object* v_e_5384_, lean_object* v_a_5385_, lean_object* v_a_5386_){
_start:
{
lean_object* v___f_5388_; lean_object* v___f_5389_; uint8_t v___x_5390_; lean_object* v___x_5391_; 
v___f_5388_ = ((lean_object*)(l_Lean_Core_betaReduce___closed__1));
v___f_5389_ = lean_alloc_closure((void*)(l_Lean_Meta_unfoldIfArgIsAppOf___lam__0___boxed), 7, 4);
lean_closure_set(v___f_5389_, 0, v_fnNames_5382_);
lean_closure_set(v___f_5389_, 1, v_numSectionVars_5383_);
lean_closure_set(v___f_5389_, 2, v_e_5384_);
lean_closure_set(v___f_5389_, 3, v___f_5388_);
v___x_5390_ = 1;
v___x_5391_ = l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg(v___f_5389_, v___x_5390_, v_a_5385_, v_a_5386_);
return v___x_5391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldIfArgIsAppOf___boxed(lean_object* v_fnNames_5392_, lean_object* v_numSectionVars_5393_, lean_object* v_e_5394_, lean_object* v_a_5395_, lean_object* v_a_5396_, lean_object* v_a_5397_){
_start:
{
lean_object* v_res_5398_; 
v_res_5398_ = l_Lean_Meta_unfoldIfArgIsAppOf(v_fnNames_5392_, v_numSectionVars_5393_, v_e_5394_, v_a_5395_, v_a_5396_);
lean_dec(v_a_5396_);
lean_dec_ref(v_a_5395_);
return v_res_5398_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2(lean_object* v_00_u03b1_5399_, lean_object* v_x_5400_, uint8_t v_isExporting_5401_, lean_object* v___y_5402_, lean_object* v___y_5403_){
_start:
{
lean_object* v___x_5405_; 
v___x_5405_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___redArg(v_x_5400_, v_isExporting_5401_, v___y_5402_, v___y_5403_);
return v___x_5405_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2___boxed(lean_object* v_00_u03b1_5406_, lean_object* v_x_5407_, lean_object* v_isExporting_5408_, lean_object* v___y_5409_, lean_object* v___y_5410_, lean_object* v___y_5411_){
_start:
{
uint8_t v_isExporting_boxed_5412_; lean_object* v_res_5413_; 
v_isExporting_boxed_5412_ = lean_unbox(v_isExporting_5408_);
v_res_5413_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2_spec__2(v_00_u03b1_5406_, v_x_5407_, v_isExporting_boxed_5412_, v___y_5409_, v___y_5410_);
lean_dec(v___y_5410_);
lean_dec_ref(v___y_5409_);
return v_res_5413_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2(lean_object* v_00_u03b1_5414_, lean_object* v_x_5415_, uint8_t v_when_5416_, lean_object* v___y_5417_, lean_object* v___y_5418_){
_start:
{
lean_object* v___x_5420_; 
v___x_5420_ = l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___redArg(v_x_5415_, v_when_5416_, v___y_5417_, v___y_5418_);
return v___x_5420_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2___boxed(lean_object* v_00_u03b1_5421_, lean_object* v_x_5422_, lean_object* v_when_5423_, lean_object* v___y_5424_, lean_object* v___y_5425_, lean_object* v___y_5426_){
_start:
{
uint8_t v_when_boxed_5427_; lean_object* v_res_5428_; 
v_when_boxed_5427_ = lean_unbox(v_when_5423_);
v_res_5428_ = l_Lean_withoutExporting___at___00Lean_Meta_unfoldIfArgIsAppOf_spec__2(v_00_u03b1_5421_, v_x_5422_, v_when_boxed_5427_, v___y_5424_, v___y_5425_);
lean_dec(v___y_5425_);
lean_dec_ref(v___y_5424_);
return v_res_5428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___lam__0(lean_object* v_x_5429_, lean_object* v___y_5430_, lean_object* v___y_5431_){
_start:
{
lean_object* v___x_5433_; lean_object* v___x_5434_; 
v___x_5433_ = ((lean_object*)(l_Lean_Core_betaReduce___lam__0___closed__0));
v___x_5434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5434_, 0, v___x_5433_);
return v___x_5434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___lam__0___boxed(lean_object* v_x_5435_, lean_object* v___y_5436_, lean_object* v___y_5437_, lean_object* v___y_5438_){
_start:
{
lean_object* v_res_5439_; 
v_res_5439_ = l_Lean_Meta_eraseInaccessibleAnnotations___lam__0(v_x_5435_, v___y_5436_, v___y_5437_);
lean_dec(v___y_5437_);
lean_dec_ref(v___y_5436_);
lean_dec_ref(v_x_5435_);
return v_res_5439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___lam__1(lean_object* v_e_5440_, lean_object* v___y_5441_, lean_object* v___y_5442_){
_start:
{
lean_object* v___y_5445_; lean_object* v___x_5448_; 
v___x_5448_ = l_Lean_inaccessible_x3f(v_e_5440_);
if (lean_obj_tag(v___x_5448_) == 1)
{
lean_object* v_val_5449_; 
lean_dec_ref(v_e_5440_);
v_val_5449_ = lean_ctor_get(v___x_5448_, 0);
lean_inc(v_val_5449_);
lean_dec_ref_known(v___x_5448_, 1);
v___y_5445_ = v_val_5449_;
goto v___jp_5444_;
}
else
{
lean_dec(v___x_5448_);
v___y_5445_ = v_e_5440_;
goto v___jp_5444_;
}
v___jp_5444_:
{
lean_object* v___x_5446_; lean_object* v___x_5447_; 
v___x_5446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5446_, 0, v___y_5445_);
v___x_5447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5447_, 0, v___x_5446_);
return v___x_5447_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___lam__1___boxed(lean_object* v_e_5450_, lean_object* v___y_5451_, lean_object* v___y_5452_, lean_object* v___y_5453_){
_start:
{
lean_object* v_res_5454_; 
v_res_5454_ = l_Lean_Meta_eraseInaccessibleAnnotations___lam__1(v_e_5450_, v___y_5451_, v___y_5452_);
lean_dec(v___y_5452_);
lean_dec_ref(v___y_5451_);
return v_res_5454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations(lean_object* v_e_5457_, lean_object* v_a_5458_, lean_object* v_a_5459_){
_start:
{
lean_object* v___f_5461_; lean_object* v___f_5462_; lean_object* v___x_5463_; 
v___f_5461_ = ((lean_object*)(l_Lean_Meta_eraseInaccessibleAnnotations___closed__0));
v___f_5462_ = ((lean_object*)(l_Lean_Meta_eraseInaccessibleAnnotations___closed__1));
v___x_5463_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_5457_, v___f_5461_, v___f_5462_, v_a_5458_, v_a_5459_);
return v___x_5463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___boxed(lean_object* v_e_5464_, lean_object* v_a_5465_, lean_object* v_a_5466_, lean_object* v_a_5467_){
_start:
{
lean_object* v_res_5468_; 
v_res_5468_ = l_Lean_Meta_eraseInaccessibleAnnotations(v_e_5464_, v_a_5465_, v_a_5466_);
lean_dec(v_a_5466_);
lean_dec_ref(v_a_5465_);
return v_res_5468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_erasePatternRefAnnotations___lam__1(lean_object* v_e_5469_, lean_object* v___y_5470_, lean_object* v___y_5471_){
_start:
{
lean_object* v___y_5474_; lean_object* v___x_5477_; 
v___x_5477_ = l_Lean_patternWithRef_x3f(v_e_5469_);
if (lean_obj_tag(v___x_5477_) == 1)
{
lean_object* v_val_5478_; lean_object* v_snd_5479_; 
lean_dec_ref(v_e_5469_);
v_val_5478_ = lean_ctor_get(v___x_5477_, 0);
lean_inc(v_val_5478_);
lean_dec_ref_known(v___x_5477_, 1);
v_snd_5479_ = lean_ctor_get(v_val_5478_, 1);
lean_inc(v_snd_5479_);
lean_dec(v_val_5478_);
v___y_5474_ = v_snd_5479_;
goto v___jp_5473_;
}
else
{
lean_dec(v___x_5477_);
v___y_5474_ = v_e_5469_;
goto v___jp_5473_;
}
v___jp_5473_:
{
lean_object* v___x_5475_; lean_object* v___x_5476_; 
v___x_5475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5475_, 0, v___y_5474_);
v___x_5476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5476_, 0, v___x_5475_);
return v___x_5476_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_erasePatternRefAnnotations___lam__1___boxed(lean_object* v_e_5480_, lean_object* v___y_5481_, lean_object* v___y_5482_, lean_object* v___y_5483_){
_start:
{
lean_object* v_res_5484_; 
v_res_5484_ = l_Lean_Meta_erasePatternRefAnnotations___lam__1(v_e_5480_, v___y_5481_, v___y_5482_);
lean_dec(v___y_5482_);
lean_dec_ref(v___y_5481_);
return v_res_5484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_erasePatternRefAnnotations(lean_object* v_e_5486_, lean_object* v_a_5487_, lean_object* v_a_5488_){
_start:
{
lean_object* v___f_5490_; lean_object* v___f_5491_; lean_object* v___x_5492_; 
v___f_5490_ = ((lean_object*)(l_Lean_Meta_eraseInaccessibleAnnotations___closed__0));
v___f_5491_ = ((lean_object*)(l_Lean_Meta_erasePatternRefAnnotations___closed__0));
v___x_5492_ = l_Lean_Core_transform___at___00Lean_Core_betaReduce_spec__0(v_e_5486_, v___f_5490_, v___f_5491_, v_a_5487_, v_a_5488_);
return v___x_5492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_erasePatternRefAnnotations___boxed(lean_object* v_e_5493_, lean_object* v_a_5494_, lean_object* v_a_5495_, lean_object* v_a_5496_){
_start:
{
lean_object* v_res_5497_; 
v_res_5497_ = l_Lean_Meta_erasePatternRefAnnotations(v_e_5493_, v_a_5494_, v_a_5495_);
lean_dec(v_a_5495_);
lean_dec_ref(v_a_5494_);
return v_res_5497_;
}
}
lean_object* runtime_initialize_Lean_Meta_FunInfo(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_RangeIterator(uint8_t builtin);
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
res = runtime_initialize_Init_Data_Range_Polymorphic_RangeIterator(builtin);
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
lean_object* initialize_Init_Data_Range_Polymorphic_RangeIterator(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Transform(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_FunInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_RangeIterator(builtin);
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
